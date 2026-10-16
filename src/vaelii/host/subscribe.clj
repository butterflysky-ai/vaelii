;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.subscribe
  "The change feed with a **cursor** where the in-process one has a callback — the
  daemon-side state a remote caller holds a feed open against.

  `core/watch` takes a function, and a function does not cross an EDN wire (the same
  wall `:export`'s `:on-progress` hits).  So the wire's half of the feed is not the
  callback marshalled somehow; it is the one thing a request/response protocol can
  carry, which is **state with a cursor**: the daemon registers an ordinary listener of
  its own, that listener files each event into a bounded ring, and a caller reads the
  ring forward from where it left off.  Three ops — register, read, drop — every one of
  them EDN in and EDN out, so the guards, the client and the error taxonomy that already
  exist carry it unchanged (docs/operations.md).

  **A cursor counts events, not handles.**  It starts at 0 when the subscription is
  registered and advances by one per delivered event, so a caller compares nothing and
  stores one integer.  `poll` answers the events past the cursor it was handed and the
  cursor to send next time.

  **The ring is bounded, and falling off it is said out loud.**  A subscriber that stops
  reading must not grow the daemon's heap, so the ring keeps `max-events` and drops the
  oldest past it — and the *count* of what it dropped is reported as `:lagged` on the
  next poll.  That number is the whole reason this is usable: a feed with a silent gap
  is strictly worse than polling, because the caller believes it is current and is not.
  `:lagged` is present on every reply, zero and all, so a client that forgets to read it
  is a client that cannot have one.

  **A token that names no subscription is refused, never answered empty.**  The same
  argument: a reaped, dropped or invented token answering `{:events []}` is a feed that
  has silently stopped.  `:unknown-subscription` says so.

  **What a subscription costs the daemon, and what bounds it.**  One listener on the
  KB's feed and one ring of at most `max-events` events; `max-subscriptions` of those at
  once, and one that nobody has polled inside `idle-ms` is reaped at the next call.
  Nothing here authenticates the caller — that is the bearer token's job, one layer out
  (`vaelii.host.serve`) — but heap a stranger can allocate wants a ceiling whether or
  not it is authenticated, and the reap is what keeps an abandoned subscription from
  holding a slot against a live one.

  **The wait happens here, outside the daemon's monitor.**  A long poll parks on the
  subscription's own signal object, so a writer serialized behind `serve`'s one monitor
  runs to completion while a poll is parked — the feature is about liveness, and a
  parked poll that blocked every writer would be a global stall wearing its name.  The
  writing thread's only cost is the swap that files the event and a `notifyAll` on a
  monitor no poller holds for longer than a compare.

  The three entry points are spelled without `!` for `core/watch`'s reason: nothing here
  destroys stored knowledge (docs/api.md).  See docs/feed.md, \"Across the wire\"."
  (:require [vaelii.core :as core]
            [vaelii.impl.opts :as opts]))

(def max-subscriptions
  "How many live subscriptions one daemon holds at once.  Reached, a further `watch` is
  refused (`:too-many-subscriptions`) rather than evicting somebody else's: a
  subscription silently dropped is the silent gap this whole namespace exists to
  refuse, and the caller that gets the refusal is the one that can still do something
  about it."
  64)

(def max-events
  "How many events one subscription's ring retains.  Past it the oldest goes and the
  drop is counted, so the depth is the slack a reader has between polls rather than a
  promise it cannot fall behind.  Reported by `watch`, since it is the number a poll
  interval is chosen against."
  256)

(def max-wait-ms
  "The longest a long poll parks before answering, whatever `:wait-ms` asks for.  A
  parked poll holds a server thread, so the ceiling is on the daemon's threads rather
  than on the caller's patience — a caller wanting to wait longer polls again, which
  costs it one round trip and costs the daemon nothing it was not already paying."
  30000)

(def max-parked
  "How many long polls may be **parked at once** on one daemon.

  A parked poll holds an HTTP worker thread for the length of its wait (the worker waits
  for the op's own thread, `serve/handle-op`), so the ceiling that matters here is the
  server's thread pool rather than anything this namespace owns:
  park more polls than the pool has threads and the daemon answers nothing at all —
  `/health`, a write, another caller's read — until one of them times out.  Moving the
  wait outside `serve`'s monitor is what keeps a parked poll from blocking the *writer*;
  it does nothing about the *threads*, and the two are separate ceilings.

  So this one is deliberately well under `vaelii.host.serve/http-threads`, and
  `serve_test` pins that relationship rather than trusting the two numbers to stay
  related.  Over it, a poll asking to wait is **refused** (`:too-many-waiters`) rather
  than parked: the caller is told to poll on a timer instead, which costs the daemon one
  request and no held thread, and is the same feed at a worse latency.  Answering it an
  immediate empty page would be the cheaper lie — the caller would see a long poll that
  never waits and a latency it has no way to explain."
  16)

(def idle-ms
  "How long a subscription survives with nobody polling it.  A client that goes away
  without saying so leaves a listener and a ring behind; without this they hold a slot
  against a live caller until the daemon restarts.  Reaped lazily, at the next `watch`
  or `poll`, so nothing here needs a thread of its own."
  300000)

(defn registry
  "The subscription state one daemon holds — `serve/app` builds one per handler, beside
  the monitor, because a token names a subscription *on this daemon* and means nothing
  anywhere else.

  `:next` is the token counter, monotone and never reissued, so a token from a dropped
  subscription is refused rather than landing on somebody else's — `feed/register!`'s
  reasoning one layer up.

  `:parked` is how many long polls are holding a thread right now — a property of the
  handler rather than of any one subscription, and the thing `max-parked` bounds.
  `:stopping` is set by `release-parked`, and a poll answers without parking once it is."
  []
  (atom {:next 0 :subs {} :parked 0 :stopping false}))

(defn- now [] (System/currentTimeMillis))

(defn- claim-park!
  "Take one of this daemon's parking permits; true when there was one to take.  Read off
  `max-parked` inside the swap rather than compared outside it, so two polls arriving
  together cannot both see the last permit."
  [reg]
  (let [[old new] (swap-vals! reg update :parked
                              #(if (< (long %) max-parked) (inc (long %)) %))]
    (not= (:parked old) (:parked new))))

(defn- release-park! [reg] (swap! reg update :parked #(max 0 (dec (long %)))))

(defn- push
  "File one event into a subscription's ring, dropping the oldest when it is full.  A
  `PersistentQueue` rather than a vector with the head sliced off: `subvec` retains the
  vector it was cut from, so a ring built that way holds every event it ever saw."
  [sub event]
  (let [q (conj (:events sub) event)]
    (assoc sub
           :events    (if (> (count q) max-events) (pop q) q)
           :delivered (inc (:delivered sub)))))

(defn- since
  "What a subscription owes a reader at `cursor`: the events past it, the cursor to send
  next, and how many were dropped before this one could read them.

  `:delivered` counts every event the subscription has ever been handed, so the oldest
  the ring still holds sits at `delivered - (count events)`.  A cursor below that is a
  reader the ring outran, and the difference is exactly what it missed."
  [sub cursor]
  (let [delivered (:delivered sub)
        oldest    (- delivered (count (:events sub)))]
    {:events (into [] (drop (- (max cursor oldest) oldest)) (:events sub))
     :cursor delivered
     :lagged (max 0 (- oldest cursor))}))

(defn- wake!
  "Wake whatever is parked on `sig`.  Held for the notify alone, so the writing thread
  filing an event waits at most for a poller's compare."
  [^Object sig]
  (when sig (locking sig (.notifyAll sig))))

(defn- file-event!
  "The listener `watch` registers: put the event in this subscription's ring and wake a
  parked poll.  Runs on the **writing** thread, inside the settle that caused it, so it
  is a swap and a notify and nothing else — docs/feed.md's warning that a slow listener
  slows the one writer applies to this one too, and the answer is that the remote
  listener is not this function, it is the poll that reads what this function left.

  A no-op for a token no longer registered: `unwatch` drops the entry and unregisters
  the listener, and the two are not one atomic step."
  [reg token sig event]
  (swap! reg (fn [r] (cond-> r
                       (get-in r [:subs token]) (update-in [:subs token] push event))))
  (wake! sig))

(defn- unregister!
  "Take `sub`'s listener off the KB it was registered on.  That KB is on the entry and
  not an argument: one registry can hold subscriptions over several KBs (the browser's
  serves whichever is active), and listener tokens are numbered per KB, so unregistering
  a token from another KB would take that KB's listener of the same number."
  [sub]
  (when-let [wt (:watch-token sub)]
    (core/unwatch (:watch-kb sub) wt)))

(defn- drop-where!
  "Drop every subscription `dead?` answers true for, unregistering each listener and waking
  a poll parked on it, and answer how many went.  The test and the removal are one swap,
  so a subscription is dropped, unregistered and woken by one caller only."
  [reg dead?]
  (let [[old new] (swap-vals! reg update :subs
                              #(into {} (remove (comp dead? val)) %))
        gone      (remove (:subs new) (keys (:subs old)))]
    (doseq [t gone
            :let [sub (get (:subs old) t)]]
      (unregister! sub)
      (wake! (:signal sub)))
    (count gone)))

(defn- reap
  "Drop the subscriptions nobody has polled inside `idle-ms`, unregistering each
  listener, and answer how many went.  Called at the head of `watch` and `poll`, which
  is every path that creates or renews one — so the cost is bounded by the traffic that
  causes it, and a daemon nobody talks to reaps nothing because there is nothing to
  reap."
  [reg at]
  (drop-where! reg (fn [sub] (> (- at (:polled-at sub)) idle-ms))))

(defn release-parked
  "Answer every long poll parked on `reg` now, with the events it has, and park none
  after it.  A daemon that stops calls this (`serve/stop-ops`): the op thread a parked
  poll runs on belongs to no server, so nothing else ends its wait before `max-wait-ms`."
  [reg]
  (swap! reg assoc :stopping true)
  (doseq [sub (vals (:subs @reg))]
    (wake! (:signal sub))))

(defn unwatch-kb
  "Drop every subscription over `kb` — the KB each was registered on, by identity — and
  answer how many went.  Each listener comes off `kb`, and a poll parked on one is woken
  and answers `:unknown-subscription`, as `unwatch` does.

  For a registry that serves several KBs when one of them is released: the browser calls
  this when `/kbs/unload` clears or closes a KB, so a client's feed over that KB is
  refused at its next poll rather than answering empty until the idle reap."
  [reg kb]
  (drop-where! reg (fn [sub] (identical? kb (:watch-kb sub)))))

(defn watch
  "Register a subscription over `kb` and answer `{:token :cursor :max-events}`.

  `goal` and `context` are `core/watch`'s, and nil for the whole feed — so a goal this
  engine cannot answer from a moved region is refused here by exactly the code that
  refuses it in process (`:not-watchable`), and the two cannot drift because there is
  only one check.

  **A context with no goal is refused**, and that one cannot be left to `core/watch`:
  its whole-feed arity takes no context at all, so a `[nil CxDeploy]` would register an
  unscoped listener while this registry stored `CxDeploy` and `subscriptions` reported
  it back — the daemon naming a scope it is not applying.  Scoping is the goal's
  (`core/watch` refuses a goal without one for the mirror-image reason), so a context
  arriving alone is a request this entry point cannot honour rather than one to drop.

  The entry lands in the registry **before** the listener is registered, so an event
  fired between the two has somewhere to go; a refused goal takes the entry back out
  again.  The token is read inside the swap that allocates it, so two concurrent
  registrations cannot be handed one."
  [reg kb goal context]
  (when (and (nil? goal) (some? context))
    (throw (ex-info (str "a whole-feed subscription is not scoped, and " (pr-str context)
                         " arrived with no goal for it to scope — watch with no"
                         " arguments for every belief change, or name a goal beside"
                         " the context.")
                    {:type :not-watchable :context context
                     :reason "a context scopes a goal, and this subscription has none"})))
  (let [at (now)
        _  (reap reg at)
        [old new]
        (swap-vals! reg
                    (fn [r]
                      (if (>= (count (:subs r)) max-subscriptions)
                        r
                        (let [t (:next r)]
                          (-> r
                              (assoc :next (inc t))
                              (assoc-in [:subs t]
                                        {:token     t :goal goal :context context
                                         :events    clojure.lang.PersistentQueue/EMPTY
                                         :delivered 0 :polled-at at
                                         :signal    (Object.)}))))))]
    (when (= (:next old) (:next new))
      (throw (ex-info (str "this daemon already holds " max-subscriptions
                           " feed subscriptions — unwatch one before opening another")
                      {:type :too-many-subscriptions
                       :max-subscriptions max-subscriptions})))
    (let [token (:next old)
          sig   (get-in new [:subs token :signal])
          f     (fn [event] (file-event! reg token sig event))
          wt    (try (if goal
                       (core/watch kb goal context f)
                       (core/watch kb f))
                     (catch Throwable t
                       (swap! reg update :subs dissoc token)
                       (throw t)))]
      ;; Guarded like `file-event!` and `poll`'s stamp, and for a sharper reason than
      ;; either: a bare `assoc-in` on a token that has gone **recreates** the entry, with
      ;; no `:polled-at`, `:events`, `:delivered` or `:signal` in it — and `reap` runs at
      ;; the head of every feed op, so the next one anywhere on this daemon reads
      ;; `(- at nil)` and throws.  One lost race would take the whole feed down until
      ;; restart, so the entry either survived and takes its token or the listener comes
      ;; straight back off the KB.
      (let [[old] (swap-vals! reg (fn [r] (cond-> r
                                            (get-in r [:subs token])
                                            (update-in [:subs token] assoc
                                                       :watch-token wt :watch-kb kb))))]
        (when-not (get-in old [:subs token])
          (core/unwatch kb wt)
          (throw (ex-info (str "feed subscription " (pr-str token)
                               " was dropped while it was being registered — watch again"
                               " to open one")
                          {:type :unknown-subscription :token token}))))
      {:token token :cursor 0 :max-events max-events})))

(def ^:private poll-opt-keys #{:wait-ms})

(defn- check-poll-opts!
  "Refuse an option `poll` does not read, and a `:wait-ms` that is not a duration.  The
  silent-default failure is a long poll that is not one: `{:wait-msec 20000}` read as no
  key at all answers instantly and forever, and the caller sees a feed that works beside
  a latency it has no way to explain."
  [opts]
  (opts/check! opts poll-opt-keys "poll")
  (when-let [w (:wait-ms opts)]
    ;; `nat-int?` rather than `number?`: a double admits `##NaN`, which coerces to 0 and
    ;; turns a long poll into one that answers instantly forever — the silent-default
    ;; failure this fn exists to refuse, wearing the right key.  It also admits `##Inf`
    ;; and a magnitude no long holds, which reached `long` below as an
    ;; `IllegalArgumentException` and answered **500** for a well-formed request.
    (when-not (nat-int? w)
      (throw (ex-info (str "poll :wait-ms must be a whole number of milliseconds,"
                           " got " (pr-str w))
                      {:type :unknown-option :mismatch :bad-value :options (vec (sort poll-opt-keys))})))))

(defn- park
  "Hold the calling thread until this subscription has an event past `cursor`, the
  subscription goes away, or `deadline` passes.

  The whole loop runs **inside** the monitor, and `file-event!` takes it to notify: the
  obvious spelling — read the registry, then wait — loses an event filed between the two
  and then answers empty for the full wait, which is the one failure a long poll must
  not have.  `.wait` releases the monitor while parked, so holding it here costs the
  writer a compare rather than the wait.

  `release-parked` ends the park the way the deadline does.  **So does an interrupt**,
  and it puts itself back: `.wait` clears the flag on its way out, so letting the
  exception travel would answer a 500, which the caller takes for the feed stopping, and
  would lose the interrupt for whoever owns the thread.  Returning instead answers the
  events it has, which is what a wait that ran out answers too."
  [reg token cursor ^Object sig deadline]
  (locking sig
    (loop []
      (let [r         @reg
            sub       (get-in r [:subs token])
            remaining (- deadline (now))]
        (when (and sub (not (:stopping r)) (<= (:delivered sub) cursor) (pos? remaining))
          (if (try (.wait sig (long remaining)) true
                   (catch InterruptedException _
                     (.interrupt (Thread/currentThread))
                     false))
            (recur)
            nil))))))

(defn poll
  "Read a subscription forward: the events past `cursor`, the cursor to send next time,
  and the number the ring dropped before this call could see them.

    (poll reg 3 17)                  => {:events [{…}] :cursor 19 :lagged 0}
    (poll reg 3 17 {:wait-ms 20000}) => the same, waiting for the first one

  `:wait-ms` is the long poll: park until an event arrives or the wait runs out, capped
  at `max-wait-ms`.  It buys the latency a feed is for while keeping one wire format and
  one content type; nothing about the reply changes, so a caller that does not want it
  omits the key and polls on a timer.

  Refused rather than answered empty: a `token` naming no live subscription
  (`:unknown-subscription` — dropped, timed out, or from another daemon), and a `cursor`
  that is not a whole number or that runs ahead of what the subscription has delivered
  (`:bad-cursor`).  Either of those answered `{:events []}` would be a feed that has
  stopped without saying so."
  ([reg token cursor] (poll reg token cursor nil))
  ([reg token cursor opts]
   (check-poll-opts! opts)
   (let [at  (now)
         _   (reap reg at)
         sub (or (get-in @reg [:subs token])
                 (throw (ex-info (str "no feed subscription " (pr-str token)
                                      " — it was dropped, it timed out, or it belongs"
                                      " to another daemon; watch again")
                                 {:type :unknown-subscription :token token})))]
     (when-not (nat-int? cursor)
       (throw (ex-info (str "a feed cursor is a whole number, got " (pr-str cursor))
                       {:type :bad-cursor :token token :cursor cursor})))
     (when (> cursor (:delivered sub))
       (throw (ex-info (str "feed cursor " cursor " is ahead of subscription "
                            (pr-str token) ", which has delivered " (:delivered sub))
                       {:type :bad-cursor :token token :cursor cursor
                        :delivered (:delivered sub)})))
     ;; stamped before the park as well as after it, so a wait that outlasts `idle-ms`
     ;; cannot have this subscription reaped out from under the thread parked on it
     (swap! reg (fn [r] (cond-> r
                          (get-in r [:subs token])
                          (assoc-in [:subs token :polled-at] at))))
     ;; `min` before `long`, not after: `:wait-ms` is a whole number with no upper bound
     ;; — the cap is applied here rather than refused above — so coercing first throws on
     ;; a magnitude no long holds, for a request the cap was going to answer in 30 s.
     (let [wait (long (min max-wait-ms (:wait-ms opts 0)))]
       ;; A permit is taken only when this poll would really block.  With events already
       ;; past the cursor, or with no wait asked for, `park` returns at once and holds no
       ;; thread worth counting — so an ordinary timer poll is never refused, whatever
       ;; the daemon is holding.
       (when (and (pos? wait) (<= (long (:delivered sub)) (long cursor)))
         (if (claim-park! reg)
           (try (park reg token cursor (:signal sub) (+ at wait))
                (finally (release-park! reg)))
           (throw (ex-info (str "this daemon already has " max-parked " long polls parked"
                                " — poll again without :wait-ms until one of them returns")
                           {:type :too-many-waiters :max-parked max-parked
                            :token token})))))
     (let [current (or (get-in @reg [:subs token])
                       (throw (ex-info (str "feed subscription " (pr-str token)
                                            " was dropped while this poll was waiting —"
                                            " watch again, and poll the new token from"
                                            " cursor 0")
                                       {:type :unknown-subscription :token token})))]
       (swap! reg (fn [r] (cond-> r
                            (get-in r [:subs token])
                            (assoc-in [:subs token :polled-at] (now)))))
       (since current cursor)))))

(defn unwatch
  "Drop the subscription `token` names and unregister its listener; true if there was
  one.  Idempotent, like `core/unwatch` — a token already dropped removes nothing and
  says so, and never lands on the next subscription because tokens are not reissued.

  A poll parked on it is woken rather than left to time out: it finds the subscription
  gone and answers `:unknown-subscription`, which is the true thing to tell a reader
  whose feed no longer exists."
  [reg token]
  (let [[old] (swap-vals! reg update :subs dissoc token)]
    (if-let [sub (get-in old [:subs token])]
      (do (unregister! sub)
          (wake! (:signal sub))
          true)
      false)))

(defn subscriptions
  "What this daemon is holding open, in token order: the goal and context each
  subscription watches, how far it has been delivered, and how many events are waiting
  on its ring.  The listener functions are left out for `core/watchers`' reason — a
  token is what the ops take, and a listener is not a value to compare.

  `:delivered` is how many events the subscription has been handed and `:pending` how
  many its ring still holds — neither is the *reader's* position, which lives on the
  client and is a thing this daemon has no way to know.  Together they are the read that
  answers \"is the caller keeping up\": a `:pending` sitting at `max-events` is a
  subscriber already dropping events.

  Reaps first, like the other three, so it answers what the daemon is holding rather
  than what it has not got round to letting go of — a listing naming a subscription the
  very next call would drop is a listing nobody can act on."
  [reg]
  (reap reg (now))
  (->> (vals (:subs @reg))
       (sort-by :token)
       (mapv (fn [s] (cond-> {:token     (:token s)
                              :delivered (:delivered s)
                              :pending   (count (:events s))}
                       (:goal s)    (assoc :goal (:goal s))
                       (:context s) (assoc :context (:context s)))))))
