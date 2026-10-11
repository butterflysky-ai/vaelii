;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.full-kb-test
  "Probes that read and write a full-size KB and hold each one to a ceiling, so a change
  whose cost grows with the corpus fails here rather than in front of a user.

  The suite's other tests run on KBs of a few thousand sentexes, where a write that walks
  the whole corpus costs the same as one that does not.  The class of regression this
  catches is that one: a guard, a closure walk or a check whose cost is a function of what
  the KB holds rather than of what the write names.  Each probe runs under the counting
  instrument (`vaelii.impl.profile`, the one `assert_cost_test` pins) and reports its
  index operations, record fetches and wall-clock milliseconds.  **A ceiling is a count
  first**: a count does not move with the machine's load, so it can sit close to what a
  probe costs today, and a walk of a full-size corpus lands orders of magnitude over it.
  The millisecond ceiling is the backstop for work no counted call sees, a taxonomy walk
  or a TMS relabel, and is set loose enough for a busy machine.

  ## Two halves

  `^:full-kb` tests open the KB named by `VAELII_FULL_KB_DIR` once per JVM and run every
  probe on it.  Nothing runs them for you: `lein test-full-kb` does
  (`scripts/test-full-kb.sh`), which brings the KB up to this engine and hands the test
  JVM a disposable clone of it.  The probes write into that clone.

  The unmarked twin runs the same probes on the starter plus a few facts, so the harness
  itself runs on every commit and a probe that stops finding its subject fails at
  `:default` rather than on the next full-KB run.  The twin holds no ceiling: on a starter
  KB every probe is cheap whatever the engine does.

  ## The probes

  In this order, in one test, since a write past its deadline leaves every write after
  it skipped — the `known-unbounded` probes last:

  * **reads** — up to `per-context` ground premises and as many ground derived literals
    from every context: each one the KB believes in its context, `ask` answers; and each
    binary one, asked with its second argument open, answers with that argument among the
    bindings.  The report names the costliest reads.
  * **a fact** — a corpus type applied to a new individual, in the corpus context that
    holds the type's sampled fact.
  * **a rule** — a new type concluding the corpus type, and its firing.
  * **retracting them** — in reverse; the corpus context holds what it held and the
    sampled corpus sentexes' belief is what it was.
  * **a corpus premise out and back** — a stored premise something rests on, retracted
    and reasserted under its own strength; what rested on it is believed as before.
  * **the spindle** — `sync-spindle!`, and a second one that finds nothing to do.
  * **a genl edge** — a new type made a spec of the corpus type, and retracted.
  * **a new context** — wired under that corpus context by a `genlCx` edge, the edge that
    reseeds visibility, and retracted."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.host.spindle :as spindle]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

;; ---- measuring ----------------------------------------------------------------

(def ^:private full-kb-ceilings
  "What each probe may cost on the full KB, as `{:ops n :ms n}`: about three times what it
  cost on the full KB it was set against (2026-09-27), so the ceiling is a baseline a change
  may not grow past rather than a statement of what a write ought to cost.  `:reads` is
  the costliest single read and `:reads-total` all of them; every other is per probe."
  {:reads         {:ops 6000    :ms 5000}
   :reads-total   {:ops 55000   :ms 30000}
   ;; the first write into a mapped index thaws the roots it touches: 73% of the
   ;; fact probe's wall time, an order of magnitude over the rule after it
   :fact          {:ops 220000  :ms 120000}
   :rule          {:ops 220000  :ms 30000}
   :teardown      {:ops 1600000 :ms 60000}
   :premise       {:ops 450000  :ms 30000}
   :spindle       {:ops 5000000 :ms 120000}
   :spindle-again {:ops 5000000 :ms 120000}
   :genl          {:ops 220000  :ms 60000}
   :context       {:ops 220000  :ms 60000}})

(def ^:private known-unbounded
  "Probes that outlive their deadline on the full KB today, and what was seen.  One still
  runs and reports its cost, and fails nothing: the suite catches a probe that grows, and
  one already past any ceiling cannot grow into a failure.  A probe that comes in under
  its ceiling says so, and leaves this map."
  {:spindle "the sync did not return by its deadline (2026-09-28): 95% of samples in the
             settle after its retractions, re-examining remembered clash pairs and the
             genl closures of their types"
   :genl    "a genl edge onto a corpus type did not return by its deadline (2026-09-27)"
   :context "a genlCx edge under a corpus context did not return by its deadline (2026-09-27)"})

(def ^:private known-slow-reads
  "Goals the read probe samples from the full KB whose `ask` is past any per-read ceiling
  today, and what was seen.  Each is still asked, answered and reported, and counts toward
  neither `:reads` ceiling."
  {'(artifact-result transformation_paradox-contraction)
   "past the per-read ceiling in one run, and further past it in the next (2026-09-27)"})

(def ^:dynamic ^:private *ceilings*
  "The ceilings `within?` and `measure` hold a probe to, or nil to hold it to none."
  full-kb-ceilings)

(defn- row-total [rows] (reduce + 0 (mapcat #(filter number? (vals %)) rows)))

(def ^:private wedged
  "The probe still running past its deadline, or nil.  A write that never returns holds
  the KB's writer, so every write probe after it is skipped rather than queued behind it."
  (atom nil))

(defn- frame-name
  "A stack frame as `ns/fn`, the compiled class name demunged."
  [^StackTraceElement f]
  (str (Compiler/demunge (.getClassName f)) " " (.getMethodName f) ":" (.getLineNumber f)))

(defn- engine-frames
  "The engine's own frames in `stack`, innermost first."
  [stack]
  (->> stack
       (map frame-name)
       (filter #(and (str/starts-with? % "vaelii.") (not (str/starts-with? % "vaelii.full-kb-test"))))))

(def ^:private sample-every-ms 100)
(def ^:private profile-after-ms
  "A probe running longer than this has its sampled frames printed."
  10000)
(def ^:private hottest 12)

(defn- print-profile!
  "The frames `samples` (one engine-frame list per sample) spent their time in: the frame
  each sample was executing, and every frame on the stack."
  [probe ms samples]
  (let [n (count samples)
        top (fn [fs] (take hottest (sort-by (comp - val) (frequencies fs))))]
    (println (format "\n%s after %,d ms, %d samples — executing:" (name probe) (long ms) n))
    (doseq [[f c] (top (keep first samples))]
      (println (format "  %5.1f%%  %s" (* 100.0 (/ c (max n 1))) f)))
    (println "  on the stack, less the frames every sample holds:")
    (doseq [[f c] (->> (frequencies (mapcat distinct samples))
                       (remove #(= n (val %)))
                       (sort-by (comp - val))
                       (take (* 2 hottest)))]
      (println (format "  %5.1f%%  %s" (* 100.0 (/ c (max n 1))) f)))
    (flush)))

(defn- measure
  "Run `f` under the counting instrument and return `[result cost]`, cost as `{:ms :ops}`:
  `:ops` is every index read, record fetch, index write and index retract the instrument
  counted.  The instrument is process-wide, so it is stopped whatever `f` does.

  `f` runs on its own thread, sampled every `sample-every-ms`: a probe past
  `profile-after-ms` prints where its time went, once a minute while it runs and once when
  it stops, so a run that hangs says where.

  Under a ceiling for `probe`, `f` has twice the ceiling's milliseconds to return.  Past
  that the probe is wedged: this throws and leaves `f` running on its daemon thread, since
  nothing interrupts a write safely."
  [probe f]
  (let [deadline (some-> *ceilings* (get probe) :ms (* 2))
        t0       (System/nanoTime)
        elapsed  #(/ (- (System/nanoTime) t0) 1e6)
        _        (when-not (= :reads probe)
                   (println (str (java.time.LocalTime/now) " " (name probe)))
                   (flush))
        _        (prof/start)
        out      (promise)
        run      (bound-fn [] (deliver out (try [:ok (f)] (catch Throwable t [:threw t]))))
        ;; a daemon, so a probe still running when the tests end does not hold the JVM
        ;; open: a `future`'s pool thread is not one, and kept a finished run alive
        th       (doto (Thread. ^Runnable run "full-kb-probe") (.setDaemon true) (.start))
        [k r samples]
        (loop [samples [] shown 0]
          (let [got (deref out sample-every-ms nil)
                ms  (elapsed)]
            (cond
              got                                  (conj got samples)
              (and deadline (> ms deadline))       [:ok ::late samples]
              :else
              (let [samples (conj samples (engine-frames (.getStackTrace ^Thread th)))
                    minute  (long (/ ms 60000))]
                (when (and (> ms profile-after-ms) (> minute shown))
                  (print-profile! probe ms samples))
                (recur samples (max shown minute))))))
        _        (when (> (elapsed) profile-after-ms) (print-profile! probe (elapsed) samples))
        _        (when (= :threw k) (prof/stop) (throw r))
        ms       (elapsed)
        snap     (prof/stop)]
    (when (= ::late r)
      ;; a read holds no writer, so one past its deadline stops nothing after it
      (when-not (= :reads probe) (reset! wedged probe))
      (throw (ex-info (str (name probe) " probe still running after " deadline " ms") {:probe probe})))
    [r {:ms  (Math/round (double ms))
        :ops (+ (reduce + 0 (vals (:reads snap)))
                (reduce + 0 (vals (:fetches snap)))
                (row-total (vals (:writes snap)))
                (row-total (vals (:retracts snap))))}]))

(defn- clear-to-write?
  "Whether no earlier probe is still writing, as a clojure.test assertion."
  []
  (let [w @wedged]
    (is (nil? w) (str "skipped: the " (some-> w name) " probe is still running"))
    (nil? w)))

(def ^:dynamic ^:private *report*
  "An atom the probes file their costs in, as `[probe cost]` pairs, or nil."
  nil)

(defn- file! [probe cost]
  (when *report* (swap! *report* conj [probe cost]))
  cost)

(defn- within?
  "Whether `cost` is under `probe`'s ceiling, as a clojure.test assertion — or, for a
  `known-unbounded` probe, a line saying whether it now is."
  [probe cost]
  (when-let [{:keys [ops ms]} (get *ceilings* probe)]
    (if (known-unbounded probe)
      (when (and (<= (:ops cost) ops) (<= (:ms cost) ms))
        (println (str "\n" (name probe) " came in under its ceiling: drop it from known-unbounded")))
      (do (is (<= (:ops cost) ops) (str (name probe) " cost " (:ops cost) " ops, ceiling " ops))
          (is (<= (:ms cost) ms) (str (name probe) " took " (:ms cost) " ms, ceiling " ms))))))

;; ---- the subjects -------------------------------------------------------------

(def ^:private per-context
  "How many premises, and how many derived sentences, the probes take from each context."
  4)

(defn- ground? [form]
  (not-any? #(and (symbol? %) (str/starts-with? (name %) "?")) (flatten (seq form))))

(defn- literals
  "Up to `per-context` ground stored literals from each context that are premises, and as
  many that are not, in context order.  Ground, which leaves out the `exceptWhen` metas:
  a literal in storage, a rule qualifier in meaning."
  [kb]
  (vec (for [c    (sort-by str (v/contexts kb))
             :let [ls (filter #(and (nil? (:antecedent %)) (ground? (:sentence %)))
                              (v/sentexes-in-context kb c))]
             s    (concat (take per-context (filter :strength ls))
                          (take per-context (remove :strength ls)))]
         s)))

(defn- named? [re x] (and (symbol? x) (nil? (namespace x)) (boolean (re-matches re (name x)))))
(def ^:private type-name? (partial named? #"[a-z][a-z0-9_]*"))
(def ^:private individual-name? #(and (named? #"[A-Z][A-Za-z0-9]*" %) (not (named? #"Cx[A-Z].*" %))))

(defn- about-an-individual?
  "Whether `sentence` is a literal whose first argument is an individual — corpus content,
  as against the vocabulary's declarations about its own terms."
  [sentence]
  (and (seq? sentence) (symbol? (first sentence)) (individual-name? (second sentence))))

(defn- typed-literal
  "A believed `(T x)` from `sample`, `T` a type and `x` an individual.  A function's name
  is spelled as an individual's, so `x` must not be a `relation` in its context."
  [kb sample]
  (first (filter (fn [{:keys [id sentence context]}]
                   (and (= 2 (count sentence))
                        (type-name? (first sentence))
                        (about-an-individual? sentence)
                        (not (v/isa? kb (second sentence) 'relation context))
                        (v/believed? kb id context)))
                 sample)))

(def ^:private most-dependents
  "The most sentences a probed premise may have resting on it: the probe prices one
  premise's round trip, and a premise half the corpus rests on prices the corpus."
  20)

(defn- supporting-premise
  "A premise about an individual from `sample` that at least one and at most
  `most-dependents` derived sentences rest on, with those sentences:
  `{:sentex s :dependents [[sentence context] …]}`."
  [kb sample]
  (first (for [{:keys [id sentence strength] :as s} sample
               :when (and strength (about-an-individual? sentence)
                          ;; counted off the network first: `dependent-justifications`
                          ;; fetches and sorts every one, and a corpus premise can have
                          ;; hundreds of thousands
                          (<= 1 (count (jtms/dependents (reasoning/tms kb) id)) most-dependents))
               :let [deps (->> (v/dependent-justifications kb id)
                               (keep #(some->> (:consequence %) (v/sentex kb)))
                               (map (juxt :sentence :context))
                               distinct)]
               :when (<= 1 (count deps) most-dependents)]
           {:sentex s :dependents (vec deps)})))

(defn- belief-of [kb pairs]
  (mapv (fn [[sentence context]]
          (when-let [h (v/handle-of kb sentence context)] (v/believed? kb h context)))
        pairs))

;; ---- the probes -----------------------------------------------------------------

(def ^:private costliest
  "How many of the costliest reads the report names."
  5)

(defn- probe-reads!
  "Every sampled literal the KB believes, `ask` answers, and a binary one answers with its
  second argument open, as one assertion over the sample: the sample follows the
  handles `sentexes-in-context` orders by and what the argument reading mints, so an
  assertion per member would move the suite's count with the configuration.  Files the
  costliest single read, and prints the `costliest` reads with their goals."
  [kb sample]
  (let [reads (atom [])
        slow  (atom [])
        read! (fn [goal context]
                (if-let [why (known-slow-reads goal)]
                  (let [t0 (System/nanoTime)
                        r  (vec (v/ask kb goal context))]
                    (swap! slow conj [(quot (- (System/nanoTime) t0) 1000000) goal context why])
                    r)
                  (let [[r cost] (measure :reads #(vec (v/ask kb goal context)))]
                    (swap! reads conj [cost goal context])
                    r)))]
    (is (= [] (vec (for [{:keys [id sentence context]} sample
                         :when (v/believed? kb id context)
                         :let [open (when (and (= 3 (count sentence)) (symbol? (first sentence)))
                                      (list (first sentence) (second sentence) '?x))]
                         miss [(when-not (seq (read! sentence context))
                                 (str "believed and not answered: " (pr-str sentence) " in " context))
                               (when (and open (not-any? #(= (nth sentence 2) (get % '?x))
                                                         (read! open context)))
                                 (str (pr-str open) " in " context " misses " (pr-str (nth sentence 2))))]
                         :when miss]
                     miss))))
    (doseq [[ms goal context why] @slow]
      (println (format "\nknown slow read, %,d ms: %s in %s — %s" ms (pr-str goal) context why)))
    (println (format "\n%d reads; the costliest:" (count @reads)))
    (doseq [[{:keys [ops ms]} goal context] (take costliest (sort-by (comp - :ops first) @reads))]
      (println (format "  %,12d ops %,8d ms  %s in %s" ops ms (pr-str goal) context)))
    (within? :reads-total (file! :reads-total (reduce #(merge-with + %1 (first %2)) {:ms 0 :ops 0} @reads)))
    (file! :reads (reduce #(merge-with max %1 (first %2)) {:ms 0 :ops 0} @reads))))

(defn- step!
  "Run one write under the instrument, file its cost and hold it to its ceiling.  A
  `known-unbounded` probe past its deadline is filed as `:wedged` and returns
  `::wedged`; any other is an error."
  [probe f]
  (try
    (let [[r cost] (measure probe f)]
      (file! probe cost)
      (within? probe cost)
      r)
    (catch clojure.lang.ExceptionInfo e
      (if (and (= probe (:probe (ex-data e))) (known-unbounded probe))
        (do (println (str "\n" (name probe) " is still running, as known: " (known-unbounded probe)))
            (file! probe :wedged)
            ::wedged)
        (throw e)))))

(defn- subject
  "The corpus type the write probes borrow and the context holding its sampled fact."
  [kb sample]
  (let [{t :sentence home :context :as s} (typed-literal kb sample)]
    (is s "no believed (T x) in the sample to borrow a type from")
    (when s
      (println (str "\nwrite probes borrow " (first t) " in " home))
      {:corpus-t (first t) :home home})))

(defn- probe-writes!
  "A fact and a forward rule borrowing a corpus type, written into the corpus context that
  holds it, and their retraction."
  [kb sample]
  (let [{:keys [corpus-t home] :as subj} (subject kb sample)
        [a b]  (repeatedly 2 #(tu/fresh-term :individual 'Probe))
        rk     (tu/fresh-term :type 'probe_kind)
        made   (atom [])
        assert! (fn [sentence] (let [h (v/assert kb sentence home)]
                                 (swap! made into (if (vector? h) h [h]))
                                 h))
        holds? (fn [sentence] (seq (v/ask kb sentence home)))]
    (when (and subj (clear-to-write?))
      (let [stored (v/count-in-context kb home)
            before (belief-of kb (map (juxt :sentence :context) sample))]
        (step! :fact #(assert! (list corpus-t a)))
        (is (holds? (list corpus-t a)))
        (assert! (list 'unary_predicate rk))
        (assert! (list rk b))
        (step! :rule #(assert! (list 'set/forwardRule (list 'implies (list rk '?x) (list corpus-t '?x)))))
        (is (holds? (list corpus-t b)) "the rule's firing")
        (step! :teardown #(doseq [h (rseq @made)] (v/retract! kb h)))
        (is (= stored (v/count-in-context kb home)) "the corpus context holds what it held")
        (is (= before (belief-of kb (map (juxt :sentence :context) sample)))
            "the sampled corpus belief moved across a write and its retraction")))))

(defn- probe-genl!
  "A new type made a spec of the corpus type, its reading, and the edge retracted."
  [kb sample]
  (let [{:keys [corpus-t home] :as subj} (subject kb sample)
        c  (tu/fresh-term :individual 'Probe)
        sk (tu/fresh-term :type 'probe_kind)]
    (when (and subj (clear-to-write?))
      (let [decl (v/assert kb (list 'unary_predicate sk) home)
            fact (v/assert kb (list sk c) home)
            edge (step! :genl #(v/assert kb (list 'genl sk corpus-t) home))]
        (when-not (= ::wedged edge)
          (is (seq (v/ask kb (list corpus-t c) home)) "the genl edge's reading")
          (doseq [h [edge fact decl]] (v/retract! kb h)))))))

(defn- probe-context!
  "A new context wired under a corpus context by a `genlCx` edge, and the edge retracted."
  [kb sample]
  (let [{home :context :as subj} (typed-literal kb sample)
        cx (tu/fresh-term :context 'CxFullKbProbe)]
    (when (and subj (clear-to-write?))
      (let [h (step! :context #(v/assert kb (list 'genlCx cx home) 'CxUniverse))]
        (when-not (= ::wedged h)
          (is (contains? (set (v/context-up kb cx)) home))
          (v/retract! kb h)
          (is (not (contains? (set (v/context-up kb cx)) home))))))))

(defn- probe-premise!
  "A corpus premise that something rests on, retracted and reasserted as its own form."
  [kb sample]
  (let [{:keys [sentex dependents]} (supporting-premise kb sample)]
    (is sentex "no premise in the sample that anything rests on")
    (when (and sentex (clear-to-write?))
      (let [[[entry]] (text/premise-entries kb [sentex])
            before    (belief-of kb dependents)
            [_ cost]  (measure :premise #(do (v/retract! kb (:id sentex))
                                             (v/assert kb (:form entry) (:context entry))))]
        (file! :premise cost)
        (within? :premise cost)
        (is (v/handle-of kb (:sentence sentex) (:context sentex)))
        (is (= before (belief-of kb dependents)))))))

(def ^:private shipped
  "What this engine ships, loaded once: a scratch KB's load, which the spindle probe would
  otherwise count as its own cost."
  (delay (spindle/shipped)))

(defn- probe-spindle!
  [kb]
  (when (clear-to-write?)
    (let [ships @shipped
          r     (step! :spindle #(spindle/sync-spindle! kb ships))]
      (when-not (= ::wedged r)
        (is (empty? (:refused r)) (str "the KB refused shipped sentences: " (pr-str (:refused r))))
        (is (= {:added 0 :removed 0 :refused []}
               (step! :spindle-again #(spindle/sync-spindle! kb ships)))
            "a second sync found work")))))

(defn- report!
  "Print the filed costs as one table, for the run's log."
  [rows]
  (println "\nfull-KB probe costs")
  (doseq [[probe cost] rows]
    (if (= :wedged cost)
      (println (format "  %-11s past its deadline" (name probe)))
      (println (format "  %-11s %,12d ops %,10d ms" (name probe) (:ops cost) (:ms cost))))))

;; ---- the full KB ----------------------------------------------------------------

(def ^:private full-kb
  "The KB under `VAELII_FULL_KB_DIR`, opened once, with what opening it cost."
  (delay
    (let [dir (System/getenv "VAELII_FULL_KB_DIR")]
      (when-not dir
        (throw (ex-info "VAELII_FULL_KB_DIR names no KB — run `lein test-full-kb`" {})))
      (let [t0 (System/nanoTime)
            kb (v/open-kb {:backend (v/store-backend dir) :dir dir :recover? :auto})]
        {:kb kb :dir dir :open-ms (quot (- (System/nanoTime) t0) 1000000)}))))

(defn- full [] (:kb @full-kb))

(deftest ^:full-kb the-full-kb-opens-writable
  (let [{:keys [kb dir open-ms]} @full-kb]
    (println (format "\nfull KB %s: %,d sentexes, opened in %,d ms" dir (v/sentex-count kb) open-ms))
    (is (= {} (v/write-hazards kb)))))

(def ^:private halt-grace-ms 60000)

(defn- halt-after-tests!
  "Halt the JVM `halt-grace-ms` from now, on a daemon thread.  A wedged probe holds the
  KB's writer, and the disk store's shutdown hook waits for that writer, so the exit the
  test runner makes after its summary never returns.  A halt skips the hooks; the KB is
  the run's disposable clone.  An exit that completes first takes the thread with it."
  []
  (println (str "\na probe is still running: the JVM halts " (quot halt-grace-ms 1000)
                " s from now if its exit has not returned"))
  (flush)
  (doto (Thread. ^Runnable (fn [] (Thread/sleep (long halt-grace-ms))
                             (.halt (Runtime/getRuntime) 1))
                 "full-kb-halt")
    (.setDaemon true)
    (.start)))

(deftest ^:full-kb the-full-kb-reads-and-writes-within-its-ceilings
  ;; one test, so the order is this one: the `known-unbounded` probes last, since a write
  ;; that outlives its deadline leaves every write after it skipped
  (let [kb (full) rows (atom [])]
    (try
      (binding [*report* rows]
        (let [sample (literals kb)]
          (is (seq sample))
          (within? :reads (probe-reads! kb sample))
          (probe-writes! kb sample)
          (probe-premise! kb sample)
          (probe-spindle! kb)
          (probe-genl! kb sample)
          (probe-context! kb sample)))
      (finally
        (report! @rows)
        (when @wedged (halt-after-tests!))))))

;; ---- the twin -------------------------------------------------------------------

(def ^:private twin-corpus
  "A corpus context under the spindle, with a type fact, a binary fact and a firing."
  '[[(genlCx CxFullKbTwin CxWell) CxUniverse]
    [(animal Rex) CxFullKbTwin]
    [(animal Tib) CxFullKbTwin]
    [(ancestorOf Tib Rex) CxFullKbTwin]])

(deftest the-full-kb-probes-find-their-subjects-on-a-small-kb
  (let [kb (doto (v/open-kb (assoc tu/starter-build-space :space [::full-kb :twin]))
             (tu/clear-kb!)
             (tu/load-starter!))]
    (try
      (doseq [[s c] twin-corpus] (v/assert kb s c))
      (binding [*ceilings* nil]
        (let [sample (literals kb)]
          (is (some? (typed-literal kb sample)) "no (T x) to borrow a type from")
          (is (some? (supporting-premise kb sample)) "no premise that something rests on")
          (probe-reads! kb sample)
          (probe-writes! kb sample)
          (probe-premise! kb sample)
          (probe-spindle! kb)
          (probe-genl! kb sample)
          (probe-context! kb sample)))
      (finally (tu/clear-kb! kb)))))
