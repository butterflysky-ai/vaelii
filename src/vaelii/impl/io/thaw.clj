;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.io.thaw
  "The class-name check on every nippy thaw the engine runs over a file.

  A frozen nippy value can **name a class** in three of its type ids, and reading one
  resolves that name and builds an instance of it: a record frame (`Class/forName`, then
  the static `create`), a deftype frame (`Class/forName`, then the first public
  constructor over the fields that follow), and a `Serializable` frame (an
  `ObjectInputStream` over the bytes that follow).  nippy 3.9.0 gates the third behind
  `*thaw-serializable-allowlist*` and the first two behind nothing at all.

  Every file the engine reads is **untrusted input** — a store directory or a dump
  arrives from wherever an operator copied it — so all three are gated here, and the
  gate is the tightest one there is:

  > **A vaelii frame never carries a class name.**

  That is already the export format's stated rule (`vaelii.impl.io.export`), and the
  disk codec writes a record's fields **positionally** for a size reason
  (`vaelii.impl.disk.codec`), so nothing the engine writes states a class either.  A
  frame that names one therefore came from somewhere else, and `allowed-classes` is
  empty: the name is refused (`:disallowed-class`) before the class is resolved.

  **The `Serializable` allowlist is pinned rather than inherited.**  nippy's default is
  a safe set, but it lives in a dynamic var an embedding application is invited to
  widen — nippy documents `allow-and-record-any-serializable-class-unsafe` for exactly
  that migration — and a host that widened it would widen the engine's file readers with
  it.  Binding it per read makes the entry point this namespace's rather than the host's.

  **How the first two are gated**, since nippy exposes no hook for them: the readers
  `taoensso.nippy.io` dispatches to are vars, and this namespace installs a checked
  reader in place of each.  A refusal is thrown from there, which is *before* nippy's own
  `try` — so it travels rather than becoming the `{:nippy/unthawable …}` placeholder a
  failed resolution otherwise reads as, and no class is loaded on the way.  The
  replacement calls straight through to the reader it replaced unless `with-guard` is in
  force, so a host application thawing its own records in this JVM is unaffected.

  **What holds that wrap to the release it was written against** is
  `pinned-nippy-version`: three internals are reached into here, and a bump that keeps
  their names while routing deserialization around them would narrow this entry point without
  reddening anything.  So the version is checked at load and the namespace refuses to
  come up against another one."
  (:require [clojure.java.io :as io]
            [taoensso.nippy :as nippy]
            [taoensso.nippy.io :as nippy-io]
            [vaelii.impl.sentex :as sx])
  (:import [it.unimi.dsi.fastutil.longs Long2ObjectOpenHashMap]))

(def allowed-classes
  "The class names a file the engine wrote may state — **none**.

  Measured rather than asserted: a store built on each of the four durable backends and
  a dump written in each variant and codec drive nippy's three class-name readers zero
  times.  A dump frame is a field map, a log frame is a positional vector, and every
  leaf a sentence may carry is a type nippy has an id for (`vaelii.impl.checks`'
  `check-encodable` refuses the rest at the public entry point).  So the allowlist is empty, and
  a name is a name this engine did not write.

  A set rather than `false` because the refusal names the class either way, and because
  a format that one day carried one would add it here and nowhere else."
  #{})

(def ^:dynamic *guarding*
  "Is a thaw inside `with-guard`?  The checked readers below stand in for nippy's own
  process-wide, so this is what keeps the gate the engine's own: false — a host
  application's thaw — calls straight through."
  false)

(defn- refuse-class!
  "Refuse the class name a frame states, naming it and which reader met it."
  [reader ^String class-name]
  (throw (ex-info (str "a frame names the class " class-name
                       " — a vaelii dump or store never carries a class name (its frames"
                       " are field maps and positional vectors), so this file was written"
                       " by something else, and resolving the name would load and"
                       " instantiate it")
                  {:type :disallowed-class :class class-name :reader reader
                   :allowed allowed-classes})))

(defn- serializable-allowed?
  "The predicate nippy's `Serializable` reader asks before it opens an
  `ObjectInputStream` over the bytes a frame carries.  A predicate rather than a set
  because nippy calls one directly (`taoensso.nippy.impl/serializable-allowed?`), which
  is what lets the refusal name the class here instead of arriving as a quarantined
  placeholder the caller has to go looking for."
  [class-name]
  (or (contains? allowed-classes class-name)
      (refuse-class! :serializable class-name)))

;; ---- the nippy release the three attachment points were read against -----

(def pinned-nippy-version
  "The nippy release this entry point was written against, and the whole of what keeps it from
  narrowing in silence.

  The gate reaches into three of nippy's **internals**: the vars
  `taoensso.nippy.io/read-record` and `taoensso.nippy.io/read-deftype`, wrapped in place
  below, and nippy's own call to `taoensso.nippy.impl/serializable-allowed?`, which is
  what lets a `Serializable` frame be refused by name rather than arrive as a placeholder.
  A bump that **renames or moves** any of them fails this namespace at load, and that is
  visible enough.  The failure this pin exists for is the quiet one: a bump that keeps the
  vars and stops routing a class name through them — a new reader path, an inlined call —
  wraps cleanly, evaluates green, and covers less than it did.  On a **deserialization
  trust boundary** \"the guard silently narrowed\" is the worst available outcome, so the
  version is asserted rather than assumed.

  **Moving this string is the ceremony, and the ceremony is the point.**  Whoever bumps
  nippy re-reads those three attachment points against the new release, confirms that
  every path resolving a class name still passes through them, and only then writes the
  new version here.  One line per upgrade buys a guard that cannot drift without a
  reader."
  "3.9.0")

(defn resolved-nippy-version
  "The nippy release actually on the classpath, or nil when it cannot be read.

  Off the artifact's own Maven descriptor, because nippy states its version nowhere a
  caller can read it — it asserts *encore*'s (`enc/assert-min-encore-version`) and exposes
  none of its own.  Every jar Maven builds carries
  `META-INF/maven/<group>/<artifact>/pom.properties`, and leiningen's uberjar keeps it
  (only signature files are excluded), so this reads the same string from a checkout and
  from the standalone jar."
  []
  (when-let [u (io/resource "META-INF/maven/com.taoensso/nippy/pom.properties")]
    (let [props (java.util.Properties.)]
      (with-open [in (io/input-stream u)] (.load props in))
      (.getProperty props "version"))))

(defn check-nippy-pin!
  "Refuse to go on unless the nippy on the classpath is `pinned`; the version agreed on,
  otherwise a throw, which fails this namespace and with it the build.

  This throws for two distinct reasons.  The descriptor is **unreadable**, so nothing is
  known about which nippy the wrap below is wrapping (`:nippy-version-unreadable`); or it
  is readable and names **another release** (`:nippy-version-moved`).  Both refuse,
  because a class-name check that cannot say which nippy release it is guarding checks
  nothing, and both messages say what the reader has to do next."
  [pinned]
  (let [found (resolved-nippy-version)]
    (cond
      (nil? found)
      (throw (ex-info (str "cannot read which nippy is on the classpath, so the class-name"
                           " entry point cannot say it is guarding the release it was written"
                           " against (" pinned ") — expected the artifact's own"
                           " META-INF/maven/com.taoensso/nippy/pom.properties")
                      {:type :nippy-version-unreadable :pinned pinned}))

      (not= pinned found)
      (throw (ex-info (str "nippy " found " is on the classpath and the class-name check was"
                           " written against " pinned " — re-read"
                           " taoensso.nippy.io/read-record,"
                           " taoensso.nippy.io/read-deftype and nippy's call to"
                           " taoensso.nippy.impl/serializable-allowed?, confirm that every"
                           " path resolving a class name still routes through them, then"
                           " move `pinned-nippy-version` to " found)
                      {:type :nippy-version-moved :pinned pinned :found found}))

      :else found)))

;; ---- the two readers nippy gates behind nothing --------------------------
;; Installed once, at load.  `defonce` on the originals, so reloading this namespace in
;; a REPL does not wrap a wrapper: what is captured the first time is nippy's own.

(defonce ^:private original-read-record  nippy-io/read-record)
(defonce ^:private original-read-deftype nippy-io/read-deftype)

;; Read by nothing: the value is the install having happened, and requiring this
;; namespace is what runs it.  `defonce` rather than a bare `do`, so a REPL reload
;; replaces neither reader.
#_{:clj-kondo/ignore [:unused-private-var]}
(defonce ^:private installed
  (do
    (check-nippy-pin! pinned-nippy-version)
    (alter-var-root #'nippy-io/read-record
                    (constantly
                     (fn [ibr class-name]
                       (when (and *guarding* (not (contains? allowed-classes class-name)))
                         (refuse-class! :record class-name))
                       (original-read-record ibr class-name))))
    (alter-var-root #'nippy-io/read-deftype
                    (constantly
                     (fn [ibr class-name legacy?]
                       (when (and *guarding* (not (contains? allowed-classes class-name)))
                         (refuse-class! :deftype class-name))
                       (original-read-deftype ibr class-name legacy?))))
    true))

(defmacro ^:private with-guard
  "Run `body` with the class-name check closed: the two checked readers armed, and the
  `Serializable` allowlist pinned to this namespace's.  One binding frame, so a caller
  that opens the entry point once for a run of frames pays one push and one pop."
  [& body]
  `(binding [*guarding*                          true
             nippy/*thaw-serializable-allowlist* serializable-allowed?]
     ~@body))

(defn- refusal
  "The `:disallowed-class` refusal in `t`'s cause chain, or nil.  `nippy/thaw` catches
  what a reader throws and re-throws it as its own \"Thaw failed\" `ex-info` with the
  original as the cause — a fair report of a *damaged* file and the wrong one for a
  refusal, which is a claim about the file's content and carries the class name in its
  `ex-data`.  So the chain is walked and the refusal raised as itself."
  [^Throwable t]
  (loop [^Throwable e t]
    (cond
      (nil? e)                                     nil
      (= :disallowed-class (:type (ex-data e)))    e
      :else                                        (recur (.getCause e)))))

(defn vm-error
  "The `VirtualMachineError` in `t`'s cause chain (an `OutOfMemoryError`, a
  `StackOverflowError`), or nil.  `nippy/thaw` wraps one as it wraps a refusal, and a
  caller that reads a wrapped one as a damaged file discards a sound one."
  ^VirtualMachineError [^Throwable t]
  (loop [^Throwable e t]
    (cond
      (nil? e)                          nil
      (instance? VirtualMachineError e) e
      :else                             (recur (.getCause e)))))

(defn guarded
  "Run `f` — a thunk that thaws — behind the entry point, raising a `:disallowed-class`
  refusal and a `VirtualMachineError` (`vm-error`) as themselves rather than as whatever
  wrapped them.

  The entry point for a caller reading **many** frames off one stream
  (`vaelii.impl.io.frames`): the entry point is opened once for the run instead of once per
  frame, which is one binding frame for ten thousand of them."
  [f]
  (try (with-guard (f))
       (catch Throwable t (throw (or (refusal t) (vm-error t) t)))))

(defn sharing
  "A `nippy/*thaw-xform*` under which a thaw keeps one object per value it repeats: each
  symbol a thawed collection holds, as an element, a map key or a map value, is the symbol
  pool's (`sentex/intern-sym`), and each `Long` is the first one this xform met with that
  value.  A thaw otherwise allocates a symbol and a box per occurrence, where the process
  that froze the value held one object shared by every structure naming it.  The `Long`
  pool belongs to the returned xform and lives as long as the caller holds it."
  []
  (let [boxes (Long2ObjectOpenHashMap.)
        one   (fn [x]
                (cond
                  (symbol? x)       (sx/intern-sym x)
                  (instance? Long x) (let [l (long x)]
                                       (or (.get boxes l) (do (.put boxes l x) x)))
                  :else             x))]
    (map (fn [x]
           (if (map-entry? x)
             (let [k (key x) v (val x) k' (one k) v' (one v)]
               (if (and (identical? k k') (identical? v v')) x (clojure.lang.MapEntry/create k' v')))
             (one x))))))

(defn thaw
  "`nippy/thaw` of `bs` behind the entry point, with nippy's `*thaw-xform*` bound to
  `xform` when given (`sharing`)."
  ([^bytes bs] (guarded (fn [] (nippy/thaw bs))))
  ([^bytes bs xform]
   (guarded (fn [] (binding [nippy/*thaw-xform* xform] (nippy/thaw bs))))))

(defn thaw-from-in!
  "`nippy/thaw-from-in!` from `in` behind the entry point, with `xform` as `thaw` takes
  it."
  ([^java.io.DataInput in] (guarded (fn [] (nippy/thaw-from-in! in))))
  ([^java.io.DataInput in xform]
   (guarded (fn [] (binding [nippy/*thaw-xform* xform] (nippy/thaw-from-in! in))))))
