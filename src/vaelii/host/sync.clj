;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.sync
  "Bring a KB's shipped contexts up to the running engine's.

  A KB stores the starter ontology it was built with, and the engine that opens it later
  ships its own: a strength marked `set/monotonic`, a vocabulary term added to core.txt, a
  disjointness the ontology stopped stating.  `sync!` makes the KB state what this engine
  ships, context by context, and leaves everything else alone.

  **What is shipped** is what `starter/load-into` produces, read off a scratch in-memory KB
  it is loaded into — not the text of the files.  The two differ: `genlCx` edges are stored
  in CxUniverse whichever file states them, and the closing `unary_predicate` batch is
  stated by no file.  Each premise is attributed to the load that stored it: CxUniverse
  for the upper ontology, the middle context for a middle file.

  **Which contexts are synced exactly**: CxUniverse and the `kb/middle/` contexts.  A
  premise there that the engine does not ship is retracted, a strength that differs is
  restated, and a missing one is asserted.  CxUniverse is locked to the files with two
  exceptions, which sync neither retracts nor restates: a `genlCx` premise, stored in
  CxUniverse whichever file or author states it, and a sentex that is not a premise (a
  lifted `decontextualized_predicate` copy, a rule firing).  An author's own context, wired
  below CxUniverse, is not one of them and is not read.

  **Only added to**: any other context a shipped file's content is stored in.

  **Only the layers a KB has.**  A middle file whose context holds nothing in the KB is
  not loaded into it.  The upper ontology is loaded only into a KB whose CxUniverse holds
  a premise the upper load ships, and the `unary_predicate` batch only into one that also
  holds a mark the batch ships.

  Comparison is by the form a KB file writes (`text/premise-entries`): a fact or rule
  under its strength wrapper, an `exceptWhen` as the wrapper it was asserted as.  A
  strength the engine **raised** is only an assertion, since `assert` raises a held
  premise's strength in place; one it **lowered** is the form retracted and the weaker one
  asserted, since nothing lowers a strength in place.

  **One batch.**  The sync is one `v/edit!`: the additions first, then the retractions,
  one settle.  So the belief a retraction would sweep and the addition rebuild keeps its
  witness through the batch, where retracting first tore the TMS down only to build it
  back up.  What cannot go in that order — a retraction of a record an addition lands on —
  goes before it (`sync!`).

  **Write-back** is the other direction: `write-back!` edits the shipped files to state
  what a KB's exact contexts gained and lost since a `held` reading, one line per
  premise.  The development browser runs it for the starter (docs/catalog.md)."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.seed :as seed]
            [vaelii.host.starter :as starter]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.kb :as kbi]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]))

(defn exact-contexts
  "The contexts `sync!` makes state exactly what the engine ships: CxUniverse and the
  middle layer's contexts, as discovered on the classpath."
  []
  (into [sx/root-context] (seed/layer-contexts "middle")))

(defn- edge?
  "Is `form` (a KB-file form, under its strength wrapper or not) a `genlCx` sentence?"
  [form]
  (let [[sentence _] (text/peel-form form)]
    (and (seq? sentence) (= 'genlCx (first sentence)))))

(defn- premise-records
  [kb ids]
  (let [recs (:records kb)]
    (into [] (keep #(p/get-sentex recs %)) ids)))

(defn premises
  "Every premise the starter stores, as `{:context c :form f :file ctx}`: the form a KB
  file writes it in, the context it is stored in, and the context of the load that stored
  it — CxUniverse for the upper ontology, `:unary-predicates` for the closing batch no
  file states.  In the order the
  load stored them, which is an order they assert in: the load retried what arrived
  before its dependencies.  Built in a scratch in-memory KB that is cleared before this
  returns."
  []
  (let [kb      (v/open-kb {:backend :memory :space [::shipped (random-uuid)] :recover? false})
        recs    (:records kb)
        seen    (volatile! #{})
        file-of (volatile! {})]
    (try
      (starter/load-into kb (fn [file]
                              (let [ids (set (p/premise-ids recs))]
                                (vswap! file-of into (map (fn [h] [h file])) (remove @seen ids))
                                (vreset! seen ids))))
      (let [[entries _] (text/premise-entries kb (premise-records kb (sort (p/premise-ids recs))))]
        (mapv (fn [{:keys [handles] :as e}]
                (-> e (dissoc :handles) (assoc :file (@file-of (first handles)))))
              entries))
      (finally
        (v/clear! kb)
        (v/close! kb)))))

(defn- held-forms
  "`{[context form] entry}` for the premises `kb` stores in `context`, less the `genlCx`
  premises in CxUniverse, which sync leaves as they are."
  [kb context]
  (let [[entries _] (text/premise-entries
                     kb (filterv #(some? (:strength %)) (v/sentexes-in-context kb context)))]
    (into {}
          (comp (remove #(and (= sx/root-context context) (edge? (:form %))))
                (map (fn [e] [[(:context e) (:form e)] e])))
          entries)))

(defn- stored?
  "Does `kb` hold `form` in `context` as a premise at least as strong as the form states?
  Asked by lookup, so a context holding a whole corpus is not read to answer it.  A form
  the lookup cannot take — a rule under its wrapper — reads as absent, and asserting it
  again is a no-op when it is there."
  [kb context form]
  (let [[sentence o] (text/peel-form form)
        h (try (v/handle-of kb sentence context) (catch clojure.lang.ExceptionInfo _ nil))
        have (some->> h (v/sentex kb) :strength)]
    (boolean (and have (or (= have :monotonic) (not= :monotonic (:strength o)))))))

(defn plan
  "What `sync!` would change in `kb`, without changing it:

    :add     `{:context :form}` the shipped content `kb` lacks, in the layers it has,
             in `premises`'s order
    :remove  `{:context :form :handles}` premises in an exact context the engine does not
             ship

  A premise the engine ships at a higher strength is an `:add` alone: asserting it raises
  the held one.  One it ships at a lower strength is a `:remove` and an `:add`.

  `shipped` defaults to a fresh `(premises)`."
  ([kb] (plan kb (premises)))
  ([kb shipped]
   (let [exact   (set (exact-contexts))
         root    sx/root-context
         ;; each layer belongs to a KB that holds some of it: the upper ontology to one
         ;; whose CxUniverse holds a premise it ships, and the closing batch, which a
         ;; vocabulary KB does not run, to one holding a mark the batch ships
         holds?  (fn [load] (some (fn [{:keys [context form file]}]
                                    (and (= load file) (= root context) (not (edge? form))
                                         (stored? kb context form)))
                                  shipped))
         upper?  (holds? root)
         present (into (cond-> #{}
                         upper?                                (conj root)
                         (and upper? (holds? :unary-predicates)) (conj :unary-predicates))
                       (filter #(and (not= root %) (pos? (v/count-in-context kb %))))
                       (distinct (filter symbol? (keep :file shipped))))
         ours    (into #{} (map (juxt :context :form)) shipped)
         held    (into {} (mapcat #(held-forms kb %)) (filter (every-pred exact present) exact))
         wanted  (filter #(present (:file %)) shipped)
         ;; a default premise of one record, shipped known-true: the `:add` raises it.
         ;; An exceptWhen is two records, and is restated whole.
         raised? (fn [{:keys [context form handles]}]
                   (and (= 1 (count handles))
                        (nil? (second (text/peel-form form)))
                        (contains? ours [context (list sx/strength-wrapper form)])))]
     {:add    (into []
                    (comp (remove (fn [{:keys [context form]}]
                                    (if (and (exact context) (not (edge? form)))
                                      (contains? held [context form])
                                      (stored? kb context form))))
                          (map #(select-keys % [:context :form])))
                    wanted)
      :remove (into [] (comp (remove (fn [[k _]] (ours k))) (map val) (remove raised?)) held)})))

(defn- add!
  "Assert every `{:context :form}` of `entries` into `kb`, retrying the refused ones while a
  round makes progress — a file's order is its terms', not its dependencies'
  (`text/load-entries!`).  Returns what is still refused, each with the refusal's `:type`
  and message, rather than throwing: a KB whose own content refuses a shipped sentence is
  a finding about that KB, and the rest of the sync still applies."
  [kb entries]
  (let [attempt (fn [es]
                  (reduce (fn [acc {:keys [context form] :as e}]
                            (let [[sentence o] (text/peel-form form)]
                              (try (v/assert kb sentence context (or o {})) acc
                                   (catch clojure.lang.ExceptionInfo ex
                                     (conj acc (assoc e :type (:type (ex-data ex))
                                                      :message (ex-message ex)))))))
                          [] es))]
    (v/with-deferred-settle kb
      (loop [pending (attempt entries)]
        (if (empty? pending)
          []
          (let [remaining (attempt (map #(select-keys % [:context :form]) pending))]
            (if (< (count remaining) (count pending))
              (recur remaining)
              remaining)))))))

(defn- records
  "The records asserting `form` lands on, each spelled without its strength: the sentence,
  or for an `exceptWhen` the wrapper and the rule it qualifies — a rule another form
  states too."
  [form]
  (let [[s _] (text/peel-form form)]
    (if (and (seq? s) (= sx/except-wrapper (first s)) (= 3 (count s)))
      (let [[_ q rule] s]
        #{(list sx/except-wrapper (first (text/peel-form q)) rule) rule})
      #{s})))

(defn- edit-entry
  "`{:context :form}` as a `v/edit!` `:add` line."
  [{:keys [context form]}]
  (let [[sentence o] (text/peel-form form)]
    (cond-> [sentence context] o (conj o))))

(defn- batch!
  "Assert `entries`, then retract `handles`, as one `v/edit!`: one settle.  The edit is
  all-or-nothing, so an entry it refuses rolls the batch back; that entry is set aside
  with its refusal's `:type` and message and the batch runs again without it.  Returns
  the entries set aside."
  [kb entries handles]
  (loop [entries (vec entries) aside []]
    (if (and (empty? entries) (empty? handles))
      aside
      (let [refused (try (v/edit! kb {:add (mapv edit-entry entries) :remove handles})
                         nil
                         (catch clojure.lang.ExceptionInfo ex
                           (let [{:keys [rolled-back in index] :as data} (ex-data ex)]
                             ;; a removal's refusal is the KB refusing writes: not an
                             ;; entry to set aside
                             (if (and rolled-back (= :add in))
                               {:index index :type (:type data) :message (ex-message ex)}
                               (throw ex)))))]
        (if-let [{:keys [index] :as r} refused]
          (recur (into (subvec entries 0 index) (subvec entries (inc index)))
                 (conj aside (merge (nth entries index) (dissoc r :index))))
          aside)))))

(defn sync!
  "Make `kb`'s shipped contexts state what this engine ships (see the namespace doc), as
  one `v/edit!`: the additions, then the retractions, one settle.  Returns

    {:added n :removed n :refused [{:context :form :type :message} …]}

  **A retraction goes first** only when an addition lands on a record it retracts: a
  strength the engine lowered, whose weaker form would otherwise be asserted onto the
  premise and then retracted with it, or an `exceptWhen` restated around a rule the KB
  keeps.  Those are their own `edit!` before the batch.

  **An addition the batch refuses is set aside**, the batch rolled back and run without
  it, so the rest lands in one settle.  The ones set aside are asserted after it,
  retrying while a round makes progress (`add!`): the batch's refusal can be an order the
  batch could not fix, or content its own retractions then took away.  What still refuses
  is `:refused`.  Each refusal costs the batch one rollback.

  `kb` must accept writes (`v/write-hazards` empty).  `ships` is `(premises)`, passed by a
  caller that syncs more than one KB or prices the sync apart from the scratch load."
  ([kb] (sync! kb (premises)))
  ([kb ships]
   (let [{adds :add removes :remove} (plan kb ships)
         landing  (into #{} (mapcat (fn [{:keys [context form]}]
                                      (map #(vector context %) (records form))))
                        adds)
         restated (fn [{:keys [context form]}] (some #(landing [context %]) (records form)))
         handles  (fn [es] (into [] (comp (mapcat :handles) (distinct)) es))
         before   (handles (filter restated removes))]
     (when (seq before)
       (v/edit! kb {:remove before}))
     (let [aside   (batch! kb adds (handles (remove restated removes)))
           refused (if (seq aside)
                     (add! kb (map #(select-keys % [:context :form]) aside))
                     [])]
       {:added   (- (count adds) (count refused))
        :removed (count removes)
        :refused refused}))))

;; ---- writing back ---------------------------------------------------------

(defn held
  "`{[context form] entry}` for every premise `kb` stores in the exact contexts, less the
  `genlCx` premises in CxUniverse: the reading two `write-back!` changes are diffed from."
  [kb]
  (into {} (mapcat #(held-forms kb %)) (exact-contexts)))

(defn context-files
  "The shipped files `context`'s premises are written in, as `java.io.File`s, the one a
  premise about no defined term is appended to first: core.txt and the other upper files
  for CxUniverse, `kb/middle/<context>.txt` for a middle context.  Nil where the layer is
  not a directory on the classpath."
  [context]
  (let [file (fn [path]
               (when-let [r (io/resource path)]
                 (when (= "file" (.getProtocol r)) (io/file r))))]
    (if (= sx/root-context context)
      (seq (keep #(file (str "kb/upper/" %)) (core-context/upper-files)))
      (some-> (file (str "kb/middle/" context ".txt")) vector))))

(defn- subject-terms
  "The terms a premise's line is placed by, in order: a rule's consequent's, a wrapped
  sentence's own, and a literal's first argument and then its functor."
  [sentence]
  (when (seq? sentence)
    (let [[f a b] sentence]
      (cond
        (#{'implies sx/except-wrapper} f)                         (subject-terms b)
        (= 'not f)                                                (subject-terms a)
        (and (symbol? f) (namespace f) (seq? a) (= 2 (count sentence))) (subject-terms a)
        :else (filter #(and (symbol? %) (not (sx/variable? %))) [a f])))))

(defn- blocks
  "`{term [file line]}`: for each `(comment term …)` in `files`, the last line of the
  forms from that comment to the next one.  The first file defining a term wins."
  [spans-of files]
  (reduce (fn [m [t at]] (if (contains? m t) m (assoc m t at)))
          {}
          (for [f files
                :let [ss     (spans-of f)
                      starts (keep-indexed (fn [i {:keys [form]}]
                                             (when (and (seq? form) (= 'comment (first form))) i))
                                           ss)]
                [i j] (map vector starts (concat (rest starts) [(count ss)]))]
            [(second (:form (nth ss i))) [f (:end (nth ss (dec j)))]])))

(defn- edit-file!
  "Apply `edits` to file `f`: `{:start :end :text}` replaces lines start..end with `text`
  (nil deletes them), `{:after line :text}` inserts `text` after `line` (`:end` after the
  last).  Lines are 1-based, and edits at one place keep their order."
  [^java.io.File f edits]
  (let [lines (str/split (slurp f) #"\n" -1)
        n     (cond-> (count lines) (= "" (peek lines)) dec)
        pos   (fn [{:keys [start after]}]
                (if start start (+ 0.5 (if (= :end after) n after))))
        out   (reduce (fn [v {:keys [start end after text] :as e}]
                        (if start
                          (into (subvec v 0 (dec start)) (concat (when text [text]) (subvec v end)))
                          (let [at (long (- (pos e) 0.5))
                                ls (if (= :end after) ["" text] [text])]
                            (into (subvec v 0 at) (concat ls (subvec v at))))))
                      lines
                      (sort-by (juxt pos :i) #(compare %2 %1)
                               (map-indexed #(assoc %2 :i %1) edits)))]
    (spit f (str/join "\n" out))))

(defn write-back!
  "Edit the shipped files to state `changes`, `{:add [entry …] :remove [entry …]}` of
  `{:context :form}` as `held` spells them, one line edit each:

    - a removal deletes the lines of the file form whose sentence matches, compared as
      `kb` stores it in the context, so variable names and antecedent order do not count;
    - a removal and an addition of one sentence rewrite that form in place: a strength
      change;
    - an addition is one line after the forms of the `(comment T …)` block of the first
      term it is about that a file defines (`subject-terms`), or appended to the
      context's first file when none is.

  Every other line stays, comments and order included.  `files-of` maps a context to its
  files and defaults to `context-files`.  Returns `{:written n :skipped [entry …]}`, a
  skipped entry being a removal no file states or one in a context with no file."
  ([kb changes] (write-back! kb changes context-files))
  ([kb {:keys [add remove]} files-of]
   (let [spans-of (memoize (fn [f] (text/form-spans f)))
         by-cx    (group-by :context (concat (map #(assoc % :op :add) add)
                                             (map #(assoc % :op :remove) remove)))
         plan     (for [[context es] by-cx]
                    (let [files (files-of context)
                          k     (memoize (fn [form]
                                           (let [[s _] (text/peel-form form)]
                                             (try (kbi/canonical-sentence kb s context)
                                                  (catch Exception _ s)))))
                          lines (for [f files, sp (spans-of f)] (assoc sp :file f))
                          line  (fn [form]
                                  (let [[s _] (text/peel-form form)]
                                    (or (first (filter #(= s (first (text/peel-form (:form %)))) lines))
                                        (first (filter #(= (k form) (k (:form %))) lines)))))
                          adds  (filter #(= :add (:op %)) es)
                          pair  (into {} (map (fn [a] [(k (:form a)) a])) adds)
                          rems  (for [r (filter #(= :remove (:op %)) es)]
                                  (assoc r :line (when files (line (:form r)))
                                         :into (pair (k (:form r)))))
                          taken (set (keep #(when (:line %) (:into %)) rems))
                          at    (when files (blocks spans-of files))]
                      {:skipped (if files (filterv (complement :line) rems) es)
                       :edits   (when files
                                  (concat
                                   (for [{:keys [line into]} rems :when line]
                                     {:file (:file line) :start (:start line) :end (:end line)
                                      :text (some-> into :form pr-str)})
                                   (for [a adds :when (not (taken a))
                                         :let [[s _] (text/peel-form (:form a))
                                               [f l] (or (some at (subject-terms s))
                                                         [(first files) :end])]]
                                     {:file f :after l :text (pr-str (:form a))})))}))
         edits    (mapcat :edits plan)]
     (doseq [[f es] (group-by :file edits)]
       (edit-file! f es))
     {:written (count edits)
      :skipped (into [] (comp (mapcat :skipped) (map #(dissoc % :op :line :into))) plan)})))
