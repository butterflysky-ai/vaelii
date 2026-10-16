;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.background-rebuild-test
  "`:recover? :background` over a `:disk-snapshot` store whose reasoning image was written
  under other engine source.  The open installs the image, and the KB answers from it and
  refuses writes.  Belief is rebuilt under this build on a second KB over the same stores,
  and one `vreset!` then replaces the installed belief with the rebuilt one; a read view
  taken before it reads the installed belief whole.  A close or a `recover` during the
  rebuild stops the rebuild first.  `:recover? :trust` installs the same image and keeps
  it: no rebuild, writes accepted at once, and the image's source stamp kept at close."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.recovery :as recovery]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]
           [java.util.concurrent CountDownLatch TimeUnit]
           [vaelii.impl.types.kb KB]
           [vaelii.impl.types.reasoning Reasoning]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-rebuild-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (io/file dir)))] (.delete ^File f)))

(defn- manifest ^File [dir] (io/file dir "reasoning" "manifest.edn"))

(defn- stamp [dir] (edn/read-string (slurp (manifest dir))))

(defn- restamp! [dir k v] (spit (manifest dir) (pr-str (assoc (stamp dir) k v))))

(defn- store!
  "A closed `:disk-snapshot` store holding a taxonomy edge and a membership, whose image
  is stamped as written under the engine source \"stale\"."
  ^String []
  (let [dir (tmpdir)
        kb  (v/open-kb {:backend :disk-snapshot :dir dir})]
    (v/assert kb '(genl dog animal) 'CxUniverse {:strength :monotonic})
    (v/assert kb '(dog Rex) 'CxUniverse)
    (v/close! kb)
    (restamp! dir :source "stale")
    dir))

(defn- dogs [kb] (mapv v/sentence-of (v/sentexes-matching kb '(dog ?x) 'CxUniverse)))

(defn- open-held
  "Open `dir` under `:recover? :background` with the rebuild held before its install until
  `release` counts down or the rebuild is asked to stop.  Returns `[kb reached release]`;
  `reached` counts down when the rebuild arrives at the hold."
  [dir]
  (let [reached (CountDownLatch. 1)
        release (CountDownLatch. 1)
        kb      (binding [recovery/*before-install*
                          (fn [_]
                            (.countDown reached)
                            (loop [i 0]
                              (when (and (pos? (.getCount release))
                                         (not (recovery/abandoning?))
                                         (< i 6000))
                                (Thread/sleep 5)
                                (recur (inc i)))))]
                  (v/open-kb {:backend :disk-snapshot :dir dir :recover? :background}))]
    [kb reached release]))

(defn- await-rebuilt
  "Wait up to 30 s for `kb`'s rebuilt belief to be installed; true when it was."
  [kb]
  (loop [i 0]
    (cond
      (empty? (kb/write-hazards kb)) true
      (< i 3000)                     (do (Thread/sleep 10) (recur (inc i)))
      :else                          false)))

(deftest every-kb-field-is-shared-owned-or-the-belief-a-rebuild-makes-new
  (tu/with-snapshot-platform
    (let [dir (store!)
          kb  (v/open-kb {:backend :disk-snapshot :dir dir})]
      (try
        (let [shared (set kb/rebuild-shared)
              own    (set kb/rebuild-own)
              fields (into (set (map keyword (KB/getBasis))) (keys kb))]
          (is (= fields (conj (set/union shared own) :reasoning))
              "a KB field other than `:reasoning` must be named in `kb/rebuild-shared` or `kb/rebuild-own`")
          (is (empty? (set/intersection shared own)))
          (is (not-any? #{:reasoning} (set/union shared own)))
          (is (= (set (map keyword (Reasoning/getBasis))) (set (keys (reasoning/of kb))))
              "`kb/empty-reasoning` makes exactly the `Reasoning` fields")
          (is (not-any? nil? (vals (reasoning/of kb))) "and fills every one")
          (let [r (kb/rebuild-kb kb)]
            (doseq [f shared]
              (is (identical? (get kb f) (get r f)) (str f " is shared with the rebuild KB")))
            (doseq [f own]
              (is (or (nil? (get r f)) (not (identical? (get kb f) (get r f))))
                  (str f " is not shared with the rebuild KB")))
            (doseq [[f x] (reasoning/of r)]
              (is (not (identical? x (get (reasoning/of kb) f)))
                  (str f " is the rebuild KB's own")))))
        (finally (v/close! kb) (rm-rf! dir))))))

(deftest no-source-reads-a-belief-field-off-the-kb-by-keyword
  ;; The KB record has no `Reasoning` field, so a keyword read of one off a KB answers nil and
  ;; fails nowhere at compile time.  The readers in `vaelii.impl.types.reasoning` are the way
  ;; in, and this scans the tree for the keyword read.
  (let [re   (re-pattern (str "\\(:(" (str/join "|" (map name (Reasoning/getBasis)))
                              ") (kb|kb#|kb1|kb2|ref-kb)\\)"))
        hits (for [dir      ["src" "test" "bench"]
                   ^File f  (file-seq (io/file dir))
                   :when    (str/ends-with? (.getName f) ".clj")
                   [i line] (map-indexed vector (str/split-lines (slurp f)))
                   :when    (re-find re line)]
               (str (.getPath f) ":" (inc i)))]
    (is (empty? hits) "read a `Reasoning` field through `vaelii.impl.types.reasoning`")))

(def ^:private unviewed
  "The public fns taking a KB first that are neither writes nor reads run against
  `kb/read-view`.  `close!` stops the rebuild and releases the KB's own directory.
  `with-deferred-settle` is a macro.  `seal` writes the images of a KB with an operation
  log, which a KB rebuilding behind an image never carries.  The rest read or set
  subscriptions, caches, statistics or hazards rather than belief, or open another KB."
  #{#'v/close! #'v/with-deferred-settle #'v/watch #'v/unwatch #'v/watchers #'v/caches
    #'v/clear-caches #'v/reset-settle-stats! #'v/write-hazards #'v/rebuild-progress
    #'v/fork #'v/load-foreign! #'v/seal})

(deftest every-public-fn-taking-a-kb-is-a-write-a-viewed-read-or-unviewed
  (let [takes-kb? (fn [v] (let [as (:arglists (meta v))]
                            (and (seq as) (every? #(= 'kb (first %)) as))))
        kb-fns    (set (filter takes-kb? (vals (ns-publics 'vaelii.core))))
        writes    (set (keys @#'v/write-ops))
        reads     (set (map #(ns-resolve 'vaelii.core (symbol (name %))) @#'v/read-ops))]
    (is (= kb-fns (set/union writes reads unviewed))
        "a public fn taking a KB first must be in `write-ops`, `read-ops` or `unviewed`")
    (is (empty? (set/intersection writes reads)))
    (is (empty? (set/intersection writes unviewed)))
    (is (empty? (set/intersection reads unviewed)))
    (is (not-any? #(:macro (meta %)) reads) "a macro cannot be wrapped as a read")))

(deftest a-read-view-taken-before-the-install-reads-the-installed-belief-whole
  (tu/with-snapshot-platform
    ;; The install is one `vreset!`, so the read it has to get right is one that takes the
    ;; network before the install and the taxonomy after it.  The view here is taken before
    ;; the install and read after it.
    (let [dir (store!)
          [kb ^CountDownLatch reached ^CountDownLatch release] (open-held dir)]
      (try
        (is (.await reached 30 TimeUnit/SECONDS) "the rebuild reaches its install")
        (let [rex     (v/handle-of kb '(dog Rex) 'CxUniverse)
              ;; each half of a reading shows which belief it came from
              reading (fn [k] [(jtms/in? (reasoning/tms k) rex)
                               (contains? (set (tax/genls-global (reasoning/taxonomy k) 'dog)) 'ghost)])]
          ;; move the installed belief away from what the records say, in the network and in
          ;; the taxonomy, so the rebuilt belief differs from it in both
          (jtms/suspend-premise (reasoning/tms kb) rex)
          (tax/add-genl (reasoning/taxonomy kb) 'dog 'ghost 999999)
          (is (= [false true] (reading kb)))
          (let [view (kb/read-view kb)]
            (is (not (identical? kb view)) "while the install is pending, a view is a copy")
            (.countDown release)
            (is (await-rebuilt kb) "the rebuilt belief is installed within 30 s")
            (is (= [true false] (reading kb)) "the KB reads the rebuilt belief")
            (is (= [false true] (reading view)) "the view reads the installed belief, both halves")
            (is (identical? kb (kb/read-view kb)) "with no install pending, the view is the KB")
            (is (= ['(dog Rex)] (dogs kb)) "and a public read reads the rebuilt belief")))
        (finally
          (.countDown release)
          (v/close! kb)
          (rm-rf! dir))))))

(deftest a-stale-image-answers-while-belief-is-rebuilt-behind-it
  (tu/with-snapshot-platform
    (let [dir (store!)
          [kb ^CountDownLatch reached ^CountDownLatch release] (open-held dir)]
      (try
        (is (.await reached 30 TimeUnit/SECONDS) "the rebuild reaches its install")
        (testing "the installed image answers, and writes are refused"
          (is (= ['(dog Rex)] (dogs kb)))
          (is (= {:stale-belief true} (kb/write-hazards kb)))
          (let [e (try (v/assert kb '(dog Fido) 'CxUniverse) nil
                       (catch clojure.lang.ExceptionInfo e e))]
            (is (= :unrecovered-kb (:type (ex-data e))))
            (is (= [:stale-belief] (:hazards (ex-data e)))))
          (is (thrown? clojure.lang.ExceptionInfo
                       (binding [v/*write-unrecovered?* true]
                         (v/assert kb '(dog Fido) 'CxUniverse)))
              "*write-unrecovered?* does not open a KB whose belief is being rebuilt")
          (is (= "stale" (:source (stamp dir))) "the image is not rewritten before the install"))
        ;; move the installed belief away from what the records say, so the install shows
        (jtms/suspend-premise (reasoning/tms kb) (v/handle-of kb '(dog Rex) 'CxUniverse))
        (is (= [] (dogs kb)))
        (.countDown release)
        (is (await-rebuilt kb) "the rebuilt belief is installed within 30 s")
        (testing "the rebuilt belief replaces the installed belief, and writes are accepted"
          (is (= ['(dog Rex)] (dogs kb)))
          (is (not= "stale" (:source (stamp dir))) "the rebuild writes an image under this build")
          (is (some? (v/assert kb '(dog Fido) 'CxUniverse))))
        (finally
          (.countDown release)
          (v/close! kb)
          (rm-rf! dir))))))

(deftest a-rebuild-reports-its-step-against-the-recover-the-image-records
  (tu/with-snapshot-platform
    (let [dir (store!)
          _   (restamp! dir :recover {:ms 600 :steps {:network 100 :taxonomy 100 :depths 100
                                                      :rosters 100 :settle 100 :refusals 100}})
          [kb ^CountDownLatch reached ^CountDownLatch release] (open-held dir)]
      (try
        (is (.await reached 30 TimeUnit/SECONDS) "the rebuild reaches its install")
        (let [p (v/rebuild-progress kb)]
          (is (= [6 8 "re-recording refusals"] ((juxt :step :of :label) p))
              "held before its install, the rebuild is at the recover's last step")
          (is (= "stale" (get-in p [:image :source])))
          (is (string? (get-in p [:image :written-at])))
          (is (not= "stale" (:source p)) "the running build's digest is reported beside it")
          (is (nat-int? (:elapsed-ms p)))
          (is (= 600 (:expected-ms p)))
          (is (<= (/ 5.0 6.0) (:fraction p) 1.0)
              "five of the six recorded steps are done, and the sixth is running"))
        (.countDown release)
        (is (await-rebuilt kb) "the rebuilt belief is installed within 30 s")
        (is (nil? (v/rebuild-progress kb)) "no rebuild runs once the rebuilt belief is installed")
        (is (= #{:network :taxonomy :depths :rosters :settle :refusals}
               (set (keys (:steps (:recover (stamp dir))))))
            "the image the rebuild writes records the step timings of its recover")
        (finally
          (.countDown release)
          (v/close! kb)
          (rm-rf! dir))))))

(defn- await-failed
  "Wait up to 30 s for `kb`'s rebuild to report `:failed`; its progress then, or at the
  timeout."
  [kb]
  (loop [i 0]
    (let [p (v/rebuild-progress kb)]
      (if (or (:failed p) (>= i 3000)) p (do (Thread/sleep 10) (recur (inc i)))))))

(deftest a-rebuild-that-throws-is-reported-until-recover-replaces-it
  (tu/with-snapshot-platform
    ;; A failure read as "no rebuild runs" would leave a caller polling progress with a KB
    ;; that refuses writes for no reason it can see.
    (let [dir    (store!)
          logged (atom [])
          kb     (binding [recovery/*before-install*
                           (fn [_] (throw (ex-info "injected rebuild failure" {})))
                           trove/*log-fn*
                           (fn [_ns _coords level id _payload]
                             (when (= :error level) (swap! logged conj id)))]
                   (v/open-kb {:backend :disk-snapshot :dir dir :recover? :background}))]
      (try
        (let [p (await-failed kb)]
          (testing "progress reports the throw, the step it was in, and a stopped clock"
            (is (= "injected rebuild failure" (get-in p [:failed :message])))
            (is (= "clojure.lang.ExceptionInfo" (get-in p [:failed :class])))
            (is (= [6 8 "re-recording refusals"] ((juxt :step :of :label) p)))
            (is (= (:elapsed-ms p) (:elapsed-ms (v/rebuild-progress kb)))
                "a failed rebuild's elapsed time does not grow"))
          (is (= [::recovery/belief-rebuild-failed] @logged) "the throw is logged at :error"))
        (testing "the image still answers, and writes are still refused"
          (is (= {:stale-belief true} (kb/write-hazards kb)))
          (is (= ['(dog Rex)] (dogs kb)))
          (is (= :unrecovered-kb
                 (:type (ex-data (try (v/assert kb '(dog Fido) 'CxUniverse) nil
                                      (catch clojure.lang.ExceptionInfo e e)))))))
        (testing "recover rebuilds on the calling thread and clears the report"
          (v/recover kb)
          (is (nil? (v/rebuild-progress kb)))
          (is (= {} (kb/write-hazards kb)))
          (is (not= "stale" (:source (stamp dir))))
          (is (some? (v/assert kb '(dog Fido) 'CxUniverse))))
        (finally
          (v/close! kb)
          (rm-rf! dir))))))

(deftest a-background-rebuild-writes-no-record-and-fails-naming-recover
  (tu/with-snapshot-platform
    ;; The rule is stored unchained, so the store holds no `(pet Rex)`, and a recover's
    ;; re-fire of the rules that can refuse places it.  A rebuild on its own thread writes
    ;; neither the shared record store nor the shared index a caller's read walks.
    (let [dir (tmpdir)
          kb0 (v/open-kb {:backend :disk-snapshot :dir dir})
          _   (v/assert kb0 '(dog Rex) 'CxUniverse)
          _   (v/assert kb0 '(set/forwardRule (implies (and (dog ?x) (unknown (cat ?x))) (pet ?x)))
                        'CxUniverse
                        {:chain? false})
          pets   (fn [kb] (mapv v/sentence-of (v/sentexes-matching kb '(pet ?x) 'CxUniverse)))
          counts (fn [kb] [(count (p/sentex-ids (:records kb)))
                           (count (p/justification-ids (:records kb)))])
          stored (counts kb0)]
      (is (= [] (pets kb0)) "the unchained rule placed nothing")
      (v/close! kb0)
      (restamp! dir :source "stale")
      (let [logged (atom [])
            kb     (binding [trove/*log-fn* (fn [_ns _coords level id _payload]
                                              (when (= :error level) (swap! logged conj id)))]
                     (v/open-kb {:backend :disk-snapshot :dir dir :recover? :background}))]
        (try
          (let [p (await-failed kb)]
            (is (= "clojure.lang.ExceptionInfo" (get-in p [:failed :class])))
            (is (str/includes? (str (get-in p [:failed :message])) "(recover kb)")
                "the failure names the call that rebuilds on the calling thread"))
          (is (= [::recovery/belief-rebuild-failed] @logged))
          (is (= stored (counts kb)) "the rebuild wrote no sentex and no justification")
          (is (nil? (v/handle-of kb '(pet Rex) 'CxUniverse)) "and no index posting")
          (is (= {:stale-belief true} (kb/write-hazards kb)))
          (v/recover kb)
          (is (= {} (kb/write-hazards kb)))
          (is (= ['(pet Rex)] (pets kb)) "recover on the calling thread places the conclusion")
          (finally
            (v/close! kb)
            (rm-rf! dir)))))))

(deftest a-close-during-the-rebuild-stops-it-and-the-next-open-recovers
  (tu/with-snapshot-platform
    (let [dir (store!)
          [kb ^CountDownLatch reached ^CountDownLatch release] (open-held dir)]
      (try
        (is (.await reached 30 TimeUnit/SECONDS))
        (v/close! kb)
        (is (= "stale" (:source (stamp dir))) "a stopped rebuild installs nothing and writes no image")
        (let [kb2 (v/open-kb {:backend :disk-snapshot :dir dir})]
          (try
            (is (= {} (kb/write-hazards kb2)))
            (is (= ['(dog Rex)] (dogs kb2)))
            (is (not= "stale" (:source (stamp dir))))
            (finally (v/close! kb2))))
        (finally
          (.countDown release)
          (rm-rf! dir))))))

(deftest a-close-waiting-on-the-rebuild-blocks-no-other-directory
  (tu/with-snapshot-platform
    ;; The hold stands in for a whole-store settle, which reads no stop request: it goes on
    ;; after the close asks it to stop.  The close waits for it, and that wait must not hold
    ;; the monitor every other directory's open takes.
    (let [dir     (store!)
          other   (tmpdir)
          reached (CountDownLatch. 1)
          asked   (CountDownLatch. 1)
          release (CountDownLatch. 1)
          kb      (binding [recovery/*before-install*
                            (fn [_]
                              (.countDown reached)
                              (loop [i 0]
                                (when (recovery/abandoning?) (.countDown asked))
                                (when (and (pos? (.getCount release)) (< i 6000))
                                  (Thread/sleep 5)
                                  (recur (inc i)))))]
                    (v/open-kb {:backend :disk-snapshot :dir dir :recover? :background}))]
      (try
        (let [held?   (.await reached 30 TimeUnit/SECONDS)
              closing (future (v/close! kb))
              asked?  (.await asked 30 TimeUnit/SECONDS)
              opening (future (v/close! (v/open-kb {:backend :disk-log :dir other
                                                    :recover? false}))
                              :opened)
              opened  (deref opening 10000 ::blocked)]
          (.countDown release)
          @closing
          (is (and held? asked?) "the close asked the held rebuild to stop")
          (is (= :opened opened)
              "another directory opens while the close waits on the rebuild")
          (is (= :opened (deref opening 30000 ::blocked))))
        (finally
          (.countDown release)
          (rm-rf! dir)
          (rm-rf! other))))))

(deftest recover-during-the-rebuild-runs-it-on-the-calling-thread
  (tu/with-snapshot-platform
    (let [dir (store!)
          [kb ^CountDownLatch reached ^CountDownLatch release] (open-held dir)]
      (try
        (is (.await reached 30 TimeUnit/SECONDS))
        (v/recover kb)
        (is (= {} (kb/write-hazards kb)))
        (is (= ['(dog Rex)] (dogs kb)))
        (is (not= "stale" (:source (stamp dir))))
        (finally
          (.countDown release)
          (v/close! kb)
          (rm-rf! dir))))))

(deftest an-image-declined-for-its-records-is-recovered-under-background-too
  (tu/with-snapshot-platform
    (let [dir (store!)]
      (restamp! dir :records :moved)
      (let [kb (v/open-kb {:backend :disk-snapshot :dir dir :recover? :background})]
        (try
          (is (= {} (kb/write-hazards kb)) "the open recovered, so nothing is being rebuilt")
          (is (= ['(dog Rex)] (dogs kb)))
          (is (not= :moved (:records (stamp dir))))
          (finally
            (v/close! kb)
            (rm-rf! dir)))))))

(deftest a-trusted-image-is-kept-writable-and-keeps-its-source-stamp
  (tu/with-snapshot-platform
    (let [dir (store!)]
      (try
        (let [kb (v/open-kb {:backend :disk-snapshot :dir dir :recover? :trust})]
          (try
            (testing "the image answers, no rebuild runs, and writes are accepted"
              (is (= ['(dog Rex)] (dogs kb)))
              (is (not (:stale-belief (kb/write-hazards kb))))
              (is (nil? (v/rebuild-progress kb)))
              (is (some? (v/assert kb '(dog Fido) 'CxUniverse))))
            (testing "a write settles under this build over the trusted belief"
              (is (= #{'(dog Rex) '(dog Fido)} (set (dogs kb))))
              (is (some #(= 'Fido (get % '?x)) (v/ask kb '(animal ?x) 'CxUniverse))))
            (finally (v/close! kb))))
        (is (= "stale" (:source (stamp dir)))
            "the close stamps the source the belief was last derived under in full")
        (let [recovers (atom 0)
              real     @#'recovery/recover-from-records
              kb       (with-redefs-fn {#'recovery/recover-from-records
                                        (fn [& args] (swap! recovers inc) (apply real args))}
                         #(v/open-kb {:backend :disk-snapshot :dir dir :recover? :trust}))]
          (try
            (is (= #{'(dog Rex) '(dog Fido)} (set (dogs kb)))
                "a second trusted open installs the image the first one closed with")
            (is (zero? @recovers)
                "the close wrote the trusted session's write into the image, so nothing recovers")
            (finally (v/close! kb))))
        (let [kb (v/open-kb {:backend :disk-snapshot :dir dir})]
          (try
            (is (= #{'(dog Rex) '(dog Fido)} (set (dogs kb))))
            (finally (v/close! kb))))
        (is (not= "stale" (:source (stamp dir))) "an :auto open recovers and restamps")
        (finally (rm-rf! dir))))))
