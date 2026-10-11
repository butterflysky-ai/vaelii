;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.wire-contract-test
  "The daemon's wire contract, pinned pair by pair: every refusal `POST /op` can
  answer is a status code *and* a plain `:type` keyword, the two halves
  `docs/operations.md` promises together.  Driven against `serve/app` directly —
  the handler is pure `request -> response`, so no socket — with one property over
  the lot: `:ok` is false and `:type` is a non-nil keyword, whichever entry point refused.

  Two handlers, because the 401 is the entry point in front of the others: `open-app` holds
  no token (every refusal below is reachable), `authed-app` holds one (the 401 is the
  only refusal reachable at all)."
  (:require [clojure.edn :as edn]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.host.guard :as guard]
            [vaelii.host.serve :as serve]
            [vaelii.host.subscribe :as sub]
            [vaelii.impl.config :as config]
            [vaelii.test-util :as tu])
  (:import [java.io ByteArrayInputStream]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- post-raw
  "POST the exact `body` string to /op under `headers` and return the parsed EDN
  reply with `:status` assoc'd — raw, so an unreadable body is drivable at all."
  ([handler headers body] (post-raw handler headers body "/op"))
  ([handler headers ^String body uri]
   (let [resp (handler {:request-method :post :uri uri
                        :headers headers
                        :body (ByteArrayInputStream. (.getBytes body "UTF-8"))})]
     (assoc (edn/read-string (:body resp)) :status (:status resp)))))

(def ^:private edn-headers {"content-type" "application/edn"})

(defn- op-body [op args] (pr-str {:op op :args (vec args)}))

(defn- open-app
  "The handler with no bearer token — the loopback default, and the posture under which
  every refusal below is reachable.  Named rather than defaulted, since the default
  reads `VAELII_API_TOKEN` and a shell that has one would turn these pairs into 401s."
  [kb]
  (serve/app kb {:token nil}))

(defn- authed-app
  "The handler holding a token, which is where the 401 pair lives."
  [kb]
  (serve/app kb {:token "s3cret-token"}))

(tu/deftest-kb every-wire-refusal-is-a-status-and-a-type
  (tu/with-terms [dog Rex CxWireProbe]
    (let [handler (open-app kb)
          oversized (with-redefs [guard/max-body-bytes 8]
                      (post-raw handler edn-headers
                                (op-body :assert [(list dog Rex) CxWireProbe])))
          pinned
          [["a wrong content-type" 415 :not-edn
            (post-raw handler {"content-type" "text/plain"}
                      (op-body :assert [(list dog Rex) CxWireProbe]))]
           ["a body that does not read as EDN" 400 :not-edn
            (post-raw handler edn-headers "{:op :assert :args [(dog")]
           ["an op the allowlist does not name" 400 :unknown-op
            (post-raw handler edn-headers (op-body :not-an-op []))]
           ["the wrong number of args for the op" 400 :bad-args
            (post-raw handler edn-headers (op-body :assert []))]
           ["a non-sequential :args" 400 :bad-args
            (post-raw handler edn-headers (pr-str {:op :assert :args 5}))]
           ["a body over the ceiling" 413 :body-too-large
            oversized]
           ;; a request picks among the KBs the server serves and names no path
           ["a path a request names for the server to read" 403 :path-not-served
            (post-raw handler edn-headers (op-body :kb-diff ["/etc/hosts"]))]
           ;; the change feed's three, which are refusals about a *subscription* rather
           ;; than about a sentence — 400 like the rest, because the caller is who can
           ;; act on each, and a status of their own would break the promise that a
           ;; client discriminates on `:type` (docs/operations.md)
           ["a feed token naming no subscription" 400 :unknown-subscription
            (post-raw handler edn-headers (op-body :poll [4200 0]))]
           ["a feed cursor that is not one" 400 :bad-cursor
            (post-raw handler edn-headers
                      (op-body :poll [(:token (:result (post-raw handler edn-headers
                                                                 (op-body :watch []))))
                                      :soon]))]
           ["more subscriptions than the daemon holds" 400 :too-many-subscriptions
            (with-redefs [sub/max-subscriptions 0]
              (post-raw handler edn-headers (op-body :watch [])))]
           ;; the daemon is at capacity rather than the request being wrong, and it is
           ;; still a 400: the caller is the one who can fix it, by polling on a timer
           ["more parked long polls than the daemon's threads allow" 400 :too-many-waiters
            (with-redefs [sub/max-parked 0]
              (post-raw handler edn-headers
                        (op-body :poll [(:token (:result (post-raw handler edn-headers
                                                                   (op-body :watch []))))
                                        0 {:wait-ms 10000}])))]
           ;; a well-formed request whose option value no long holds: it reached `long`
           ;; and answered 500 with the cast error on it
           ["a :wait-ms larger than a long" 400 :unknown-option
            (post-raw handler edn-headers
                      (op-body :poll [(:token (:result (post-raw handler edn-headers
                                                                 (op-body :watch []))))
                                      0 {:wait-ms 1e300}]))]
           ;; the outermost entry point, and the only one whose refusal is deliberately
           ;; uninformative: same body for a missing, wrong or malformed credential
           ["no bearer token, to a daemon holding one" 401 :unauthorized
            (post-raw (authed-app kb) edn-headers
                      (op-body :assert [(list dog Rex) CxWireProbe]))]]
          ;; the engine's own refusal rides the wire under the engine's `:type`, and a
          ;; request-refusal is the *caller's* fault, so it is a 400 like the daemon's
          ;; own — answered 500 it counts as a backend fault at every reverse proxy
          ;; and 5xx alarm between the caller and the daemon
          engine (post-raw handler edn-headers
                           (op-body :assert [(list dog '?x) CxWireProbe]))]
      (doseq [[label status type reply] pinned]
        (testing label
          (is (= status (:status reply)) label)
          (is (= type (:type reply)) label)))
      (testing "an engine refusal keeps the engine's :type on the wire, at 400"
        (is (= :not-ground (:type engine)))
        (is (= 400 (:status engine))))
      (testing "the refusal-vocabulary statuses: naming, options, handles, levels"
        (doseq [[label args ty] [["snake_case arity 2" [(list 'lives_in Rex 'cold_place) CxWireProbe] :naming]
                                 ["an unread option" [(list dog Rex) CxWireProbe {:strenth :monotonic}] :unknown-option]]]
          (let [r (post-raw handler edn-headers (op-body :assert args))]
            (is (= 400 (:status r)) label)
            (is (= ty (:type r)) label))))
      (testing "a route nothing serves is a typed reply too"
        (let [r (post-raw handler edn-headers "{:op :assert}" "/nothing-here")]
          ;; any client, any body: the default handler answers 404 with a :type
          (is (= 404 (:status r)))
          (is (= :not-found (:type r)))))
      (testing "the property over every refusal: :ok false, :type a non-nil keyword"
        (doseq [[label _ _ reply] (conj pinned ["an engine refusal" nil nil engine])]
          (is (false? (:ok reply)) label)
          (is (keyword? (:type reply)) label))))))

(tu/deftest-kb a-refusal-from-any-served-entry-point-is-a-400
  ;; `client-error-types` is a roster written by hand, and its failure mode is quiet: a
  ;; refusal type born at one entry point and never added to it answers **500**, which every
  ;; reverse proxy and 5xx alarm between the caller and the daemon counts as a backend
  ;; fault — for a request the caller wrote.  `assert`'s own vocabulary is pinned above;
  ;; these are the entry points beside it, one refusal each, driven through the same handler.
  (tu/with-terms [dog cat Rex]
    (let [handler (open-app kb)
          op!     (fn [op args] (post-raw handler edn-headers (op-body op args)))
          ;; a directory no export ever reaches: the refusals below run before the
          ;; destination is touched, so nothing is created and nothing needs cleaning up
          nowhere "/vaelii-export-that-is-never-written"
          paths!  #(with-redefs [config/request-paths? (constantly true)] (%))]
      (doseq [[label ty reply]
              [;; the read entry points that do not resolve a query context refuse it rather
               ;; than answering empty (docs/contexts.md); over the wire that refusal is
               ;; the caller naming a reading this op does not offer
               ["a query context at a read that does not resolve one" :unsupported-context
                (op! :why-not [(list dog Rex) 'CxEverything])]
               ["a dump variant this build does not write" :unsupported-variant
                (paths! #(op! :export [nowhere {:variant :everything}]))]
               ["a codec this build does not write" :unsupported-compression
                (paths! #(op! :export [nowhere {:compression :zstd}]))]
               ["a try-assert that would open a definitional clash" :definitional-clash
                (do (op! :assert [(list 'disjoint dog cat) 'CxUniverse])
                    (op! :assert [(list dog Rex) 'CxUniverse])
                    (op! :try-assert [(list cat Rex) 'CxUniverse]))]
               ;; a `:find-terms` regex whose backtracking blows the per-term step
               ;; budget is the caller's abuse, refused rather than left to pin the
               ;; writer's core (docs/web.md); over the wire it is a 400 like the rest
               ["a pathological find-terms regex" :pattern-too-costly
                (do (op! :assert [(list 'genl (symbol (str (apply str (repeat 2000 \a)) "b"))
                                        'thing) 'CxUniverse])
                    (op! :find-terms ["(a*)*$" {:match :regex}]))]]]
        (testing label
          (is (false? (:ok reply)) label)
          (is (= ty (:type reply)) label)
          (is (= 400 (:status reply)) label))))))
