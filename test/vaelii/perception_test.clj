;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.perception-test
  "CxPerception: the perception relations, shipped as an opt-in theory below
  CxUniverse. CxWell does not see the theory, so the everyday contexts below CxWell
  take in no perception relation, and a user's own context opts in by placing itself
  under CxPerception.

  `sees` specializes `perceives` through a `genl` edge stated inside the theory, and
  `seeImage` and `watchVideo` conclude `sees` by a rule guarded by `sees`'s `spatial`
  second argument. A context under CxPerception reads the whole chain for a spatial
  image or video; a context that does not see the theory reads only the fact asserted
  there."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private PCP 'CxPerception)

;; Each reader answers a boolean, so a failing `is` prints the question and not the KB.
(defn- holds-ask  [s ctx]         (boolean (v/ask? tu/*kb* s ctx)))
(defn- holds-sees [k y]           (boolean (v/sees? tu/*kb* k y)))
(defn- holds-genl [sub super ctx] (boolean (v/genl? tu/*kb* sub super ctx)))

(tu/deftest-kb the-theory-is-opt-in-below-cxuniverse
  (testing "the theory sees the upper ontology through CxUniverse"
    (is (holds-sees PCP 'CxUniverse))
    (is (holds-sees PCP 'CxAbstract)))
  (testing "neither CxWell nor the upper ontology sees the theory"
    (is (not (holds-sees 'CxWell PCP)))
    (is (not (holds-sees 'CxAbstract PCP)))
    (is (not (holds-sees 'CxUniverse PCP)))))

(tu/deftest-kb the-specialization-chain-is-the-theorys-own
  (is (holds-genl 'sees 'perceives PCP))
  (is (not (holds-genl 'sees 'perceives 'CxUniverse)))
  (is (not (holds-genl 'sees 'perceives 'CxAbstract)))
  (doseq [sub '[seeImage watchVideo]]
    (is (not (holds-genl sub 'sees PCP)) (str sub " reaches sees by a rule, not a genl edge"))))

(tu/deftest-kb an-aspatial-image-seen-stores-no-clash
  ;; A genl edge to `sees` would carry `(arg sees 2 spatial)` down and mint `(spatial Img)`,
  ;; which the `spatial`/`aspatial` partition convicts.
  (tu/with-terms [CxRoom Ann Img Clip]
    (v/assert kb (list 'genlCx CxRoom PCP) 'CxUniverse)
    (v/assert kb (list 'aspatial Img) CxRoom)
    (v/assert kb (list 'aspatial Clip) CxRoom)
    (is (not (tu/stored-in-clash? kb (list 'seeImage Ann Img) CxRoom)))
    (is (not (tu/stored-in-clash? kb (list 'watchVideo Ann Clip) CxRoom)))
    (is (not (holds-ask (list 'spatial Img) CxRoom)))
    (is (not (holds-ask (list 'sees Ann Img) CxRoom)))))

(tu/deftest-kb cxwell-concludes-no-specialization
  ;; CxWell does not see CxPerception: a fact asserted at the narrowest predicate is
  ;; itself visible there (an assert is never refused), but it specializes nothing.
  (tu/with-terms [Viewer Image Watcher Video]
    (v/assert kb (list 'seeImage Viewer Image) 'CxWell)
    (v/assert kb (list 'watchVideo Watcher Video) 'CxWell)
    (testing "the asserted fact holds"
      (is (holds-ask (list 'seeImage Viewer Image) 'CxWell))
      (is (holds-ask (list 'watchVideo Watcher Video) 'CxWell)))
    (testing "no specialization above it holds"
      (is (not (holds-ask (list 'sees Viewer Image) 'CxWell)))
      (is (not (holds-ask (list 'perceives Viewer Image) 'CxWell)))
      (is (not (holds-ask (list 'sees Watcher Video) 'CxWell))))))

(tu/deftest-kb a-user-context-under-cxperception-derives-the-chain
  (tu/with-terms [CxRoom Viewer Image Watcher Video Seer Scene]
    (v/assert kb (list 'genlCx CxRoom 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxRoom PCP) 'CxUniverse)
    (v/assert kb (list 'spatial Image) CxRoom)
    (v/assert kb (list 'spatial Video) CxRoom)
    (v/assert kb (list 'seeImage Viewer Image) CxRoom)
    (v/assert kb (list 'watchVideo Watcher Video) CxRoom)
    (v/assert kb (list 'sees Seer Scene) CxRoom)
    (testing "seeImage of a spatial image derives sees and perceives"
      (is (holds-ask (list 'sees Viewer Image) CxRoom))
      (is (holds-ask (list 'perceives Viewer Image) CxRoom)))
    (testing "watchVideo of a spatial video derives sees and perceives"
      (is (holds-ask (list 'sees Watcher Video) CxRoom))
      (is (holds-ask (list 'perceives Watcher Video) CxRoom)))
    (testing "sees derives perceives, and derives from neither spec"
      (is (holds-ask (list 'perceives Seer Scene) CxRoom))
      (is (not (holds-ask (list 'seeImage Seer Scene) CxRoom)))
      (is (not (holds-ask (list 'watchVideo Seer Scene) CxRoom))))
    (testing "a context that does not see the theory still concludes none of it"
      (doseq [ctx ['CxWell 'CxAbstract 'CxUniverse]]
        (is (not (holds-ask (list 'sees Viewer Image) ctx)) (str "Viewer sees in " ctx))
        (is (not (holds-ask (list 'perceives Seer Scene) ctx)) (str "Seer perceives in " ctx))))))

(tu/deftest-kb image-viewing-is-an-acausal-event-kind-the-theory-states
  (testing "the edge is the theory's, not the upper ontology's"
    (is (holds-genl 'image_viewing 'acausal_event PCP))
    (is (holds-genl 'image_viewing 'event PCP))
    (is (holds-genl 'image_viewing 'acausal PCP))
    (is (not (holds-genl 'image_viewing 'acausal_event 'CxUniverse)))
    (is (not (holds-genl 'image_viewing 'acausal_event 'CxAbstract)))))

(tu/deftest-kb a-user-context-under-cxperception-derives-hascapability-of-image-viewing
  (tu/with-terms [CxRoom Viewer]
    (v/assert kb (list 'genlCx CxRoom 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxRoom PCP) 'CxUniverse)
    (v/assert kb (list 'hasCapability Viewer 'image_viewing) CxRoom)
    (testing "a context under the theory reads the ability and its causal class"
      (is (holds-ask (list 'hasCapability Viewer 'image_viewing) CxRoom))
      (is (holds-ask (list 'hasCapability Viewer 'event) CxRoom))
      (is (holds-ask (list 'hasCapability Viewer 'acausal_event) CxRoom)))
    (testing "a context that does not see the theory concludes no such capability class"
      (doseq [ctx ['CxWell 'CxAbstract 'CxUniverse]]
        (is (not (holds-ask (list 'hasCapability Viewer 'acausal_event) ctx))
            (str "Viewer hasCapability acausal_event in " ctx))))))
