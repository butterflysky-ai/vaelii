;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.social-extension-test
  "CxSocialExtension: nestingPartnerOf and chosenSiblingOf, shipped as an opt-in
  extension of CxSocial below CxUniverse. CxWell does not see the theory, so the
  everyday contexts below CxWell derive none of it, and a user's own context
  opts in by placing itself under CxSocialExtension — which, placed under
  CxSocial, sees CxSocial's own relations too."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private SOCX 'CxSocialExtension)

(defn- holds-ask  [s ctx]         (boolean (v/ask? tu/*kb* s ctx)))
(defn- holds-sees [k y]           (boolean (v/sees? tu/*kb* k y)))
(defn- holds-genl [sub super ctx] (boolean (v/genl? tu/*kb* sub super ctx)))

(tu/deftest-kb the-theory-is-opt-in-below-cxsocial
  (testing "the theory sees CxSocial, and through it CxUniverse"
    (is (holds-sees SOCX 'CxSocial))
    (is (holds-sees SOCX 'CxUniverse)))
  (testing "neither CxWell, CxSocial, nor the upper ontology sees the theory"
    (is (not (holds-sees 'CxWell SOCX)))
    (is (not (holds-sees 'CxSocial SOCX)))
    (is (not (holds-sees 'CxUniverse SOCX)))))

(tu/deftest-kb cxwell-concludes-none-of-the-extension
  (tu/with-terms [P1 P2 Unit]
    (v/assert kb (list 'human P1) 'CxWell)
    (v/assert kb (list 'human P2) 'CxWell)
    (v/assert kb (list 'romanticPartnerOf P1 P2) 'CxWell)
    (v/assert kb (list 'dwellsIn P1 Unit) 'CxWell)
    (v/assert kb (list 'dwellsIn P2 Unit) 'CxWell)
    (testing "CxSocial's own vocabulary still derives in CxWell"
      (is (holds-ask (list 'roommateOf P1 P2) 'CxWell)))
    (testing "the extension's nestingPartnerOf does not, though both antecedents hold"
      (is (not (holds-ask (list 'nestingPartnerOf P1 P2) 'CxWell))))))

(tu/deftest-kb a-user-context-under-the-extension-derives-nestingpartnerof
  (tu/with-terms [CxHome P1 P2 Unit]
    (v/assert kb (list 'genlCx CxHome 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxHome SOCX) 'CxUniverse)
    (v/assert kb (list 'human P1) CxHome)
    (v/assert kb (list 'human P2) CxHome)
    (v/assert kb (list 'romanticPartnerOf P1 P2) CxHome)
    (testing "romantic partners who are not yet roommates are not yet nesting partners (red)"
      (is (not (holds-ask (list 'nestingPartnerOf P1 P2) CxHome))))
    (v/assert kb (list 'dwellsIn P1 Unit) CxHome)
    (v/assert kb (list 'dwellsIn P2 Unit) CxHome)
    (testing "co-dwelling derives roommateOf, which with romanticPartnerOf derives nestingPartnerOf (green)"
      (is (holds-ask (list 'roommateOf P1 P2) CxHome))
      (is (holds-ask (list 'nestingPartnerOf P1 P2) CxHome)))
    (testing "a context that does not see the extension still concludes none of it"
      (doseq [ctx ['CxWell 'CxSocial 'CxUniverse]]
        (is (not (holds-ask (list 'nestingPartnerOf P1 P2) ctx)) (str "nestingPartnerOf in " ctx))))))

(tu/deftest-kb each-relation-specializes-what-it-is-a-kind-of
  (doseq [[sub super] '[[chosenSiblingOf relativeOf]
                        [nestingPartnerOf romanticPartnerOf]
                        [nestingPartnerOf roommateOf]]]
    (is (holds-genl sub super SOCX))
    (is (not (holds-genl sub super 'CxSocial))))
  (is (not (holds-genl 'chosenSiblingOf 'siblingOf SOCX)))
  (is (not (holds-genl 'siblingOf 'chosenSiblingOf SOCX))))

(tu/deftest-kb a-user-context-under-the-extension-concludes-from-each-relation
  (tu/with-terms [CxHome P1 P2 P3 P4]
    (v/assert kb (list 'genlCx CxHome SOCX) 'CxUniverse)
    (doseq [p [P1 P2 P3 P4]] (v/assert kb (list 'human p) CxHome))
    (v/assert kb (list 'chosenSiblingOf P1 P2) CxHome)
    (v/assert kb (list 'nestingPartnerOf P3 P4) CxHome)
    (is (holds-ask (list 'relativeOf P1 P2) CxHome))
    (is (holds-ask (list 'knows P1 P2) CxHome))
    (is (not (holds-ask (list 'siblingOf P1 P2) CxHome)))
    (is (holds-ask (list 'romanticPartnerOf P3 P4) CxHome))
    (is (holds-ask (list 'roommateOf P3 P4) CxHome))))
