;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.catbus-test
  "The fiction witness for CxRealWorld (resources/kb/CxRealWorld.txt): CxUniverse
  states (disjoint animal vehicle) at the default strength, and CxRealWorld restates
  the same separation monotonic. CxTotoro, a context under CxWell siblinged with
  CxRealWorld rather than placed below it, holds a catbus — a term that is both a cat
  and a bus — as a represented dilemma, neither side defeated. The same pair of
  memberships in CxRealWorld loses a monotonic clash instead, and an ordinary animal
  in CxWell is not a vehicle with no overlap asserted at all."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(tu/deftest-kb a-catbus-holds-in-fiction-and-loses-in-the-real-world
  (v/assert kb '(genlCx CxTotoro CxWell) 'CxUniverse)
  (v/assert kb '(context CxTotoro) 'CxUniverse)
  (tu/with-terms [tu_bus Catbus OrdinaryCat Catbus2]
    ;; bus does not exist upstream, so this is the test's own fresh spec of vehicle.
    (v/assert kb (list 'genl tu_bus 'vehicle) 'CxUniverse)

    (testing "CxTotoro holds the catbus as both a cat and a bus"
      (v/assert kb (list 'cat Catbus) 'CxTotoro)
      (v/assert kb (list tu_bus Catbus) 'CxTotoro)
      (is (v/ask? kb (list 'cat Catbus) 'CxTotoro) "the catbus is a cat")
      (is (v/ask? kb (list tu_bus Catbus) 'CxTotoro) "and a bus — neither side lost")
      (is (v/ask? kb (list 'animal Catbus) 'CxTotoro))
      (is (v/ask? kb (list 'vehicle Catbus) 'CxTotoro))
      (is (seq (filter #(contains? (:nogood %)
                                   (v/handle-of kb (list tu_bus Catbus) 'CxTotoro))
                       (v/contradictions kb)))
          "the overlap is reported as a dilemma, which is a clash that does not win"))

    (testing "the same pair in CxRealWorld loses the monotonic clash instead"
      (v/assert kb (list 'cat Catbus2) 'CxRealWorld {:strength :monotonic})
      (is (v/assert kb (list tu_bus Catbus2) 'CxRealWorld)
          "a write is never refused — the attempt is stored")
      (is (v/ask? kb (list 'cat Catbus2) 'CxRealWorld) "the monotonic membership stands")
      (is (not (v/ask? kb (list tu_bus Catbus2) 'CxRealWorld))
          "the vehicle membership loses the monotonic clash — the real world never
           holds the overlap"))

    (testing "in plain CxWell an ordinary animal is not a vehicle by default"
      (v/assert kb (list 'cat OrdinaryCat) 'CxWell)
      (is (not (v/ask? kb (list 'vehicle OrdinaryCat) 'CxWell)))
      (is (not (v/ask? kb (list tu_bus OrdinaryCat) 'CxWell))))))
