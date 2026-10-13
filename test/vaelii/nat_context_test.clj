;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.nat-context-test
  "**Object** reified NATs are not contexts — docs/nat.md, docs/naming.md, docs/contexts.md.
  (Context-denoting `Cx*Fn` NATs reify to a `cx/` constant that *is* a context — that is
  the deliberate exception, and its own contract is `docs/context-nat.md` +
  `context_nat_test`.  This namespace pins the object case that stays refused.)

  An object reified NAT is an opaque `nat/`-namespaced constant standing for a term; a
  context is a `Cx`-prefixed name (or a `cx/` context constant).  For an object NAT the two
  roles are orthogonal — reification settles *term identity*, a context is *where a sentex
  is stored* — and nothing bridges them, so a `nat/` constant can neither be wired into the
  `genlCx` hierarchy nor name the context a sentex is stored in.  Two independent gates hold
  the line, and this namespace pins both:

  - `wff/genlCx-problems` refuses a `genlCx` edge whose argument is not `Cx`-shaped
    (`:not-well-formed`), so a reified constant can never become a node of the hierarchy;
  - the naming check refuses a context slot that is not a context name (`:naming`), so a
    reified constant cannot name where a sentex is stored either.

  The refusal is an entry-point **policy**, not a store limit: with `:naming :off` the
  store will hold a sentex keyed by a `nat/` symbol — but genlCx still refuses to wire
  it, so it is an island that sees nothing and no context sees, never a member of
  `(contexts kb)`.  A reified NAT as a working context is therefore unreachable under
  every policy."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.nat :as nat]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded core-context/load-into))
(use-fixtures :each (tu/neutral))

(defn- refusal
  "The `:type` a thrown assert refused with, or ::stored when it did not throw."
  [f]
  (try (f) ::stored
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(defn- mint
  "Assert an ordinary fact carrying the ground NAT `E`, and return the reified constant
  `k` it minted — the atomic term now standing in `E`'s argument slot."
  [kb E]
  (let [Red (tu/fresh-term :individual 'Red)
        h   (v/assert kb (list 'color E Red) 'CxUniverse)]
    (second (:sentence (v/sentex kb h)))))

;; ---- classification: a reified NAT is not a context ----------------------

(tu/deftest-kb a-reified-nat-classifies-as-a-term-not-a-context
  ;; The `nat/` namespace and the `Cx` convention do not meet: a minted constant's name
  ;; half is a lowercase gensym, so `term-role` reads it as an ordinary predicate-shaped
  ;; term (the general path any bare lowercase name takes), never as a context.
  (tu/with-terms [MtFn Story1]
    (v/assert kb (list 'reifiable_function MtFn) 'CxUniverse)
    (let [k (mint kb (list MtFn Story1))]
      (is (nat/reified-nat-symbol? k))
      (is (not= :context (v/term-role k)))
      (is (not (contains? (set (v/contexts kb)) k))
          "a minted constant is no node of the context hierarchy"))))

;; ---- gate 1: genlCx refuses a reified NAT as a context edge ---------------

(tu/deftest-kb genlCx-refuses-a-reified-nat-node
  ;; `genlCx-problems` checks both arguments with `naming/context?`, so neither a NAT
  ;; compound (reified to a constant before wff sees it) nor a pre-minted constant can
  ;; be wired into the hierarchy.  Without this a reified constant would silently become
  ;; a context that sees nothing and is seen by nothing.
  (tu/with-terms [MtFn Story1]
    (v/assert kb (list 'reifiable_function MtFn) 'CxUniverse)
    (let [k (mint kb (list MtFn Story1))]
      (testing "the NAT compound spelling — reified first, then refused"
        (is (= :not-well-formed
               (refusal #(v/assert kb (list 'genlCx (list MtFn Story1) 'CxUniverse) 'CxUniverse)))))
      (testing "the pre-minted constant spelling"
        (is (= :not-well-formed
               (refusal #(v/assert kb (list 'genlCx k 'CxUniverse) 'CxUniverse)))))
      (testing "and as the super, either way round"
        (is (= :not-well-formed
               (refusal #(v/assert kb (list 'genlCx 'CxUniverse k) 'CxUniverse))))))))

;; ---- gate 2: a reified NAT cannot name the context a sentex is in ---------

(tu/deftest-kb a-reified-nat-cannot-name-a-context-slot
  (tu/with-terms [MtFn Story1 likes Tom Ann]
    (v/assert kb (list 'reifiable_function MtFn) 'CxUniverse)
    (let [k (mint kb (list MtFn Story1))]
      (testing "a NAT compound in the context slot reifies to a cx/ constant, never to the
                nat/ constant the argument position minted"
        (let [c (:context (v/sentex kb (v/assert kb (list likes Tom Ann) (list MtFn Story1))))]
          (is (nat/reified-context-symbol? c))
          (is (not= k c))))
      (testing "the minted constant as the context slot is refused by naming (strict)"
        (is (= :naming
               (refusal #(v/assert kb (list likes Tom Ann) k)))))
      (testing "(ist Ctx S) reifies its context argument, so directing a fact into a NAT
                context is the same refusal"
        (is (= :naming
               (refusal #(v/assert kb (list 'ist (list MtFn Story1)
                                            (list likes Tom Ann))))))))))

;; ---- where the refusal lives: a policy, not a store limit -----------------

(tu/deftest-kb naming-off-stores-into-a-nat-symbol-but-it-is-an-island
  ;; The store itself has no objection to a `nat/` symbol in the context slot — the
  ;; objection is the naming check's.  Turn the entry point off and the sentex stores and reads
  ;; back from that symbol; but genlCx still refuses to wire it (gate 1 is wff, not
  ;; naming), so the symbol sees nothing and no context sees it.  It is a bucket, never
  ;; a member of the hierarchy — which is why a reified NAT is unreachable as a *working*
  ;; context under every policy.
  (tu/with-terms [MtFn Story1 likes Tom Ann]
    (v/assert kb (list 'reifiable_function MtFn) 'CxUniverse)
    (let [k      (mint kb (list MtFn Story1))
          kb-off (assoc kb :naming :off)]
      (is (= ::stored (refusal #(v/assert kb-off (list likes Tom Ann) k)))
          "with naming off the store accepts the symbol as a context")
      (testing "and the fact reads back from that symbol"
        (is (= [{'?x Ann}] (v/ask kb-off (list likes Tom '?x) k))))
      (testing "but the symbol is no node of the hierarchy and sees nothing"
        (is (not (contains? (set (v/contexts kb)) k)))
        (is (not (v/sees? kb k 'CxUniverse))
            "an island: it does not even see CxUniverse, which every real context sees")))))
