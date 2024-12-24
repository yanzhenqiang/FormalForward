(ns latte-nats.minus
  "The predecessor and subtraction functions defined on ℕ."

  (:refer-clojure :exclude [and or not int = + -])

  (:require [latte.core :as latte :refer [defaxiom try-defthm defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof qed search-theorem]]

            [latte.utils :as u]

            [latte-prelude.prop :as p :refer [and or not <=>]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.algebra :as alg]

            [latte-sets.quant :as sq :refer [forall-in]]
            
            [latte-nats.core :as nats :refer [nat = <> zero succ one]]
            [latte-nats.rec :as rec]
            [latte-nats.plus :as plus :refer [+]]
                       ))


(defaxiom pred
  "The predecessor of a natural number `n`."
  []
  (==> nat nat))

(defaxiom pred-zero 
  "The predecessor of `zero` is defined as `zero`, which
makes the predecessor function non-injective since
`(pred zero)` and `(pred one)` are both equal to `zero`.

In practice, this means that one must be careful everytime
the predecessor of zero occurs."
  []
  (= (pred zero) zero))

(defaxiom pred-succ
  [n nat]
  (= (pred (succ n)) n))

(defthm pred-one
  []
  (= (pred one) zero))

(proof 'pred-one
  (qed (pred-succ zero)))

(defthm succ-pred-zero
  []
  (= (succ (pred zero)) one))

(proof 'succ-pred-zero
  (have <a> (= (succ zero) one) :by (eq/eq-refl (succ zero)))
  (have <b> (= zero (pred zero)) :by (eq/eq-sym (pred-zero)))
  (qed (eq/eq-subst (lambda [$ nat] (= (succ $) one)) <b> <a>)))

(defthm succ-pred-succ
  [n nat]
  (==> (<> n zero)
       (= (succ (pred n)) n)))

(proof 'succ-pred-succ
  (pose P := (lambda [n nat]
               (==> (<> n zero)
                    (= (succ (pred n)) n))))

  "By case analysis"

  "zero case"
  (assume [H0 (<> zero zero)]
    (have <a1> (= zero zero) :by (eq/eq-refl zero))
    (have <a2> p/absurd :by (H0 <a1>))
    (have <a3> _
          :by (<a2> (= (succ (pred zero)) zero))))
  (have <a> (P zero) :by <a3>)

  "succ case"
  (assume [n nat]
    (assume [Hn (<> (succ n) zero)]
      (have <b1> (= (pred (succ n)) n) :by (pred-succ n))
      (have <b2> (= (succ (pred (succ n))) (succ n))
            :by (eq/eq-cong succ <b1>)))
    (have <b> (P (succ n)) :by <b2>))

  (qed ((nats/nat-case P) <a> <b> n)))

(defthm pred-eq-zero
  [n nat]
  (==> (= (pred n) n)
       (= n zero)))

(proof 'pred-eq-zero
  "By case analysis"

  "Case zero"
  
  (assume [H0 (= (pred zero) zero)]
    (have <a> (= zero zero) :by (eq/eq-refl zero)))

  "Case (succ n)"

  (assume [n nat
           Hn (= (pred (succ n)) (succ n))]

    "We have to show (= (succ n) zero), but we will exhibit a contradiction"

    (have <b1> (= (pred (succ n)) n) :by (pred-succ n))
    (have <b2> (= n (succ n)) 
          :by (eq/eq-subst (lambda [$ nat] (= $ (succ n))) <b1> Hn))
    (have <b3> p/absurd :by ((nats/succ-not n) <b2>))
    
    (have <b> _ :by (<b3> (= (succ n) zero))))

  (qed ((nats/nat-case (lambda [n nat] (==> (= (pred n) n)
                                            (= n zero)))) <a> <b> n)))
    
(definition sub-prop
  "The property of the subtraction of `m` by another natural number.
Note that subtraction is not closed for natural numbers, so we
inherit the fact the `(pred zero)` is `zero`."
  [[m nat]]
  (lambda [g (==> nat nat)]
    (and (= (g zero) m)
         (forall [n nat]
           (= (g (succ n)) (pred (g n)))))))

(deflemma sub-unique
  [[m nat]]
  (q/unique (sub-prop m)))

(proof 'sub-unique
  (qed (rec/nat-recur m pred)))

(definition minus
  [[m nat]]
  (q/the (sub-unique m)))

(definition -
  "The subtraction `(- m n)` of `m` by `n`.
Note that if `(<= m n)` then (- m n) is `zero`."
  [[m n nat]]
  ((minus m) n))

(deflemma minus-prop
  [m nat]
  (and (= ((minus m) zero) m)
       (forall [n nat]
         (= ((minus m) (succ n))
            (pred ((minus m) n))))))

(proof 'minus-prop
  (qed (q/the-prop (sub-unique m))))

(defthm minus-zero
  [[m nat]]
  (= (- m zero) m))

(proof 'minus-zero
  (qed (p/and-elim-left (minus-prop m))))

(defthm minus-succ
  [[m n nat]]
  (= (- m (succ n)) (pred (- m n))))

(proof 'minus-succ
  (qed ((p/and-elim-right (minus-prop m)) n)))

(defthm minus-one
  [m nat]
  (= (- m one) (pred m)))

(proof 'minus-one
  (have <a> (= (- m one) (pred (- m zero)))
        :by (minus-succ m zero))
  (have <b> (= (- m zero) m)
        :by (minus-zero m))
  (qed (eq/eq-subst (lambda [$ nat]
                      (= (- m one) (pred $))) <b> <a>)))


        
