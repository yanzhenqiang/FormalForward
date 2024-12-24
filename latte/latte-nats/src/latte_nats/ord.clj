(ns latte-nats.ord
  "The oredering relation for natural numbers."

  (:refer-clojure :exclude [and or not = + - < <= > >=])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof qed]]

            [latte.utils :as u]

            [latte-prelude.prop :as p :refer [and or not <=>]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]

            [latte-sets.set :as s :refer [elem]]

            [latte-nats.core :as nats :refer [nat = <> zero succ one]]
            [latte-nats.rec :as rec]
            [latte-nats.plus :as plus :refer [+]]
            [latte-nats.minus :as minus :refer [- pred]]

            ))

(definition <=
  "The lower-or-equal order for natural numbers."
  [[m nat] [n nat]]
  (exists [k nat] (= (+ m k) n)))

(defthm le-refl
  [[n nat]]
  (<= n n))

(proof 'le-refl
  (have <a> (= (+ n zero) n)
        :by (plus/plus-zero n))
  (qed ((q/ex-intro (lambda [k nat] (= (+ n k) n)) zero) <a>)))

(defthm le-trans
  [[m nat] [n nat] [p nat]]
  (==> (<= m n)
       (<= n p)
       (<= m p)))

(proof 'le-trans
  (assume [H1 _
           H2 _]
    (assume [k1 nat
             Hk1 (= (+ m k1) n)]
      (assume [k2 nat
               Hk2 (= (+ n k2) p)]
        (have <a> (= (+ (+ m k1) k2) p)
              :by (eq/rewrite Hk2 (eq/eq-sym Hk1)))
        (have <b> (= (+ m (+ k1 k2)) p)
              :by (eq/rewrite <a> (eq/eq-sym (plus/plus-assoc m k1 k2))))
        (have <c> (<= m p) :by ((q/ex-intro (lambda [k nat] (= (+ m k) p)) (+ k1 k2)) <b>)))
      (have <d> (<= m p) :by (q/ex-elim H2 <c>)))
    (have <e> (<= m p) :by (q/ex-elim H1 <d>)))
  (qed <e>))

(defthm le-antisym
  [[m nat] [n nat]]
  (==> (<= m n)
       (<= n m)
       (= m n)))

(proof 'le-antisym
  (assume [H1 _
           H2 _]
    (assume [k1 nat
             Hk1 (= (+ m k1) n)]
      (assume [k2 nat
               Hk2 (= (+ n k2) m)]
        (have <a> (= (+ (+ m k1) k2) m)
              :by (eq/rewrite Hk2 (eq/eq-sym Hk1)))
        (have <b> (= (+ m (+ k1 k2)) m)
              :by (eq/rewrite <a> (eq/eq-sym (plus/plus-assoc m k1 k2))))
        (have <c> (= (+ k1 k2) zero)
              :by ((plus/plus-refl-zero m (+ k1 k2)) <b>))
        (have <d> (= k1 zero) :by ((plus/plus-any-zero-left k1 k2) <c>))
        (have <e> (= k2 zero) :by ((plus/plus-any-zero-right k1 k2) <c>))
        (have <f> (= (+ n zero) m) :by (eq/rewrite Hk2 <e>))
        (have <g> (= n m) :by (eq/rewrite <f> (plus/plus-zero n))))
      (have <h> (= n m) :by (q/ex-elim H2 <g>)))
    (have <i> (= m n) :by (eq/eq-sym (q/ex-elim H1 <h>))))
  (qed <i>))

(defthm le-zero
  [n nat]
  (<= zero n))

(proof 'le-zero
  (have <a> (= (+ zero n) n)
        :by (plus/plus-zero-swap n))
  (qed ((q/ex-intro (lambda [$ nat]
                      (= (+ zero $) n)) n) <a>)))

(defthm le-succ
  [n nat]
  (<= n (succ n)))

(proof 'le-succ
  (have <a> (= (+ n one) (succ n))
        :by (plus/plus-one-succ n))

  (qed ((q/ex-intro (lambda [$ nat] (= (+ n $) (succ n))) one) <a>)))


(defthm le-zero-right
  [n nat]
  (==> (<= n zero)
       (= n zero)))

(proof 'le-zero-right
  (assume [Hle (<= n zero)]
    (have <a> (<= zero n) :by (le-zero n))
    (have <b> (= n zero) :by ((le-antisym n zero) Hle <a>)))
  (qed <b>))

(defthm le-one
  [n nat]
  (<= one (succ n)))

(proof 'le-one
  (have <a> (= (+ n one) (+ one n))
        :by (plus/plus-commute n one))
  (have <b> (= (+ one n) (succ n))
        :by (eq/eq-subst (lambda [$ nat] (= $ (succ n))) <a> (plus/plus-one-succ n)))
  
  (qed ((q/ex-intro (lambda [$ nat] (= (+ one $) (succ n))) n) <b>)))

(definition <
  "The strict variant of [[<=]]."
  [[n nat] [m nat]]
  (and (<= n m)
       (not (= n m))))

(defthm lt-asym
  [[n nat] [m nat]]
  (==> (< n m)
       (not (< m n))))

(proof 'lt-asym
  (assume [Hnm (< n m)]
    (assume [Hmn (< m n)]
      (have <a> (= n m)
            :by ((le-antisym n m)
                 (p/and-elim-left Hnm)
                 (p/and-elim-left Hmn)))
      (have <b> p/absurd :by ((p/and-elim-right Hnm) <a>))))
  (qed <b>))


(defthm lt-trans
  [[n nat] [m nat] [p nat]]
  (==> (< n m)
       (< m p)
       (< n p)))

(proof 'lt-trans
  (assume [Hnm (< n m)
           Hmp (< m p)]
    (have <a> (<= n m) :by (p/and-elim-left Hnm))
    (have <b> (not (= n m)) :by (p/and-elim-right Hnm))
    (have <c> (<= m p) :by (p/and-elim-left Hmp))
    (have <d> (not (= m p)) :by (p/and-elim-right Hmp))
    (have <e> (<= n p) :by ((le-trans n m p) <a> <c>))
    (assume [Hcut (= n p)]
      (have <f1> (< p m)
            :by (eq/rewrite Hnm Hcut))
      (have <f2> (not (< p m)) :by ((lt-asym m p) Hmp))
      (have <f> p/absurd :by (<f2> <f1>)))
    (have <g> (< n p)
          :by (p/and-intro <e> <f>)))
  (qed <g>))

(defthm lt-trans-weak
  [[n nat] [m nat] [p nat]]
  (==> (<= n m)
       (< m p)
       (< n p)))

(proof 'lt-trans-weak
  (assume [Hnm (<= n m)
           Hmp (< m p)]
    (have <a> (<= m p) :by (p/and-elim-left Hmp))
    (have <b> (not (= m p)) :by (p/and-elim-right Hmp))
    (have <c> (<= n p) :by ((le-trans n m p) Hnm <a>))
    (assume [H (= n p)]
      (have <d1> (<= p m) :by (eq/rewrite Hnm H))
      (have <d2> (= m p) :by ((le-antisym m p) <a> <d1>))
      (have <d> p/absurd :by (<b> <d2>)))
    (have <e> (< n p) :by (p/and-intro <c> <d>)))
  (qed <e>))

(defthm lt-trans-weak-alt
  "An alternative to [[lt-trans-weak]]."
  [[n nat] [m nat] [p nat]]
  (==> (< n m)
       (<= m p)
       (< n p)))

(proof 'lt-trans-weak-alt
  (assume [Hnm (< n m)
           Hmp (<= m p)]
    (have <a> (<= n m) :by (p/and-elim-left Hnm))
    (have <b> (not (= n m)) :by (p/and-elim-right Hnm))
    (have <c> (<= n p) :by ((le-trans n m p) <a> Hmp))
    (assume [H (= n p)]
      (have <d1> (= p n) :by (eq/eq-sym H))
      (have <d2> (<= m n) :by (eq/rewrite Hmp <d1>))
      (have <d3> (= n m) :by ((le-antisym n m) <a> <d2>))
      (have <d> p/absurd :by (<b> <d3>)))
    (have <e> (< n p) :by (p/and-intro <c> <d>)))
  (qed <e>))

(defthm lt-le
  [[m nat] [n nat]]
  (==> (< m n)
       (<= m n)))

(proof 'lt-le
  (assume [Hmn (< m n)]
    (have <a> (<= m n)
          :by (p/and-elim-left Hmn)))
  (qed <a>))

(defthm lt-le-ne
  [[m n nat]]
  (==> (<= m n)
       (<> m n)
       (< m n)))

(proof 'lt-le-ne
  (assume [Hle _
           Hne _]
    (have <a> (< m n) :by (p/and-intro Hle Hne)))
  (qed <a>))


(defthm lt-succ 
  [n nat]
  (< n (succ n)))

(proof 'lt-succ
  (have <a> (<= n (succ n)) :by (le-succ n))
  (have <b> (<> n (succ n)) :by (nats/succ-not n))
  (qed (p/and-intro <a> <b>)))


(comment 

;; TODO
(defthm lt-le-succ
  [[m n nat]]
  (==> (< m (succ n))
       (<= m n)))
)

(defthm plus-le
  [[m nat] [n nat] [p nat]]
  (==> (<= (+ m p) (+ n p))
       (<= m n)))

(proof 'plus-le
  (assume [H _]
    (assume [k nat
             Hk (= (+ (+ m p) k) (+ n p))]
      
      (have <a> (= (+ (+ m p) k)
                   (+ m (+ p k)))
            :by (eq/eq-sym (plus/plus-assoc m p k)))
      (have <b> (= (+ m (+ p k))
                   (+ m (+ k p)))
            :by (eq/eq-cong (lambda [$ nat]
                              (+ m $)) (plus/plus-commute p k)))
      (have <c> (= (+ m (+ k p))
                   (+ (+ m k) p))
            :by (plus/plus-assoc m k p))
      
      (have <d> (= (+ (+ m p) k) (+ (+ m k) p))
            :by (eq/eq-trans* <a> <b> <c>))

      (have <e> (= (+ (+ m k) p) (+ n p))
            :by (eq/rewrite Hk <d>))

      (have <f> (= (+ m k) n)
            :by ((plus/plus-right-cancel (+ m k) n p) <e>))
      
      (have <g> (exists [k nat] (= (+ m k) n))
            :by ((q/ex-intro (lambda [$ nat] (= (+ m $) n)) k) <f>)))

    (have <h> (<= m n) :by (q/ex-elim H <g>)))

  (qed <h>))

(defthm plus-le-conv
  "The converse of [[plus-le]]."
  [[m nat] [n nat] [p nat]]
  (==> (<= m n)
       (<= (+ m p) (+ n p))))

(proof 'plus-le-conv
  (assume [H _]
    (assume [k nat
             Hk (= (+ m k) n)]
      (have <a> (= (+ (+ m k) p) (+ n p))
            :by (eq/eq-cong (lambda [$ nat]
                              (+ $ p)) Hk))
      (have <b> (= (+ (+ m k) p)
                   (+ (+ m p) k))
            :by (plus/plus-comm-assoc m k p))
      (have <c> (= (+ (+ m p) k) (+ n p))
            :by (eq/rewrite <a> <b>))
      (have <d> (<= (+ m p) (+ n p))
            :by ((q/ex-intro (lambda [k nat] (= (+ (+ m p) k) (+ n p))) k) <c>)))
    (have <e> _ :by (q/ex-elim H <d>)))
(qed <e>))

(defthm le-pred
  [n nat]
  (<= (pred n) n))

(proof 'le-pred
  "Case analysis"

  "Case 0"
  (have <a1> (= zero (pred zero)) :by (eq/eq-sym (minus/pred-zero)))
  (have <a2> (<= zero zero) :by (le-refl zero))
  
  (have <a> (<= (pred zero) zero)
        :by (eq/eq-subst (lambda [$ nat] (<= $ zero)) <a1> <a2>))

  "Case (succ n)"
  (assume [n nat]
    (have <b1> (= n (pred (succ n))) :by (eq/eq-sym (minus/pred-succ n)))
    (have <b2> (<= n (succ n)) :by (le-succ n))
    (have <b> (<= (pred (succ n)) (succ n))
          :by (eq/eq-subst (lambda [$ nat]
                             (<= $ (succ n))) <b1> <b2>)))

  (qed ((nats/nat-case (lambda [n nat]
                         (<= (pred n) n))) <a> <b> n)))

(defthm lt-pred
  [n nat]
  (==> (<> n zero)
       (< (pred n) n)))

(proof 'lt-pred
  (assume [Hnz (<> n zero)]
    
    (have <a> (<= (pred n) n) :by (le-pred n))
    
    (assume [Hcontra (= (pred n) n)]
      (have <b1> (= n zero) :by ((minus/pred-eq-zero n) Hcontra))
      (have <b> p/absurd :by (Hnz <b1>)))

    (have <c> (< (pred n) n) :by (p/and-intro <a> <b>)))

  (qed <c>))

(comment

  ;; TODO

(defthm le-lt-pred
  [[m n nat]]
  (==> (< m n)
       (<= m (pred n))))

(try-proof 'le-lt-pred
  "By case analysis on n"

  "Case zero"
  
  (assume [H0 (< m zero)]
    (have <a1> (<= m zero) :by ((lt-le m zero) H0))
    (have <a2> (= m zero) :by ((le-zero-right m) <a1>))
    (have <a3> p/absurd :by ((p/and-elim-right H0) <a2>))
    (have <a> _ :by (<a3> (<= m (pred zero)))))

  "Case (succ n)"

  (assume [n nat
           Hn (< m (succ n))]

    "We have to show (<= m (pred (succ n)))"
    
    (have <b1> (= (pred (succ n)) n) :by (minus/pred-succ n))
    

)

)
)
