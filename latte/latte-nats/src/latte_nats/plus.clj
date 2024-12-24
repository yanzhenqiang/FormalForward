(ns latte-nats.plus
  "The addition defined on ℕ."

  (:refer-clojure :exclude [and or not int = +])

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
            
            [latte-nats.core :as nats :refer [nat = zero succ one]]
            [latte-nats.rec :as rec]
                       ))

(definition add-prop
  "The property of the addition of `m` to a natural integer."
  [[m nat]]
  (lambda [g (==> nat nat)]
    (and (= (g zero) m)
         (forall [n nat]
           (= (g (succ n)) (succ (g n)))))))

(defthm add-unique
  "The unicity of the addition function, through [[add-prop]]."
  [[m nat]]
  (q/unique (add-prop m)))

(proof 'add-unique
  (qed (rec/nat-recur m succ)))

(definition plus
  "The function that adds `m` to a natural integer"
  [[m nat]]
  (q/the (add-unique m)))

(definition +
  "The function that adds `m` to `n`."
  [[m nat] [n nat]]
  ((plus m) n))

(defthm plus-prop
  [[m nat]]
  (and (= ((plus m) zero) m)
       (forall [n nat]
         (= ((plus m) (succ n))
            (succ ((plus m) n))))))

(proof 'plus-prop
  (qed (q/the-prop (add-unique m))))

(defthm plus-zero
  [[m nat]]
  (= (+ m zero) m))

(proof 'plus-zero
  (qed (p/and-elim-left (plus-prop m))))

(defthm plus-succ
  [[m nat] [n nat]]
  (= (+ m (succ n))
     (succ (+ m n))))

(proof 'plus-succ
  (qed ((p/and-elim-right (plus-prop m)) n)))

(defthm plus-one-succ
  [n nat]
  (= (+ n one)
     (succ n)))

(proof 'plus-one-succ
  (have <a> (= (+ n one)
               (succ (+ n zero)))
        :by (plus-succ n zero))
  (have <b> (= (+ n zero) n)
        :by (plus-zero n))

  (qed (eq/eq-subst (lambda [$ nat]
                            (= (+ n one)
                               (succ $))) <b> <a>)))

;; make the basic definitions opaque
;; (otherwise terms become extra-large)
(u/set-opacity! #'plus-prop true)
(u/set-opacity! #'plus true)
(u/set-opacity! #'+ true)

(defthm plus-zero-swap
  [[m nat]]
  (= (+ zero m) m))

(proof 'plus-zero-swap
  "We proceed by induction on `m`."
  "First the case for m=0"
  (have <a> (= (+ zero zero) zero)
        :by (plus-zero zero))
  "Then the inductive case, we assume `(P m)` for some `m`."
  (assume [m nat
           Hind (= (+ zero m) m)]
    "We must show `(P (succ m))`."
    (have <b1> (= (+ zero (succ m))
                  (succ (+ zero m)))
          :by (plus-succ zero m))
    (have <b> (= (+ zero (succ m))
                 (succ m))
          :by (eq/rewrite <b1> Hind)))
  (qed (((nats/nat-induct (lambda [m nat]
                           (= (+ zero m) m)))
        <a> <b>) m)))

(defthm plus-succ-sym
  [[m nat] [n nat]]
  (= (succ (+ m n))
     (+ m (succ n))))

(proof 'plus-succ-sym
  (qed (eq/eq-sym (plus-succ m n))))

(defthm plus-succ-swap
  [[m nat] [n nat]]
  (= (+ (succ m) n)
     (succ (+ m n))))

(proof 'plus-succ-swap
  (have <a1> (= (+ (succ m) zero)
                (succ m))
        :by (plus-zero (succ m)))
  (have <a2> (= (succ m)
                (succ (+ m zero)))
        :by (eq/eq-cong succ (eq/eq-sym (plus-zero m))))
  (have <a> (= (+ (succ m) zero)
               (succ (+ m zero)))
        :by (eq/eq-trans <a1> <a2>))
  (assume [n nat
           Hind (= (+ (succ m) n)
                   (succ (+ m n)))]
    "We show `P (succ n)`."
    (have <b1> (= (+ (succ m) (succ n))
                  (succ (+ (succ m) n)))
          :by (plus-succ (succ m) n))
    (have <b2> (= (succ (+ (succ m) n))
                  (succ (succ (+ m n))))
          :by (eq/eq-cong succ Hind))
    (have <b3> (= (+ (succ m) (succ n))
                  (succ (succ (+ m n))))
          :by (eq/eq-trans <b1> <b2>))
    (have <b4> (= (succ (succ (+ m n)))
                  (succ (+ m (succ n))))
          :by (eq/eq-cong succ (eq/eq-sym (plus-succ m n))))
    (have <b> (= (+ (succ m) (succ n))
                 (succ (+ m (succ n))))
          :by (eq/eq-trans <b3> <b4>)))

  (qed (((nats/nat-induct (lambda [n nat]
                            (= (+ (succ m) n)
                               (succ (+ m n)))))
         <a> <b>) n)))


(defthm plus-commute
  [[m nat] [n nat]]
  (= (+ m n)
     (+ n m)))

(proof 'plus-commute
  "We proceed by induction on `m`."
  (pose P := (lambda [k nat] (= (+ k n) (+ n k))))
  "First let's prove `(P zero)`."
  (have <a1> (= n (+ n zero))
        :by (eq/eq-sym (plus-zero n)))
  (have <a> (P zero) :by (eq/eq-trans (plus-zero-swap n) <a1>))
  "Now the inductive cases."
  (assume [k nat
           Hind (P k)]
    "We show `(P (succ k))`."
    (have <b1> (= (+ (succ k) n)
                  (succ (+ k n)))
          :by (plus-succ-swap k n))
    (have <b2> (= (succ (+ k n))
                  (succ (+ n k)))
          :by (eq/eq-cong succ Hind))
    (have <b3> (= (+ (succ k) n)
                  (succ (+ n k))) :by (eq/eq-trans <b1> <b2>))
    (have <b4> (= (succ (+ n k))
                  (+ n (succ k))) :by (eq/eq-sym (plus-succ n k)))
    (have <b> (P (succ k)) :by (eq/eq-trans <b3> <b4>)))

  "Now we apply integer induction."
  (have <e> (P m) :by ((nats/nat-induct P) <a> <b> m))
  (qed <e>))

(defthm plus-assoc
  [[m nat] [n nat] [p nat]]
  (= (+ m (+ n p))
     (+ (+ m n) p)))

(proof 'plus-assoc
    (pose P := (lambda [k nat]
               (= (+ m (+ n k))
                  (+ (+ m n) k))))
  "We prove `P` by induction on `k`."
  "First `(P zero)`"
  (have <a1> (= (+ m (+ n zero))
                (+ m n))
        :by (eq/eq-cong (lambda [k nat] (+ m k))
                         (plus-zero n)))
  (have <a2> (= (+ m n)
                (+ (+ m n) zero))
        :by (eq/eq-sym (plus-zero (+ m n))))
  (have <a> (P zero) :by (eq/eq-trans <a1> <a2>))
  "Then the inductive cases."
  (assume [p nat
           Hind (= (+ m (+ n p))
                   (+ (+ m n) p))]
    "Let's prove `(P (succ p))`."
    (have <b1> (= (+ m (+ n (succ p)))
                  (+ m (succ (+ n p))))
          :by (eq/eq-cong (lambda [k nat] (+ m k))
                          (plus-succ n p)))
    (have <b2>  (= (+ m (succ (+ n p)))
                   (succ (+ m (+ n p))))
          :by (plus-succ m (+ n p)))
    (have <b3> (= (+ m (+ n (succ p)))
                  (succ (+ m (+ n p))))
          :by (eq/eq-trans <b1> <b2>))
    (have <b4> (= (succ (+ m (+ n p)))
                  (succ (+ (+ m n) p)))
          :by (eq/eq-cong succ Hind))
    (have <b5> (= (+ m (+ n (succ p)))
                  (succ (+ (+ m n) p)))
          :by (eq/eq-trans <b3> <b4>))
    ;; = (+ (+ m n) (succ p))
    (have <b6> (= (succ (+ (+ m n) p))
                  (+ (+ m n) (succ p)))
          :by (eq/eq-sym (plus-succ (+ m n) p)))
    (have <b> (P (succ p))
          :by (eq/eq-trans <b5> <b6>)))
  (have <c> (P p) :by ((nats/nat-induct P) <a> <b> p))
  (qed <c>))

(defthm plus-comm-assoc
  [[m nat] [n nat] [p nat]]
  (= (+ (+ m n) p)
     (+ (+ m p) n)))

(proof 'plus-comm-assoc
  (have <a> (= (+ (+ m n) p)
               (+ m (+ n p)))
        :by (eq/eq-sym (plus-assoc m n p)))
  (have <b> (= (+ m (+ n p))
               (+ m (+ p n)))
        :by (eq/eq-cong (lambda [$ nat]
                          (+ m $)) (plus-commute n p)))
  (have <c> (= (+ m (+ p n))
               (+ (+ m p) n))
        :by (plus-assoc m p n))
  (qed (eq/eq-trans* <a> <b> <c>)))


(defthm plus-right-cancel
  [[m nat] [n nat] [p nat]]
  (==> (= (+ m p) (+ n p))
       (= m n)))

(proof 'plus-right-cancel
  "We proceed by induction."
  (pose P := (lambda [k nat]
               (==> (= (+ m k) (+ n k))
                    (= m n))))
  "Base case."
  (assume [Hz (= (+ m zero) (+ n zero))]
    (have <a1> (= m (+ n zero))
          :by (eq/rewrite Hz (plus-zero m)))
    (have <a2> (= m n)
          :by (eq/rewrite <a1> (plus-zero n))))
  (have <a> (P zero) :by <a2>)
  "Inductive case."
  (assume [k nat
           Hk (P k)]
    "Successor case."
    (assume [Hsucc (= (+ m (succ k)) (+ n (succ k)))]
      (have <b1> (= (succ (+ m k)) (+ n (succ k)))
            :by (eq/rewrite Hsucc (plus-succ m k)))
      (have <b2> (= (succ (+ m k)) (succ (+ n k)))
            :by (eq/rewrite <b1> (plus-succ n k)))
      (have <b3> (= (+ m k) (+ n k)) :by (nats/succ-injective (+ m k) (+ n k) <b2>))
      (have <b4> (= m n) :by (Hk <b3>)))
    (have <b> (P (succ k)) :by <b4>))
  "We apply the induction principle."
  (have <c> (P p) :by ((nats/nat-induct P) <a> <b> p))
  (qed <c>))

(defthm plus-left-cancel
  [[m nat] [n nat] [p nat]]
  (==>  (= (+ m n) (+ m p))
        (= n p)))

(proof 'plus-left-cancel
  (assume [H (= (+ m n) (+ m p))]
    (have <a> (= (+ n m) (+ m p))
          :by (eq/rewrite H (plus-commute m n))) 
    (have <b> (= (+ n m) (+ p m))
          :by (eq/rewrite <a> (plus-commute m p)))
    (have <c> (= n p) :by ((plus-right-cancel n p m) <b>)))
  (qed <c>))

(defthm plus-right-cancel-conv
  [[m nat] [n nat] [p nat]]
  (==> (= m n)
       (= (+ m p) (+ n p))))

(proof 'plus-right-cancel-conv
  (assume [H (= m n)]
    (have <a> (= (+ m p) (+ n p))
          :by (eq/eq-cong (lambda [k nat] (+ k p))
                          H)))
  (qed <a>))

(defthm plus-left-cancel-conv
  [[m nat] [n nat] [p nat]]
  (==> (= m n)
       (= (+ p m) (+ p n))))

(proof 'plus-left-cancel-conv
  (assume [H (= m n)]
    (have <a> (= (+ p m) (+ p n))
          :by (eq/eq-cong (lambda [k nat] (+ p k))
                          H)))
  (qed <a>))

(defthm plus-refl-zero
  [[n nat] [k nat]]
  (==> (= (+ n k) n)
       (= k zero)))

(proof 'plus-refl-zero
  (assume [H _]
    (have <a> (= n (+ n zero))
          :by (eq/eq-sym (plus-zero n)))
    (have <b> (= (+ n k) (+ n zero))
          :by (eq/nrewrite 2 H <a>))
    (have <c> (= k zero)
          :by ((plus-left-cancel n k zero) <b>)))
  (qed <c>))


(defthm plus-any-zero-left
  [[m nat] [n nat]]
  (==> (= (+ m n) zero)
       (= m zero)))

(proof 'plus-any-zero-left
  (pose P := (lambda [k nat] (==> (= (+ m k) zero)
                                  (= m zero))))
  "By case analysis"
  "Case zero"
  (assume [Hz (= (+ m zero) zero)]
    (have <a1> (= (+ m zero) m)
          :by (plus-zero m))
    (have <a2> (= m zero) :by (eq/rewrite Hz <a1>)))
  (have <a> (P zero) :by <a2>)

  "Case succ"
  (assume [k nat]
    (assume [Hsucc (= (+ m (succ k)) zero)]
      (have <b1> (= (succ (+ m k)) zero)
            :by (eq/rewrite Hsucc (plus-succ m k)))
      (have <b2> p/absurd :by ((nats/zero-not-succ (+ m k)) <b1>))
      (have <b3> (= m zero) :by (<b2> (= m zero))))
    (have <b> (P (succ k)) :by <b3>))

  (have <c> (forall [k nat] (P k)) :by ((nats/nat-case P) <a> <b>))
 
(qed (<c> n)))
    
(defthm plus-any-zero-right
  [[m nat] [n nat]]
  (==> (= (+ m n) zero)
       (= n zero)))

(proof 'plus-any-zero-right
  (have <a> (==> (= (+ n m) zero)
                 (= n zero))
        :by (plus-any-zero-left n m))
  (have <b> (= (+ n m) (+ m n))
        :by (plus-commute n m))
  (qed (eq/rewrite <a> <b>)))


;; ================================
;; Algebraic properties of addition
;; ================================

(defthm associative-plus
  []
  (alg/associative +))

(proof 'associative-plus
  (qed plus-assoc))

(defthm identity-left-plus
  []
  (alg/identity-left + zero))

;; (search-theorem 'latte-nats.plus '(= (+ zero ?x) ?y))

(proof 'identity-left-plus
  (qed plus-zero-swap))

(defthm identity-right-plus
  []
  (alg/identity-right + zero))

;; (search-theorem 'latte-nats.plus '(= (+ ?x zero) ?z))

(proof 'identity-right-plus
  (qed plus-zero))

(defthm identity-plus
  []
  (alg/identity + zero))

(proof 'identity-plus
  (qed (p/and-intro identity-left-plus
                    identity-right-plus)))

(defthm unique-identity-plus
  []
  (q/unique (alg/identity-def nat +)))

(proof 'unique-identity-plus
  (pose P := (alg/identity-def nat +))
  (have <a> (q/ex P) :by ((q/ex-intro P zero) identity-plus))
  (have <b> (q/single P) :by (alg/identity-single +))
  (qed (p/and-intro <a> <b>)))

(defthm cancel-left-plus
  []
  (alg/cancel-left +))

(proof 'cancel-left-plus
  (qed plus-left-cancel))

(defthm cancel-right-plus
  []
  (alg/cancel-right +))

(proof 'cancel-right-plus
  (assume [x nat y nat z nat]
    (have <a> _ :by (plus-right-cancel y z x)))
  (qed <a>))

(defthm monoid-plus
  []
  (alg/monoid + zero))

(proof 'monoid-plus
  (qed (p/and-intro* associative-plus
                     identity-left-plus
                     identity-right-plus)))

(defthm commutative-plus
  []
  (alg/commutative +))

(proof 'commutative-plus
  (qed plus-commute))





  
    
