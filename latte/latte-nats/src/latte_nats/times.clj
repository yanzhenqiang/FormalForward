(ns latte-nats.times
  "The multiplication defined on ℕ."

  (:refer-clojure :exclude [and or not int = + *])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof qed search-theorem]]

            [latte.utils :as u]

            [latte-prelude.prop :as p :refer [and or not <=>]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.algebra :as alg]

            [latte-sets.quant :as sq :refer [forall-in]]
            
            [latte-nats.core :as nats :refer [nat = <> zero succ]]
            [latte-nats.rec :as rec]
            [latte-nats.plus :as plus :refer [+]]
                       ))

(definition mult-prop
  "The property of the multiplication of `m` to a natural integer."
  [[m nat]]
  (lambda [g (==> nat nat)]
    (and (= (g zero) zero)
         (forall [n nat]
           (= (g (succ n)) (+ m (g n)))))))

(defthm mult-unique
  "The unicity of the multiplication function, through [[mult-prop]]."
  [[m nat]]
  (q/unique (mult-prop m)))

(proof 'mult-unique
  (qed (rec/nat-recur zero (lambda [n nat] (+ m n)))))


(definition times
  "The function that multiplies `m` to a natural number"
  [[m nat]]
  (q/the (mult-unique m)))

(definition *
  "The function that multiplies `m` with `n`."
  [[m nat] [n nat]]
  ((times m) n))


(defthm times-prop
  [[m nat]]
  (and (= (* m zero) zero)
       (forall [n nat]
         (= (* m (succ n))
            (+ m (* m n))))))

(proof 'times-prop
  (qed (q/the-prop (mult-unique m))))

;; now that we have the main property we can make
;; the basic definitions opaque
(u/set-opacity! #'mult-prop true)

(defthm times-zero
  [[n nat]]
  (= (* n zero)
     zero))

(proof 'times-zero
  (qed (p/and-elim-left (times-prop n))))


(defthm times-succ
  [[m nat] [n nat]]
  (= (* m (succ n))
     (+ m (* m n))))

(proof 'times-succ
  (qed ((p/and-elim-right (times-prop m)) n)))

(defthm times-succ-swap-right
  [[m nat] [n nat]]
  (= (* m (succ n))
     (+ (* m n) m)))

(proof 'times-succ-swap-right
  (have <a> (= (+ m (* m n))
               (+ (* m n) m))
        :by (plus/plus-commute m (* m n)))
  (qed (eq/rewrite (times-succ m n) <a>)))

;; from now on times-prop is not needed
(u/set-opacity! #'times-prop true)
(u/set-opacity! #'times true)
(u/set-opacity! #'* true)

(defthm times-zero-swap
  [[n nat]]
  (= (* zero n)
     zero))

(proof 'times-zero-swap
  "This is by induction on `n`."
  (pose P := (lambda [k nat] (= (* zero k)
                                zero)))
  "Base case: n=0"
  (have <a> (P zero)
        :by (times-zero zero))
  "Inductive case"
  (assume [k nat
           Hind (= (* zero k)
                   zero)]
    (have <b1> (= (* zero (succ k))
                  (+ zero (* zero k)))
          :by (times-succ zero k))
    (have <b2> (= (* zero (succ k))
                  (* zero k))
          :by (eq/rewrite <b1> (plus/plus-zero-swap (* zero k))))
    (have <b> (P (succ k))
          :by (eq/rewrite <b2> Hind)))
  "Conclusion"
  (qed (((nats/nat-induct P) <a> <b>) n)))

(defthm times-succ-swap-left
  [[n nat] [m nat]]
  (= (* (succ n) m)
     (+ m (* n m))))

;; This one is a fairly cumbersome one ...
(proof 'times-succ-swap-left
  "We proceed by induction on m"
  (pose P := (lambda [k nat] (= (* (succ n) k)
                                (+ k (* n k)))))
  "Base case m=0"
  (have <a1> (= (* (succ n) zero)
                zero)
        :by (times-zero (succ n)))
  (have <a2> (= (+ zero (* n zero))
                (+ zero zero))
        :by (eq/eq-cong (lambda [k nat] (+ zero k))
                        (times-zero n)))
  (have <a3> (= (+ zero (* n zero))
                zero)
        :by (eq/rewrite <a2> (plus/plus-zero zero)))
  (have <a4> (= zero
                (+ zero (* n zero)))
        :by (eq/eq-sym <a3>))
  (have <a> (P zero) :by (eq/eq-trans <a1> <a4>))
  "Inductive case"
  (assume [k nat
           Hind (= (* (succ n) k)
                   (+ k (* n k)))]
    (have <b1> (= (* (succ n) (succ k))
                  (+ (succ n) (* (succ n) k)))
          :by (times-succ (succ n) k))

    (have <b2> (= (+ (succ n) (* (succ n) k))
                  (+ (succ n) (+ k (* n k))))
          :by (eq/eq-cong (lambda [j nat] (+ (succ n) j))
                          Hind))

    (have <b2'> (= (+ (succ n) (* (succ n) k))
                  (+ (succ n) (+ (* n k) k)))
          :by (eq/rewrite <b2> (plus/plus-commute k (* n k))))

    (have <b3> (= (+ (succ n) (* (succ n) k))
                  (succ (+ n (+ (* n k) k))))
          :by (eq/rewrite <b2'> (plus/plus-succ-swap n (+ (* n k) k))))
    
    (have <b4> (= (+ (succ n) (* (succ n) k))
                  (succ (+ (+ n (* n k)) k)))
          :by (eq/rewrite <b3> (plus/plus-assoc n (* n k) k)))

    (have <b5> (= (+ (succ n) (* (succ n) k))
                  (succ (+ (+ (* n k) n) k)))
          :by (eq/rewrite <b4> (plus/plus-commute n (* n k))))

    (have <b6> (= (+ (succ n) (* (succ n) k))
                  (succ (+ (* n (succ k)) k)))
          :by (eq/rewrite <b5> (eq/eq-sym (times-succ-swap-right n k))))

    (have <b7> (= (+ (succ n) (* (succ n) k))
                  (+ (* n (succ k)) (succ k)))
          :by (eq/rewrite <b6> (plus/plus-succ-sym (* n (succ k)) k)))

    (have <b8> (= (+ (succ n) (* (succ n) k))
                  (+ (succ k) (* n (succ k))))
          :by (eq/rewrite <b7> (plus/plus-commute (* n (succ k)) (succ k))))

    (have <b> (P (succ k))
          :by (eq/eq-trans <b1> <b8>)))

  "Conclusion"
  (qed (((nats/nat-induct P) <a> <b>) m)))


(defthm times-commute
  "Commutativity of multiplication."
  [[m nat] [n nat]]
  (= (* m n) (* n m)))

(proof 'times-commute
  "By induction on `m`."
  (pose P := (lambda [k nat] (= (* k n) (* n k))))
  "Base case."
  (have <a1> (= (* zero n) zero)
        :by (times-zero-swap n))
  (have <a2> (= zero (* n zero))
        :by (eq/eq-sym (times-zero n)))  
  (have <a> (P zero) :by (eq/eq-trans <a1> <a2>))
  "Inductive cases."
  (assume [k nat
           Hind (= (* k n) (* n k))]
    (have <b1> (= (* (succ k) n)
                  (+ n (* k n)))
          :by (times-succ-swap-left k n))
    (have <b2> (= (* (succ k) n)
                  (+ n (* n k)))
          :by (eq/rewrite <b1> Hind))
    (have <b>(P (succ k))
          :by (eq/rewrite <b2> (eq/eq-sym (times-succ n k)))))

  "Conclusion"
  (qed (((nats/nat-induct P) <a> <b>) m)))

(defthm times-succ-swap-both
  [[m nat] [n nat]]
  (= (* (succ n) m)
     (+ (* m n) m)))

(try-proof 'times-succ-swap-both
  (have <a> (= (* (succ n) m) 
               (+ m (* n m)))
        :by (times-succ-swap-left n m))
  (have <b> (= (* (succ n) m)
               (+ m (* m n)))
        :by (eq/rewrite <a> (times-commute n m)))
  (have <c> (= (* (succ n) m)
               (+ (* m n) m))
        :by (eq/rewrite <b> (plus/plus-commute m (* m n))))
  (qed <c>))
  

(defthm times-dist-plus
  "Distributivity of multiplication over addition."
  [[m nat] [n nat] [p nat]]
  (= (* m (+ n p))
     (+ (* m n) (* m p))))

;; The proof is quite long so we extract
;; the inductive subcase as an auxiliary lemma.

(deflemma times-dist-plus-succ
  [[m nat][n nat] [p nat]]
  (==> (= (* m (+ n p))
          (+ (* m n) (* m p)))
       (= (* (succ m) (+ n p))
          (+ (* (succ m) n) (* (succ m) p)))))

(proof 'times-dist-plus-succ
  (assume [Hind _]
    
    (have <a> (= (* (+ n p) (succ m))
                 (+ (* (+ n p) m) (+ n p)))
          :by (times-succ-swap-right (+ n p) m))
    

    (have <b> (= (* (+ n p) (succ m))
                 (+ (* m (+ n p)) (+ n p)))
          :by (eq/rewrite <a> (times-commute (+ n p) m))) 

    (have <c> (= (* (succ m) (+ n p))
                 (+ (* m (+ n p)) (+ n p)))
          :by (eq/rewrite <b> (times-commute (+ n p) (succ m))))

    (have <d> (= (* (succ m) (+ n p))
                 (+ (+ (* m n) (* m p)) (+ n p)))
          :by (eq/rewrite <c> Hind))

    (have <e> (= (* (succ m) (+ n p))
                 (+ (* m n) (+ (* m p) (+ n p))))
          :by (eq/rewrite <d> (eq/eq-sym (plus/plus-assoc (* m n) (* m p) (+ n p)))))


    (have <f> (= (* (succ m) (+ n p))
                 (+ (* m n) (+ (* m p) (+ p n))))
          :by (eq/nrewrite 2 <e> (plus/plus-commute n p))) 

    (have <g> (= (* (succ m) (+ n p))
                 (+ (* m n) (+ (+ (* m p) p) n)))
          :by (eq/rewrite <f> (plus/plus-assoc (* m p) p n)))

    (have <h> (= (* (succ m) (+ n p))
                 (+ (* m n) (+ n (+ (* m p) p))))
          :by (eq/rewrite <g> 
                          (plus/plus-commute (+ (* m p) p) n)))

    (have <i> (= (* (succ m) (+ n p))
                 (+ (+ (* m n) n) (+ (* m p) p)))
          :by (eq/rewrite <h> (plus/plus-assoc (* m n) n (+ (* m p) p)))) 

    (have <j> (= (* (succ m) (+ n p))
                 (+ (+ (* n m) n) (+ (* m p) p)))
          :by (eq/rewrite <i> (times-commute m n)))

    (have <k> (= (* (succ m) (+ n p))
                 (+ (* n (succ m)) (+ (* m p) p)))
          :by (eq/rewrite <j> (eq/eq-sym (times-succ-swap-right n m))))

    (have <l> (= (* (succ m) (+ n p))
                 (+ (* n (succ m)) (+ (* p m) p)))
          :by (eq/rewrite <k> (times-commute m p)))

    (have <m> (= (* (succ m) (+ n p))
                 (+ (* n (succ m)) (* p (succ m))))
          :by (eq/rewrite <l> (eq/eq-sym (times-succ-swap-right p m)))) 

    (have <n> (= (* (succ m) (+ n p))
                 (+ (* (succ m) n) (* p (succ m))))
          :by (eq/rewrite <m> (times-commute n (succ m))))

    (have <o> (= (* (succ m) (+ n p))
                 (+ (* (succ m) n) (* (succ m) p)))
          :by (eq/rewrite <n> (times-commute p (succ m)))))

  (qed <o>))

(proof 'times-dist-plus
  (pose P := (lambda [k nat]
               (= (* k (+ n p))
                  (+ (* k n) (* k p)))))
  "By induction on m"
  "Case m=0"
  (have <a1> (= (* zero (+ n p))
                zero)
        :by (times-zero-swap (+ n p)))
  (have <a2> (= (* zero n) zero)
        :by (times-zero-swap n))
  (have <a3> (= (+ (* zero n) (* zero p))
                (+ zero (* zero p)))
        :by (eq/eq-cong (lambda [$ nat] (+ $ (* zero p))) <a2>))
  (have <a4> (= (* zero p) zero)
        :by (times-zero-swap p))
  (have <a5> (= (+ (* zero n) (* zero p))
                (+ zero zero))
        :by (eq/nrewrite 2 <a3> <a4>))
  (have <a6> (= (+ (* zero n) (* zero p))
                zero)
        :by (eq/rewrite <a5> (plus/plus-zero zero)))
  (have <a> (P zero) :by (eq/eq-trans <a1> (eq/eq-sym <a6>)))

  "Inductive case"
  (assume [k nat
           Hind (P k)]
    (have <b> (P (succ k)) :by ((times-dist-plus-succ k n p) Hind)))

  (qed (((nats/nat-induct P) <a> <b>) m)))

(defthm times-assoc
  "Associativity of multiplication."
  [[m nat] [n nat] [p nat]]
  (= (* (* m n) p)
     (* m (* n p))))

(proof 'times-assoc
  "By induction on `p`."
  (pose P := (lambda [k nat]
               (= (* (* m n) k)
                  (* m (* n k)))))
  "Base case"
  (have <a1> (= (* (* m n) zero)
                zero)
        :by (times-zero (* m n)))
  (have <a2> (= (* m (* n zero))
                (* m zero))
        :by (eq/eq-cong (lambda [j nat] (* m j))
                        (times-zero n))) 
  (have <a3> (= (* m (* n zero))
                zero)
        :by (eq/rewrite <a2> (times-zero m)))

  (have <a> (P zero) :by (eq/eq-trans <a1> (eq/eq-sym <a3>)))
  
  "Inductive cases."
  (assume [k nat
           Hind (P k)]

    (have <b1> (= (* (* m n) (succ k))
                  (+ (* (* m n) k) (* m n)))
          :by (times-succ-swap-right (* m n) k))

    (have <b2> (= (* (* m n) (succ k))
                  (+ (* m (* n k)) (* m n)))
          :by (eq/rewrite <b1> Hind))

    (have <b3> (= (* (* m n) (succ k))
                  (* m (+ (* n k) n)))
          :by (eq/rewrite <b2> (eq/eq-sym (times-dist-plus m (* n k) n))))

    (have <b> (P (succ k))
      #_(= (* (* m n) (succ k))
         (* m (* n (succ k))))
          :by (eq/rewrite <b3> (eq/eq-sym (times-succ-swap-right n k)))))

  "Conclusion"
  (qed (((nats/nat-induct P) <a> <b>) p)))

(comment

(defthm times-right-cancel
  [[m nat] [n nat] [p nat]]
  (==> (<> m zero)
       (= (* m n) (* m p))
       (= n p)))

(try-proof 'times-right-cancel
  "By induction on m"
  (pose P := (lambda [k nat]
               (==> (<> k zero)
                    (= (* k n) (* k p))
                    (= n p))))
  "Base case m=0"
  (assume [Hcontra (<> zero zero)
           H2 (= (* zero n) (* zero p))]
    (have <a1> (= zero zero) :by (eq/eq-refl zero))
    (have <a2> p/absurd :by (Hcontra <a1>))
    (have <a3> (= n p) :by (<a2> (= n p))))
  (have <a> (P zero) :by <a3>)

  "Inductive case"
  (assume [k nat Hind (P k)]
    (assume [H1 (<> (succ k) zero) ;; <= this is a tautology
             H2 (= (* (succ k) n) (* (succ k) p))]

      (have <b1> (= (+ n (* k n)) (* (succ k) p))
            :by (eq/rewrite H2 (times-succ-swap-left k n)))
      (have <b2> (= (+ n (* k n)) (+ p (* k p)))
            :by (eq/rewrite <b1> (times-succ-swap-left k p)))
      (have <c> (or (= k zero)
                    (exists [j nat] (= k (succ j))))
            :by (nats/nat-split k))
      (assume [Hzero (= k zero)]
        (have <d1> (= (+ n (* zero n)) (+ p (* k p)))
              :by (eq/rewrite <b2> Hzero))
        (have <d2> (= (+ n zero) (+ p (* k p)))
              :by (eq/rewrite <d1> (times-zero-swap n)))
        (have <d3> (= n (+ p (* k p)))
              :by (eq/rewrite <d2> (plus/plus-zero n)))
        (have <d4> (= n (+ p (* zero p)))
              :by (eq/rewrite <d3> Hzero))
        (have <d5> (= n (+ p zero))
              :by (eq/rewrite <d4> (times-zero-swap p)))
        (have <d> (= n p) :by (eq/rewrite <d5> (plus/plus-zero p))))

      (assume [Hsucc (exists [j nat] (= k (succ j)))]
        (assume [j nat 
                 Hj (= k (succ j))]
          ))

)))

)



