(ns latte-lists.append
  "The append function on lists."
  (:refer-clojure :exclude [list cons and or not int =])

  (:require [latte.core :as latte :refer [defaxiom defthm try-defthm
                                          definition try-definition
                                          lambda forall pose
                                          proof try-proof assume have qed]]

            [latte.utils :as u :refer [decomposer]]

            [latte-prelude.prop :as p :refer [not or and]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.algebra :as alg]

            [latte-lists.core :as lists :refer [list null cons]]
            )
  )

(definition append-property
  [[?T :type] [ys (list T)]]
  (lambda [g (==> (list T) (list T))]
    (and (equal (g (null T)) ys)
         (∀ [xs (list T)]
          (∀ [x T]
           (equal (g (cons x xs)) (cons x (g xs))))))))

(defthm append-unique
  [[?T :type] [ys (list T)]]
  (q/unique (append-property ys)))

(proof 'append-unique-thm
  (qed (lists/list-recur ys  (lists/cons-ax T))))

(definition append-fun
  [[?T :type] [ys (list T)]]
  (q/the (append-unique ys)))

(defthm append-fun-prop
  [[?T :type] [ys (list T)]]
  (and (equal ((append-fun ys) (null T)) ys)
       (forall [xs (list T)]
         (forall [x T]
           (equal ((append-fun ys) (cons x xs))
                  (cons x ((append-fun ys) xs)))))))

(proof 'append-fun-prop-thm
  (qed (q/the-prop (append-unique ys))))

(definition append
  [[?T :type] [xs ys (list T)]]
  ((append-fun ys) xs))

(defthm append-null-left
  [[?T :type] [xs (list T)]]
  (equal (append (null T) xs) xs))

(proof 'append-null-left-thm
  (qed (p/and-elim-left (append-fun-prop xs))))

(defthm append-cons
  [[?T :type] [x T] [xs ys (list T)]]
  (equal (append (cons x xs) ys)
         (cons x (append xs ys))))

(proof 'append-cons-thm
  (qed ((p/and-elim-right (append-fun-prop ys)) xs x)))

(defthm append-null-right
  [[?T :type] [xs (list T)]]
  (equal (append xs (null T)) xs))

(proof 'append-null-right-thm
  (pose P := (lambda [xs (list T)] 
               (equal (append xs (null T)) xs)))
  
  "By structural induction"

  "Base case"
  (have <a> (P (null T))
        :by (append-null-left (null T)))

  "Inductive case"
  (assume [xs (list T)
           Hind (P xs)
           x T]
    "Now we have to prove (P (cons x xs))"
    
    (have <b1> (equal (cons x (append xs (null T)))
                      (cons x xs))
          :by (eq/eq-cong (lambda [$ (list T)] (cons x $)) Hind))

    (have <b2> (equal (append (cons x xs) (null T))
                      (cons x (append xs (null T))))
          :by (append-cons x xs (null T)))
    
    (have <b> (P (cons x xs)) :by (eq/eq-trans <b2> <b1>)))

  "Use the induction principle"
  (qed ((lists/list-induct P) <a> <b> xs)))

(defthm append-assoc
  [[?T :type] [xs ys zs (list T)]]
  (equal (append (append xs ys) zs)
         (append xs (append ys zs))))

(proof 'append-assoc-thm
  (pose P := (lambda [$ (list T)]
               (equal (append (append $ ys) zs)
                      (append $ (append ys zs)))))

  "By induction"
  "Base case"

  (have <a1> (equal (append (null T) ys)
                    ys)
        :by (append-null-left ys))

  (have <a2> (equal (append (append (null T) ys) zs)
                    (append ys zs))
        :by (eq/eq-cong (lambda [$ (list T)] (append $ zs)) <a1>))

  (have <a3> (equal (append ys zs)
                    (append (null T) (append ys zs)))
        :by (eq/eq-sym (append-null-left (append ys zs))))

  (have <a> (P (null T)) :by (eq/eq-trans <a2> <a3>))

  "Inductive case"

  (assume [xs (list T)
           Hind (P xs)
           x T]
    "Now we have to prove (P (cons x xs))"
    
    (have <b1> (equal (append (cons x xs) ys)
                      (cons x (append xs ys)))
          :by (append-cons x xs ys))

    (have <b2> (equal (append (append (cons x xs) ys) zs)
                      (append (cons x (append xs ys)) zs))
          :by (eq/eq-cong (lambda [$ (list T)] (append $ zs)) <b1>))

    (have <b3> (equal (append (cons x (append xs ys)) zs)
                      (cons x (append (append xs ys) zs)))
          :by (append-cons x (append xs ys) zs))

    (have <b4> (equal (append (append xs ys) zs)
                      (append xs (append ys zs)))
          :by Hind)

    (have <b5> (equal (cons x (append (append xs ys) zs))
                      (cons x (append xs (append ys zs))))
          :by (eq/eq-cong (lambda [$ (list T)] (cons x $)) <b4>))

    (have <b6> (equal (cons x (append xs (append ys zs)))
                      (append (cons x xs) (append ys zs)))
          :by (eq/eq-sym (append-cons x xs (append ys zs))))

    (have <b> (P (cons x xs)) :by (eq/eq-trans* <b2> <b3> <b5> <b6>)))

  (qed ((lists/list-induct P) <a> <b> xs)))


;;; monoid properties

(defthm append-associative
  [T :type]
  (alg/associative (append-def T)))

(proof 'append-associative
  (assume [xs (list T) ys (list T) zs (list T)]
    (have <a> _ :by (eq/eq-sym (append-assoc xs ys zs))))
  (qed <a>))

(defthm append-id-left
  [T :type]
  (alg/identity-left (append-def T) (null T)))

(proof 'append-id-left
  (assume [xs (list T)]
    (have <a> _ :by (append-null-left xs)))
  (qed <a>))

(defthm append-id-right
  [T :type]
  (alg/identity-right (append-def T) (null T)))

(proof 'append-id-right
  (assume [xs (list T)]
    (have <a> _ :by (append-null-right xs)))
  (qed <a>))

(defthm append-monoid
  [T :type]
  (alg/monoid (append-def T) (null T)))

(proof 'append-monoid
  (qed (p/and-intro* (append-associative T)
                     (append-id-left T)
                     (append-id-right T))))

