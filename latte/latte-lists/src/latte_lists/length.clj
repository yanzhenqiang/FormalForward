(ns latte-lists.length
  "The length of finite lists."

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

            [latte-nats.core :as n]
            [latte-nats.plus :as np]

            [latte-lists.core :as l]
            [latte-lists.append :as app :refer [append]]


            )

)

(definition length-property
  [T :type]
  (lambda [g (==> (l/list T) n/nat)]
    (and (equal (g (l/null T)) n/zero)
         (forall [xs (l/list T)]
           (forall [x T]
             (equal (g (l/cons x xs)) (n/succ (g xs))))))))


(defthm length-unique
  [T :type]
  (q/unique (length-property T)))

(proof 'length-unique
  (qed (l/list-recur n/zero (lambda [x T] (lambda [k n/nat] (n/succ k))))))

(definition length-fun
  [T :type]
  (q/the (length-unique T)))

(defthm length-fun-prop
  [T :type]
  (and (equal ((length-fun T) (l/null T)) n/zero)
       (forall [xs (l/list T)]
         (forall [x T]
           (equal ((length-fun T) (l/cons x xs))
                  (n/succ ((length-fun T) xs)))))))

(proof 'length-fun-prop
  (qed (q/the-prop (length-unique T))))


(definition length
  "The length of list `xs`"
  [[?T :type] [xs (l/list T)]]
  ((length-fun T) xs))

(defthm length-null
  [T :type]
  (n/= (length (l/null T)) n/zero))

(proof 'length-null
  (qed (p/and-elim-left (length-fun-prop T))))

(defthm length-cons
  [[?T :type] [x T] [xs (l/list T)]]
  (n/= (length (l/cons x xs))
       (n/succ (length xs))))

(proof 'length-cons-thm
  (qed ((p/and-elim-right (length-fun-prop T)) xs x)))


(defthm append-length
  [[?T :type] [xs ys (l/list T)]]
  (n/= (length (append xs ys))
       (np/+ (length xs) (length ys))))


(proof 'append-length-thm
  
  (pose P := (lambda [$ (l/list T)]
               (n/= (length (append $ ys))
                    (np/+ (length $) (length ys)))))

  "By induction"

  "Base case"

  (have <a1> (equal (append (l/null T) ys)
                    ys)
        :by (app/append-null-left ys))

  (have <a> (n/= (length (append (l/null T) ys))
                  (length ys))
        :by (eq/eq-cong (length-def T) <a1>))

  (have <b1> (n/= (length (l/null T)) n/zero)
        :by (length-null T))

  (have <b2> (n/= (np/+ (length (l/null T)) (length ys))
                  (np/+ n/zero (length ys)))
        :by (eq/eq-cong (lambda [$ n/nat] (np/+ $ (length ys))) <b1>))

  (have <b3> (n/= (np/+ n/zero (length ys))
                  (length ys))
        :by (np/plus-zero-swap (length ys)))

  (have <b> (n/= (length ys)
                  (np/+ (length (l/null T)) (length ys)))
        :by (eq/eq-sym (eq/eq-trans <b2> <b3>)))

  (have <c> (P (l/null T)) :by (eq/eq-trans <a> <b>))

  "Inductive case"

  (assume [xs (l/list T)
           Hind (P xs)
           x T]

    (have <d1> (equal (append (l/cons x xs) ys)
                      (l/cons x (append xs ys)))
          :by (app/append-cons x xs ys))

    (have <d> (n/= (length (append (l/cons x xs) ys))
                    (length (l/cons x (append xs ys))))
          :by (eq/eq-cong (length-def T) <d1>))

    (have <e> (n/= (length (l/cons x (append xs ys)))
                    (n/succ (length (append xs ys))))
          :by (length-cons x (append xs ys)))

    (have <f1> (n/= (length (append xs ys))
                    (np/+ (length xs) (length ys)))
          :by Hind)

    (have <f> (n/= (n/succ (length (append xs ys)))
                    (n/succ (np/+ (length xs) (length ys))))
          :by (eq/eq-cong n/succ <f1>))

    (have <g> (n/= (n/succ (np/+ (length xs) (length ys)))
                    (np/+ (n/succ (length xs)) (length ys)))
          :by (eq/eq-sym (np/plus-succ-swap (length xs) (length ys))))

    (have <h1> (n/= (n/succ (length xs))
                    (length (l/cons x xs)))
          :by (eq/eq-sym (length-cons x xs)))

    (have <h> (n/= (np/+ (n/succ (length xs)) (length ys))
                   (np/+ (length (l/cons x xs)) (length ys)))
          :by (eq/eq-cong (lambda [$ n/nat] (np/+ $ (length ys))) <h1>))
  
    (have <i> (P (l/cons x xs))
          :by (eq/eq-trans* <d> <e> <f> <g> <h>)))

  "Use the induction principle"
  (qed ((lists/list-induct P) <c> <i> xs)))




