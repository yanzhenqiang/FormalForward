(ns latte-nats.rec
  "The recursion theorem for natural numbers,
 together with its complete (somewhat non-trivial) formal proof."

  (:refer-clojure :exclude [and or not int = set])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof qed]]

            [latte-prelude.prop :as p :refer [and or not]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.classic :as classic]
            [latte-prelude.fun :as fun]

            [latte-sets.set :as set :refer [elem]]
            [latte-sets.rel :as rel :refer [rel]]
            [latte-sets.powerrel :as prel]

            [latte-nats.core :as nats :refer [nat zero succ =]]
            ))

(definition nat-recur-prop
  "The property of the recursion principle for natural numbers."
  [[?T :type] [x T] [f (==> T T)]]
  (lambda [g (==> nat T)]
    (and (equal (g zero) x)
         (forall [n nat]
           (equal (g (succ n)) (f (g n)))))))

(defthm nat-recur
  "The recursion principle for natural numbers.
cf. [[nat-recur-prop]]."
  [[?T :type] [x T] [f (==> T T)]]
  (q/unique (nat-recur-prop x f)))

(definition nat-recur-prop-rel
  "A relational variant of the recursion principle [[nat-recur-prop]]."
  [[?T :type] [x T] [f (==> T T)]]
  (lambda [R (rel nat T)]
     (and (R zero x)
          (forall [n nat]
            (forall [y T]
              (==> (R n y)
                   (R (succ n) (f y))))))))

(defthm nat-recur-prop-prop-rel
  [[?T :type] [x T] [f (==> T T)] [g (==> nat T)]]
  (==> ((nat-recur-prop x f) g)
       ((nat-recur-prop-rel x f) (rel/funrel g))))

(proof 'nat-recur-prop-prop-rel-thm
  (assume [H _]
    (pose R := (rel/funrel g))
    "First conjunct"
    (have <a1> (equal (g zero) x) 
          :by (p/and-elim-left H))
    (have <a> (R zero x) :by <a1>)
    "Second conjunct"
    (assume [n nat
             y T
             Hy (R n y)]
      (have <b1> (equal (g n) y) :by Hy)
      (have <b2> (equal (g (succ n)) (f (g n))) 
            :by ((p/and-elim-right H) n))
      (have <b3> (R (succ n) (f (g n))) :by <b2>)
      (have <b> (R (succ n) (f y)) 
            :by (eq/rewrite <b3> <b1>)))
    (have <c> _ :by (p/and-intro <a> <b>)))
  (qed <c>))

(defthm nat-recur-prop-rel-prop
  [[?T :type] [x T] [f (==> T T)] [g (==> nat T)]]
  (==> ((nat-recur-prop-rel x f) (rel/funrel g))
       ((nat-recur-prop x f) g)))

(proof 'nat-recur-prop-rel-prop-thm
  (assume [H _]
    "First conjunct"
    (have <a> (equal (g zero) x) :by (p/and-elim-left H))
    "Second conjunct"
    (assume [n nat]
      (have <b1> (equal (g n) (g n)) :by (eq/eq-refl (g n)))
      (have <b> (equal (g (succ n)) (f (g n)))
            :by ((p/and-elim-right H) n (g n) <b1>)))
    (have <c> _ :by (p/and-intro <a> <b>)))
  (qed <c>))

(definition nat-fixpoint-rel
  "The relational definition of the least fixed-point
for (primitive) recursive functions on natural numbers."
  [[?T :type] [x T] [f (==> T T)]]
  (prel/rintersections (nat-recur-prop-rel x f)))

;; The above in expanded form: 
;; (lambda [n nat]
;;   (lambda [y T]
;;     (forall [R (rel nat T)]
;;       (==> (prel/rel-elem R (nat-recur-prop-rel x f))
;;            (R n y)))))

(defthm nat-fixpoint-elem
  "The least (relational) fixpoint is ... least."
  [[?T :type] [x T] [f (==> T T)]]
  (prel/rel-elem (nat-fixpoint-rel x f) (nat-recur-prop-rel x f)))

(deflemma nat-fixpoint-zero
  [[?T :type] [x T] [f (==> T T)]]
  ((nat-fixpoint-rel x f) zero x))

(proof 'nat-fixpoint-zero-lemma
  (assume [R (rel nat T)
           HR (prel/rel-elem R (nat-recur-prop-rel x f))]
    (have <a> (R zero x) :by (p/and-elim-left HR)))
  (qed <a>))

(deflemma nat-fixpoint-succ
  [[?T :type] [x T] [f (==> T T)]]
  (forall [n nat]
    (forall [y T]
      (==> ((nat-fixpoint-rel x f) n y)
           ((nat-fixpoint-rel x f) (succ n) (f y))))))

(proof 'nat-fixpoint-succ-lemma
  (assume [n nat
           y T
           Hny ((nat-fixpoint-rel x f) n y)]
    (assume [R (rel nat T)
             HR (prel/rel-elem R (nat-recur-prop-rel x f))]
      (have <a> (R n y) :by (Hny R HR))
      (have <b> (R (succ n) (f y)) :by ((p/and-elim-right HR) n y <a>))))
  (qed <b>))


(proof 'nat-fixpoint-elem-thm
  (qed (p/and-intro (nat-fixpoint-zero x f)
                    (nat-fixpoint-succ x f))))

(defthm nat-fixpoint-prop
  "The main property of the least (relational) fixpoint [[nat-fixpoint-rel]]."
  [[?T :type] [x T] [f (==> T T)]]
  (forall [R (rel nat T)]
    (==> (prel/rel-elem R (nat-recur-prop-rel x f))
         (rel/subrel (nat-fixpoint-rel x f) R))))

(proof 'nat-fixpoint-prop-thm
  (qed (prel/rintersections-lower-bound (nat-recur-prop-rel x f))))


(deflemma nat-fixpoint-rel-uniq
  "The (relational) fixpoint characterization of recursion is unique.
This is the core of the proof for the recursion theorem for natural integers."
  [[?T :type] [x T] [f (==> T T)]]
  (forall [n nat]
    (q/unique (lambda [y T] ((nat-fixpoint-rel x f) n y)))))

(deflemma nat-fixpoint-rel-ex
  "The existential part of the relational recursion theorem
for natural numbers."
  [[?T :type] [x T] [f (==> T T)]]
  (forall [n nat]
    (exists [y T] ((nat-fixpoint-rel x f) n y))))

(proof 'nat-fixpoint-rel-ex-lemma
  "We proceed by induction on `n`."

  (pose FIX := (nat-fixpoint-rel x f))

  "Base case n=0 : we want to prove (FIX zero y) is true for some y."
  (have <a1> (FIX zero x) :by (nat-fixpoint-zero x f))
  (have <a> (exists [y T] (FIX zero y))
        :by ((q/ex-intro (lambda [y T] (FIX zero y)) x) <a1>))

  "Inductive case"
  (assume [n nat
           Hn (exists [y T] (FIX n y))]
    (assume [y T
             Hy (FIX n y)]
      (have <b1> (FIX (succ n) (f y))
            :by ((nat-fixpoint-succ x f) n y Hy))
      (have <b2> (exists [z T] (FIX (succ n) z))
            :by ((q/ex-intro (lambda [z T] (FIX (succ n) z)) (f y)) <b1>)))

    (have <b> (exists [z T] (FIX (succ n) z))
          :by ((q/ex-elim-rule (lambda [y T] (FIX n y)) (exists [z T] (FIX (succ n) z)))
               Hn <b2>)))

  (have <c> (forall [n nat]
              (exists [z T] (FIX n z)))
        :by ((nats/nat-induct (lambda [n nat]
                                (exists [z T] (FIX n z))))
             <a> <b>))

  (qed <c>))

(deflemma nat-fixpoint-rel-sing
  "The singleness part of the relational recursion theorem
for natural numbers."
  [[?T :type] [x T] [f (==> T T)]]
  (forall [n nat]
    (q/single (lambda [y T] ((nat-fixpoint-rel x f) n y)))))


(deflemma nat-fixpoint-rel-sing-zero-aux
  [[?T :type] [x T] [f (==> T T)]]
  (forall [y T]
    (==> ((nat-fixpoint-rel x f) zero y)
         (equal x y))))

(proof 'nat-fixpoint-rel-sing-zero-aux-lemma
  (pose FIX := (nat-fixpoint-rel x f))
  (assume [y T
           Hy (FIX zero y)]
    (assume [Hneq (not (equal x y))]
      (pose R := (lambda [n nat]
                   (lambda [z T]
                     (and (FIX n z)
                          (not (and (equal n zero) (equal z y)))))))

      (have <a1> (FIX zero x) :by (nat-fixpoint-zero x f))
      (assume [Hna (and (equal zero zero) (equal x y))]
        (have <a2> p/absurd :by (Hneq (p/and-elim-right Hna))))

      (have <a> (R zero x) :by (p/and-intro <a1> <a2>))

      (assume [n nat
               z T
               Hny (R n z)]
        (have <b1> (FIX n z) :by (p/and-elim-left Hny))
        (have <b2> (FIX (succ n) (f z)) :by ((nat-fixpoint-succ x f) n z <b1>))
        (assume [Hneq (and (equal (succ n) zero) (equal (f z) y))]
          (have <b3> (not (equal (succ n) zero))
                :by (nats/zero-not-succ n))
          (have <b4> p/absurd :by (<b3> (p/and-elim-left Hneq))))
        (have <b> (R (succ n) (f z)) :by (p/and-intro <b2> <b4>)))

      (have <c> (prel/rel-elem R (nat-recur-prop-rel x f))
            :by (p/and-intro <a> <b>))

      (have <d> (R zero y) :by (Hy R <c>))

      (have <e> (and (equal zero zero) (equal y y))
            :by (p/and-intro (eq/eq-refl zero) (eq/eq-refl y)))

      (have <f> p/absurd :by ((p/and-elim-right <d>) <e>)))

    (have <g1> (not (not (equal x y))) :by <f>)
    ;; Q : is classical reasoning mandatory here ?
    (have <g> (equal x y) :by ((classic/not-not-impl (equal x y)) <g1>)))

  (qed <g>))


(deflemma nat-fixpoint-rel-sing-succ-aux
  [[?T :type] [x T] [f (==> T T)]]
  (forall [n nat]
    (==> (forall [y1 y2 T]
           (==> ((nat-fixpoint-rel x f) n y1)
                ((nat-fixpoint-rel x f) n y2)
                (equal y1 y2)))
         (forall [y fy T]
           (==> ((nat-fixpoint-rel x f) n y)
                ((nat-fixpoint-rel x f) (succ n) fy)
                (equal fy (f y)))))))

(proof 'nat-fixpoint-rel-sing-succ-aux-lemma
  (pose FIX := (nat-fixpoint-rel x f))
  (assume [n nat
           Hind (forall [y1 y2 T]
                  (==> (FIX n y1)
                       (FIX n y2)
                       (equal y1 y2)))
           y T fy T
           Hn (FIX n y)
           Hsn (FIX (succ n) fy)]
    (have <a1> (prel/rel-elem FIX (nat-recur-prop-rel x f))
          :by (nat-fixpoint-elem x f))

    (have <a> (FIX (succ n) (f y))
          :by ((p/and-elim-right <a1>) n y Hn))

    (pose R := (lambda [m nat]
                 (lambda [z T]
                   (and (FIX m z)
                        (not (and (equal (succ n) m) (equal z fy)))))))

    (assume [Hneq (not (equal fy (f y)))]
      (have <b1> (FIX zero x) :by (nat-fixpoint-zero x f))
      (assume [Hna (and (equal (succ n) zero) (equal x fy))]
        (have <b2> (not (equal (succ n) zero)) :by (nats/zero-not-succ n))
        (have <b3> p/absurd :by (<b2> (p/and-elim-left Hna))))
      (have <b> (R zero x) :by (p/and-intro <b1> <b3>))

      (assume [m nat
               z T
               Hz (R m z)]

        (have <c1> (FIX m z) :by (p/and-elim-left Hz))

        (have <c2> (or (equal n m) (not (equal n m)))
              :by (classic/excluded-middle-ax (equal n m)))

        (assume [Hor1 (equal n m)]
          (have <c3> (FIX n z) :by (eq/rewrite <c1> (eq/eq-sym Hor1)))
          (have <c4> (FIX (succ n) (f z)) :by ((p/and-elim-right <a1>) n z <c3>))
          (have <cc5> (equal z y) :by (Hind z y <c3> Hn))
          (have <c5> (equal (f z) (f y)) :by (eq/eq-cong f <cc5>))

          (assume [Hna (and (equal (succ n) (succ n)) (equal (f z) fy))]
            (have <c6> (equal fy (f y)) :by (eq/eq-trans (eq/eq-sym (p/and-elim-right Hna))
                                                         <c5>))
            (have <c7> p/absurd :by (Hneq <c6>)))


          (have <c8> (R (succ n) (f z))
                :by (p/and-intro <c4> <c7>))

          (have <c> (R (succ m) (f z)) :by (eq/rewrite <c8> Hor1)))

        (assume [Hor2 (not (equal n m))]
          (have <d1> (FIX (succ m) (f z)) :by ((p/and-elim-right <a1>) m z <c1>))
          (assume [Hna (and (equal (succ n) (succ m)) (equal (f z) fy))]
            (have <d2> (equal n m) :by (nats/succ-injective n m (p/and-elim-left Hna)))
            (have <d3> p/absurd :by (Hor2 <d2>)))
          (have <d> (R (succ m) (f z)) :by (p/and-intro <d1> <d3>)))

        (have <e> (R (succ m) (f z)) :by (p/or-elim <c2> <c> <d>)))

      (have <f> (prel/rel-elem R (nat-recur-prop-rel x f))
            :by (p/and-intro <b> <e>))

      (have <g> (R (succ n) fy) :by (Hsn R <f>))

      (have <h> (and (equal (succ n) (succ n)) (equal fy fy))
            :by (p/and-intro (eq/eq-refl (succ n)) (eq/eq-refl fy)))

      (have <i> p/absurd :by ((p/and-elim-right <g>) <h>)))

    (have <j> (equal fy (f y)) :by ((classic/not-not-impl (equal fy (f y))) <i>)))

  (qed <j>))


(proof 'nat-fixpoint-rel-sing-lemma
  (pose FIX := (nat-fixpoint-rel x f))
  (pose P := (lambda [n nat] (q/single (lambda [y T] (FIX n y)))))

  "We proceed by induction on n"
  "Base case : n = 0"
  (assume [x1 T x2 T
           Hx1 (FIX zero x1)
           Hx2 (FIX zero x2)]
    (have <a> (equal x x1)
          :by ((nat-fixpoint-rel-sing-zero-aux x f) x1 Hx1))
    (have <b> (equal x x2)
          :by ((nat-fixpoint-rel-sing-zero-aux x f) x2 Hx2))

    (have <c> (equal x1 x2)
          :by (eq/eq-trans (eq/eq-sym <a>) <b>)))

  (have <base> (P zero) :by <c>)

  "Induction step"
  (assume [n nat
           Hn (P n)]
    "We have to show (P (succ n))"

    (assume [fx1 T
             fx2 T
             Hfx1 (FIX (succ n) fx1)
             Hfx2 (FIX (succ n) fx2)]

      (have <d1> (exists [x1 T] (FIX n x1))
            :by ((nat-fixpoint-rel-ex x f) n))

      (assume [x1 T
               Hx1 (FIX n x1)]
        (have <d2> (exists [x2 T] (FIX n x2))
              :by ((nat-fixpoint-rel-ex x f) n))
        (assume [x2 T
                 Hx2 (FIX n x2)]
          (have <d3> (equal x1 x2) :by (Hn x1 x2 Hx1 Hx2))

          (have <d4> (equal fx1 (f x1))
                :by ((nat-fixpoint-rel-sing-succ-aux x f) n Hn x1 fx1 Hx1 Hfx1))

          (have <d5> (equal fx2 (f x2))
                :by ((nat-fixpoint-rel-sing-succ-aux x f) n Hn x2 fx2 Hx2 Hfx2))

          (have <d6> (equal (f x1) (f x2)) :by (eq/eq-cong f <d3>))

          (have <d> (equal fx1 fx2)
                :by (eq/eq-trans* <d4> <d6> (eq/eq-sym <d5>))))

        (have <e1> (equal fx1 fx2) :by (q/ex-elim <d2> <d>)))

      (have <e2> (equal fx1 fx2) :by (q/ex-elim <d1> <e1>)))


    (have <e> (P (succ n)) :by <e2>))

  (have <f> (forall [n nat] (P n))
        :by ((nats/nat-induct P) <c> <e>))


  (qed <f>))

(proof 'nat-fixpoint-rel-uniq-lemma
  (assume [n nat]
    (have <a> _ :by ((nat-fixpoint-rel-ex x f) n))
    (have <b> _ :by ((nat-fixpoint-rel-sing x f) n))
    (have <c> _ :by (p/and-intro <a> <b>)))
  (qed <c>))


(defthm nat-fixpoint-functional
  "The least (relational) fixpoint is functional, which is one important
 ingredient of the proof of the recursion theorem."
  [[?T :type] [x T] [f (==> T T)]]
  (rel/functional (nat-fixpoint-rel x f)))

(proof 'nat-fixpoint-functional-thm
  (qed (nat-fixpoint-rel-uniq x f)))

(definition nat-fixpoint-fun
  "The (type-theoretic) function corresponding to the least (relational) fixpoint."
  [[?T :type] [x T] [f (==> T T)]]
  (rel/relfun (nat-fixpoint-rel x f) (nat-fixpoint-functional x f)))

(deflemma nat-recur-rel-prop-rel-prop
  [[?T :type] [x T] [f (==> T T)] [R (rel nat T)] [func (rel/functional R)]]
  (==> ((nat-recur-prop-rel x f) R)
       ((nat-recur-prop x f) (rel/relfun R func))))

(proof 'nat-recur-rel-prop-rel-prop-lemma
  (assume [H _]
    (pose g := (rel/relfun R func))
    "First conjunct"
    (have <a1> (R zero x) :by (p/and-elim-left H))
    (have <a> (equal (g zero) x)
          :by ((rel/relfun-img R func) zero x <a1>))
    "Second conjunct"
    (assume [n nat]
      (have <b1> (R n (g n)) :by ((rel/relfun-img-prop R func) n))
      (have <b2> (R (succ n) (f (g n)))
            :by ((p/and-elim-right H) n (g n) <b1>))
      (have <b> (equal (g (succ n)) (f (g n)))
            :by ((rel/relfun-img R func) (succ n) (f (g n)) <b2>)))
    (have <c> _ :by (p/and-intro <a> <b>)))
  (qed <c>))


(defthm nat-fixpoint-fun-prop
  "The least relational fixpoint as a total function satisfies the recursion theorem."
  [[?T :type] [x T] [f (==> T T)]]
  ((nat-recur-prop x f) (nat-fixpoint-fun x f)))

(proof 'nat-fixpoint-fun-prop-thm
  (pose g := (nat-fixpoint-fun x f))
  (pose R := (nat-fixpoint-rel x f))
  (have <a> ((nat-recur-prop-rel x f) R) :by (nat-fixpoint-elem x f))
  (have <b> ((nat-recur-prop x f) g) 
        :by ((nat-recur-rel-prop-rel-prop x f
                                          (nat-fixpoint-rel x f)
                                          (nat-fixpoint-functional x f))
             <a>))
  (qed <b>))

(deflemma nat-rec-ex
  [[?T :type] [x T] [f (==> T T)]]
  (exists [g (==> nat T)]
    ((nat-recur-prop x f) g)))

(proof 'nat-rec-ex-lemma
  (qed ((q/ex-intro (lambda [g (==> nat T)]
                      ((nat-recur-prop x f) g))
                    (nat-fixpoint-fun x f))
        (nat-fixpoint-fun-prop x f))))

(deflemma nat-rec-single
  [[?T :type] [x T] [f (==> T T)]]
  (forall [g1 g2 (==> nat T)]
    (==> ((nat-recur-prop x f) g1)
         ((nat-recur-prop x f) g2)
         (equal g1 g2))))

(proof 'nat-rec-single-lemma
  (assume [g1 _ g2 _
           Hg1 _ Hg2 _]
    "We proceed by induction"
    "Case zero"
    (have <a1> (equal (g1 zero) x) :by (p/and-elim-left Hg1))
    (have <a2> (equal (g2 zero) x) :by (p/and-elim-left Hg2))
    (have <a> (equal (g1 zero) (g2 zero)) :by (eq/eq-trans <a1> (eq/eq-sym <a2>)))
    "Case successor"
    (assume [n nat
             Hn (equal (g1 n) (g2 n))]
      (have <b1> (equal (g1 (succ n)) (f (g1 n)))
            :by ((p/and-elim-right Hg1) n))
      (have <b2> (equal (g1 (succ n)) (f (g2 n)))
            :by (eq/rewrite <b1> Hn))
      (have <b3> (equal (g2 (succ n)) (f (g2 n)))
            :by ((p/and-elim-right Hg2) n))
      (have <b> (equal (g1 (succ n)) (g2 (succ n)))
            :by (eq/eq-trans <b2> (eq/eq-sym <b3>))))
    "We apply the induction principle"
    (have <c> (forall [n nat] (equal (g1 n) (g2 n)))
          :by ((nats/nat-induct (lambda [n nat] (equal (g1 n) (g2 n))))
               <a> <b>))
    "And now we use functional extensionality"
    (have <d> (equal g1 g2)
          :by ((fun/functional-extensionality g1 g2) <c>)))
  (qed <d>))


;;; Made it, yaye !
(proof 'nat-recur-thm
  (qed (p/and-intro (nat-rec-ex x f)
                    (nat-rec-single x f))))
