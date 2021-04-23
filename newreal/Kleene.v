Require Import Base.


Parameter K : Set.
Parameter trueK : K.
Parameter falseK : K.

Definition upK : K -> Prop := fun b : K => b = trueK.
Definition downK : K -> Prop := fun b : K => b = falseK.

Parameter M : Type -> Type.
Parameter unitM : forall T : Type, T -> M T.
Parameter multM : forall T : Type, M (M T) -> M T.
Parameter liftM : forall A B, (A -> B) -> M A -> M B.
Definition lift_domM : forall A B, (A -> M B) -> M A -> M B :=
  fun A B f => fun x => multM B ((liftM A (M B) f) x).
                                                  
(* coherence conditions *)
Axiom unitM_ntrans : forall A B (f : A -> B) x, (liftM A B f) (unitM A x) = unitM B (f x).
Axiom multM_ntrans : forall A B (f : A -> B) x, multM B ((liftM (M A) (M B) (liftM A B f)) x) = (liftM A B f) (multM A x).  
Axiom M_coh1 : forall A x, multM A (unitM (M A) x) = x.
Axiom M_coh2 : forall A x, multM A (liftM A (M A) (unitM A)  x) = x.
Axiom M_coh3 : forall A x, multM A (multM (M A) x) = multM A (liftM (M (M A)) (M A) (multM A) x). 

Definition isSubsingleton := fun P : Type => forall x y : P, x = y.


Definition mjoin (p q : Prop) (T : Type) : ({p}+{q} -> T) ->  M ({p}+{q}) -> M T.
Proof.
  intros f x.
  exact (liftM _ _ f x).
Defined.



Axiom singletonM : forall A, isSubsingleton A -> M A -> A.

Axiom countableM : forall P : nat -> Type,
    (forall n, M (P n)) -> M (forall n, P n). 
Definition countableMinv : forall P : nat -> Type,
    M (forall n, P n) -> (forall n, M (P n)).
Proof.
  intros P X n.
  apply (liftM _ _ (fun f => f n) X).
Defined.

Axiom countableMprop : forall P : nat -> Type, forall f,
      countableMinv P  (countableM P f) = f.

Parameter select : forall x y : K, upK x \/ upK y -> M ({ (upK x) } + { (upK y) }).

Notation "[ x | P ]" := (M {x | P}) : type_scope.
Notation "[ x : T | P ]" := (M {x : T | P}) : type_scope.
Notation "[ ( a , b ) | P ]" := (M (sigT (fun a => {b | P}))) : type_scope.

Definition semidec := fun P : Prop => {x : K | upK x <-> P}.

Definition choose : forall p q, semidec p -> semidec q -> p \/ q -> M ({p}+{q}).
Proof.
  intros.
  destruct H.
  destruct H0.
  destruct i.
  destruct i0.
  apply (liftM ({upK x} + {upK x0})).
  intro.
  destruct H4; auto.
  apply select.
  destruct H1; auto.
Defined.


Definition dec := fun P : Prop =>  {P} + {~ P}.
Lemma semidec_dec : forall P, semidec P -> semidec (~ P) -> dec P.
Proof.
  intros P p q.
  pose proof (choose _ _ p q (lem P)).
  apply singletonM.
  
  intros t1 t2.
  destruct t1, t2.
  induction (irrl _ p0 p1);
    auto.
  induction (n p0).
  induction (n p0).
  induction (irrl _ n n0); auto.
  exact X.
Defined.


