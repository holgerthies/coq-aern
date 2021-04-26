Require Import Real.
Require Import Reals.

Definition inProp T := exists t : T, True.

Definition Prop_inj : forall T, T -> inProp T.
Proof.
  intros.
  exists X.
  auto.
Defined.

Parameter Classical_embedding : Real -> R.
Definition sheafs : forall P : R -> Prop, Real -> Prop.
Proof.
  intros.
  exact (P (Classical_embedding H)).
Defined.

  

(* embedding *)
Axiom mymy : Real -> inProp R.
Axiom Real_coq_R : inProp Real -> inProp R.
Axiom coq_R_Real : inProp R -> inProp Real.
Axiom my : forall x :  Real, coq_R_Real (mymy x) = Prop_inj _ x.


Goal forall x y : inProp Real, x = y.
  apply irrl.
  

Goal forall x  y : Real, x + y = y + x.
Proof.
  intros.
  pose proof (my x).
  destruct (mymy x).
  pose proof (my y).
  destruct (mymy y).
  
  
  destruct H.
  destruct H0.
  
  
  (mymy y).
