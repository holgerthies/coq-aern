Require Import Real.
Require Import MultiLimit.
Require Import Euclidean.



Definition Complex := euclidean 2.

Definition Real_to_Complex : Real -> Complex.
Proof.
  intro x.
  exact (cons x (cons Real0 nil)).
Defined.

Definition Imag_to_Complex : Real -> Complex.
Proof.
  intro x.
  exact (cons Real0 (cons x nil)).
Defined.

Definition complex : Real -> Real -> Complex.
Proof.
  intros r i.
  exact (cons r (cons i nil)).
Defined.

Definition Complex_destruct : forall x : Complex, {r & {i | x = complex r i} }.
Proof.
  intros.
  destruct (dim_succ_destruct x).
  destruct s.
  exists x0.
  destruct (dim_succ_destruct x1).
  exists x2.
  destruct s.
  rewrite e.
  rewrite e0.
  unfold complex.
  rewrite (dim_zero_destruct x3).
  auto.
Defined.

Definition Complex0 := @euclidean_zero 2.
Definition Complex1 := complex Real1 Real0.
Definition Complex_plus := @euclidean_plus 2.
Definition Complex_opp := @euclidean_opp 2.
Definition Complex_minus := @euclidean_minus 2.
Definition Complex_mult : Complex -> Complex -> Complex.
Proof.
  intros x y.
  destruct (Complex_destruct x) as [rx [ix ex]].
  destruct (Complex_destruct y) as [ry [iy ey]].
  exact (complex (rx * ry - ix * iy) (rx * iy + ix * ry)).
Defined.

Lemma Complex_plus_unit : forall x : Complex, Complex_plus Complex0 x = x.
Proof.
  intros.
  destruct (Complex_destruct x) as [rx [ix ex]].
  rewrite ex.
  unfold complex.
  unfold Complex_plus.
  simpl.
  replace (Real0 + rx) with rx by ring.
  replace (Real0 + ix) with ix by ring.
  auto.
Qed.

Lemma Complex_plus_comm : forall (x y : Complex), Complex_plus x y = Complex_plus y x.
Proof.
  apply euclidean_plus_comm.
Qed.
  
Lemma Complex_plus_assoc : forall  (x y z : Complex), Complex_plus x (Complex_plus y z) = Complex_plus (Complex_plus x y) z.
Proof.
  apply euclidean_plus_assoc.
Qed.

Lemma Complex_mult_unit : forall x, Complex_mult Complex1 x = x.
Proof.
  intros.
  destruct (Complex_destruct x) as [rx [ix ex]].
  rewrite ex.
  unfold Complex1.
  unfold Complex_mult.
  simpl.
  unfold complex.
  replace (Real1 * rx - Real0 * ix) with rx by ring.
  replace (Real1 * ix + Real0 * rx) with ix by ring.
  auto.
Defined.


Lemma Complex_mult_comm : forall x y, Complex_mult x y = Complex_mult y x.
Proof.
  intros.
  destruct (Complex_destruct x) as [rx [ix ex]].
  destruct (Complex_destruct y) as [ry [iy ey]].
  rewrite ex, ey.
  unfold complex, Complex_mult.
  simpl.
  replace (rx * ry - ix * iy) with (ry * rx - iy * ix) by ring. 
  replace (rx * iy + ix * ry) with (ry * ix + iy * rx) by ring.
  auto.
Qed.

Definition lp2 : forall S T R (f : S -> T -> R) (a b : S) (c d  : T), a = b -> c = d -> f a c = f b d.
Proof.
  intros.
  rewrite H, H0.
  exact (eq_refl _).
Defined.

Lemma Complex_mult_assoc : forall x y z, Complex_mult x (Complex_mult y z) = Complex_mult (Complex_mult x y) z.
Proof.
  intros.
  destruct (Complex_destruct x) as [rx [ix ex]].
  destruct (Complex_destruct y) as [ry [iy ey]].
  destruct (Complex_destruct z) as [rz [iz ez]].

  rewrite ex, ey, ez.
  unfold complex, Complex_mult.
  simpl.
  apply lp2; ring.
Qed.

Lemma Complex_mult_plus_distr : forall x y z, Complex_mult (Complex_plus x y) z = Complex_plus (Complex_mult x z) (Complex_mult y z).
Proof.
  intros.
  destruct (Complex_destruct x) as [rx [ix ex]].
  destruct (Complex_destruct y) as [ry [iy ey]].
  destruct (Complex_destruct z) as [rz [iz ez]].

  rewrite ex, ey, ez.
  unfold complex, Complex_plus, Complex_mult.
  simpl.
  unfold complex.
  apply lp2.
  ring.
  apply lp2.
  ring.
  auto.
Qed.

Check Realplus_inv.
Lemma Complex_plus_inv : forall x, Complex_plus x (Complex_opp x) = Complex0.
Proof.
  apply euclidean_plus_inv.
Qed.


Require Import Nnat.
Require Import ArithRing.
Require Export Ring Field.

Lemma ComplexTheory : ring_theory Complex0 Complex1 Complex_plus Complex_mult Complex_minus Complex_opp (eq (A:=Complex)).
Proof.
  constructor.
  intro; apply Complex_plus_unit.
  exact Complex_plus_comm.
  apply Complex_plus_assoc.
  intro; apply Complex_mult_unit.
  exact Complex_mult_comm.

  apply Complex_mult_assoc.
  intros m n p.
  apply Complex_mult_plus_distr.
  auto.
  exact Complex_plus_inv.
Qed.

Definition IZComplex p := Real_to_Complex (IZReal p).

Ltac IZComplex_tac t :=
  match t with
  | Complex0 => constr:(0%Z)
  | Complex1 => constr:(1%Z)
  | IZComplex ?u =>
    match isZcst u with
    | true => u
    | _ => constr:(InitialRing.NotConstant)
    end
  | _ => constr:(InitialRing.NotConstant)
  end.

Add Ring ComplexRing : ComplexTheory (constants [IZComplex_tac]).

Declare Scope C_scope.
Delimit Scope C_scope with C. 
Infix "+" := Complex_plus : C_scope.
Infix "*" := Complex_mult : C_scope.
Notation "- x" := (Complex_opp x) : C_scope.
Infix "-" := Complex_minus : C_scope.

(* Definition separated_predicate {n :nat} (P : euclidean n -> Prop) : Prop *)
(*   := exists n, forall x y, P x -> P y -> euclidean_max_dist x y >= prec n.  *)

(* Lemma separated_predicate_is_closed : forall {n :nat} (P : euclidean n -> Prop), *)
(*     separated_predicate P -> closed_predicate P. *)
(* Admitted. *)
(* Definition is_csqrt x y: Prop :=  (x * x = y)%C. *)
(* Lemma is_csqrt_is_separated : forall x, separated_predicate (fun y => is_csqrt y x). *)
(* Proof. *)
(*   intros. *)
(*   destruct (Complex_destruct x) as [rx [ix ex]]. *)
(*   rewrite ex. *)
(*   unfold is_csqrt. *)
  
(*   simpl. *)
(*   exists O. *)
(*   intros. *)
  
(*   intros n. *)
    
(*     : Prop *)
(*   := exists n, forall x y, P x -> P y -> euclidean_max_dist x y >= prec n.  *)


(* Lemma is_csqrt_is_closed : forall x, closed_predicate (fun y => is_csqrt y x). *)
(* Proof. *)
(*   intros. *)
(*   intro. *)
(*   intros. *)
  
(*   pose proof (euclidean_limit f H). *)
(*   destruct H2. *)
(*   assert (x0 = x1). *)
(*   apply (euclidean_limit_is_unique f _ _ H1 e). *)
(*   induction H2. *)
(*   assert (x0 =  *)
