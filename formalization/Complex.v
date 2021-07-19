Require Import Real.
Require Import MultiLimit.
Require Import Euclidean.
Require Import Nnat.
Require Import ArithRing.
Require Export Ring Field.



Section Complex.
  Context {T : ComplArchiSemiDecOrderedField}.
  Notation R := (CarrierField T).
  
  Ltac IZReal_tac t :=
    match t with
    | @real_0 R => constr:(0%Z)
    | @real_1 R => constr:(1%Z)
    | @IZreal R ?u =>
      match isZcst u with
      | true => u
      | _ => constr:(InitialRing.NotConstant)
      end
    | _ => constr:(InitialRing.NotConstant)
    end.

  Add Ring realRing : (realTheory R) (constants [IZReal_tac]).
  
  Notation real_ := (real R).
  Notation real_0_ := (@real_0 R).
  Notation real_1_ := (@real_1 R).
  Notation prec_ := (@prec R).


  Definition complex := @euclidean T 2.
  

  Definition real_to_complex : real_ -> complex.
  Proof.
    intro x.
    exact (cons x (cons real_0 nil)).
  Defined.

  Definition Imag_to_complex : real_ -> complex.
  Proof.
    intro x.
    exact (cons real_0 (cons x nil)).
  Defined.

  Definition Complex : real_ -> real_ -> complex.
  Proof.
    intros r i.
    exact (cons r (cons i nil)).
  Defined.

  Definition complex_destruct : forall x : complex, {r & {i | x = Complex r i} }.
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
    unfold Complex.
    rewrite (dim_zero_destruct x3).
    auto.
  Defined.

  Definition complex0 := @euclidean_zero T 2.
  Definition complex1 := Complex real_1 real_0.
  Definition complex_plus := @euclidean_plus T 2.
  Definition complex_opp := @euclidean_opp T 2.
  Definition complex_minus := @euclidean_minus T 2.
  Definition complex_mult : complex -> complex -> complex.
  Proof.
    intros x y.
    destruct (complex_destruct x) as [rx [ix ex]].
    destruct (complex_destruct y) as [ry [iy ey]].
    exact (Complex (rx * ry - ix * iy) (rx * iy + ix * ry)).
  Defined.

  Lemma complex_plus_unit : forall x : complex, complex_plus complex0 x = x.
  Proof.
    intros.
    destruct (complex_destruct x) as [rx [ix ex]].
    rewrite ex.
    unfold Complex.
    unfold complex_plus.
    simpl.
    replace (real_0 + rx) with rx by ring.
    replace (real_0 + ix) with ix by ring.
    auto.
  Qed.

  Lemma complex_plus_comm : forall (x y : complex), complex_plus x y = complex_plus y x.
  Proof.
    apply euclidean_plus_comm.
  Qed.
  
  Lemma complex_plus_assoc : forall  (x y z : complex), complex_plus x (complex_plus y z) = complex_plus (complex_plus x y) z.
  Proof.
    apply euclidean_plus_assoc.
  Qed.

  Lemma complex_mult_unit : forall x, complex_mult complex1 x = x.
  Proof.
    intros.
    destruct (complex_destruct x) as [rx [ix ex]].
    rewrite ex.
    unfold complex1.
    unfold complex_mult.
    simpl.
    unfold Complex.
    replace (real_1 * rx - real_0 * ix) with rx by ring.
    replace (real_1 * ix + real_0 * rx) with ix by ring.
    auto.
  Defined.


  Lemma complex_mult_comm : forall x y, complex_mult x y = complex_mult y x.
  Proof.
    intros.
    destruct (complex_destruct x) as [rx [ix ex]].
    destruct (complex_destruct y) as [ry [iy ey]].
    rewrite ex, ey.
    unfold Complex, complex_mult.
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

  Lemma complex_mult_assoc : forall x y z, complex_mult x (complex_mult y z) = complex_mult (complex_mult x y) z.
  Proof.
    intros.
    destruct (complex_destruct x) as [rx [ix ex]].
    destruct (complex_destruct y) as [ry [iy ey]].
    destruct (complex_destruct z) as [rz [iz ez]].

    rewrite ex, ey, ez.
    unfold Complex, complex_mult.
    simpl.
    apply lp2; ring.
  Qed.

  Lemma complex_mult_plus_distr : forall x y z, complex_mult (complex_plus x y) z = complex_plus (complex_mult x z) (complex_mult y z).
  Proof.
    intros.
    destruct (complex_destruct x) as [rx [ix ex]].
    destruct (complex_destruct y) as [ry [iy ey]].
    destruct (complex_destruct z) as [rz [iz ez]].

    rewrite ex, ey, ez.
    unfold Complex, complex_plus, complex_mult.
    simpl.
    unfold Complex.
    apply lp2.
    ring.
    apply lp2.
    ring.
    auto.
  Qed.

  Lemma complex_plus_inv : forall x, complex_plus x (complex_opp x) = complex0.
  Proof.
    apply euclidean_plus_inv.
  Qed.


  Lemma complexTheory : ring_theory complex0 complex1 complex_plus complex_mult complex_minus complex_opp (eq (A:=complex)).
  Proof.
    constructor.
    intro; apply complex_plus_unit.
    exact complex_plus_comm.
    apply complex_plus_assoc.
    intro; apply complex_mult_unit.
    exact complex_mult_comm.

    apply complex_mult_assoc.
    intros m n p.
    apply complex_mult_plus_distr.
    auto.
    exact complex_plus_inv.
  Qed.

  Definition IZcomplex p := real_to_complex (IZreal p).

  Ltac IZcomplex_tac t :=
    match t with
    | complex0 => constr:(0%Z)
    | complex1 => constr:(1%Z)
    | IZcomplex ?u =>
      match isZcst u with
      | true => u
      | _ => constr:(InitialRing.NotConstant)
      end
    | _ => constr:(InitialRing.NotConstant)
    end.

  Add Ring complexRing : complexTheory (constants [IZcomplex_tac]).

End Complex.


Declare Scope Complex_scope.
Delimit Scope Complex_scope with Complex.
Local Open Scope Complex_scope.

Infix "+" := complex_plus : Complex_scope.
Infix "*" := complex_mult : Complex_scope.
Notation "- x" := (complex_opp x) : Complex_scope.
Infix "-" := complex_minus : Complex_scope.
