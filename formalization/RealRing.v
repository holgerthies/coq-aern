Require Import Nnat.
Require Import ArithRing.
Require Export Ring Field.
Require Import Kleene Monad ClassicalMonads MultivalueMonad RealAxioms.

Local Open Scope Real_scope.

Section RealRing.

Generalizable Variables K M R.

Context `{klb : LazyBool K} `{M_Monad : Monad M}
  {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
  {M_MultivalueMonad : MultivalueMonad}
  {R : Type}
  {SemiDecOrderedField_Real : SemiDecOrderedField R}.
  
  Fixpoint pow (r : R) (n : nat) : R :=
    match n with
    | O => real_1
    | S m => r * pow r m
    end.

  Lemma realTheory : ring_theory real_0 real_1 real_plus real_mult real_minus real_opp (eq (A:=R)).
  Proof.
    constructor.
    intro; apply real_plus_unit.
    exact real_plus_comm.
    symmetry; apply real_plus_assoc.
    intro; apply real_mult_unit.
    exact real_mult_comm.
    symmetry ; apply real_mult_assoc.
    intros m n p.
    rewrite real_mult_comm.
    rewrite (real_mult_comm n p).
    rewrite (real_mult_comm m p).
    apply real_mult_plus_distr.
    reflexivity.
    exact (real_plus_inv).
  Qed.

  Ltac IZReal_tac t :=
    match t with
    | real_0 => constr:(0%Z)
    | real_1 => constr:(1%Z)
    | IZreal ?u =>
      match isZcst u with
      | true => u
      | _ => constr:(InitialRing.NotConstant)
      end
    | _ => constr:(InitialRing.NotConstant)
    end.

  (* Add Ring realRing : realTheory (constants [IZReal_tac]). *)
End RealRing.

