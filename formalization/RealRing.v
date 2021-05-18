Require Import Nnat.
Require Import ArithRing.
Require Export Ring Field.
Require Import RealAxioms.

Local Open Scope Real_scope.

Fixpoint pow (r : Real) (n : nat) : Real :=
  match n with
  | O => Real1
  | S m => r * pow r m
  end.


Lemma RealRealheory : ring_theory Real0 Real1 Realplus Realmult Realminus Realopp (eq (A:=Real)).
Proof.
  constructor.
  intro; apply Realplus_unit.
  exact Realplus_comm.
  symmetry; apply Realplus_assoc.
  intro; apply Realmult_unit.
  exact Realmult_comm.
  symmetry ; apply Realmult_assoc.
  intros m n p.
  rewrite Realmult_comm.
  rewrite (Realmult_comm n p).
  rewrite (Realmult_comm m p).
  apply Realmult_plus_distr.
  reflexivity.
  exact Realplus_inv.
Qed.

Ltac IZReal_tac t :=
  match t with
  | Real0 => constr:(0%Z)
  | Real1 => constr:(1%Z)
  | IZReal ?u =>
    match isZcst u with
    | true => u
    | _ => constr:(InitialRing.NotConstant)
    end
  | _ => constr:(InitialRing.NotConstant)
  end.

Add Ring RealRing : RealRealheory (constants [IZReal_tac]).
