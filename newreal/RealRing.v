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

(*
Lemma Realfield : field_theory Real0 Real1 Realplus Realmult Realminus Realopp Realdiv Realinv (eq(A:=Real)).
Proof.
constructor.
 exact RealRealheory.
 exact Real1_neq_Real0.
 reflexivity.
 exact Realmult_inv.
Qed.
Notation Realset := (Eqsth Real).
Notation Realext := (Eq_ext Realplus Realmult Realopp).

Lemma Realgen_phiPOS : forall x, InitialRing.gen_phiPOS1 Real1 Realplus Realmult x > Real0.
unfold Realgt.
induction x; simpl; intros.
 apply Reallt_lt_lt with (Real1 + Real0).
  rewrite Realplus_comm.
    apply Reallt_n_Sn.
  apply Reallt_plus_lt.
    rewrite <- (Rmul_0_l Realset Realext RealRealheory (Real1+Real1)).
    rewrite Realmult_comm.
    apply Reallt_mult_pos_lt.
   apply Reallt_0_2.
   trivial.
 rewrite <- (Rmul_0_l Realset Realext RealRealheory Real2).
   rewrite Realmult_comm.
   apply Reallt_mult_pos_lt.
  apply Reallt_0_2.
  trivial.
  replace Real1 with (Real0 + Real1).
  apply Reallt_n_Sn.
  apply Realplus_unit.
Qed.


Lemma Realgen_phiPOS_not_0 :
  forall x, InitialRing.gen_phiPOS1 Real1 Realplus Realmult x <> Real0.
red; intros.
specialize (Realgen_phiPOS x).
rewrite H; intro.
apply (Reallt_nlt Real0 Real0); trivial.
Qed.

Lemma Zeq_bool_complete : forall x y,
  InitialRing.gen_phiZ Real0%Real Real1%Real Realplus Realmult Realopp x =
  InitialRing.gen_phiZ Real0%Real Real1%Real Realplus Realmult Realopp y ->
  Zeq_bool x y = true.
Proof gen_phiZ_complete Realset Realext Realfield Realgen_phiPOS_not_0.

Lemma Realdef_pow_add : forall (x:Real) (n m:nat), pow x  (n + m) = pow x n * pow x m.
Proof.
  intros x n; elim n; simpl; auto with Realiny.
  intros n0 H' m; rewrite H'; auto with Realiny.
Qed.

Lemma Real_power_theory : power_theory Real1%Real Realmult (@eq Real) N.to_nat pow.
Proof.
 constructor. destruct n. reflexivity.
 simpl. induction p.
 - rewrite Pos2Nat.inj_xI. simpl. now rewrite plus_0_r, Realdef_pow_add, IHp.
 - rewrite Pos2Nat.inj_xO. simpl. now rewrite plus_0_r, Realdef_pow_add, IHp.
 - simpl. rewrite Realmult_comm;apply Realmult_unit.
Qed.

Ltac Realpow_tac t :=
  match isnatcst t with
  | false => constr:(InitialRing.NotConstant)
  | _ => constr:(N.of_nat t)
  end.
*)
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
(*Add Field RealField : Realfield
   (completeness Zeq_bool_complete, constants [IZReal_tac], power_tac Real_power_theory [Realpow_tac]).
*)
