Require Import Nnat.
Require Import ArithRing.
Require Export Ring Field.
Require Import RealAxioms.

Local Open Scope T_scope.

Fixpoint pow (r : T) (n : nat) : T :=
  match n with
  | O => T1
  | S m => r * pow r m
  end.


Lemma TTheory : ring_theory T0 T1 Tplus Tmult Tminus Topp (eq (A:=T)).
Proof.
  constructor.
  intro; apply Tplus_unit.
  exact Tplus_comm.
  symmetry; apply Tplus_assoc.
  intro; apply Tmult_unit.
  exact Tmult_comm.
  symmetry ; apply Tmult_assoc.
  intros m n p.
  rewrite Tmult_comm.
  rewrite (Tmult_comm n p).
  rewrite (Tmult_comm m p).
  apply Tmult_plus_distr.
  reflexivity.
  exact Tplus_inv.
Qed.

(*
Lemma Tfield : field_theory T0 T1 Tplus Tmult Tminus Topp Tdiv Tinv (eq(A:=T)).
Proof.
constructor.
 exact TTheory.
 exact T1_neq_T0.
 reflexivity.
 exact Tmult_inv.
Qed.
Notation Tset := (Eqsth T).
Notation Text := (Eq_ext Tplus Tmult Topp).

Lemma Tgen_phiPOS : forall x, InitialRing.gen_phiPOS1 T1 Tplus Tmult x > T0.
unfold Tgt.
induction x; simpl; intros.
 apply Tlt_lt_lt with (T1 + T0).
  rewrite Tplus_comm.
    apply Tlt_n_Sn.
  apply Tlt_plus_lt.
    rewrite <- (Rmul_0_l Tset Text TTheory (T1+T1)).
    rewrite Tmult_comm.
    apply Tlt_mult_pos_lt.
   apply Tlt_0_2.
   trivial.
 rewrite <- (Rmul_0_l Tset Text TTheory T2).
   rewrite Tmult_comm.
   apply Tlt_mult_pos_lt.
  apply Tlt_0_2.
  trivial.
  replace T1 with (T0 + T1).
  apply Tlt_n_Sn.
  apply Tplus_unit.
Qed.


Lemma Tgen_phiPOS_not_0 :
  forall x, InitialRing.gen_phiPOS1 T1 Tplus Tmult x <> T0.
red; intros.
specialize (Tgen_phiPOS x).
rewrite H; intro.
apply (Tlt_nlt T0 T0); trivial.
Qed.

Lemma Zeq_bool_complete : forall x y,
  InitialRing.gen_phiZ T0%T T1%T Tplus Tmult Topp x =
  InitialRing.gen_phiZ T0%T T1%T Tplus Tmult Topp y ->
  Zeq_bool x y = true.
Proof gen_phiZ_complete Tset Text Tfield Tgen_phiPOS_not_0.

Lemma Tdef_pow_add : forall (x:T) (n m:nat), pow x  (n + m) = pow x n * pow x m.
Proof.
  intros x n; elim n; simpl; auto with Tiny.
  intros n0 H' m; rewrite H'; auto with Tiny.
Qed.

Lemma T_power_theory : power_theory T1%T Tmult (@eq T) N.to_nat pow.
Proof.
 constructor. destruct n. reflexivity.
 simpl. induction p.
 - rewrite Pos2Nat.inj_xI. simpl. now rewrite plus_0_r, Tdef_pow_add, IHp.
 - rewrite Pos2Nat.inj_xO. simpl. now rewrite plus_0_r, Tdef_pow_add, IHp.
 - simpl. rewrite Tmult_comm;apply Tmult_unit.
Qed.

Ltac Tpow_tac t :=
  match isnatcst t with
  | false => constr:(InitialRing.NotConstant)
  | _ => constr:(N.of_nat t)
  end.
*)
Ltac IZT_tac t :=
  match t with
  | T0 => constr:(0%Z)
  | T1 => constr:(1%Z)
  | IZT ?u =>
    match isZcst u with
    | true => u
    | _ => constr:(InitialRing.NotConstant)
    end
  | _ => constr:(InitialRing.NotConstant)
  end.

Add Ring TRing : TTheory (constants [IZT_tac]).
(*Add Field TField : Tfield
   (completeness Zeq_bool_complete, constants [IZT_tac], power_tac T_power_theory [Tpow_tac]).
*)
