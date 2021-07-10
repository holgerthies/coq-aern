Set Warnings "-parsing".
Require Import Real testsearch.
From mathcomp Require Import all_ssreflect.
Require Import Psatz.
Require Import Nat.
Require Import PeanoNat.

Require Import Kleene.
Require Import Reals.
Require Import RealCoqReal RealHelpers.
Set Warnings "parsing".

Lemma half_lt_one : Real1 / Real2_neq_Real0 < Real1.
Proof.
classical.
relate.
suff -> : (y = 2)%R by lra.
by apply relate_IZReal.
Qed.

Definition lt_prec x n := prec n < x.

Definition is_magnitude1 x n := 
  lt_prec x n.+2 /\ not (lt_prec x n)
.
    (* prec n.+2 < x < prec n. *)
Definition magnitude1 x : (Real0 < x < Real1 / Real2_neq_Real0) 
  -> M { n | is_magnitude1 x n }.
Proof.
  move => [pos lt2].

  (* x < Real1 *)
  have lt1 : x < Real1.
  have h := half_lt_one.
  apply (Reallt_lt_lt _ (Real1 / Real2_neq_Real0) _); auto.

  unfold is_magnitude1.
  Definition P x n := lt_prec x (n.+1).
  suff g1M : M { n : nat | P x n.+1 /\ (forall k : nat, (k < n)%coq_nat -> ~ P x k)}.
  apply (liftM ({n : nat | P x n.+1 /\ (forall k : nat, (k < n)%coq_nat -> ~ P x k)})).
  2: { exact g1M. }
  clear g1M. intro g1.
  destruct g1 as [n H].
  exists n.
  unfold P in H.
  split.
  destruct H. auto.
  destruct H.

  destruct n.
  (* ~ lt_prec x 0 *)
  unfold lt_prec. apply Realgt_ngt. unfold prec. unfold Realgt. auto. 

  (* ~ lt_prec x n.+1 *)
  have H0n := H0 n.
  suff lt_S : (n < n.+1)%coq_nat by auto.
  by lia.
  
  apply (epsilon_smallest_choose_M).
  unfold P. unfold lt_prec.
  intros.
  apply (weaken_orM_r _ (x < prec n.+1) _).
  intros.
  apply Reallt_nlt. auto.

  apply choose.
  auto with Realiny.
  auto with Realiny.

  (* prec n.+2 < x \/ x < prec n.+1 *)
  destruct (Realtotal_order x (prec n.+1)) as [H|[H|H]].
  right. exact H.
  left. rewrite H. apply prec_S.
  left. unfold Realgt in H. apply (Reallt_lt_lt _ (prec n.+1) _).
  apply prec_S. exact H.

  unfold P. unfold lt_prec.
  case (ana1 x) => xr [R1 R2].
  suff : exists n,  (/ 2 ^ n.+1 < xr)%R.
  - case => n nprp.
    exists n.
    have P := (relate_prec n.+1).
    classical.
    relate; by trivial.
  have xrpos : (0 < xr)%R.
  apply /transport_lt_inv/pos/R1/relate_constant0.
  have xrlt1 : (xr < 1)%R.
  apply /transport_lt_inv/lt1. auto. 
  apply relate_constant1.

  have H := dns0_tpmn xr xrpos.
  destruct H as [n H].
  destruct n.
  have xrgt1 : (1 < xr)%R. lra. 
  lra. (* contradiction between xrlt1 xrgt1 *)

  exists n. auto.
Defined.

Definition Zpow (x : Real) (xne0 : x <> Real0) z := match z with
                       | 0%Z => Real1
                       | Z.pos p => RealRing.pow x (Pos.to_nat p)
                       | Z.neg p => RealRing.pow (/ xne0) (Pos.to_nat p)
                     end.

Lemma dec_x_lt_2 x : M ({x < Real2} + {Real1 < x}).
Proof.
  have := (M_split x (IZReal 3 / dReal2) (/ dReal2) dReal2_pos).
  apply mjoin.
  case => H.
  right.
  - classical.
    relate.
    suff : ((3 / 2) - (/ 2) < y)%R by lra.
    apply /transport_lt_inv/H/H1.
    by apply /relate_addition/relate_subtraction/relate_divison/IZReal_relator/relate_multiplication/relate_divison/IZReal_relator/IZReal_relator.
  left.
  classical.
  relate.
  have -> : (y = 2)%R by apply relate_IZReal.
  suff : (x0 - ( / 2) < (3 / 2))%R by lra.
  by apply /transport_lt_inv/H/relate_multiplication/relate_divison/IZReal_relator/IZReal_relator/relate_addition/relate_subtraction/relate_divison/IZReal_relator.
Qed.

Lemma Zpow_prec n : Zpow _ Real2_neq_Real0 (- Z.of_nat n) = prec n.
Proof.
  rewrite /Zpow.
  case e :(- Z.of_nat n)%Z => [| p | p]; try by lia.
  - suff  -> : (n = 0) by auto.
    lia.
  have -> : Pos.to_nat p = n by lia.
  elim n => // n' IH /=.
  rewrite Realmult_comm.
  by apply Realeq_eq_mult_eq.
Qed.  


Definition is_magnitude x z := Zpow _ Real2_neq_Real0 (z - 2) <= x <= Zpow _ Real2_neq_Real0 z. 

Lemma inv_neq0 (x : Real) (xneq0 : x <> Real0) : (/ xneq0) <> Real0. 
Proof.
  classical.
  relate.
  apply Rinv_neq_0_compat.
  by apply /transport_neq_inv/xneq0/relate_constant0/Ha.
Qed.


Lemma Zpow_pos x xneq0 z : (0 <= z)%Z -> Zpow x xneq0 z = RealRing.pow x (Z.to_nat z).
Proof.
  move => H.
  by case e : z => //; lia.
Qed.

Lemma Zpow_neg x xneq0 z : (z <= 0)%Z -> Zpow x xneq0 z = RealRing.pow (/ xneq0) (Z.to_nat (-z)).
Proof.
  move => H.
  by case e : z => // /=; try lia.
Qed.

Lemma pow_plus x n1 n2 : RealRing.pow x (n1+n2) = RealRing.pow x n1 * RealRing.pow x n2.
Proof.
  elim n2 => [| n' IH ]; first by rewrite /= Nat.add_0_r Realmult_comm Realmult_unit.
  have ->  : ((n1 + n'.+1) = ((n1+n').+1))%coq_nat by lia.
  rewrite Realmult_comm /= Realmult_assoc.
  apply Realeq_mult_eq.
  by rewrite Realmult_comm.
Qed.


Lemma Zpow_inv x xneq0 z : Zpow x xneq0 (-z) = Zpow (/ xneq0) (inv_neq0 _ xneq0) z.
Proof.
  case (Z.neg_nonneg_cases z) => H.
  - rewrite Zpow_pos; try by lia.
    rewrite Zpow_neg; try by lia.
    suff -> : (/ inv_neq0 x xneq0) = x by trivial. 
    classical.
    relate.
    apply Rinv_involutive.
    by apply /transport_neq_inv/xneq0/relate_constant0/Ha0.
  rewrite Zpow_neg; try by lia.
  rewrite Zpow_pos; try by lia.
  by rewrite Z.opp_involutive.
Qed.

Lemma Zpow_succ x xneq0 z : Zpow x xneq0 (Z.succ z) = x * Zpow x xneq0 z.
Proof.
  case (Z.neg_nonneg_cases z) => H;case (Z.neg_nonneg_cases (Z.succ z)) => H'; try by lia.
  - rewrite !Zpow_neg; try lia.
    have -> : (- z = -Z.succ z  + 1)%Z by lia. 
    rewrite Z2Nat.inj_add; try by lia.
    have -> : (Z.to_nat (- Z.succ z) + Z.to_nat 1 = (Z.to_nat (- Z.succ z)).+1)%coq_nat by lia.
    rewrite /= -Realmult_assoc.
    suff -> : x * / xneq0 = Real1 by rewrite Realmult_unit.
    rewrite Realmult_comm.
    by apply Realmult_inv.
  - have -> : (z = -1)%Z by lia.
    rewrite /=.
    by rewrite  /= -Realmult_assoc Realmult_comm Realmult_unit Realmult_comm Realmult_inv.
  rewrite !Zpow_pos; try by lia.
  rewrite Z2Nat.inj_add; try by lia.
  have -> : (Z.to_nat z + Z.to_nat 1 = (Z.to_nat z).+1)%coq_nat by lia.
  by auto.
Qed.

Lemma Zpow_plus x xneq0 z1 z2 : Zpow x xneq0 (z1+z2) = Zpow x xneq0 z1  * Zpow x xneq0 z2.
  move : z2.
  apply Z.bi_induction => [x0 y -> | | z] => // /=; first by rewrite Z.add_0_r Realmult_comm Realmult_unit.
  split => H.
  - have -> : (z1 + Z.succ z = Z.succ (z1+z) )%Z by lia.
    rewrite !Zpow_succ.
    by rewrite -Realmult_assoc (Realmult_comm _ x) H Realmult_assoc.
  have T y u1 u2 : x * y = u1 * (x * u2) -> y = u1 * u2 by clear H;intros;Holger H;Holger xneq0;classical;relate;nra. 
  apply T.
  rewrite -!Zpow_succ.
  have -> : (Z.succ (z1+z) = z1 + Z.succ z)%Z by lia.
  exact H.
Qed.

Lemma magnitude_half x z : is_magnitude (x / Real2_neq_Real0) z -> is_magnitude x (z+1).
Proof.
  move => [H1 H2].
  split.
  - have -> : (z + 1 - 2 = z - 1)%Z by lia.
    move : H1.
    rewrite !Zpow_plus /= => H1.
    classical; relate.

    have -> : (x2 = 2)%R by apply relate_IZReal.

    suff : (x1 * (/ 2 * (/ 2 * 1) ) <= y / 2)%R by lra.
    apply /transport_leq_inv/H1/relate_multiplication/relate_divison/IZReal_relator/H0.
    apply /relate_multiplication/relate_multiplication/relate_multiplication/relate_constant1/relate_divison/IZReal_relator/relate_divison/IZReal_relator.
    apply Ha.
  rewrite Zpow_plus /=.
  classical;relate.
  have -> : (x2 = 2)%R by apply relate_IZReal.
  suff : (x0 / 2 <= x1)%R by lra.
  by apply /transport_leq_inv/H2/Ha/relate_multiplication/relate_divison/IZReal_relator/H.
Qed.



Lemma magnitude_fourth x z : is_magnitude (x /IZReal4neq0) z -> is_magnitude x (z+2).
Proof.
  suff -> : (x / IZReal4neq0) = (x / Real2_neq_Real0 / Real2_neq_Real0).
  - move => H.
    have H' := (magnitude_half _ _ (magnitude_half _ _ H)).
    have -> : (z + 2 = z + 1 + 1)%Z by lia.
    exact H'.
  classical.
  relate.
  rewrite (relate_IZReal _ _ Hb1).
  rewrite (relate_IZReal _ _ Hb0).
  by lra.
Qed.


(* first extend magnitude to numbers <= 2 *)
Definition magnitude2 x : (Real0 < x < Real2) -> M { z | is_magnitude x z }.
Proof.
  move => [xgt0 xle1].
  pose y := (x / IZReal4neq0).
  have yB : (Real0 < y < Real1 / Real2_neq_Real0).
  - rewrite /Realdiv; rewrite Realmult_unit/y.
    split;classical;relate;rewrite (relate_IZReal _ _ Hb).
    suff : (0 < x0)%R by lra.
    apply /transport_lt_inv/xgt0/Ha/relate_constant0.
    rewrite (relate_IZReal _ _ Ha0).
    suff : (x1 < 2)%R by lra.
    by apply /transport_lt_inv/xle1/IZReal_relator/Ha.
  have magy n : is_magnitude y n -> is_magnitude x (n+2)%Z by apply magnitude_fourth.
  suff : M { z | is_magnitude y z}.
  - apply liftM.
    case => z zprp.
    exists (z+2)%Z.
    exact (magy _ zprp).
  (* y is less than 1/2 => magnitude1 can be used *)
  have := magnitude1 _ yB.
  apply liftM.
  case => n nprp.
  exists (- Z.of_nat n)%Z.
  split; last by rewrite Zpow_prec; apply Realge_le; apply Realnge_le; apply nprp.
  have -> : ((- Z.of_nat n - 2) = (- Z.of_nat (n.+2)%coq_nat))%Z by lia.
  by rewrite Zpow_prec; apply Reallt_le;apply nprp.
Qed.


Lemma Zpow_relate x xneq0 z xr: relate x xr -> relate (Zpow x xneq0 z) (powerRZ xr z). 
Proof.
  move => R.
  have xrneg0 : (xr <> R0)%R by Holger xneq0;relate.
  move : z.
  apply Z.bi_induction => [x0 y -> | | z] => // /=; first by apply relate_constant1.
  split => H.
  - rewrite Zpow_succ powerRZ_add /= => //.
    have ->: forall p, (p * (xr * 1) = xr * p)%R by intros;lra. 
    by apply relate_multiplication.
  move : H.
  rewrite Zpow_succ powerRZ_add /= => //.
  have ->: forall p, (p * (xr * 1) = xr * p)%R by intros;lra. 
  move => H.
  have := relate_multiplication _ _ _ _ (relate_divison _ xneq0 _ R) H.
  rewrite -Realmult_assoc -Rmult_assoc Realmult_inv Realmult_unit Rinv_l => //.
  by rewrite Rmult_1_l.
Qed.

Lemma magnitude_inv x (xneq0 : x<> Real0) z : is_magnitude (/ xneq0) z -> is_magnitude x (-z+2).
Proof.
  move => [H1 H2].
  have R1 := Zpow_relate Real2 Real2_neq_Real0 (z-2) _ (IZReal_relator 2).
  have R2 := Zpow_relate Real2 Real2_neq_Real0 z _ (IZReal_relator 2). 
  have R3 := Zpow_relate Real2 Real2_neq_Real0 (-z + 2 - 2) _ (IZReal_relator 2). 
  have R4 := Zpow_relate Real2 Real2_neq_Real0 (-z + 2 ) _ (IZReal_relator 2). 
  have P := (powerRZ_lt 2 z Rlt_0_2).
  have P2 := (powerRZ_lt 2 (z-2) Rlt_0_2).
  split; classical;relate;Holger H1;Holger H2;relate;Holger xneq0;relate.
  - have -> : (-z + 2 - 2 = -z)%Z by lia.
    rewrite powerRZ_neg; try by lra.
    rewrite powerRZ_inv; try by lra.
    rewrite -(Rinv_involutive y); try by lra.
    apply Rle_Rinv; try by lra.
  have -> : (-z + 2 = -(z-2))%Z by lia.
  rewrite powerRZ_neg; try by lra.
  rewrite powerRZ_inv; try by lra.
  rewrite -(Rinv_involutive x0); try by lra.
  by apply Rle_Rinv; try by lra.
Qed.


Definition magnitude x : Real0 < x -> M {z | is_magnitude x z}.
Proof.
  move => xgt0.
  have := dec_x_lt_2 x. 
  apply lift_domM.
  case => H; first by apply magnitude2.
  have xneg0 : (x <> Real0) by apply (Realgt_neq _ _ xgt0).
  suff I : (Real0 < / xneg0 < Real2).
  - have := magnitude2 _ I.
    apply liftM.
    case => z zprp.
    exists (-z+2)%Z.
    by apply (magnitude_inv x xneg0).
  split; classical; relate.
  - apply Rinv_0_lt_compat.
    by apply /transport_lt_inv/xgt0/Ha/relate_constant0.
   rewrite (relate_IZReal _ _ H1).
   have -> : (2 = / / 2)%R by lra.
   apply Rinv_lt_contravar.
   suff : (0 < x1)%R by lra.
   apply /transport_lt_inv/xgt0/Ha/relate_constant0.
   suff : (1 < x1)%R by lra.
   apply /transport_lt_inv/H/Ha/relate_constant1.
Defined.
