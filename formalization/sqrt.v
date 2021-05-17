From mathcomp Require Import all_ssreflect.
Require Import Real Reals RealCoqReal.
From Coquelicot Require Import Coquelicot.
Require Import Psatz.

Require Import Interval.Tactic.
Open Scope Real_scope.

Lemma IZReal_relator z : relate (IZReal z) (IZR z).
Proof.
  suff H : forall z', (0 <= z')%Z -> relate (IZReal z') (IZR z').
  - case z => [| p |p]; try by apply H;lia.
    rewrite IZReal_neg IZR_NEG.
    apply relate_subtraction.
    by apply H.
  apply Z_of_nat_prop.
  elim => [| n' IH]; first by rewrite Nat2Z.inj_0;apply relate_constant0.
  rewrite Nat2Z.inj_succ.
  have -> : (Z.succ (Z.of_nat n')) = ((Z.of_nat n') +1)%Z by lia.
  rewrite IZReal_hom plus_IZR.
  apply relate_addition =>//.
  suff -> : (IZReal 1) = Real1 by apply relate_constant1.
  by exact Logic.eq_refl.
Qed.

Lemma relate_IZReal z x : relate (IZReal z) x -> x = (IZR z).
Proof.
  suff H: relate (IZReal z) (IZR z).
  - move => R.
   by relate.
  by apply IZReal_relator.
Qed.

Lemma IZReal4neq0 : IZReal 4 <> Real0.
Proof.
  classical.
  relate.
  rewrite (relate_IZReal _ _ H).
  by lra.
Qed.

Lemma sqrt_bound_helper x :  (/ IZReal4neq0) <= x -> (x <= Real2) -> forall rx, relate x rx -> ((/ 4) <= rx <= 2)%R.
Proof.
  move => Bl Bu rx RX.
  split.
  - apply /transport_leq_inv/Bl => //.
    by apply  (relate_divison _ IZReal4neq0 4%R (IZReal_relator 4)).
  apply /transport_leq_inv/Bu => //.
  by apply IZReal_relator.
Qed.

Lemma sqrt_bounds x :  (/ IZReal4neq0) <= x -> (x <= Real2) -> forall rx, relate x rx -> ((/ 2) <= (sqrt rx) <= (sqrt 2))%R.
Proof.
  move => Bl Bu rx RX.
  have [B1 B2] := sqrt_bound_helper x Bl Bu rx RX.
  suff -> : (/ 2)%R = (sqrt (/ 4)) by split;apply sqrt_le_1;lra.
  rewrite <-inv_sqrt; last by lra.
  have -> : (4 = 2 * 2)%R by lra.
  by rewrite sqrt_square; lra.
Qed.

Lemma sqrt_expand x : (0 < x)%R -> (sqrt x) = ((/ 2)*((sqrt x) + (x / sqrt x)))%R.
Proof.
  move => H.
  field_simplify_eq.
  rewrite //= Rmult_1_r sqrt_sqrt; lra.
  suff : (0 < sqrt x)%R by lra.
  by apply sqrt_lt_R0.
Qed.

Definition sqrt_approx x n : (/ IZReal4neq0) <= x -> (x <= Real2) -> {y | forall rx ry, relate x rx -> relate y ry -> (Rabs (ry - sqrt rx) <= (/ 2 ^ (2 ^ n)))%R}.
Proof.
  move => B1 B2.
  suff [y P] : {y | (Real0 < y) /\ forall rx ry, relate x rx -> relate y ry -> (ry = 1 \/ sqrt rx <= ry)%R /\ (Rabs (ry - sqrt rx) <= (/ 2 ^ (2 ^ n)))%R} by exists y; apply P.
  elim n =>[| n' [y [ygt0 IH]]].
  - exists Real1; split => [| rx ry RX RY]; first by apply Real1_gt_Real0.
    split; first by relate; auto.
    have [B1' B2'] := (sqrt_bound_helper _ B1 B2 _ RX).
    relate.
    apply Rcomplements.Rabs_le_between' => /=.
    split;ring_simplify; first by interval.
    suff : ((/ 2) <= sqrt rx)%R by lra.
    suff -> : (/ 2)%R = (sqrt (/ 4)) by apply sqrt_le_1;lra.
    rewrite <-inv_sqrt; last by lra.
    have -> : (4 = 2 * 2)%R by lra.
    by rewrite sqrt_square; lra.
  have yneq0 : y <> Real0 by apply Realgt_neq.
  exists (/ dReal2 * (y + x / yneq0)).
  split.
  - classical. 
    relate.
    have [B1' B2'] := (sqrt_bound_helper _ B1 B2 _ Ha1).
    have ygt0' : (0 < x1)%R by apply /transport_lt_inv/ygt0/Hb/relate_constant0.
    rewrite (relate_IZReal _ _ Ha2).
    apply Rmult_lt_0_compat; first by lra.
    apply Rplus_lt_0_compat; first by lra.
    by apply Rdiv_lt_0_compat; lra.
  move => rx ry RX RY.
  relate.
  rewrite (relate_IZReal _ _ Ha2).
  have [ygt IH'] := IH _ _ Ha1 Hb. 
  have [B1' B2'] := (sqrt_bound_helper _ B1 B2 _ Ha1).
  have ygt0' : (0 < x1)%R by apply /transport_lt_inv/ygt0/Hb/relate_constant0.
  have p : (0 < rx / x1)%R by apply Rdiv_lt_0_compat; lra.
  split.
  - apply or_intror. 
    rewrite <- sqrt_pow2; last by lra.
    apply sqrt_le_1; [by lra| by apply pow2_ge_0|].
    rewrite Rpow_mult_distr.
    have -> : (x1 + (rx/x1))^2 = (x1^2 + 2*rx + (rx/x1)^2)%R by field_simplify_eq;lra.
    suff : (0 <= (x1 ^ 2 - 2*rx + (rx/x1)^2))%R by lra.
    have -> : (x1^2 - 2*rx + (rx / x1)^2 = ((x1-(rx/x1)) ^ 2))%R by field_simplify_eq;lra.
    by apply pow2_ge_0.
  rewrite sqrt_expand; last by lra.
  rewrite <- Rmult_minus_distr_l, Rabs_mult, Rabs_right; last by lra.
  have -> : (x1 + (rx/x1) - ((sqrt rx) + (rx / sqrt rx)) = (x1 - (sqrt rx))+(rx/x1 - (rx / sqrt rx)))%R by lra.
  have -> : (x1 - (sqrt rx) + ((rx/x1) - (rx / sqrt rx)) = (x1 - sqrt rx)*(x1 - (rx / sqrt rx ))*(/ x1))%R.
  - field_simplify_eq;try by lra.
    split; try by lra.
    by interval.
 have -> : ((x1 - (sqrt rx))*(x1 - (rx / sqrt rx)) = ((x1 - (sqrt rx)) ^ 2))%R.
 - field_simplify_eq; try by interval.
   rewrite /= !Rmult_1_r.
   by rewrite !sqrt_sqrt; lra.
  suff H : (Rabs (/ x1) <= 2)%R.
  - rewrite Rabs_mult.
    ring_simplify.
    rewrite <- RPow_abs.
    apply /Rle_trans.
    apply Rmult_le_compat_l; first by apply Rmult_le_pos; [lra|apply pow2_ge_0].
    apply H.
    suff : ((Rabs (x1 - sqrt rx))^2 <= (/ 2 ^ (2 ^ (n'.+1))))%R by lra.
    have -> : ((2 ^ (n'.+1)) = ((2 ^ n')*2))%nat by rewrite Nat.pow_succ_r' Nat.mul_comm.
    rewrite pow2_abs.
    rewrite pow_mult.
    rewrite Rinv_pow; last by apply pow_nonzero;lra.
    by apply pow_maj_Rabs.
  rewrite Rabs_Rinv; last by lra.
  rewrite Rabs_right; last by lra.
  have -> : (2 = / / 2)%R by lra.
  apply Rle_Rinv; try by lra.
  case ygt => H; first by lra.
  suff: (/ 2 <= sqrt rx)%R by lra.
  suff -> : ((/ 2) = (sqrt (/ 4)))%R by apply sqrt_le_1;lra.
  have -> : ((/ 4) = (/ 2) ^ 2)%R by lra.
  rewrite sqrt_pow2;lra.
Defined.
Definition sqrt_approx_fast x n : (/ IZReal4neq0) <= x -> (x <= Real2) -> {y | forall rx ry, relate x rx -> relate y ry -> (Rabs (ry - sqrt rx) < (/ 2 ^ n))%R}.
Proof.
  move => B1 B2.
  have [y P] := sqrt_approx x (Nat.log2 n.+1).+1 B1 B2.
  exists y => rx ry RX RY.
  have P' := (P _ _ RX RY).
  suff : ((/ 2 ^ (2 ^ (Nat.log2 n.+1).+1)) < (/ 2 ^ n))%R by lra.
  apply Rinv_lt_contravar; first by apply Rmult_lt_0_compat; apply pow_lt;lra.
  apply Rlt_pow; first by lra.
  suff : (n.+1 < (2 ^ (Nat.log2 n.+1).+1))%coq_nat by lia.
  by apply Nat.log2_spec;lia.
Defined. 

Lemma sqrt_approx_coq_real x : is_total x -> (/ 4 <= x <= 2)%R ->  forall n, exists y, is_total y /\ (Rabs (y - sqrt x) < (/ 2 ^ n))%R.
Proof.
  move => H1 H2.
  have [x' [P1 P2]] := (ana2 _ H1) .
  have [H2' H2''] : (/ IZReal4neq0) <= x' /\ x' <= Real2.
  - split; classical; relate; first by rewrite (relate_IZReal _ _ Ha);lra.
    by rewrite (relate_IZReal _ _ H0);lra.
  move => n.
  case (sqrt_approx_fast x' n H2' H2'') => y P. 
  case (ana1 y) => y' [Ry1 Ry2].
  exists y'; split; first by apply (relate_total _ _ Ry1).
  by apply P.
Qed.


Lemma relate_prec n : relate (prec n) (/ 2 ^ n)%R.
Proof.
  elim n =>  [ /=  | n' IH ]; first by rewrite Rinv_1; apply relate_constant1.
  have -> : (prec n'.+1) = (prec n') * (prec 1).
  - have -> : n'.+1 = (n'+1)%coq_nat by lia.
    by apply prec_hom.
  have -> : (prec 1) = (Real1 / Real2_neq_Real0) by [].
  rewrite  /= Rinv_mult_distr; [| by lra| by apply pow_nonzero].
  rewrite Rmult_comm.
  apply relate_multiplication => //.
  rewrite /Realdiv.
  have -> : (/ 2 = 1 *  /2)%R by lra.
  apply relate_multiplication; first by apply relate_constant1.
  apply (relate_divison Real2 Real2_neq_Real0 2).
  by apply IZReal_relator.
Qed.


Definition restr_sqrt x : (/ IZReal4neq0) <= x -> (x <= Real2) -> {y | Real0 <= y /\ y * y = x}.
Proof.
  move => B1 B2.
  have T xr : is_total xr ->  (/ 4 <= xr <= 2)%R -> is_total (sqrt xr).
  - move => H1 H2.
    apply is_total_limit.
    by apply sqrt_approx_coq_real.
  apply limit.
  - case (ana1 x) => xr [R1 R2].
    Holger B1.
    Holger B2.
    relate.
    have L : (/ 4 <= xr <= 2)%R by rewrite <- (relate_IZReal _ _ Ha), <- (relate_IZReal _ _ Hy0); lra.
    have [y [S1 S2]] := (ana2 _ (T _ (relate_total _ _ Hx0) L)).
    exists y.
    split => [ | x' [P1 P2]]; first by split;classical;relate;[apply sqrt_pos | apply sqrt_sqrt; lra].
    Holger P1.
    Holger P2.
    classical.
    relate.
    by apply sqrt_lem_1;lra.
  move => n.
  have [y P] := (sqrt_approx_fast x n B1 B2).
  exists y.
  Holger B1.
  Holger B2.
  relate.
  have L : (/ 4 <= y0 <= 2)%R by rewrite <- (relate_IZReal _ _ Ha), <- (relate_IZReal _ _ Hy0); lra.
  have [sx [S1 S2]] := (ana2 _ (T _ (relate_total _ _ Hx0) L)).
  have Rp := (relate_prec n).
  exists sx.
  split.
  - split; classical; relate; first by apply sqrt_pos.
    by apply sqrt_def;lra.
  split; classical; relate.
  - have -> : (x0 = - (/ 2 ^ n))%R by apply (Holber4 (/ 2 ^ n) (prec n)) => //.
    suff: (sqrt y0 - x1 < (/ 2 ^ n))%R by lra.
    apply Rabs_lt_between.
    rewrite Rabs_minus_sym.
    by apply (P _ _ Hx0 Ha0).
  apply Rabs_lt_between.
  by apply (P _ _ Hx0 Ha0).
Qed.
