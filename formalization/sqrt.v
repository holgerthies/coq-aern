Set Warnings "-parsing".
From mathcomp Require Import all_ssreflect.
Require Import Real Reals RealCoqReal RealHelpers magnitude.
From Coquelicot Require Import Coquelicot.
Require Import Psatz.
 Import testsearch.
Require Import Interval.Tactic.
Open Scope Real_scope.
Set Warnings "parsing".


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


Lemma sqrt_unique x :  forall z z', Real0 <= z /\ z * z = x -> Real0 <= z' /\ z' * z' = x -> z = z'.
Proof.
  move => z z' [P1 P2] [P1' P2'].
  Holger P1.
  Holger P2.
  Holger P1'.
  Holger P2'.
  classical.
  relate.
  have B : (0 <= y0)%R by rewrite <- H2;apply Rmult_le_pos.
  by rewrite <-(sqrt_lem_1 y0 y1), <- (sqrt_lem_1 y0 y) => //.
Qed.  

Definition restr_sqrt x : (/ IZReal4neq0) <= x -> (x <= Real2) -> {y | Real0 <= y /\ y * y = x}.
Proof.
  move => B1 B2.
  have T xr : is_total xr ->  (/ 4 <= xr <= 2)%R -> is_total (sqrt xr).
  - move => H1 H2.
    apply is_total_limit.
    by apply sqrt_approx_coq_real.
  apply Real_limit_P_lt_p.
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


Definition scale x : (Real0 < x) -> M { zy | (Zpow Real2 dReal2 (2*zy.1)) * zy.2 = x /\ (/ IZReal4neq0) <= zy.2 <= Real2 }.
Proof.
  move => H.
  have := (magnitude x H).
  apply liftM.
  case => z [zprp1 zprp2].
  have :  {z' | (z-1 <= 2*z')%Z /\ (2*z' <= z)%Z }.
  - exists (z / 2)%Z.
    split; last by apply Zdiv.Z_mult_div_ge; lia.
    rewrite {1}(Z.div_mod z 2); last by lia.
    suff : (z mod 2 < 2)%Z by lia.
    by apply Z.mod_pos_bound;lia.
  case => z' [z'prp1 z'prp2].
  exists (z', (Zpow Real2 dReal2 (-2*z')%Z)*x).
  split.
  - rewrite -Realmult_assoc -Zpow_plus.
    have -> : (2*z' + (-2*z') = 0)%Z by lia.
    by rewrite Realmult_unit.
  Holger H.
  have R1 := Zpow_relate Real2 dReal2 (z-2) _ (IZReal_relator 2).
  have R2 := Zpow_relate Real2 dReal2 z _ (IZReal_relator 2). 
  have R3 := Zpow_relate Real2 dReal2 (-2*z') _ (IZReal_relator 2). 
  Holger zprp1.
  Holger zprp2.
  relate.
  split => /=; classical; relate.
  - rewrite (relate_IZReal _ _ Ha0).
    apply /Rle_trans/Rmult_le_compat_l/H/powerRZ_le; last by lra.
    rewrite -powerRZ_add; last by lra.
    rewrite powerRZ_Rpower; last by lra.
    have p1 : (- 2 <= -2*z' + (z-2))%Z by lia.
    apply /Rle_trans/Rle_Rpower/IZR_le/p1; try by lra.
    by rewrite -powerRZ_Rpower => /=; try lra.   
  rewrite (relate_IZReal _ _ H3).
  apply /Rle_trans.
  apply /Rmult_le_compat_l/H1; first by apply powerRZ_le;lra.
  rewrite -powerRZ_add; last by lra.
  rewrite powerRZ_Rpower; last by lra.
  have p1 : (-2*z' + z <= 1)%Z by lia.
  apply /Rle_trans.
  apply /Rle_Rpower/IZR_le/p1; try by lra.
  by rewrite Rpower_1; lra.
Defined.

Lemma sqrt_scale x y z sqy: (Zpow Real2 dReal2 (2*z))*y = x -> sqy * sqy = y ->  ((Zpow Real2 dReal2 z)*sqy) * ((Zpow Real2 dReal2 z)*sqy) = x.
Proof.
  move => H1 H2.
  rewrite Realmult_comm -Realmult_assoc -(Realmult_comm sqy) -Realmult_assoc H2.
  by rewrite Realmult_assoc -Zpow_plus Realmult_comm Z.add_diag.
Qed.


Definition sqrt x : Real0 < x -> {y | Real0 <= y /\ y * y = x}.
Proof.
  move => H.
  apply singletonM => [E1 E2 | ].
  - elim E1; elim E2 => y [P1 P2] y' [P1' P2']. 
    apply /sigma_eqP;last by intros;apply irrl.  
    by apply (sqrt_unique x).
  have := (scale x H).
  apply liftM.
  case => [[z y] [P1 [P2 P2']]].
  case (restr_sqrt y P2 P2') => sqy [S1 S2].
  exists ((Zpow Real2 dReal2 z)*sqy).
  split; last by apply /sqrt_scale/S2.
  classical.
  have R := Zpow_relate Real2 dReal2 z _ (IZReal_relator 2).
  Holger S1.
  relate.
  apply Rmult_le_pos => //.
  by apply powerRZ_le; lra.
Qed.
