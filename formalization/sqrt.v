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


Definition sqrt_pos x : Real0 < x -> {y | Real0 <= y /\ y * y = x}.
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
Defined.


Lemma sqrt_unique_existence x : (Real0 <= x) -> exists ! y, Real0 <= y /\ y*y = x.
Proof.
  case (Realtotal_order x Real0) => [p | [-> | p]];  [by pose (Realgt_nle _ _ p) |  |].
  - exists Real0; by split => [| y]; [ |  apply sqrt_unique]; split; ring_simplify; try apply Realle_triv.
  case (sqrt_pos _ p) => y prp.
  exists y.
  split => // y'.
  by apply sqrt_unique.
Qed.

Definition sqrt x : Real0 <= x -> {y | Real0 <= y /\ y * y = x}.
Proof.
  move => H.
  apply Real_mslimit_P_p; first by apply sqrt_unique_existence.
  move => n.
  have := M_split x (prec (2*n+1)) (prec (2*n+1)) (prec_pos (2*n+1)).
  rewrite /Realminus Realplus_inv.
  apply liftM.
  case => P.
  - case (sqrt_pos _ P) => sqx prp.
    exists sqx.
    exists sqx.
    split => //.
    rewrite Realplus_inv.
    split; apply Reallt_le; [| by apply prec_pos].
    apply (Reallt_add_r (prec n)).
    rewrite Realplus_unit;ring_simplify.
    by apply prec_pos.
  exists Real0.
  case (Realtotal_order x Real0) => [p | [-> | p]];  [by pose (Realgt_nle _ _ p) | exists Real0 |].
  - split;[by split; ring_simplify;[apply Realle_triv|] |].
    rewrite Realplus_inv; split; apply Reallt_le; [| by apply prec_pos].
    apply (Reallt_add_r (prec n)).
    rewrite Realplus_unit;ring_simplify.
    by apply prec_pos.
    case (sqrt_pos _ p) => sqx [prp1 prp2].
    exists sqx; split => //.
    rewrite Realplus_unit.
    split; last by apply Reallt_le;apply /Realle_lt_lt/prec_pos;apply (Realle_add_r sqx); rewrite Realplus_unit Realplus_comm Realplus_inv.
    have P' : prec (2*n + 1) + prec(2*n +1) > x by apply (Realgt_add_r (-prec (2*n+1))); rewrite Realplus_assoc Realplus_inv Realplus_comm Realplus_unit.
    apply Reallt_le.
    apply Reallt_anti.
    apply pos_square_gt_gt; [by apply prec_pos | |].
    - apply Realnle_ge => /Realle_ge H'.
      rewrite <-(Realle_ge_eq _ _  prp1 H') in prp2.
      ring_simplify in prp2.   
      move : p.
      rewrite prp2.
      by apply Realngt_triv.
    rewrite prp2 -prec_hom.
    have -> : (n + n = 2*n)%coq_nat by lia.
    by rewrite -prec_twice.
Defined. 

Require Import Complex Euclidean.

Open Scope C_scope.

Lemma complex_nonzero_cases  a b : complex a b <> Complex0 -> M ({Real0 < a} + {a < Real0} + {Real0 < b} + {b < Real0}).
Proof.
  move => H.
  have neq0_cases : ~(a = Real0 /\ b  = Real0) by move => [C1 C2];rewrite C1 C2 in H.
  have neq0_cases' : (Real0 < a \/ a < Real0 \/  Real0 < b \/ b < Real0).
  - case (Realtotal_order Real0 a) => [p | [p | p]]; try by auto.
    case (Realtotal_order Real0 b) => [p' | [p' | p']]; try by auto.
    move : neq0_cases.
    rewrite -p -p'.
    by case.
  apply (lift_domM ({Real0 < a} + {a < Real0 \/ Real0 < b \/ b < Real0})).
  - case => P; first by apply unitM; auto.
    apply (lift_domM ({a < Real0} + {Real0 < b \/ b < Real0})).
    case => P'; first by apply unitM; auto.
    apply (lift_domM ({Real0 < b} + {b < Real0})).
    case => P'';  by apply unitM; auto.
  - apply choose => //; try by apply Reallt_semidec.
  - apply choose => //; try by apply Reallt_semidec.
    by apply semidec_or; try apply Reallt_semidec.
  apply choose => //; try by apply Reallt_semidec.
  apply semidec_or; try apply semidec_or; try by apply Reallt_semidec.
Qed.

Lemma square_nonneg : forall z, Real0 <= z *z.
Proof.
  intros.
  destruct (Realtotal_order z Real0) as [a|[b|c]].
  - by apply Reallt_le;apply square_pos;apply Reallt_neq.
  - by rewrite b; ring_simplify;apply Realle_triv.
  by apply Reallt_le;apply square_pos;apply Realgt_neq.
Qed.

Definition csqrt_neq0 (z : Complex) : z <> Complex0  -> M {sqz | sqz * sqz = z}.
Proof.
  destruct (Complex_destruct z) as [a [b ->]] => H.
  have := complex_nonzero_cases _ _ H.
  have gt0 : Real0 <= a*a + b*b by rewrite -(Realplus_unit Real0);apply Realle_le_plus_le; apply square_nonneg.
  case (sqrt _ gt0) => absz [absp1 absp2].
  have [absz_prp1 absz_prp2] : - absz <= a <= absz.
  - Holger absp2;Holger gt0;Holger absp1.
    by split; classical;relate; try pose (Holber4 _ _ _ Hb3 H3);nra.
  have absz_prp' : b <> Real0 -> - absz < a < absz.
  - move => H0.
    Holger H0;Holger absp2;Holger gt0;Holger absp1.
    split; by classical;relate; try pose (Holber4 _ _ _ Hb3 H4);nra.
  have [absgt1 absgt2] : Real0 <= (absz + a) / dReal2 /\ Real0 <= (absz - a) / dReal2 by split;Holger absz_prp1; Holger absz_prp2; classical; relate; rewrite (relate_IZReal _ _ Hb); pose (Holber4 _ _ _ Ha0 Hx); lra.
  case (sqrt _ absgt1) => c [cprp1 cprp2].
  case (sqrt _ absgt2) => d [dprp1 dprp2].
  have P0 : (b*b - (Real2*d)*(Real2 * d)*d*d = (Real2*d)*(Real2*d)*a)%Real.
  - Holger absp2.
    Holger cprp2.
    Holger dprp2.
    classical.
    relate.
    move : H1 H2.
    rewrite (relate_IZReal _ _ Ha8) => H1 H2.
    ring_simplify.
    have -> : (y6 ^ 4 = (y6 ^ 2) ^2)%R by field.
    have -> : (y6 ^2 = y6*y6)%R by field.
    by rewrite H2; lra.
  have P1 : (c*c - d*d = a)%Real.
  - rewrite cprp2 dprp2.
    by classical;relate;rewrite (relate_IZReal _ _ Hb1);lra.
  have simpl1 x y (yneq0 : (Real2*y <> Real0)%Real)  : (x / yneq0 * y = x / dReal2)%Real by classical;relate;Holger yneq0;relate;field; apply Rmult_neq_0_reg.
  have simpl2 x : (x / dReal2 + x / dReal2 = x)%Real by  classical; relate;rewrite (relate_IZReal _ _ Hb);lra.
  apply liftM => [[[[]|]| ]] P.
  - have cneq0 : (Real2*c)%Real <> Real0 by Holger P;Holger cprp2;Holger absp1;classical;relate; rewrite (relate_IZReal _ _ Ha); rewrite (relate_IZReal _ _ Ha) in H1; nra.
    exists (complex c (b / cneq0)).
    rewrite /Complex_mult /=.
    rewrite (Realmult_comm c).
    suff -> : (c*c - b / cneq0 * (b / cneq0) = a)%Real by rewrite simpl1 simpl2.
    rewrite -P1.
    rewrite -P1 in P0.
    Holger P0.
    classical.
    relate.   
    Holger cneq0.
    relate.
    move : H0 H1.
    rewrite (relate_IZReal _ _ Ha) => H1 H0.
    by field_simplify_eq; lra.
  - have dneq0 : (Real2*d)%Real <> Real0 by Holger P;Holger dprp2;Holger absp1;classical;relate;rewrite (relate_IZReal _ _ Ha); rewrite (relate_IZReal _ _ Ha) in H1;nra.
    exists (complex (b / dneq0) d).
    rewrite /Complex_mult /=.
    rewrite (Realmult_comm d).
    suff -> : (b / dneq0 * (b / dneq0) - d*d = a)%Real by rewrite simpl1 simpl2.
    Holger P0;Holger dprp2;classical;relate;Holger dneq0;relate.
    field_simplify_eq; last by apply Rmult_neq_0_reg; lra.
    by lra.
  - have cneq0 : (Real2*c)%Real <> Real0.
    have [absz_prp3 absz_prp4] := (absz_prp' (Realgt_neq _ _ P)).
    + Holger absz_prp3; Holger absz_prp4; Holger cprp2; classical; relate.
      by move : H0 H1 H2;rewrite (relate_IZReal _ _ Ha); rewrite (Holber4 _ _ _ Ha0 Hx); intros; nra.
    exists (complex c (b / cneq0)).
    rewrite /Complex_mult /=.
    rewrite (Realmult_comm c).
    suff -> : (c*c - b / cneq0 * (b / cneq0) = a)%Real by rewrite simpl1 simpl2.
    rewrite -P1.
    rewrite -P1 in P0.
    Holger P0;classical;relate;Holger cneq0;relate.
    move : H0 H1.
    rewrite (relate_IZReal _ _ Ha) => H1 H0.
    by field_simplify_eq; lra.
  exists (complex c (-d)%Real).
  rewrite /Complex_mult /=.
  have -> : (c*c - - d * -d = c*c - d*d)%Real by classical;relate;rewrite (Holber4 _ _ _ Hb2 Hb1);lra.
  suff H0 : (c* -d = b / dReal2)%Real by rewrite P1 (Realmult_comm (-d)) H0 simpl2.
  suff H1 : (c*d = - b / dReal2)%Real by Holger H1; Holger P; classical; relate;move : H0;rewrite (Holber4 _ _ _ Ha Ha0) (Holber4 _ _ _ Hb2 Hb1);lra.
  ring_simplify.
  apply (sqrt_unique (b / dReal2 * b / dReal2)%Real); Holger absp2; Holger cprp1; Holger cprp2; Holger dprp1; Holger dprp2; Holger P; split; classical;relate; [by apply Rmult_le_pos | | |  ].
  - rewrite (relate_IZReal _ _ Hb6).
    move : H2 H4.
    rewrite (relate_IZReal _ _ Hb6) => H2 H4.
    field_simplify.
    field_simplify in H2.
    field_simplify in H4.
    rewrite H2 H4.
    by lra.
  - by rewrite (relate_IZReal _ _ Hb3) (Holber4 _ _ _ Hb5 Ha0);lra.
  by rewrite (relate_IZReal _ _ Hb8) (Holber4 _ _ _ Hb7 Ha6);lra.
Defined.

Lemma prec_lt m n: (m <= n)%coq_nat -> prec n <= prec m. 
Proof.
  move => H.
  have -> : (n = m + (n - m)%coq_nat)%coq_nat by lia. 
  elim (n-m)%coq_nat => [|m' IH]; first by rewrite Nat.add_0_r; apply Realle_triv.
  have -> : (m + m'.+1 = (m+m')%coq_nat.+1)%coq_nat by lia.
  apply Reallt_le.
  apply /Reallt_le_lt/IH.
  by apply prec_S.
Qed.

Lemma two_point_set_closed n (P : euclidean n -> Prop): (forall x1 x2 x3, P x1 -> P x2 -> P x3 -> x1 = x2 \/ x1 = x3 \/ x2 = x3) -> euclidean_is_closed P.
Proof.
   move => H.
   move => x.
   move => Cx.
   have Pprp : (forall x, ~ P x) \/ (exists x, P x /\ forall x',  P x' -> x = x') \/ (exists x1 x2, P x1 /\ P x2 /\ (x1 <> x2) /\ forall x3, P x3 -> x1 = x3 \/ x2 = x3).
   - case (lem (forall x, ~ P x)); try by auto.
     case (lem (exists x, P x /\ forall x',  P x' -> x = x')); try by auto.
     case (lem (exists x1 x2, P x1 /\ P x2 /\ (x1 <> x2) /\ forall x3, P x3 -> x1 = x3 \/ x2 = x3)); try by auto.
     move => H1 H2 H3.
     apply Classical_Pred_Type.not_all_not_ex in H3.
     have  H1' := (Classical_Pred_Type.not_ex_all_not _  _ H1 ).
     have  H2' := (Classical_Pred_Type.not_ex_all_not _  _ H2 ).
     case H3 => x0 Px0.
     have /Classical_Prop.not_and_or := (H2' x0); case => // /Classical_Pred_Type.not_all_ex_not x0p.
     case x0p => x1 x1p.
     have [x1p1 x1p2] := Classical_Prop.imply_to_and _ _ x1p.
     have /Classical_Prop.not_and_or := (Classical_Pred_Type.not_ex_all_not _ _ (H1' x0) x1); case => // /Classical_Prop.not_and_or ; case  => // => /Classical_Prop.not_and_or; case => // /Classical_Pred_Type.not_all_ex_not;case => x2 x2prp.
     have [x2prp1 /Classical_Prop.not_or_and [x2prp2 x2prp3]] := Classical_Prop.imply_to_and _ _ x2prp.
     have H' := (H _ _ _ Px0 x1p1 x2prp1).
     contradict H'.
     case;by auto.
  case Pprp => [prp | [[x1 [x1prp x1prp']] | [x1 [x2 [Px1 [Px2 [neq prp] ] ]]] ]]; first by exists (0%nat); intros;apply prp.
  - have dp := (euclidean_max_dist_pos x x1).
    move : Cx.
    case (Realtotal_order (euclidean_max_dist x x1) Real0) => [/Realgt_nge | [/euclidean_max_dist_id ->| dx Cx] ] //.
    case (RealArchimedean _ dx) => m mprp.
    exists m => y yprp.
    move => H0.
    move : mprp yprp.
    have -> := (x1prp' y H0) => /Reallt_nlt.
    by auto.
  have dp1 := (euclidean_max_dist_pos x x1).
  have dp2 := (euclidean_max_dist_pos x x2).
  move : Cx.
  case (Realtotal_order (euclidean_max_dist x x1) Real0) => [/Realgt_nge | [/euclidean_max_dist_id ->| dx1  ] ] //.
  case (Realtotal_order (euclidean_max_dist x x2) Real0) => [/Realgt_nge | [/euclidean_max_dist_id ->| dx2 Cx] ] //.
  case (RealArchimedean _ dx1) => m1 m1prp.
  case (RealArchimedean _ dx2) => m2 m2prp.
  exists (max m1 m2) => y yprp.
  suff [H1 H2]: (x1 <> y) /\ (x2 <> y) by move => H0;case (prp y H0).
  have [P1' P2'] : prec (max m1 m2) < euclidean_max_dist x x1 /\ prec (max m1 m2) < euclidean_max_dist x x2.
  - split;first by apply /Realle_lt_lt/m1prp/prec_lt/Nat.le_max_l.
    apply /Realle_lt_lt/m2prp/prec_lt/Nat.le_max_r.
  split => eq; [move : P1' | move: P2']; by rewrite eq => /Reallt_nlt.
Qed.


Lemma csqrt_solutions (x y z : Complex) : x*x = z -> y*y = z -> (x=y \/ x=-y).
Proof.
  case (Complex_destruct x) => [xr [xi ->]].
  case (Complex_destruct y) => [yr [yi ->]].
  case (Complex_destruct z) => [zr [zi ->]].
  rewrite /Complex_mult /= => [[[H1 H1'] [H2 H2']] ].
  suff : (xr = yr /\ xi = yi)%Real  \/ (xr = -yr /\ xi = -yi)%Real by case => [[-> ->]|[-> ->] ];auto.
  move : H1 H1' H2 H2'.
  case (Realtotal_order xr yr) => [p | [->  | p]]; [right | left; split=>// | right].
Admitted.
  
(* approximates  square root by either returning zero for small numbers or computing the actual square root *)
Definition csqrt_approx (z : Complex) n: M {sqapprox | exists x, x*x = z /\ euclidean_max_dist sqapprox x <= prec n}.
Admitted.

Definition csqrt (z: Complex) : M {sqz | sqz * sqz = z}.
Proof.
  apply euclidean_mlimit_P.
  - apply euclidean_is_closed_is_seq_complete.
    apply two_point_set_closed => x1 x2 x3 x1p x2p x3p.
    case (csqrt_solutions _ _ _ x1p x3p) => P; try by auto.
    case (csqrt_solutions _ _ _ x2p x3p) => ->; try by auto.
  - apply /liftM/(csqrt_approx z 0) => [[x0 x0prp]].
    exists x0.
    case x0prp => y yprp.
    by exists y.
  move => n x.
Admitted.
