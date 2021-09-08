Set Warnings "-parsing".
From mathcomp Require Import all_ssreflect.
Require Import Real Reals RealCoqReal RealHelpers magnitude.
From Coquelicot Require Import Coquelicot.
Require Import Psatz.
 Import testsearch.
Require Import Interval.Tactic.
Require Import Complex Euclidean.
Open Scope Real_scope.
Set Warnings "parsing".

Section sqrt.
  Generalizable Variables K M Real.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
          {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
          {M_MultivalueMonad : MultivalueMonad}
          {Real : Type}
          {SemiDecOrderedField_Real : SemiDecOrderedField Real}
          {ComplArchiSemiDecOrderedField_Real : ComplArchiSemiDecOrderedField}.

  (* ring structure on Real *)
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

  Add Ring realRing : (realTheory ) (constants [IZReal_tac]).

  

  
Lemma sqrt_bound_helper x :  (/ IZreal4neq0) <= x -> (x <= real_2) -> forall rx, relate x rx -> ((/ 4) <= rx <= 2)%R.
Proof.
  move => Bl Bu rx RX.
  split.
  - apply /transport_leq_inv/Bl => //.
    by apply  (relate_divison _ IZreal4neq0 4%R (IZreal_relator 4)).
  apply /transport_leq_inv/Bu => //.
  by apply IZreal_relator.
Qed.

Lemma sqrt_bounds x :  (/ IZreal4neq0) <= x -> (x <= real_2) -> forall rx, relate x rx -> ((/ 2) <= (sqrt rx) <= (sqrt 2))%R.
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

Definition sqrt_approx x n : (/ IZreal4neq0) <= x -> (x <= real_2) -> {y | forall rx ry, relate x rx -> @relate Real y ry -> (Rabs (ry - sqrt rx) <= (/ 2 ^ (2 ^ n)))%R}.
Proof.
  move => B1 B2.
  assert (yP : {y | (real_0 < y) /\ forall rx ry, relate x rx -> relate y ry -> (ry = 1 \/ sqrt rx <= ry)%R /\ (Rabs (ry - sqrt rx) <= (/ 2 ^ (2 ^ n)))%R}).
  elim n =>[| n' [y [ygt0 IH]]].
  - exists real_1; split => [| rx ry RX RY]; first by apply real_1_gt_0.
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
  have yneq0 : y <> real_0 by apply real_gt_neq.
  exists (/ RealOrder.d2 * (y + x / yneq0)).
  split.
  - classical. 
    relate.
    have [B1' B2'] := (sqrt_bound_helper _ B1 B2 _ Ha1).
    have ygt0' : (0 < x1)%R by apply /transport_lt_inv/ygt0/Hb/relate_constant0.
    rewrite (relate_IZreal _ _ Ha2).
    apply Rmult_lt_0_compat; first by lra.
    apply Rplus_lt_0_compat; first by lra.
    by apply Rdiv_lt_0_compat; lra.
  move => rx ry RX RY.
  relate.
  rewrite (relate_IZreal _ _ Ha2).
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
  destruct yP as [y P].
  exists y; apply P.
Defined.
Definition sqrt_approx_fast x n : (/ IZreal4neq0) <= x -> (x <= real_2) -> {y | forall rx ry, relate x rx -> @relate Real y ry -> (Rabs (ry - sqrt rx) < (/ 2 ^ n))%R}.
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
  have [x' [P1 P2]] := (@ana2 Real _ H1) .
  have [H2' H2''] : (/ IZreal4neq0) <= x' /\ x' <= real_2.
  - split; classical; relate; first by rewrite (relate_IZreal _ _ Ha);lra.
    by rewrite (relate_IZreal _ _ H0);lra.
  move => n.
  case (sqrt_approx_fast x' n H2' H2'') => y P. 
  case (ana1 y) => y' [Ry1 Ry2].
  exists y'; split; first by apply (relate_total _ _ Ry1).
  by apply P.
Qed.


Lemma sqrt_unique x :  forall z z', real_0 <= z /\ z * z = x -> real_0 <= z' /\ z' * z' = x -> z = z'.
Proof.
  move => z z' [P1 P2] [P1' P2'].
  Holger P1.
  Holger P2.
  Holger P1'.
  Holger P2'.
  apply transport_eq.
  intros.
  relate.
  have B : (0 <= y0)%R by rewrite <- H2;apply Rmult_le_pos.
  by rewrite <-(sqrt_lem_1 y0 y1), <- (sqrt_lem_1 y0 y) => //.
Qed.  

Definition restr_sqrt x : (/ IZreal4neq0) <= x -> (x <= real_2) -> {y | real_0 <= y /\ y * y = x}.
Proof.
  move => B1 B2.
  have TT xr : is_total xr ->  (/ 4 <= xr <= 2)%R -> is_total (sqrt xr).
  - move => H1 H2.
    apply is_total_limit.
    by apply sqrt_approx_coq_real.
  apply real_limit_P_lt_p.
  - case (ana1 x) => xr [R1 R2].
    Holger B1.
    Holger B2.
    relate.
    have L : (/ 4 <= xr <= 2)%R by rewrite <- (relate_IZreal _ _ Ha), <- (relate_IZreal _ _ Hy0); lra.
    have [y [S1 S2]] := (@ana2 Real _ (TT _ (relate_total _ _ Hx0) L)).
    exists y.
    split => [ | x' [P1 P2]].
    split.
    apply transport_leq.
    intros.
    relate.
    apply sqrt_pos.
    apply transport_eq.
    intros.
    relate.
    apply sqrt_sqrt.
    lra.
    Holger P1.
    Holger P2.
    apply transport_eq; intros; relate.
    by apply sqrt_lem_1;lra.
  move => n.
  have [y P] := (sqrt_approx_fast x n B1 B2).
  exists y.
  Holger B1.
  Holger B2.
  relate.
  have L : (/ 4 <= y0 <= 2)%R by rewrite <- (relate_IZreal _ _ Ha), <- (relate_IZreal _ _ Hy0); lra.
  have [sx [S1 S2]] := (@ana2 Real _ (TT _ (relate_total _ _ Hx0) L)).
  pose proof(relate_prec n) as Rp.
  exists sx.
  split.
  - split.
    apply transport_leq; intros; relate.
    apply sqrt_pos.
    apply transport_eq; intros; relate.
    apply sqrt_def; lra.
  split; classical; relate.
  - have -> : (x0 = - (/ 2 ^ n))%R by apply (Holber4 (/ 2 ^ n) (prec n)) => //.
    suff: (sqrt y0 - x1 < (/ 2 ^ n))%R by lra.
    apply Rabs_lt_between.
    rewrite Rabs_minus_sym.
    by apply (P _ _ Hx0 Ha0).
  apply Rabs_lt_between.
  apply P; auto.
Qed.


Definition scale x : (real_0 < x) -> M { zy | (Zpow real_2 RealOrder.d2 (2*zy.1)) * zy.2 = x /\ (/ IZreal4neq0) <= zy.2 <= real_2 }.
Proof.
  move => H.
  pose proof (magnitude x H).
  move : X.
  apply M_lift.
  case => z [zprp1 zprp2].
  have :  {z' | (z-1 <= 2*z')%Z /\ (2*z' <= z)%Z }.
  - exists (z / 2)%Z.
    split; last by apply Zdiv.Z_mult_div_ge; lia.
    rewrite {1}(Z.div_mod z 2); last by lia.
    suff : (z mod 2 < 2)%Z by lia.
    by apply Z.mod_pos_bound;lia.
  case => z' [z'prp1 z'prp2].
  exists (z', (Zpow real_2 RealOrder.d2 (-2*z')%Z)*x).
  split.
  - rewrite -real_mult_assoc -Zpow_plus.
    have -> : (2*z' + (-2*z') = 0)%Z by lia.
    by rewrite real_mult_unit.
  Holger H.
  pose proof (Zpow_relate real_2 RealOrder.d2 (z-2) _ (IZreal_relator 2)) as R1.
  pose proof (Zpow_relate real_2 RealOrder.d2 z _ (IZreal_relator 2)) as R2. 
  pose proof (Zpow_relate real_2 RealOrder.d2 (-2*z') _ (IZreal_relator 2)) as R3. 
  Holger zprp1.
  Holger zprp2.
  relate.
  split => /=; classical; relate.
  - rewrite (relate_IZreal _ _ Ha0).
    apply /Rle_trans/Rmult_le_compat_l/H/powerRZ_le; last by lra.
    rewrite -powerRZ_add; last by lra.
    rewrite powerRZ_Rpower; last by lra.
    have p1 : (- 2 <= -2*z' + (z-2))%Z by lia.
    apply /Rle_trans/Rle_Rpower/IZR_le/p1; try by lra.
    by rewrite -powerRZ_Rpower => /=; try lra.   
  rewrite (relate_IZreal _ _ H3).
  apply /Rle_trans.
  apply /Rmult_le_compat_l/H1; first by apply powerRZ_le;lra.
  rewrite -powerRZ_add; last by lra.
  rewrite powerRZ_Rpower; last by lra.
  have p1 : (-2*z' + z <= 1)%Z by lia.
  apply /Rle_trans.
  apply /Rle_Rpower/IZR_le/p1; try by lra.
  by rewrite Rpower_1; lra.
Defined.

Lemma sqrt_scale x y z sqy: (Zpow real_2 RealOrder.d2 (2*z))*y = x -> sqy * sqy = y ->  ((Zpow real_2 RealOrder.d2 z)*sqy) * ((Zpow real_2 RealOrder.d2 z)*sqy) = x.
Proof.
  move => H1 H2.
  rewrite real_mult_comm -real_mult_assoc -(real_mult_comm sqy) -real_mult_assoc H2.
  by rewrite real_mult_assoc -Zpow_plus real_mult_comm Z.add_diag.
Qed.


Definition sqrt_pos x : real_0 < x -> {y | real_0 <= y /\ y * y = x}.
Proof.
  move => H.
  apply M_hprop_elim_f => [E1 E2 | ].
  - elim E1; elim E2 => y [P1 P2] y' [P1' P2']. 
    apply /sigma_eqP;last by intros;apply irrl.  
    by apply (sqrt_unique x).
  have := (scale x H).
  apply M_lift.
  case => [[z y] [P1 [P2 P2']]].
  case (restr_sqrt y P2 P2') => sqy [S1 S2].
  exists ((Zpow real_2 RealOrder.d2 z)*sqy).
  split; last by apply /sqrt_scale/S2.
  classical.
  pose proof (Zpow_relate real_2 RealOrder.d2 z _ (IZreal_relator 2)) as R.
  Holger S1.
  relate.
  apply Rmult_le_pos => //.
  by apply powerRZ_le; lra.
Defined.


Lemma sqrt_unique_existence x : (real_0 <= x) -> exists ! y, real_0 <= y /\ y*y = x.
Proof.
  case (real_total_order x real_0) => [p | [-> | p]];  [by pose (real_gt_nle _ _ p) |  |].
  - exists real_0; by split => [| y]; [ |  apply sqrt_unique]; split; ring_simplify; try apply Realle_triv.
  case (sqrt_pos _ p) => y prp.
  exists y.
  split => // y'.
  by apply sqrt_unique.
Qed.

Definition sqrt x : real_0 <= x -> {y | real_0 <= y /\ y * y = x}.
Proof.
  move => H.
  apply real_mslimit_P_p; first by apply sqrt_unique_existence.
  move => n.
  pose proof ( M_split x (prec (2*n+1)) (prec (2*n+1)) (prec_pos (2*n+1))) as X; move : X.
  rewrite /real_minus real_plus_inv.
  apply M_lift.
  case => P.
  - case (sqrt_pos _ P) => sqx prp.
    exists sqx.
    exists sqx.
    split => //.
    rewrite real_plus_inv.
    split; apply real_lt_le; [| by apply prec_pos].
    apply (real_lt_add_r (prec n)).
    rewrite real_plus_unit;ring_simplify.
    by apply prec_pos.
  exists real_0.
  case (real_total_order x real_0) => [p | [-> | p]];  [by pose (real_gt_nle _ _ p) | exists real_0 |].
  - split;[by split; ring_simplify;[apply real_le_triv|] |].
    rewrite real_plus_inv; split; apply real_lt_le; [| by apply prec_pos].
    apply (real_lt_add_r (prec n)).
    rewrite real_plus_unit;ring_simplify.
    by apply prec_pos.
    case (sqrt_pos _ p) => sqx [prp1 prp2].
    exists sqx; split => //.
    rewrite real_plus_unit.
    split; last by apply real_lt_le;apply /real_le_lt_lt/prec_pos;apply (real_le_add_r sqx); rewrite real_plus_unit real_plus_comm real_plus_inv.
    have P' : prec (2*n + 1) + prec(2*n +1) > x by apply (real_gt_add_r (-prec (2*n+1))); rewrite real_plus_assoc real_plus_inv real_plus_comm real_plus_unit.
    apply real_lt_le.
    apply real_lt_anti.
    apply real_pos_square_gt_gt; [by apply prec_pos | |].
  -
    apply real_nle_ge.
    intro H'.
    apply real_le_ge in H'.
      rewrite <-(real_le_ge_eq _ _  prp1 H') in prp2.
      ring_simplify in prp2.   
      move : p.
      ring_simplify real_0.
      rewrite prp2.
      by apply real_ngt_triv.
    rewrite prp2 -prec_hom.
    have -> : (n + n = 2*n)%coq_nat by lia.
    by rewrite -prec_twice.
Defined. 

Lemma complex_nonzero_cases  a b : Complex a b <> complex0 -> M ({real_0 < a} + {a < real_0} + {real_0 < b} + {b < real_0}).
Proof.
  move => H.
  have neq0_cases : ~(a = real_0 /\ b  = real_0) by move => [C1 C2];rewrite C1 C2 in H.
  have neq0_cases' : (real_0 < a \/ a < real_0 \/  real_0 < b \/ b < real_0).
  - case (real_total_order real_0 a) => [p | [p | p]]; try by auto.
    case (real_total_order real_0 b) => [p' | [p' | p']]; try by auto.
    move : neq0_cases.
    rewrite -p -p'.
    by case.
  apply (M_lift_dom ({real_0 < a} + {a < real_0 \/ real_0 < b \/ b < real_0})).
  - case => P; first by apply M_unit; auto.
    apply (M_lift_dom ({a < real_0} + {real_0 < b \/ b < real_0})).
    case => P'; first by apply M_unit; auto.
    apply (M_lift_dom ({real_0 < b} + {b < real_0})).
    case => P'';  by apply M_unit; auto.
  - apply choose => //; try by apply real_lt_semidec.
  - apply choose => //; try by apply real_lt_semidec.
    by apply semidec_or; try apply real_lt_semidec.
  apply choose => //; try by apply real_lt_semidec.
  apply semidec_or; try apply semidec_or; try by apply real_lt_semidec.
Qed.

Lemma square_nonneg : forall z, real_0 <= (z * z)%Real.
Proof.
  intros.
  destruct (real_total_order z real_0) as [a|[b|c]].
  - by apply real_lt_le;apply square_pos;apply real_lt_neq.
  - rewrite b; right; ring.
  by apply real_lt_le;apply square_pos;apply real_gt_neq.
Qed.

Definition csqrt_neq0 (z : complex) : z <> complex0  -> M {sqz | complex_mult sqz sqz = z}.
Proof.
  destruct (complex_destruct z) as [a [b ->]] => H.
  have := complex_nonzero_cases _ _ H.
  have gt0 : real_0 <= (a*a + b*b)%Real by rewrite -(real_plus_unit real_0);apply real_le_le_plus_le; apply square_nonneg.
  case (sqrt _ gt0) => absz [absp1 absp2].
  have [absz_prp1 absz_prp2] : (- absz <= a <= absz)%Real.
  - Holger absp2;Holger gt0;Holger absp1.
    by split; classical;relate; try pose (Holber4 _ _ _ Hb3 H3);nra.
  have absz_prp' : b <> real_0 -> (- absz < a < absz)%Real.
  - move => H0.
    Holger H0;Holger absp2;Holger gt0;Holger absp1.
    split; by classical;relate; try pose (Holber4 _ _ _ Hb3 H4);nra.
  have [absgt1 absgt2] : real_0 <= (absz + a) / RealOrder.d2 /\ real_0 <= (absz - a) / RealOrder.d2 by split;Holger absz_prp1; Holger absz_prp2; classical; relate; rewrite (relate_IZreal _ _ Hb); pose (Holber4 _ _ _ Ha0 Hx); lra.
  case (sqrt _ absgt1) => c [cprp1 cprp2].
  case (sqrt _ absgt2) => d [dprp1 dprp2].
  have P0 : (b*b - (real_2*d)*(real_2 * d)*d*d = (real_2*d)*(real_2*d)*a)%Real.
  - Holger absp2.
    Holger cprp2.
    Holger dprp2.
    apply transport_eq; intros; relate.
    move : H1 H2.
    rewrite (relate_IZreal _ _ Ha8) => H1 H2.
    ring_simplify.
    have -> : (y6 ^ 4 = (y6 ^ 2) ^2)%R by field.
    have -> : (y6 ^2 = y6*y6)%R by field.
    by rewrite H2; lra.
  have P1 : (c*c - d*d = a)%Real.
  - rewrite cprp2 dprp2.
    by apply transport_eq; intros; relate;rewrite (relate_IZreal _ _ Hb1);lra.
  have simpl1 x y (yneq0 : (real_2*y <> real_0)%Real)  : (x / yneq0 * y = x / RealOrder.d2)%Real by classical2;relate;Holger yneq0;relate;field; apply Rmult_neq_0_reg.
  have simpl2 x : (x / RealOrder.d2 + x / RealOrder.d2 = x)%Real by  classical2; relate;rewrite (relate_IZreal _ _ Hb);lra.
  apply M_lift => [[[[]|]| ]] P.
  - have cneq0 : (real_2*c)%Real <> real_0 by Holger P;Holger cprp2;Holger absp1;classical2;relate; rewrite (relate_IZreal _ _ Ha); rewrite (relate_IZreal _ _ Ha) in H1; nra.
    exists (Complex c (b / cneq0)).
    rewrite /complex_mult /=.
    rewrite (real_mult_comm c).
    assert (c*c - b / cneq0 * (b / cneq0) = a)%Real.

    rewrite -P1.
    rewrite -P1 in P0.
    Holger P0.
    classical2.
    relate.   
    Holger cneq0.
    relate.
    move : H0 H1.
    rewrite (relate_IZreal _ _ Ha) => H1 H0.
    by field_simplify_eq; lra.

  -
    rewrite simpl1.
    rewrite simpl2.
    rewrite H0.
    auto.


  - have dneq0 : (real_2*d)%Real <> real_0 by Holger P;Holger dprp2;Holger absp1;classical2;relate;rewrite (relate_IZreal _ _ Ha); rewrite (relate_IZreal _ _ Ha) in H1;nra.
    exists (Complex (b / dneq0) d).
    rewrite /complex_mult /=.
    rewrite (real_mult_comm d).
    assert (b / dneq0 * (b / dneq0) - d*d = a)%Real.
    Holger P0;Holger dprp2;classical2;relate;Holger dneq0;relate.
    field_simplify_eq; last by apply Rmult_neq_0_reg; lra.
    by lra.

  --
    rewrite simpl1 simpl2 H0; auto.
    
  - have cneq0 : (real_2*c)%Real <> real_0.
    have [absz_prp3 absz_prp4] := (absz_prp' (real_gt_neq _ _ P)).
    + Holger absz_prp3; Holger absz_prp4; Holger cprp2; classical2; relate.
      by move : H0 H1 H2;rewrite (relate_IZreal _ _ Ha); rewrite (Holber4 _ _ _ Ha0 Hx); intros; nra.
    exists (Complex c (b / cneq0)).
    rewrite /complex_mult /=.
    rewrite (real_mult_comm c).
    assert (c*c - b / cneq0 * (b / cneq0) = a)%Real.
    rewrite -P1.
    rewrite -P1 in P0.
    Holger P0;classical2;relate;Holger cneq0;relate.
    move : H0 H1.
    rewrite (relate_IZreal _ _ Ha) => H1 H0.
    by field_simplify_eq; lra.

  --
    rewrite simpl1 simpl2 H0; auto.
  -
    exists (Complex c (-d)%Real).
    rewrite /complex_mult /=.
  have -> : (c*c - - d * -d = c*c - d*d)%Real by classical2;relate;rewrite (Holber4 _ _ _ Hb2 Hb1);lra.
  assert (H0 : (c* -d = b / RealOrder.d2)%Real).
  
  assert (H1 : (c*d = - b / RealOrder.d2)%Real).

    
  ring_simplify.
  apply (sqrt_unique (b / RealOrder.d2 * b / RealOrder.d2)%Real); Holger absp2; Holger cprp1; Holger cprp2; Holger dprp1; Holger dprp2; Holger P; split; classical2;relate; [by apply Rmult_le_pos | | |  ].
  - rewrite (relate_IZreal _ _ Hb6).
    move : H2 H4.
    rewrite (relate_IZreal _ _ Hb6) => H2 H4.
    field_simplify.
    field_simplify in H2.
    field_simplify in H4.
    rewrite H2 H4.
    by lra.
  - by rewrite (relate_IZreal _ _ Hb3) (Holber4 _ _ _ Hb5 Ha0);lra.
  by rewrite (relate_IZreal _ _ Hb8) (Holber4 _ _ _ Hb7 Ha6);lra.

  by Holger H1; Holger P; classical2; relate;move : H0;rewrite (Holber4 _ _ _ Ha Ha0) (Holber4 _ _ _ Hb2 Hb1);lra.
  
  by rewrite P1 (real_mult_comm (-d)) H0 simpl2.
  Defined.

Lemma prec_lt m n: (m <= n)%coq_nat -> prec n <= prec m. 
Proof.
  move => H.
  have -> : (n = m + (n - m)%coq_nat)%coq_nat by lia. 
  elim (n-m)%coq_nat => [|m' IH]; first by rewrite Nat.add_0_r; apply real_le_triv.
  have -> : (m + m'.+1 = (m+m')%coq_nat.+1)%coq_nat by lia.
  apply real_lt_le.
  apply /real_lt_le_lt/IH.
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
  - pose proof (euclidean_max_dist_pos x x1) as dp.
    move : Cx.
    elim (real_total_order (euclidean_max_dist x x1) real_0); intros dx Cx.
    apply real_gt_nge in dx.
    contradiction (dx dp).
    destruct dx as [dx | dx].
    apply euclidean_max_dist_id in dx.
    induction dx.
    contradiction (Cx x1prp).
    (* => [/real_gt_nge | [/euclidean_max_dist_id ->| dx Cx] ] //. *)
    case (real_Archimedean _ dx) => m mprp.
    exists m => y yprp.
    move => H0.
    move : mprp yprp.
    pose proof (x1prp' y H0).
    intros.
    induction H1.
    apply real_lt_nlt in yprp.
    exact (yprp mprp).

  pose proof (euclidean_max_dist_pos x x1) as dp1.
  pose proof (euclidean_max_dist_pos x x2) as dp2.
  move : Cx.
  destruct dp1, dp2; intro Cx.
  rename H0 into dx1.
  rename H1 into dx2.
  case (real_Archimedean _ dx1) => m1 m1prp.
  case (real_Archimedean _ dx2) => m2 m2prp.
  exists (max m1 m2) => y yprp.
  suff [H1 H2]: (x1 <> y) /\ (x2 <> y) by move => H0;case (prp y H0).
  have [P1' P2'] : prec (max m1 m2) < euclidean_max_dist x x1 /\ prec (max m1 m2) < euclidean_max_dist x x2.
  - split;first by apply /real_le_lt_lt/m1prp/prec_lt/Nat.le_max_l.
    apply /real_le_lt_lt/m2prp/prec_lt/Nat.le_max_r.
    split => eq; [move : P1' | move: P2'].
    induction eq.
    intro.
    apply real_lt_nlt in P1'.
    exact (P1' yprp).
    intro.
    induction eq.
    apply real_lt_nlt in P2'.
    exact (P2' yprp).

  apply euclidean_max_dist_id in H1.
  induction H1.
  contradiction (Cx Px2).
  apply euclidean_max_dist_id in H0.
  induction H0.
  contradiction (Cx Px1).
  apply euclidean_max_dist_id in H0.
  induction H0.
  contradiction (Cx Px1).
Qed.

Open Scope C_scope.

Lemma csqrt_solutions (x y z : complex ) : (x * x)%Complex = z -> (y * y)%Complex = z -> (x=y \/ x=-y)%Complex.
Proof.
  case (complex_destruct x) => [xr [xi ->]].
  case (complex_destruct y) => [yr [yi ->]].
  case (complex_destruct z) => [zr [zi ->]].
  rewrite /complex_mult /= => [[[H1 H1'] [H2 H2']] ].
  suff : (xr = yr /\ xi = yi)%Real  \/ (xr = -yr /\ xi = -yi)%Real by case => [[-> ->]|[-> ->] ];auto.
  move : H1 H1' H2 H2'.
  case (real_total_order xr yr) => [p | [->  | p]]; [right | left; split=>// | right].
Admitted.
  
(* approximates  square root by either returning zero for small numbers or computing the actual square root *)
Definition csqrt_approx (z : complex) n: M {sqapprox | exists x, (x*x)%Complex = z /\ euclidean_max_dist sqapprox x <= prec n}.
Admitted.

Definition csqrt (z: complex) : M {sqz | (sqz * sqz)%Complex = z}.
Proof.
  apply euclidean_mlimit_P.
  - apply euclidean_is_closed_is_seq_complete.
    apply two_point_set_closed => x1 x2 x3 x1p x2p x3p.
    case (csqrt_solutions _ _ _ x1p x3p) => P; try by auto.
    case (csqrt_solutions _ _ _ x2p x3p) => ->; try by auto.
    Admitted.

  (* - apply /M_lift/(csqrt_approx z 0) => [[x0 x0prp]]. *)
  (*   exists x0. *)
  (*   case x0prp => y yprp. *)
  (*   by exists y. *)
  (* move => n x. *)

End sqrt.
