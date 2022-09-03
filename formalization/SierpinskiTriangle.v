(* this file proves various properties of subsets of real numbers *)
Require Import Lia.
Require Import Real Euclidean List Minmax Subsets.

Section SierpinskiTriangle.

Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).
#[local] Definition sofReal := @sofReal types casofReal.
#[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).
#[local] Notation "^euclidean" := (@euclidean types) (at level 0).
#[local] Notation "^ball" := (@ball types) (at level 0).

(* ring structure on Real *)
Ltac IZReal_tac t :=
  match t with
  | real_0 => constr:(0%Z)
  | real_1 => constr:(1%Z)
  | IZreal 2%Z => constr:(2%Z)
  | IZreal ?u =>
    match isZcst u with
    | true => u
    | _ => constr:(InitialRing.NotConstant)
    end
  | _ => constr:(InitialRing.NotConstant)
  end.

Add Ring realRing : (realTheory ) (constants [IZReal_tac]).

  Lemma real_0_neg_eq : - real_0 = real_0. 
  Proof. ring. Qed.

  Definition one_half := / real_2_neq_0.

  Lemma one_half_pos : one_half > real_0.
  Proof.
    unfold one_half.
    apply real_pos_inv_pos.
    apply real_2_pos.
  Qed.

  Lemma one_half_neq0 : one_half <> real_0.
    apply real_gt_neq.
    apply one_half_pos.
  Qed.

  Lemma one_half_plus_one_half : one_half + one_half = real_1.
  Proof.
    apply (real_eq_mult_cancel real_2).
    apply real_2_neq_0.
    rewrite real_mult_comm, real_mult_plus_distr.
    unfold one_half.
    rewrite real_mult_comm.
    rewrite real_mult_inv.
    unfold real_2.
    ring.
  Qed.

  Lemma one_minus_one_half : real_1 + (- one_half) = one_half.
  Proof.
    apply (real_eq_plus_cancel one_half).
    ring_simplify (real_1 + - one_half + one_half).
    rewrite one_half_plus_one_half. auto.
  Qed.

  Lemma one_half_times_2 : one_half * real_2 = real_1.
  Proof.
    unfold one_half.
    apply real_mult_inv.
  Qed.


  (* The vertices of the triangle hull *)
  Variables ST_v1 ST_v2 ST_v3 : ^euclidean 2.
  Variable ST_initial_ball : ^ball 2.
  Variable ST_initial_ball_radius_bound : snd ST_initial_ball <= real_1.
  Variable ST_initial_ball_contains_v1 : 
    ball_to_subset 2 ST_initial_ball ST_v1.
  Variable ST_initial_ball_contains_v2 : 
    ball_to_subset 2 ST_initial_ball ST_v2.
  Variable ST_initial_ball_contains_v3 : 
    ball_to_subset 2 ST_initial_ball ST_v3.

  Definition ST_has_v123 (s : euclidean_subset 2) : Prop :=
    (s ST_v1) /\ (s ST_v2) /\ (s ST_v3).

  (* The convex hull of the vertices defined using weights *)

  Definition ST_weighted_pt (c1 c2 c3 : ^Real) : ^euclidean 2.
    destruct (split_euclidean2 ST_v1) as [x1 [y1 _]].
    destruct (split_euclidean2 ST_v2) as [x2 [y2 _]].
    destruct (split_euclidean2 ST_v3) as [x3 [y3 _]].
    pose (c1 * x1 + c2 * x2 + c3 * x3) as x.
    pose (c1 * y1 + c2 * y2 + c3 * y3) as y.
    apply (make_euclidean2 x y).
  Defined.

  Definition ST_weights123_valid (c1 c2 c3 : ^Real) : Prop :=
    c1 >= real_0 /\ c2 >= real_0 /\ c3 >= real_0 /\ c1 + c2 + c3 = real_1.

  Definition ST_weights123_no_middle (c1 c2 c3 : ^Real) : Prop :=
    (c1 >= one_half \/ c2 >= one_half \/ c3 >= one_half).

  Definition ST_inside_hull_no_middle_pt (pt : ^euclidean 2) : Prop :=
    exists c1 c2 c3 : ^Real, 
    pt = (ST_weighted_pt c1 c2 c3) /\ ST_weights123_valid c1 c2 c3 /\ ST_weights123_no_middle c1 c2 c3.
  
  Definition ST_inside_hull_no_middle (s : euclidean_subset 2) : Prop :=
    forall pt : ^euclidean 2, s pt -> ST_inside_hull_no_middle_pt pt.

  (* Lemmas about the weights of points *)

  Lemma weights12_c1_le_1 c1 c2 : 
    real_0 <= c1 /\ real_0 <= c2 /\ c1 + c2 <= real_1
    -> c1 <= real_1.
  Proof.
    intros [c1pos [c2pos c12sum]].

    assert ((c1+real_0) <= (c1+c2)) as Temp.
    apply real_le_plus_le. apply c2pos.
    pose proof (real_le_le_le _ _ _ Temp c12sum) as Temp2.
    rewrite real_plus_comm in Temp2.
    rewrite real_plus_unit in Temp2.
    auto.
  Qed.

  Lemma weights12_c2_le_1 c1 c2 : 
    real_0 <= c1 /\ real_0 <= c2 /\ c1 + c2 <= real_1
    -> c2 <= real_1.
  Proof.
    intros [c1pos [c2pos c12sum]].
    rewrite real_plus_comm in c12sum.

    apply (weights12_c1_le_1 c2 c1).
    split; auto; split; auto.
  Qed.

  Lemma weights123_le_1 c1 c2 c3 : 
    ST_weights123_valid c1 c2 c3 -> 
    c1 <= real_1 /\ c2 <= real_1 /\ c3 <= real_1.
  Proof.
    intros [c1pos [c2pos [c3pos c123sum]]].
    apply real_eq_le in c123sum.

    assert (real_0 <= c1 + c2) as c12pos.
    rewrite <- (real_plus_unit real_0).
    apply real_le_le_plus_le; auto.

    assert (c1 + c2 <= real_1) as c12sum.
    apply (weights12_c1_le_1 (c1+c2) c3).
    split; auto; split; auto.

    split.
    apply (weights12_c1_le_1 c1 c2).
    split; auto; split; auto.

    split.
    apply (weights12_c2_le_1 c1 c2).
    split; auto; split; auto.

    apply (weights12_c2_le_1 (c1+c2) c3).
    split.
    rewrite <- (real_plus_unit real_0).
    apply real_le_le_plus_le; auto.
    split; auto; split; auto.
  Qed.

  Lemma ST_weighted_pt_in_init_ball (c1 c2 c3 : ^Real) : 
    ST_weights123_valid c1 c2 c3 ->
    ball_to_subset 2 ST_initial_ball (ST_weighted_pt c1 c2 c3).
  Proof.
      intro valid123.
      pose proof (weights123_le_1 _ _ _ valid123) as [c1le1 [c2le1 c3le1]].
      destruct valid123 as [c1pos [c2pos [c3pos c123sum]]].

      unfold ST_weighted_pt.

      pose proof ST_initial_ball_contains_v1 as v1in.
      pose proof ST_initial_ball_contains_v2 as v2in.
      pose proof ST_initial_ball_contains_v3 as v3in.

      destruct (split_euclidean2 ST_v1) as [x1 [y1 xy1]].
      destruct (split_euclidean2 ST_v2) as [x2 [y2 xy2]].
      destruct (split_euclidean2 ST_v3) as [x3 [y3 xy3]].
      rewrite xy1 in v1in.
      rewrite xy2 in v2in.
      rewrite xy3 in v3in.
      clear xy1 xy2 xy3.

      destruct ST_initial_ball as [c r].
      destruct (split_euclidean2 c) as [xc [yc xyc]].
      rewrite xyc in v1in, v2in, v3in.
      rewrite xyc; clear xyc.

      unfold ball_to_subset in v1in, v2in, v3in.
      simpl in v1in, v2in, v3in.
      unfold ball_to_subset. simpl.

      unfold euclidean_max_dist, euclidean_minus, euclidean_plus in v1in, v2in, v3in.
      simpl in v1in, v2in, v3in.

      unfold make_euclidean2, euclidean_max_dist, euclidean_minus, euclidean_plus.
      simpl.

      pose proof v1in as v1inX.
      pose proof v2in as v2inX.
      pose proof v3in as v3inX.
      apply real_max_le_fst_le in v1inX, v2inX, v3inX.
      pose proof v1in as v1inY.
      pose proof v2in as v2inY.
      pose proof v3in as v3inY.
      apply real_max_le_snd_le in v1inY, v2inY, v3inY.
      apply real_max_le_fst_le in v1inY, v2inY, v3inY.
      clear v1in v2in v3in.

      assert (real_0 <= r) as rpos.
      apply (real_le_le_le _ (abs (x1 + - xc))); auto.
      apply abs_pos.

      (* assert (real_0 <= c1 + c2) as c12pos.
      rewrite <- (real_plus_unit real_0).
      apply real_le_le_plus_le; auto.

      assert (real_0 <= c2 + c3) as c23pos.
      rewrite <- (real_plus_unit real_0).
      apply real_le_le_plus_le; auto.

      assert (c1 + c2 <= real_1) as c12sum.
      apply (weights12_c1_le_1 (c1+c2) c3).
      split; auto; split; auto; right; auto.
  
      assert (c2 + c3 <= real_1) as c23sum.
      rewrite real_plus_assoc in c123sum.
      apply (weights12_c2_le_1 c1 (c2+c3)).
      split; auto; split; auto; right; auto. *)

      rewrite <- (real_mult_unit xc).
      rewrite <- (real_mult_unit yc).
      rewrite <- c123sum.
      assert ((c1 * x1 + c2 * x2 + c3 * x3 + - ((c1 + c2 + c3) * xc)) = 
         c1 * (x1 + - xc) + c2 * (x2 + - xc) + c3 * (x3 + - xc)) as Temp. ring.
      rewrite Temp; clear Temp.
      assert ((c1 * y1 + c2 * y2 + c3 * y3 + - ((c1 + c2 + c3) * yc)) = 
         c1 * (y1 + - yc) + c2 * (y2 + - yc) + c3 * (y3 + - yc)) as Temp. ring.
      rewrite Temp; clear Temp.

      apply real_max_le_le_le.
      - 
        (* use triangle inequality to distribute the abs *)
        apply (real_le_le_le _ (abs (c1 * (x1 + - xc) + c2 * (x2 + - xc)) + abs(c3 * (x3 + - xc)))).
        apply abs_tri.
        pose proof (abs_tri (c1 * (x1 + - xc)) (c2 * (x2 + - xc))) as Temp.
        apply (real_le_plus_le (abs (c3 * (x3 + - xc)))) in Temp.
        rewrite (real_plus_comm (abs (c3 * (x3 + - xc)))) in Temp.
        rewrite (real_plus_comm (abs (c3 * (x3 + - xc)))) in Temp.
        apply (real_le_le_le _ _ _ Temp).
        clear Temp.

        rewrite abs_mult, abs_mult, abs_mult.
        rewrite (abs_pos_id c1), (abs_pos_id c2), (abs_pos_id c3); auto.
    
        assert (c1 * abs (x1 + - xc) <= c1 * r) as T1.
        destruct c1pos.
        apply (real_le_mult_pos_le c1); auto.
        rewrite <- H; right; ring.
        assert (c2 * abs (x2 + - xc) <= c2 * r) as T2.
        destruct c2pos.
        apply (real_le_mult_pos_le c2); auto.
        rewrite <- H; right; ring.
        assert (c3 * abs (x3 + - xc) <= c3 * r) as T3.
        destruct c3pos.
        apply (real_le_mult_pos_le c3); auto.
        rewrite <- H; right; ring.

        rewrite <- (real_mult_unit r).
        rewrite <- c123sum.
        ring_simplify.
        apply (real_le_le_plus_le); auto.
        apply (real_le_le_plus_le); auto.

      - apply real_max_le_le_le; auto.
        (* as above but for y instead of x *)
        apply (real_le_le_le _ (abs (c1 * (y1 + - yc) + c2 * (y2 + - yc)) + abs(c3 * (y3 + - yc)))).
        apply abs_tri.
        pose proof (abs_tri (c1 * (y1 + - yc)) (c2 * (y2 + - yc))) as Temp.
        apply (real_le_plus_le (abs (c3 * (y3 + - yc)))) in Temp.
        rewrite (real_plus_comm (abs (c3 * (y3 + - yc)))) in Temp.
        rewrite (real_plus_comm (abs (c3 * (y3 + - yc)))) in Temp.
        apply (real_le_le_le _ _ _ Temp).
        clear Temp.

        rewrite abs_mult, abs_mult, abs_mult.
        rewrite (abs_pos_id c1), (abs_pos_id c2), (abs_pos_id c3); auto.
    
        assert (c1 * abs (y1 + - yc) <= c1 * r) as T1.
        destruct c1pos.
        apply (real_le_mult_pos_le c1); auto.
        rewrite <- H; right; ring.
        assert (c2 * abs (y2 + - yc) <= c2 * r) as T2.
        destruct c2pos.
        apply (real_le_mult_pos_le c2); auto.
        rewrite <- H; right; ring.
        assert (c3 * abs (y3 + - yc) <= c3 * r) as T3.
        destruct c3pos.
        apply (real_le_mult_pos_le c3); auto.
        rewrite <- H; right; ring.

        rewrite <- (real_mult_unit r).
        rewrite <- c123sum.
        ring_simplify.
        apply (real_le_le_plus_le); auto.
        apply (real_le_le_plus_le); auto.
  Qed.

  (* Self-similarity with ratio 1/2 *)

  Definition point_point_mid (p1 : ^euclidean 2) (p2 : ^euclidean 2) : ^euclidean 2.
    destruct (split_euclidean2 p1) as [x1 [y1 _]].
    destruct (split_euclidean2 p2) as [x2 [y2 _]].
    apply (make_euclidean2 ((x1 + x2) * one_half) ((y1 + y2) * one_half)).
  Defined.

  Definition point_point_away (p1 : ^euclidean 2) (p2 : ^euclidean 2) : ^euclidean 2.
    destruct (split_euclidean2 p1) as [x1 [y1 _]].
    destruct (split_euclidean2 p2) as [x2 [y2 _]].
    apply (make_euclidean2 ((x2 + x2 - x1)) ((y2 + y2 - y1))).
  Defined.

  Lemma point_point_away_mid_id  (p1 : ^euclidean 2) (p2 : ^euclidean 2) : p2 = point_point_mid p1 (point_point_away p1 p2).
  Proof.
    destruct (split_euclidean2 p1) as [x1 [y1 pxy1]].
    destruct (split_euclidean2 p2) as [x2 [y2 pxy2]].
    rewrite pxy1, pxy2.
    unfold point_point_mid, point_point_away, make_euclidean2. simpl.
    clear pxy1 pxy2 p1 p2.

    f_equal.
    assert ((x1 + (x2 + x2 - x1)) = x2*real_2) as Temp.
    unfold real_2.
    ring. rewrite Temp; clear Temp.
    rewrite real_mult_assoc.
    unfold one_half.
    rewrite (real_mult_comm real_2).
    rewrite real_mult_inv.
    rewrite real_mult_comm.
    rewrite real_mult_unit.
    auto.
    
    f_equal.
    assert ((y1 + (y2 + y2 - y1)) = y2*real_2) as Temp.
    unfold real_2.
    ring. rewrite Temp; clear Temp.
    rewrite real_mult_assoc.
    unfold one_half.
    rewrite (real_mult_comm real_2).
    rewrite real_mult_inv.
    rewrite real_mult_comm.
    rewrite real_mult_unit.
    auto.
  Qed.

  Definition point_ball_mid (p : ^euclidean 2) (b : ^ball 2) : ^ball 2.
    destruct b as [bc br].
    apply (pair (point_point_mid p bc) (br * one_half)).
  Defined.

  Lemma point_ball_mid_halves p b d : (snd b <= d) -> snd (point_ball_mid p b) <= d * one_half.
  Proof.
    intro.
    unfold point_ball_mid.
    rewrite (surjective_pairing b). 
    simpl.
    unfold real_div.
    rewrite real_mult_comm.
    rewrite (real_mult_comm d).
    apply real_le_mult_pos_le.
    apply real_pos_inv_pos.
    apply real_2_pos.
    auto.
  Qed.

  Lemma point_point_mid_in_ball_mid v b pt : 
    ball_to_subset 2 b pt <-> 
    ball_to_subset 2 (point_ball_mid v b) (point_point_mid v pt).
  Proof.
    destruct b as [bc br].
    unfold ball_to_subset.
    unfold point_ball_mid, point_point_mid.
    destruct (split_euclidean2 v) as [vx [vy vxy]].
    destruct (split_euclidean2 pt) as [px [py pxy]].
    simpl.
    destruct (split_euclidean2 bc) as [bcx [bcy bcxy]].
    unfold euclidean_max_dist, euclidean_minus.
    unfold euclidean_opp. rewrite bcxy, pxy. simpl.

    assert ((vx + px) * one_half + - ((vx + bcx) * one_half) = (px + - bcx)*one_half) as Temp.
    ring. rewrite Temp; clear Temp.
    assert ((vy + py) * one_half + - ((vy + bcy) * one_half) = (py + - bcy)*one_half) as Temp.
    ring. rewrite Temp; clear Temp.

    assert (abs ((px + - bcx) * one_half) = abs(px + - bcx) * one_half) as Temp.
    rewrite <- (abs_pos_id one_half) at 2.
    apply abs_mult. left. apply one_half_pos.
    rewrite Temp; clear Temp.

    assert (abs ((py + - bcy) * one_half) = abs(py + - bcy) * one_half) as Temp.
    rewrite <- (abs_pos_id one_half) at 2.
    apply abs_mult. left. apply one_half_pos.
    rewrite Temp; clear Temp.

    split.

    (* process the assumption *)
    intro.
    pose proof H as H2.
    apply real_max_le_fst_le in H.
    apply real_max_le_snd_le in H2.
    pose proof H2 as H3.
    apply real_max_le_fst_le in H2.
    apply real_max_le_snd_le in H3.

    apply real_max_le_le_le.
    rewrite real_mult_comm.
    rewrite (real_mult_comm br).
    apply real_le_mult_pos_le.
    apply one_half_pos.
    auto.

    apply real_max_le_le_le.
    rewrite real_mult_comm.
    rewrite (real_mult_comm br).
    apply real_le_mult_pos_le.
    apply one_half_pos.
    auto.

    apply real_le_pos_mult_pos_pos.
    auto.
    left; apply one_half_pos.

    (* Now, the other way round. *)
    intro.
    pose proof H as H2.
    apply real_max_le_fst_le in H.
    apply real_max_le_snd_le in H2.
    pose proof H2 as H3.
    apply real_max_le_fst_le in H2.
    apply real_max_le_snd_le in H3.

    apply real_max_le_le_le.
    destruct H.
    left.
    apply (real_lt_mult_pos_cancel one_half).
    apply one_half_pos.
    auto.
    right.
    apply real_eq_mult_cancel in H. auto.
    apply one_half_neq0.
    
    apply real_max_le_le_le.
    destruct H2.
    left.
    apply (real_lt_mult_pos_cancel one_half).
    apply one_half_pos.
    auto.
    right.
    apply real_eq_mult_cancel in H0. auto.
    apply one_half_neq0.

    assert (real_0 * one_half = real_0) as Temp.
    ring. rewrite <- Temp in H3; clear Temp.
    destruct H3.
    left.
    apply (real_lt_mult_pos_cancel one_half) in H0; auto.
    apply one_half_pos.
    right.
    apply real_eq_mult_cancel in H0. auto.
    apply one_half_neq0.
  Qed.

  Definition ST_selfSimilar (s : euclidean_subset 2) : Prop :=
    forall pt : ^euclidean 2, 
    ST_inside_hull_no_middle_pt pt ->
    s pt = s (point_point_mid ST_v1 pt)
    /\ 
    s pt = s (point_point_mid ST_v2 pt)
    /\ 
    s pt = s (point_point_mid ST_v3 pt).  

  (* Characterisation of the Sierpinski triangle (except being closed) *)

  Definition ST (s : euclidean_subset 2) : Prop :=
    ST_has_v123 s /\ ST_inside_hull_no_middle s /\ ST_selfSimilar s.

  (* Constructive definition of the Sierpinski triangle using covers *)

  Definition ST_split_ball (b : ball 2) :=
    (point_ball_mid ST_v1 b) :: 
    (point_ball_mid ST_v2 b) :: 
    (point_ball_mid ST_v3 b) :: nil.

  Fixpoint STn n : list (ball 2) := 
    match n with
    | 0 => ST_initial_ball :: nil 
    | (S n') => List.concat (List.map ST_split_ball (STn n'))
    end.

  (* Tools for coverage derived from self-similarity *)

  Definition ST_initial_ball_split_1 := point_ball_mid ST_v1 ST_initial_ball.
  Definition ST_initial_ball_split_2 := point_ball_mid ST_v2 ST_initial_ball.
  Definition ST_initial_ball_split_3 := point_ball_mid ST_v3 ST_initial_ball.

  Lemma ST_inside_first_split pt :
    ST_inside_hull_no_middle_pt pt ->
    ball_to_subset 2 ST_initial_ball pt -> 
    ball_to_subset 2 ST_initial_ball_split_1 pt
    \/
    ball_to_subset 2 ST_initial_ball_split_2 pt
    \/
    ball_to_subset 2 ST_initial_ball_split_3 pt.
  Proof.
    (* Capture the following lemma to the context because it will not be available later directly, 
      as its variables will no longer be available after we transform the context. *)
    pose proof (ST_weighted_pt_in_init_ball) as weighted_pt_in_init_ball.
    unfold ST_weighted_pt in weighted_pt_in_init_ball.

    (* split pt *)
    destruct (split_euclidean2 pt) as [px [py pxy]].
    rewrite pxy; clear pxy pt.

    (* split ST_v1, ST_v2, ST_v3 *)
    unfold ST_initial_ball_split_1, ST_initial_ball_split_2, ST_initial_ball_split_3.
    unfold ST_inside_hull_no_middle_pt, ST_weighted_pt.

    destruct (split_euclidean2 ST_v1) as [v1x [v1y v1xy]].
    destruct (split_euclidean2 ST_v2) as [v2x [v2y v2xy]].
    destruct (split_euclidean2 ST_v3) as [v3x [v3y v3xy]].
    rewrite v1xy in ST_initial_ball_contains_v1.
    rewrite v2xy in ST_initial_ball_contains_v2.
    rewrite v3xy in ST_initial_ball_contains_v3.
    rewrite v1xy, v2xy, v3xy.
    clear v1xy v2xy v3xy ST_v1 ST_v2 ST_v3.

    (* split ST_initial_ball *)
    destruct (ST_initial_ball) as [c r].
    clear ST_initial_ball.

    rename ST_initial_ball_radius_bound into rLe1.
    simpl in rLe1.

    (* split c *)
    destruct (split_euclidean2 c) as [cx [cy cxy]].
    rewrite cxy in ST_initial_ball_contains_v1, ST_initial_ball_contains_v2, ST_initial_ball_contains_v3.
    rewrite cxy in weighted_pt_in_init_ball.
    rewrite cxy.
    clear cxy c.

    (* simplify: cx cy inside initial ball *)
    destruct (split_ball_to_subset2 _ _ _ _ _ ST_initial_ball_contains_v1) as [v1cx v1cy].
    destruct (split_ball_to_subset2 _ _ _ _ _ ST_initial_ball_contains_v2) as [v2cx v2cy].
    destruct (split_ball_to_subset2 _ _ _ _ _ ST_initial_ball_contains_v3) as [v3cx v3cy].
    clear ST_initial_ball_contains_v1 ST_initial_ball_contains_v2 
ST_initial_ball_contains_v3.

    (* process hypothesis: pt in hull *)
    intro ptInHull.
    destruct ptInHull as [c1 [c2 [c3 [ptWeighted [[c1Pos [c2Pos [c3Pos c123sum]]] c123noMiddle]]]]].
    injection ptWeighted.
    intros pyWeighted pxWeighted.
    clear ptWeighted.

    unfold ST_weights123_no_middle in c123noMiddle. 

    intros ptInInit.
    destruct (split_ball_to_subset2 _ _ _ _ _ ptInInit) as [ptInInitX ptInInitY].
    clear ptInInit.

    (* simplify goal *)
    unfold ball_to_subset, point_ball_mid, euclidean_max_dist.
    simpl.

    (* pose proof ptInInitX as ptInInitXle.
    apply real_abs_le_pos_le in ptInInitXle.
    pose proof ptInInitX as ptInInitXge.
    apply real_abs_le_neg_le in ptInInitXge.
    clear ptInInitX.
    pose proof ptInInitY as ptInInitYle.
    apply real_abs_le_pos_le in ptInInitYle.
    pose proof ptInInitY as ptInInitYge.
    apply real_abs_le_neg_le in ptInInitYge.
    clear ptInInitY. *)

    (* some mini helpers *)
    assert (real_0 <= r) as rPos.
    apply (real_le_le_le _ (abs (py + - cy))); auto.
    apply abs_pos.

    assert (forall t, t * one_half * real_2 = t) as th2.
    intro t. rewrite real_mult_assoc. rewrite one_half_times_2. ring.

    (* pick one among c1, c2, c3 which is over 1/2 *)
    destruct c123noMiddle as [c1big | [c2big | c3big]].
    (* 1/2 <= c1 *)
    - left.
      admit.
    (* 1/2 <= c2 *)
    - right; left.
      admit.
    (* 1/2 <= c3 *)
    - right; right.

      (* define pt2 and pt shifted away from ST_v3 by 2 *)
      assert (ST_weights123_valid (real_2 * c1) (real_2 * c2) (real_2*c3 - real_1)) as pt2Valid.
      split. apply real_le_pos_mult_pos_pos; auto.
      left; apply real_2_pos.
      split.
      apply real_le_pos_mult_pos_pos; auto.
      left; apply real_2_pos.
      split.
      unfold real_minus.
      rewrite real_plus_comm.
      assert (real_0 = - real_1 + real_1) as Temp.
      ring. rewrite Temp. clear Temp.
      apply real_le_plus_le.
      rewrite <- one_half_times_2.
      rewrite real_mult_comm.
      apply real_le_mult_pos_le.
      apply real_2_pos.
      auto.
      rewrite <- c123sum.
      unfold real_2.
      ring.

      pose proof (weighted_pt_in_init_ball _ _ _ pt2Valid) as pt2inInit.
      destruct (split_ball_to_subset2 _ _ _ _ _ pt2inInit) as [pt2InInitX pt2InInitY].
      clear pt2inInit weighted_pt_in_init_ball pt2Valid.

      (* branch into real_max cases *)
      apply real_max_le_le_le.
      ring_simplify (px + - ((v3x + cx) * one_half)).
      rewrite pxWeighted.
      assert (c1 * v1x + c2 * v2x + c3 * v3x - v3x * one_half - cx * one_half 
           =  ((real_2 * c1) * v1x + (real_2 * c2) * v2x + (real_2 * c3 - real_1) * v3x + - cx) * one_half) as Temp.
      + ring_simplify.
        repeat rewrite th2. auto.
      + rewrite Temp; clear Temp. 
        rewrite abs_mult.
        rewrite (abs_pos_id one_half).
        rewrite (real_mult_comm _ one_half).
        rewrite (real_mult_comm _ one_half).
        apply real_le_mult_pos_le.
        apply one_half_pos.

        auto.
        left. apply one_half_pos.
      + apply real_max_le_le_le.
        ring_simplify (py + - ((v3y + cy) * one_half)).
        rewrite pyWeighted.
        assert (c1 * v1y + c2 * v2y + c3 * v3y - v3y * one_half - cy * one_half 
            =  ((real_2 * c1) * v1y + (real_2 * c2) * v2y + (real_2 * c3 - real_1) * v3y + - cy) * one_half) as Temp.
        * ring_simplify.
          repeat rewrite th2. auto.
        * rewrite Temp; clear Temp. 
          rewrite abs_mult.
          rewrite (abs_pos_id one_half).
          rewrite (real_mult_comm _ one_half).
          rewrite (real_mult_comm _ one_half).
          apply real_le_mult_pos_le.
          apply one_half_pos.

          auto.
          left. apply one_half_pos.
        * apply real_le_pos_mult_pos_pos; auto.
          left; apply one_half_pos.
  Admitted.

  Lemma ST_selfSimilar_inverse s pt :
    ST_selfSimilar s -> ST_inside_hull_no_middle s -> s pt -> 
    (s (point_point_away ST_v1 pt))
    \/
    (s (point_point_away ST_v2 pt))
    \/
    (s (point_point_away ST_v3 pt)).
  Proof.
    intros selfSimilar insideHull spt.

  Admitted.

  (* The diameter shrinks exponentially with n *)

  Lemma STn_diam n : diam 2 (STn n) <= prec n.
  Proof.
    induction n.
    - simpl.
      apply real_max_le_le_le.
      apply ST_initial_ball_radius_bound.
      left; apply real_1_gt_0.
    - simpl.
      induction (STn n).
      + simpl.
        assert (real_0 < / real_2_neq_0).
        apply real_pos_inv_pos.
        apply real_2_pos.
        apply real_le_pos_mult_pos_pos.
        auto. left. auto.
      + simpl.
        simpl in IHn.
        assert (snd a <= prec n) as IHa.
        apply (real_max_le_fst_le _ (diam 2 l)); auto.
        apply real_max_le_snd_le in IHn.
        pose proof (IHl IHn) as IH.

        apply real_max_le_le_le.
        apply point_ball_mid_halves; auto.
        apply real_max_le_le_le.
        apply point_ball_mid_halves; auto.
        apply real_max_le_le_le.
        apply point_ball_mid_halves; auto.

        auto.
  Qed.

  (* Intersection of cover and ST *)

  Lemma STn_intersects n s: (ST s) -> Forall (fun b : ^ball 2 => intersects 2 (ball_to_subset 2 b) s) (STn n).
  Proof.
    intro STs.
    destruct STs as [[hasV1 _] [insideHull selfSimilar]].
    induction n.
    - simpl.
      apply Forall_cons.
      + exists ST_v1.
        unfold intersection.
        split.
        * apply ST_initial_ball_contains_v1.
          (* unfold ST_v1, ball_to_subset, euclidean_max_dist.
          simpl.
          apply real_max_le_le_le.
          assert (- real_1 + (- real_0) = -real_1). ring.
          rewrite H. clear H.
          right.
          rewrite abs_neg_id_neg. ring.
          rewrite <- real_0_neg_eq.
          apply real_lt_anti.
          apply (real_1_gt_0).
          apply real_max_le_le_le.
          assert (real_1 + (- real_0) = real_1). ring.
          rewrite H. clear H.
          right.
          rewrite abs_pos_id. auto.
          left; apply (real_1_gt_0).
          left; apply (real_1_gt_0). *)
        * auto.
      + apply Forall_nil.
    - simpl.
      induction (STn n).
      auto.
      pose proof IHn as IHn2.
      apply (Forall_inv) in IHn.
      apply (Forall_inv_tail) in IHn2.
      pose proof (IHl IHn2) as IHl2.

      apply Forall_concat.
      apply Forall_map.
      apply Forall_cons.

      + unfold ST_split_ball.
        destruct IHn as [pt [pt_in_a spt]].
        apply Forall_cons.
        * exists (point_point_mid ST_v1 pt).
          unfold intersection; split.
          apply point_point_mid_in_ball_mid.
          auto.

          destruct (selfSimilar pt) as [spt1 _].
          apply insideHull; auto.
          rewrite <-spt1; auto.

        * apply Forall_cons.
          exists (point_point_mid ST_v2 pt).
          unfold intersection; split.
          apply point_point_mid_in_ball_mid.
          auto.

          destruct (selfSimilar pt) as [_ [spt2 _]].
          apply insideHull; auto.
          rewrite <-spt2; auto.
        
          apply Forall_cons.
          exists (point_point_mid ST_v3 pt).
          unfold intersection; split.
          apply point_point_mid_in_ball_mid.
          auto.

          destruct (selfSimilar pt) as [_ [_ spt3]].
          apply insideHull; auto.
          rewrite <-spt3; auto.

          apply Forall_nil.
      + apply Forall_map. apply Forall_concat. auto.
  Qed.  

  Lemma ST_compact : forall s, (ST s) -> is_compact 2 s.
  Proof.
    intros s STs n.
    exists (STn n).
    split.
    exact (STn_diam n).
    split.
    apply (STn_intersects n).
    auto.

    (* coverage: *)

    destruct STs as [[hasV1 [hasV2 hasV3]] [insideHull selfSimilar]].

    induction n.
    - simpl. 
      intros pt spt.

      (* break down the assumptions *)
      apply Exists_cons_hd.      
      destruct (insideHull pt) as [c1 [c2 [c3 [ptc123 [valid123 noMiddle123]]]]]. auto.
      rewrite ptc123.
      apply (ST_weighted_pt_in_init_ball c1 c2 c3). auto.

    - intros pt spt.

    (* work out the nearest vertex to pt *)

    (* move pt away from the nearest vertex *)

    (*  *)
      
  Admitted.
  
End SierpinskiTriangle.

Section ST_RightAngled.

Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).
#[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).
#[local] Notation "^euclidean" := (@euclidean types) (at level 0).
#[local] Notation "^ball" := (@ball types) (at level 0).

(* ring structure on Real *)
Ltac IZReal_tac t :=
  match t with
  | real_0 => constr:(0%Z)
  | real_1 => constr:(1%Z)
  | real_2 => constr:(2%Z)
  | IZreal ?u =>
    match isZcst u with
    | true => u
    | _ => constr:(InitialRing.NotConstant)
    end
  | _ => constr:(InitialRing.NotConstant)
  end.

Add Ring realRing : (realTheory ) (constants [IZReal_tac]).

  Definition STR_initial_ball := make_ball real_0 real_0 real_1.

  Definition STR_v1 := make_euclidean2 (- real_1) real_1.
  Definition STR_v2 := make_euclidean2 (- real_1) (- real_1).
  Definition STR_v3 := make_euclidean2 real_1 (- real_1).

  Lemma STR_initial_ball_radius_bound : snd STR_initial_ball <= real_1.
  Proof.
    unfold STR_initial_ball. 
    simpl. 
    apply real_le_triv.
  Qed.

  Definition STRn := STn STR_v1 STR_v2 STR_v3 STR_initial_ball.

  (* bits needed for verification *)

  Lemma STR_initial_ball_contains_v1 : ball_to_subset 2 STR_initial_ball STR_v1.
  Proof.
    unfold STR_initial_ball, ball_to_subset, euclidean_max_dist, make_ball, euclidean_max_norm, euclidean_minus, euclidean_opp, euclidean_plus. 
    simpl.
    ring_simplify (- real_1 + - real_0).
    ring_simplify (real_1 + - real_0).
    rewrite (abs_pos_id real_1).
    rewrite (abs_neg_id_neg).
    ring_simplify (- - real_1).

    apply real_max_le_le_le. 
    apply real_le_triv.
    apply real_max_le_le_le. 
    apply real_le_triv.
    left. apply real_1_gt_0.
    rewrite <- (real_0_neg_eq).
    apply real_lt_anti.
    apply real_1_gt_0.
    left. apply real_1_gt_0.
  Qed.
  
  Lemma STR_initial_ball_contains_v2 : ball_to_subset 2 STR_initial_ball STR_v2.
  Proof.
    unfold STR_initial_ball, ball_to_subset, euclidean_max_dist, make_ball, euclidean_max_norm, euclidean_minus, euclidean_opp, euclidean_plus. 
    simpl.
    ring_simplify (- real_1 + - real_0).
    rewrite (abs_neg_id_neg).
    ring_simplify (- - real_1).

    apply real_max_le_le_le. 
    apply real_le_triv.
    apply real_max_le_le_le. 
    apply real_le_triv.
    left. apply real_1_gt_0.
    rewrite <- (real_0_neg_eq).
    apply real_lt_anti.
    apply real_1_gt_0.
  Qed.
  
  Lemma STR_initial_ball_contains_v3 : ball_to_subset 2 STR_initial_ball STR_v3.
  Proof.
    unfold STR_initial_ball, ball_to_subset, euclidean_max_dist, make_ball, euclidean_max_norm, euclidean_minus, euclidean_opp, euclidean_plus. 
    simpl.
    ring_simplify (- real_1 + - real_0).
    ring_simplify (real_1 + - real_0).
    rewrite (abs_pos_id real_1).
    rewrite (abs_neg_id_neg).
    ring_simplify (- - real_1).

    apply real_max_le_le_le. 
    apply real_le_triv.
    apply real_max_le_le_le. 
    apply real_le_triv.
    left. apply real_1_gt_0.
    rewrite <- (real_0_neg_eq).
    apply real_lt_anti.
    apply real_1_gt_0.
    left. apply real_1_gt_0.
  Qed.

  Definition STR_compact := 
    ST_compact 
      STR_v1 STR_v2 STR_v3 STR_initial_ball
      STR_initial_ball_radius_bound
      STR_initial_ball_contains_v1
      STR_initial_ball_contains_v2
      STR_initial_ball_contains_v3
      .

End ST_RightAngled.

