(* this file proves various properties of subsets of real numbers *)
Require Import Lia.
Require Import Real Euclidean List Minmax Subsets.
Require Import simpletriangle.

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
    | real_2 => constr:(2%Z)
    | IZreal ?u =>
      match isZcst u with
      | true => u
      | _ => constr:(InitialRing.NotConstant)
      end
    | _ => constr:(InitialRing.NotConstant)
    end.

  Add Ring realRing : (realTheory ) (constants [IZReal_tac]).

  (* TODO: remove and replace with ring_simplify *)
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
    ring.
  Qed.

  Lemma one_minus_one_half : real_1 + (- one_half) = one_half.
  Proof.
    apply (real_eq_plus_cancel one_half).
    ring_simplify (real_1 + - one_half + one_half).
    rewrite one_half_plus_one_half. auto.
  Qed.


  (* The vertices of the triangle hull *)

  Definition ST_v1 := make_euclidean2 (- real_1) real_1.
  Definition ST_v2 := make_euclidean2 (- real_1) (- real_1).
  Definition ST_v3 := make_euclidean2 real_1 (- real_1).

  Definition has_ST_v123 (s : euclidean_subset 2) : Prop :=
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

  Definition weights123_valid (c1 c2 c3 : ^Real) : Prop :=
    c1 >= real_0 /\ c2 >= real_0 /\ c3 >= real_0 /\ c1 + c2 + c3 = real_1.

  Definition ST_inside_hull_pt (pt : ^euclidean 2) : Prop :=
    exists c1 c2 c3 : ^Real, pt = (ST_weighted_pt c1 c2 c3) /\ weights123_valid c1 c2 c3.
  
  Definition ST_inside_hull (s : euclidean_subset 2) : Prop :=
    forall pt : ^euclidean 2, s pt -> ST_inside_hull_pt pt.

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
    weights123_valid c1 c2 c3 -> 
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

    apply real_0_mult_le.
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
    ST_inside_hull_pt pt ->
    s pt = s (point_point_mid ST_v1 pt)
    /\ 
    s pt = s (point_point_mid ST_v2 pt)
    /\ 
    s pt = s (point_point_mid ST_v3 pt).  

  (* Characterisation of the Sierpinski triangle (except being closed) *)

  Definition ST (s : euclidean_subset 2) : Prop :=
    has_ST_v123 s /\ ST_inside_hull s /\ ST_selfSimilar s.

  (* Constructive definition of the Sierpinski triangle using covers *)

  Definition ST_split_ball (b : ball 2) :=
    (point_ball_mid ST_v1 b) :: 
    (point_ball_mid ST_v2 b) :: 
    (point_ball_mid ST_v3 b) :: nil.

  (* the square ([-1,1],[-1,1]) *) 
  Definition ST_initial_ball := make_ball real_0 real_0 real_1.

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
    ST_inside_hull_pt pt ->
    ball_to_subset 2 ST_initial_ball pt -> 
    ball_to_subset 2 ST_initial_ball_split_1 pt
    \/
    ball_to_subset 2 ST_initial_ball_split_2 pt
    \/
    ball_to_subset 2 ST_initial_ball_split_3 pt.
  Proof.
    intros ptInHull ptInInit.
    destruct ptInHull as [c1 [c2 [c3 [ptWeighted [c1Pos [c2Pos [c3Pos c123sum]]]]]]].
    destruct (split_euclidean2 pt) as [px [py pxy]].
    rewrite pxy.

    (* simplify ptWeighted to basic arithmetic *)
    rewrite pxy in ptWeighted.
    unfold ST_weighted_pt, make_euclidean2 in ptWeighted.
    simpl in ptWeighted.
    injection ptWeighted.
    intros pyWeighted pxWeighted.
    clear ptWeighted.
    ring_simplify in pxWeighted.
    ring_simplify in pyWeighted.

    (* simplify ptInInit to basic arithmetic *)
    rewrite pxy in ptInInit.
    unfold ball_to_subset, ST_initial_ball, make_ball, euclidean_max_dist, make_euclidean2, euclidean_minus, euclidean_plus, euclidean_max_norm in ptInInit.
    simpl in ptInInit.
    clear pxy pt.
    ring_simplify (px + - real_0) in ptInInit.
    ring_simplify (py + - real_0) in ptInInit.
    pose proof ptInInit as ptInInitX.
    apply real_max_le_fst_le in ptInInitX.
    pose proof ptInInit as ptInInitY.
    apply real_max_le_snd_le, real_max_le_fst_le in ptInInitY.
    clear ptInInit.
    pose proof ptInInitX as ptInInitXle.
    apply real_abs_le_pos_le in ptInInitXle.
    pose proof ptInInitX as ptInInitXge.
    apply real_abs_le_neg_le in ptInInitXge.
    clear ptInInitX.
    pose proof ptInInitY as ptInInitYle.
    apply real_abs_le_pos_le in ptInInitYle.
    pose proof ptInInitY as ptInInitYge.
    apply real_abs_le_neg_le in ptInInitYge.
    clear ptInInitY.

    (* pick a maximal among c1, c2, c3 *)
    destruct (real_total_order c1 c2) as [c1_le_c2|c2_le_c1].
    apply real_lt_le in c1_le_c2.
    (* c1 <= c2 *)
    destruct (real_total_order c2 c3) as [c2_le_c3|c3_le_c2].
    apply real_lt_le in c2_le_c3.
    (* c1 <= c2 <= c3, c3 is maximal *)
    - right. right.
      (* simplify to basic arithmetic *)
      unfold ST_initial_ball_split_3, ball_to_subset, ST_initial_ball, make_ball, euclidean_max_dist, make_euclidean2, euclidean_minus, euclidean_plus, euclidean_max_norm.
      simpl.
      ring_simplify (px + - ((real_1 + real_0) * one_half)).
      ring_simplify (py + - ((- real_1 + real_0) * one_half)).
      ring_simplify.
      
      (* branch into real_max and abs cases *)
      apply real_max_le_le_le.
      apply real_abs_le_le_le.

      unfold real_minus.
      apply (real_le_plus_le (- one_half)) in ptInInitXle.
      rewrite real_plus_comm in ptInInitXle.
      rewrite (real_plus_comm (- one_half)) in ptInInitXle.
      rewrite one_minus_one_half in ptInInitXle.
      auto.

      ring_simplify.

      Search (abs _ <= _).

      admit.
    (* c1 < c2 >= c3, c2 is maximal *)
    - right. left.
      admit.
    (* c2 <= c1 *)
    - destruct (real_total_order c1 c3) as [c1_le_c3|c3_le_c1].
      (* c2 <= c1 < c3, c3 is largest *)
      + right. right.
        admit.
      (* c2 <= c1 >= c3, c1 is maximal *)
      + left.
      admit. 
  Admitted.

  Lemma ST_selfSimilar_inverse s pt :
    ST_selfSimilar s -> ST_inside_hull s -> s pt -> 
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
      apply real_le_triv.
      left. apply real_1_gt_0.
    - simpl.
      induction (STn n).
      + simpl.
        assert (real_0 < / real_2_neq_0).
        apply real_pos_inv_pos.
        apply real_2_pos.
        apply real_0_mult_le.
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
        * unfold ST_v1, ball_to_subset, euclidean_max_dist.
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
          left; apply (real_1_gt_0).
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
      destruct (insideHull pt) as [c1 [c2 [c3 [ptc123 valid123]]]]. auto.
      pose proof (weights123_le_1 _ _ _ valid123) as [c1le1 [c2le1 c3le1]].
      destruct valid123 as [c1pos [c2pos [c3pos c123sum]]].

      assert (real_0 <= c1 + c2) as c12pos.
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
      split; auto; split; auto; right; auto.
  
      destruct (split_euclidean2 pt) as [px [py pxy]].
      (* destruct (split_euclidean2 ST_v1) as [x1 [y1 _]].
      destruct (split_euclidean2 ST_v2) as [x2 [y2 _]].
      destruct (split_euclidean2 ST_v3) as [x3 [y3 _]]. *)  
      rewrite pxy in ptc123.
      unfold ST_weighted_pt in ptc123.
      simpl in ptc123.
      unfold make_euclidean2 in ptc123.
      injection ptc123.
      intros py_sum px_sum.

      (* simplify the goal *)
      rewrite pxy.
      unfold make_ball, make_euclidean2.
      unfold ball_to_subset, euclidean_max_dist, euclidean_minus, euclidean_plus.
      simpl.
      rewrite px_sum, py_sum.
      clear px_sum py_sum pxy spt pt ptc123 px py.

      (* simplify ring subexpressions in the goal *)
      assert (c1 * - real_1 + c2 * - real_1 + c3 * real_1 + - real_0 = (- c1) + (- c2) + c3) as Temp.
      ring. rewrite Temp; clear Temp.
      assert (c1 * real_1 + c2 * - real_1 + c3 * - real_1 + - real_0 = c1 + (- c2) + (- c3)) as Temp.
      ring. rewrite Temp; clear Temp.

      apply real_max_le_le_le.
      destruct (real_total_order (- c1 + - c2 + c3) real_0).
      + rewrite abs_neg_id_neg.
        ring_simplify.
        unfold real_minus.
        rewrite <- real_plus_unit.
        rewrite (real_plus_comm real_0).
        apply real_le_le_plus_le.
        auto.
        destruct c3pos as [c3pos | c3eq0].
        left.
        rewrite <- real_0_neg_eq.
        apply real_lt_anti; auto.
        right.
        rewrite <- c3eq0.
        apply real_0_neg_eq. 
        auto.
      + destruct H.
        rewrite H.
        assert (abs real_0 = real_0) as Temp.
        apply abs_zero; auto.
        rewrite Temp; clear Temp.
        left.
        apply real_1_gt_0.
        rewrite abs_pos_id.
        ring_simplify.
        unfold real_minus.
        rewrite <- real_plus_unit.
        apply real_le_le_plus_le.
        assert (- c1 + - c2 = - (c1 + c2)) as Temp.
        ring. rewrite Temp; clear Temp.
        destruct c12pos as [c12pos | c12eq0].
        left.
        rewrite <- real_0_neg_eq.
        apply real_lt_anti; auto.
        right.
        rewrite <- c12eq0.
        apply real_0_neg_eq. 
        auto.
        left; auto.
      + apply real_max_le_le_le.
        destruct (real_total_order (c1 + - c2 + - c3) real_0).
        * rewrite abs_neg_id_neg.
          ring_simplify.
          rewrite real_plus_assoc.
          rewrite <- real_plus_unit.
          apply real_le_le_plus_le.
          destruct c1pos as [c1pos | c1eq0].
          left.
          rewrite <- real_0_neg_eq.
          apply real_lt_anti; auto.
          right.
          rewrite <- c1eq0.
          apply real_0_neg_eq.
          auto.
          auto.
        * destruct H.
          rewrite H.
          assert (abs real_0 = real_0) as Temp.
          apply abs_zero; auto.
          rewrite Temp; clear Temp.
          left.
          apply real_1_gt_0.

          rewrite abs_pos_id.
          ring_simplify.
          unfold real_minus.
          rewrite real_plus_assoc.
          rewrite <- real_plus_unit.
          rewrite (real_plus_comm real_0).
          apply real_le_le_plus_le.
          auto.
          assert (- c2 + - c3 = - (c2 + c3)) as Temp.
          ring. rewrite Temp; clear Temp.

          destruct c23pos as [c23pos | c23eq0].
          left.
          rewrite <- real_0_neg_eq.
          apply real_lt_anti; auto.
          right.
          rewrite <- c23eq0.
          apply real_0_neg_eq. 
          auto.
          left; auto.
        * left. apply real_1_gt_0.

    - intros pt spt.

    (* work out the nearest vertex to pt *)

    (* move pt away from the nearest vertex *)

    (*  *)
      
  Admitted.
  
End SierpinskiTriangle.
