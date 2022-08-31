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
    | IZreal ?u =>
      match isZcst u with
      | true => u
      | _ => constr:(InitialRing.NotConstant)
      end
    | _ => constr:(InitialRing.NotConstant)
    end.

  Add Ring realRing : (realTheory ) (constants [IZReal_tac]).

  Definition one_half := / real_2_neq_0.

  Lemma one_half_pos : one_half > real_0.
  Proof.
    unfold one_half.
    apply real_pos_inv_pos.
    apply real_2_pos.
  Qed.

  Definition ST_v1 := make_euclidean2 (- real_1) real_1.
  Definition ST_v2 := make_euclidean2 (- real_1) (- real_1).
  Definition ST_v3 := make_euclidean2 real_1 (- real_1).

  Definition has_ST_v123 (s : euclidean_subset 2) : Prop :=
    (s ST_v1) /\ (s ST_v2) /\ (s ST_v3).

  Definition ST_weighted_pt (c1 c2 c3 : ^Real) : ^euclidean 2.
    destruct (split_euclidean2 ST_v1) as [x1 [y1 _]].
    destruct (split_euclidean2 ST_v2) as [x2 [y2 _]].
    destruct (split_euclidean2 ST_v3) as [x3 [y3 _]].
    pose (c1 * x1 + c2 * x2 + c3 * x3) as x.
    pose (c1 * y1 + c2 * y2 + c3 * y3) as y.
    apply (make_euclidean2 x y).
  Defined.

  Definition inside_ST_hull (s : euclidean_subset 2) : Prop :=
    forall pt : ^euclidean 2, s pt -> exists c1 c2 c3 : ^Real, pt = (ST_weighted_pt c1 c2 c3) /\ c1 >= real_0 /\ c1 >= real_0 /\ c3 >= real_0.

  Definition point_point_mid (p1 : ^euclidean 2) (p2 : ^euclidean 2) : ^euclidean 2.
    destruct (split_euclidean2 p1) as [x1 [y1 _]].
    destruct (split_euclidean2 p2) as [x2 [y2 _]].
    apply (make_euclidean2 ((x1 + x2) * one_half) ((y1 + y2) * one_half)).
  Defined.

  Definition point_ball_mid (p : ^euclidean 2) (b : ^ball 2) : ^ball 2.
    destruct b as [bc br].
    apply (pair (point_point_mid p bc) (br * one_half)).
  Defined.

  Definition ST_selfSimilar (s : euclidean_subset 2) : Prop :=
    forall pt : ^euclidean 2, 
    s pt = s (point_point_mid ST_v1 pt)
    /\ 
    s pt = s (point_point_mid ST_v2 pt)
    /\ 
    s pt = s (point_point_mid ST_v3 pt).  

  Definition ST (s : euclidean_subset 2) : Prop :=
    has_ST_v123 s /\ inside_ST_hull s /\ ST_selfSimilar s.

  Definition ST_split_ball (b : ball 2) :=
    (point_ball_mid ST_v1 b) :: 
    (point_ball_mid ST_v2 b) :: 
    (point_ball_mid ST_v3 b) :: nil.

  Fixpoint STn n : list (ball 2) := 
    match n with
    | 0 => (make_ball real_0 real_0 real_1) :: nil 
           (* the initial cover is the square ([-1,1],[-1,1]) *) 
    | (S n') => List.concat (List.map ST_split_ball (STn n'))
    end.

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

  Lemma real_0_neg_eq : - real_0 = real_0.
  Proof. ring. Qed.

  Lemma mid_pt_in_ball v b pt : ball_to_subset 2 b pt -> ball_to_subset 2 (point_ball_mid v b) (point_point_mid v pt).
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

    (* process the assumption *)
    intro.
    pose proof H as H2.
    apply real_max_le_fst_le in H.
    apply real_max_le_snd_le in H2.
    pose proof H2 as H3.
    apply real_max_le_fst_le in H2.
    apply real_max_le_snd_le in H3.

    assert ((vx + px) * one_half + - ((vx + bcx) * one_half) = (px + - bcx)*one_half) as Temp.
    ring. rewrite Temp; clear Temp.
    assert ((vy + py) * one_half + - ((vy + bcy) * one_half) = (py + - bcy)*one_half) as Temp.
    ring. rewrite Temp; clear Temp.

    apply real_max_le_le_le.
    assert (abs ((px + - bcx) * one_half) = abs(px + - bcx) * one_half) as Temp.
    rewrite <- (abs_pos_id one_half) at 2.
    apply abs_mult. left. apply one_half_pos.
    rewrite Temp; clear Temp.
    rewrite real_mult_comm.
    rewrite (real_mult_comm br).
    apply real_le_mult_pos_le.
    apply one_half_pos.
    auto.

    apply real_max_le_le_le.
    assert (abs ((py + - bcy) * one_half) = abs(py + - bcy) * one_half) as Temp.
    rewrite <- (abs_pos_id one_half) at 2.
    apply abs_mult. left. apply one_half_pos.
    rewrite Temp; clear Temp.
    rewrite real_mult_comm.
    rewrite (real_mult_comm br).
    apply real_le_mult_pos_le.
    apply one_half_pos.
    auto.

    apply real_0_mult_le.
    auto.
    left; apply one_half_pos.
  Qed.

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
          apply mid_pt_in_ball.
          auto.

          destruct (selfSimilar pt) as [spt1 _].
          rewrite <-spt1; auto.

        * apply Forall_cons.
          exists (point_point_mid ST_v2 pt).
          unfold intersection; split.
          apply mid_pt_in_ball.
          auto.

          destruct (selfSimilar pt) as [_ [spt2 _]].
          rewrite <-spt2; auto.
        
          apply Forall_cons.
          exists (point_point_mid ST_v3 pt).
          unfold intersection; split.
          apply mid_pt_in_ball.
          auto.

          destruct (selfSimilar pt) as [_ [_ spt3]].
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
      apply Exists_cons_hd.
      destruct (insideHull pt) as [c1 [c2 [c3 [ptc123 [c1pos [c2pos c3pos]]]]]]. auto.
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
      unfold ball_to_subset.
      
      
      inside_ST_hull
    
  Admitted.
  
End SierpinskiTriangle.
