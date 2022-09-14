(* this file proves various properties of subsets of real numbers *)
Require Import Lia.
Require Import Real Euclidean List Vector Minmax Subsets.

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
  Variable ST_vs_size_pred : nat.
  (* Notation ST_vs_size := (S ST_vs_size_pred). *)
  
  Variable ST_vs : t (^euclidean 2) (S ST_vs_size_pred).
  Definition ST_v1 := hd ST_vs.

  Lemma ST_v1_in_vs : In ST_v1 ST_vs.
  Proof.
    rewrite (eta ST_vs).
    apply In_cons_hd.
  Qed.

  Variable ST_initial_ball : ^ball 2.
  Variable ST_initial_ball_radius_bound : snd ST_initial_ball <= real_1.
  Variable ST_initial_ball_contains_vs : 
    Forall (ball_to_subset 2 ST_initial_ball) ST_vs.


  Definition ST_has_vs (A : euclidean_subset 2) : Prop := Forall A ST_vs.

  (* The convex hull of a vector of points defined using weights *)

  Definition sum {sz} (cs : t _ sz) := fold_right real_plus cs real_0.

  Lemma sum_0 (cs : t _ 0) : sum cs = real_0.
  Proof.
    assert (T : sum (nil ^Real) = real_0).
    auto.
    apply (case0 (fun v => sum v = real_0) T cs).
  Qed.

  Lemma sum_S n (cs : t _ (S n)) : sum cs = hd cs + sum (tl cs).
  Proof.
    rewrite (eta cs) at 1.
    auto.
  Qed.

  Definition weighted_pt {sz} (cs : t ^Real sz) (pts : t (^euclidean 2) sz) : ^euclidean 2 
    := fold_right euclidean_plus
        (map2 euclidean_scalar_mult cs pts) (euclidean_zero 2).

  Lemma weighted_pt_0 (cs : t _ 0) pts : weighted_pt cs pts = euclidean_zero 2.
  Proof.
    assert (T1 : weighted_pt (nil ^Real) (nil (^euclidean 2)) = euclidean_zero 2).
    auto.
    assert (T2 : weighted_pt (nil ^Real) pts = euclidean_zero 2).
    apply (case0 (fun v => weighted_pt (nil ^Real) v = euclidean_zero 2) T1 pts).
    apply (case0 (fun v => weighted_pt v pts = euclidean_zero 2) T2 cs).
  Qed.

  Lemma weighted_pt_S n (cs : t _ (S n)) (pts : t _ (S n)) : 
    weighted_pt cs pts = 
      euclidean_plus 
        (euclidean_scalar_mult (hd cs) (hd pts))
        (weighted_pt (tl cs) (tl pts)).
  Proof.
    rewrite (eta cs) at 1.
    rewrite (eta pts) at 1.
    auto.
  Qed.

  Lemma weighted_pt_in_ball {sz} c r cs pts : 
    Forall (ball_to_subset 2 (c,r)) pts ->
    Forall (fun ci => ci >= real_0) cs ->
    ball_to_subset 2 (euclidean_scalar_mult (sum cs) c, r * (sum cs)) (@weighted_pt sz cs pts).
  Proof.
    intros pts_in cs_pos.
    rewrite (Forall_forall) in pts_in, cs_pos.

    induction sz.
    -
      rewrite sum_0.
      rewrite weighted_pt_0.
      rewrite euclidean_scalar_mult_zero.
      unfold ball_to_subset. simpl.
      unfold euclidean_max_dist, euclidean_max_norm. simpl.
      assert (T : r * real_0 = real_0). ring.
      rewrite T; clear T.
      assert (T:abs(real_0 + - real_0) = real_0). apply abs_zero. ring.
      rewrite T; clear T.
      repeat apply real_max_le_le_le; apply real_le_triv.
    - 
      rewrite sum_S.
      rewrite weighted_pt_S.
      rewrite (eta pts) in pts_in.
      rewrite (eta cs) in cs_pos.
      specialize (IHsz (tl cs) (tl pts)).
      set (p1 := hd pts) in *|-*.
      set (tps := tl pts) in *|-*.
      set (c1 := hd cs) in *|-*.
      move c1 after pts.
      set (tcs := tl cs) in *|-*.
      move tcs after pts.

      rewrite <- euclidean_scalar_mult_plus.
      ring_simplify (r * (c1 + sum tcs)).

      apply ball_to_subset_plus.
      + specialize (pts_in p1); specialize (cs_pos c1).
        rewrite real_mult_comm.
        apply ball_to_subset_scalar_mult; auto.
        apply cs_pos. 
        apply In_cons_hd.
        apply pts_in.
        apply In_cons_hd.
      + apply IHsz; clear IHsz.
        intros; apply pts_in.
        apply In_cons_tl; auto.
        intros; apply cs_pos.
        apply In_cons_tl; auto.
  Qed.

  (* The convex hull of the vertices defined using weights *)

  Definition ST_weighted_pt (cs : t ^Real (S ST_vs_size_pred)) : ^euclidean 2
    := weighted_pt cs ST_vs.

  Definition ST_weights_valid (cs : t ^Real (S ST_vs_size_pred)) : Prop :=
    (Forall (fun c => c >= real_0) cs) 
    /\ sum cs = real_1.

  Definition ST_inside_hull_pt (pt : ^euclidean 2) : Prop :=
    exists cs : t ^Real (S ST_vs_size_pred), 
    pt = (ST_weighted_pt cs) /\ ST_weights_valid cs.
  
  Definition ST_inside_hull (A : euclidean_subset 2) : Prop :=
    forall pt : ^euclidean 2, A pt -> ST_inside_hull_pt pt.

  Lemma ST_weighted_pt_in_init_ball (cs : t ^Real (S ST_vs_size_pred)) : 
    ST_weights_valid cs ->
    ball_to_subset 2 ST_initial_ball (ST_weighted_pt cs).
  Proof.
      intros [pos sum1].
      destruct ST_initial_ball as [c r].
      pose proof (weighted_pt_in_ball c r cs ST_vs).
      rewrite sum1, real_mult_comm, real_mult_unit in H.
      rewrite euclidean_scalar_mult_unit in H.
      apply H; auto.
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

  Lemma point_point_mid_away_id  (p1 : ^euclidean 2) (p2 : ^euclidean 2) : p2 = point_point_away p1 (point_point_mid p1 p2).
  Proof.
    destruct (split_euclidean2 p1) as [x1 [y1 pxy1]].
    destruct (split_euclidean2 p2) as [x2 [y2 pxy2]].
    rewrite pxy1, pxy2.
    unfold point_point_mid, point_point_away, make_euclidean2. simpl.
    clear pxy1 pxy2 p1 p2.

    f_equal.
    assert (((x1 + x2) * one_half + (x1 + x2) * one_half) = (x1 + x2) * (one_half + one_half)) as T. ring. rewrite T; clear T.
    rewrite one_half_plus_one_half.
    ring.

    f_equal.
    assert (((y1 + y2) * one_half + (y1 + y2) * one_half) = (y1 + y2) * (one_half + one_half)) as T. ring. rewrite T; clear T.
    rewrite one_half_plus_one_half.
    ring.
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
    left; apply real_pos_inv_pos.
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
    left; apply one_half_pos.
    auto.

    apply real_max_le_le_le.
    rewrite real_mult_comm.
    rewrite (real_mult_comm br).
    apply real_le_mult_pos_le.
    left; apply one_half_pos.
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

  Definition ST_equal_union (A : euclidean_subset 2) : Prop :=
    forall pt : ^euclidean 2, 
    A pt = 
      Exists (fun v => A (point_point_away v pt)) ST_vs.

  (* Characterisation of the Sierpinski triangle (except being closed) *)

  Definition ST (A : euclidean_subset 2) : Prop :=
    ST_has_vs A /\ ST_inside_hull A /\ ST_equal_union A.

  (* Constructive definition of the Sierpinski triangle using covers *)

  Definition ST_split_ball (b : ^ball 2)
   := to_list (map (fun v => (point_ball_mid v b)) ST_vs).

  Fixpoint STn n : list (ball 2) := 
    match n with
    | 0 => ST_initial_ball :: List.nil 
    | (S n') => List.concat (List.map ST_split_ball (STn n'))
    end.

  Lemma ST_split_ball_in v a : 
    List.In v (VectorDef.to_list ST_vs) -> 
    List.In (point_ball_mid v a) (ST_split_ball a).
  Proof.
    intro.
    unfold ST_split_ball.
    rewrite to_list_map.
    apply (in_map (fun v0 : ^euclidean 2 => point_ball_mid v0 a)).
    auto.
  Qed.

  (* The diameter shrinks exponentially with n *)

  Lemma STn_rad n : rad 2 (STn n) <= prec n.
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
        apply (real_max_le_fst_le _ (rad 2 l)); auto.
        apply real_max_le_snd_le in IHn.
        specialize (IHl IHn).
        apply rad_le.
        * unfold real_div.
          apply real_le_pos_mult_pos_pos.
          left. apply prec_pos.
          left. apply one_half_pos.
        * intros.
          destruct (in_app_or _ _ _ H) as [Ha|Hl].
          {
            clear H.
            unfold ST_split_ball in Ha.
            rewrite to_list_map in Ha.
            apply in_map_iff in Ha.
            destruct Ha as [x [ab _]].
            rewrite <- ab.
            unfold real_div.
            apply point_ball_mid_halves; auto.
          }
          clear H.
          rewrite <- rad_le in IHl.
          specialize (IHl b).
          auto.
          unfold real_div.
          apply real_le_pos_mult_pos_pos.
          left. apply prec_pos.
          left. apply one_half_pos.
  Qed.

  (* Intersection of cover and ST *)

  Lemma STn_intersects n A: (ST A) -> List.Forall (fun b : ^ball 2 => intersects 2 (ball_to_subset 2 b) A) (STn n).
  Proof.
    intro STs.
    destruct STs as [hasVs [insideHull equalsUnion]].
    unfold ST_has_vs in hasVs.
    rewrite Forall_forall in hasVs.
    pose proof (hasV1 := hasVs ST_v1 ST_v1_in_vs).
    induction n.
    - simpl.
      apply List.Forall_cons.
      + exists ST_v1.
        unfold intersection.
        split.
        * rewrite Forall_forall in ST_initial_ball_contains_vs.
          apply (ST_initial_ball_contains_vs ST_v1 ST_v1_in_vs).
        * auto.
      + apply List.Forall_nil.
    - simpl.
      induction (STn n).
      auto.
      pose proof IHn as IHn2.
      apply (Forall_inv) in IHn.
      apply (Forall_inv_tail) in IHn2.
      pose proof (IHl IHn2) as IHl2.

      apply Forall_concat.
      apply Forall_map.
      apply List.Forall_cons.

      + 
        destruct IHn as [pt [pt_in_a spt]].
        unfold ST_split_ball.
        rewrite to_list_map.
        rewrite Forall_map.
        rewrite List.Forall_forall.
        intros v H.
        exists (point_point_mid v pt).
        unfold intersection; split.
        apply point_point_mid_in_ball_mid; auto.
        rewrite (equalsUnion (point_point_mid v pt)).
        rewrite to_list_Exists.
        rewrite List.Exists_exists.
        exists v.
        split; auto.
        rewrite <- point_point_mid_away_id. auto.
      + rewrite Forall_concat in IHl2.  
        rewrite Forall_map in IHl2.
        auto.
  Qed.

  Lemma Exists_concat_map A B l (P : B -> Prop) (fl : A -> list B) (f : A -> B):
    (forall a, List.In (f a) (fl a)) ->
    List.Exists P (List.map f l) -> 
    List.Exists P (List.concat (List.map fl l)).
  Proof.
    intros fInfl existsfl.
    apply Exists_concat.
    apply Exists_map.
    apply Exists_exists in existsfl. 
    destruct existsfl as [b [bInfl Pb]].
    apply in_map_iff in bInfl.
    destruct bInfl as [a [fab ainl]].
    apply Exists_exists.
    exists a.
    split; auto.
    apply Exists_exists.
    exists b.
    split; auto.
    rewrite <- fab.
    auto.
  Qed.

  Lemma ST_is_covert : forall A, (ST A) -> is_covert 2 A.
  Proof.
    intros A STs n.
    exists (STn n).
    split.
    exact (STn_rad n).
    split.
    apply (STn_intersects n).
    auto.

    (* coverage: *)

    destruct STs as [hasVs [insideHull equalsUnion]].

    induction n.
    - simpl. 
      intros pt spt.

      (* break down the assumptions *)
      apply List.Exists_cons_hd.      
      destruct (insideHull pt spt) as [cs [pt_cs valid_cs]].
      rewrite pt_cs.
      apply (ST_weighted_pt_in_init_ball cs). auto.

    - intros pt spt.

      rewrite (equalsUnion pt) in spt.
      rewrite to_list_Exists in spt.
      rewrite Exists_exists in spt.
      destruct spt as [v [v_vs pt'In]].

      pose (point_point_away v pt) as pt'.
      pose proof (IHn pt' pt'In) as IHn'.
      unfold STn.
      apply (Exists_concat_map _ _ _ _ _ (point_ball_mid v)).
      intro.
      apply ST_split_ball_in; auto.
      
      fold STn.
      apply Exists_exists in IHn'.
      destruct IHn' as [b [bInSTn p1Inb]].
      apply Exists_exists.
      exists (point_ball_mid v b).
      split.
      apply in_map_iff.
      exists b; auto.
      assert (pt = point_point_mid v pt') as pt'pt.
      apply point_point_away_mid_id.
      rewrite pt'pt.
      apply point_point_mid_in_ball_mid.
      auto.
  Qed.

End SierpinskiTriangle.

Section Known_Sized_Vectors.

  Definition t3_new {A} (a b c : A) : t A n3 := 
    cons _ a _ (cons _ b _ (cons _ c _ (nil _))).
    
  Definition t3_get {A} (t3 : t A n3) : (A * A * A) :=
    ((hd t3, hd (tl t3)), hd (tl (tl t3))).
    
  (* Lemma t3_new_get {A} a b c : @t3_get A (@t3_new A a b c) = ((a, b), c).
  Proof.
    Admitted. *)

  Lemma t3_in {A} e a b c: In e (@t3_new A a b c) -> e = a \/ e = b \/ e = c.
  Proof.
    rewrite to_list_In.
    simpl.
    intro.
    repeat (destruct H; auto).
  Qed.
  
  Definition t4_new {A} (a b c d : A) : t A n4 := 
    cons _ a _ (cons _ b _ (cons _ c _ (cons _ d _ (nil _)))).
    
  (* Definition t4_get {A} (t3 : t A 3) : (A * A * A) :=
    ((hd t3, hd (tl t3)), hd (tl (tl t3))). *)
    
  (* Lemma t3_new_get {A} a b c : @t3_get A (@t3_new A a b c) = ((a, b), c).
  Proof.
    Admitted. *)

  Lemma t4_in {A} e a b c d: In e (@t4_new A a b c d) -> e = a \/ e = b \/ e = c \/ e = d.
  Proof.
    rewrite to_list_In.
    simpl.
    intro.
    repeat (destruct H; auto).
  Qed.
  
End Known_Sized_Vectors.

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
  | IZreal 2%Z => constr:(2%Z)
  | IZreal ?u =>
    match isZcst u with
    | true => u
    | _ => constr:(InitialRing.NotConstant)
    end
  | _ => constr:(InitialRing.NotConstant)
  end.

Add Ring realRing : (realTheory ) (constants [IZReal_tac]).

  Definition STR_initial_ball := make_ball2 one_half one_half one_half.

  Definition STR_v1 := make_euclidean2 real_0 real_1.
  Definition STR_v2 := make_euclidean2 real_0 real_0.
  Definition STR_v3 := make_euclidean2 real_1 real_0.

  Definition STR_vs := t3_new STR_v1 STR_v2 STR_v3.

  Lemma STR_initial_ball_radius_bound : snd STR_initial_ball <= real_1.
  Proof.
    unfold STR_initial_ball. 
    simpl.
    rewrite <- one_half_plus_one_half.
    rewrite <- (real_plus_unit one_half) at 1.
    apply real_le_le_plus_le.
    left. apply one_half_pos. 
    apply real_le_triv.
  Qed.

  Definition STR := ST _ STR_vs.

  Definition STRn := STn _ STR_vs STR_initial_ball.

  (* bits needed for verification *)

  Lemma STR_initial_ball_contains_v1 : ball_to_subset n2 STR_initial_ball STR_v1.
  Proof.
    unfold STR_initial_ball, ball_to_subset, euclidean_max_dist, make_ball2, euclidean_max_norm, euclidean_minus, euclidean_opp, euclidean_plus. 
    simpl.
    ring_simplify (real_0 + - one_half).
    rewrite <- one_half_plus_one_half.
    ring_simplify (one_half + one_half + - one_half).
    rewrite (abs_pos_id one_half).
    rewrite (abs_neg_id_neg).
    ring_simplify (- - one_half).

    apply real_max_le_le_le. 
    apply real_le_triv.
    apply real_max_le_le_le. 
    apply real_le_triv.
    left. apply one_half_pos.
    rewrite <- (real_0_neg_eq).
    left; apply real_lt_anti.
    apply one_half_pos.
    left. apply one_half_pos.
  Qed.
  
  Lemma STR_initial_ball_contains_v2 : ball_to_subset n2 STR_initial_ball STR_v2.
  Proof.
    unfold STR_initial_ball, ball_to_subset, euclidean_max_dist, make_ball2, euclidean_max_norm, euclidean_minus, euclidean_opp, euclidean_plus. 
    simpl.
    ring_simplify (real_0 + - one_half).
    rewrite (abs_neg_id_neg).
    ring_simplify (- - one_half).

    apply real_max_le_le_le. 
    apply real_le_triv.
    apply real_max_le_le_le. 
    apply real_le_triv.
    left. apply one_half_pos.
    rewrite <- (real_0_neg_eq).
    left; apply real_lt_anti.
    apply one_half_pos.
  Qed.
  
  Lemma STR_initial_ball_contains_v3 : ball_to_subset n2 STR_initial_ball STR_v3.
  Proof.
    unfold STR_initial_ball, ball_to_subset, euclidean_max_dist, make_ball2, euclidean_max_norm, euclidean_minus, euclidean_opp, euclidean_plus. 
    simpl.
    rewrite <- one_half_plus_one_half.
    ring_simplify (one_half + one_half + - one_half).
    ring_simplify (real_0 + - one_half).
    rewrite (abs_pos_id one_half).
    rewrite (abs_neg_id_neg).
    ring_simplify (- - one_half).

    apply real_max_le_le_le. 
    apply real_le_triv.
    apply real_max_le_le_le. 
    apply real_le_triv.
    left. apply one_half_pos.
    rewrite <- (real_0_neg_eq).
    left; apply real_lt_anti.
    apply one_half_pos.
    left. apply one_half_pos.
  Qed.

  Lemma STR_initial_ball_contains_vs : 
    Forall (ball_to_subset n2 STR_initial_ball) STR_vs.
  Proof.
    unfold STR_vs.
    rewrite Forall_forall.
    intros.
    apply t3_in in H.
    destruct H.
    rewrite H.
    apply STR_initial_ball_contains_v1.
    destruct H.
    rewrite H.
    apply STR_initial_ball_contains_v2.
    rewrite H.
    apply STR_initial_ball_contains_v3.
  Qed.


  Definition STR_is_covert := 
    ST_is_covert n2
      STR_vs STR_initial_ball
      STR_initial_ball_radius_bound
      STR_initial_ball_contains_vs
      .

End ST_RightAngled.

Require Import sqrt.

Section ST_Equilateral.

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

  Definition STE_initial_ball := make_ball2 real_0 real_0 real_1.

  Lemma real_3_pos : (IZreal z3) > real_0.
  Proof.
    unfold z3.
    assert (IZreal 3 = IZreal 2 + real_1) as Temp. ring.
    rewrite Temp; clear Temp.
    rewrite <- (real_plus_unit real_0).
    apply real_lt_lt_plus_lt.
    apply real_2_pos.
    apply real_1_gt_0.
  Qed.

  Definition real_3_neq_0 : (IZreal z3) <> real_0.
    apply real_gt_neq.
    apply real_3_pos.
  Defined.

  Definition sqrt_3_exists : {y : ^Real | real_0 <= y /\ y * y = IZreal z3}.
    assert (IZreal 3 >= real_0) as ge0.
    left. apply real_3_pos.
    apply (sqrt (IZreal 3) ge0).
  Defined.

  Definition sqrt_3 : ^Real.
    pose proof sqrt_3_exists as Res.
    destruct Res as [R _].
    apply R.
  Defined.

  Lemma sqrt_3_pos : sqrt_3 > real_0.
  Proof.
    unfold sqrt_3.
    destruct sqrt_3_exists as [s3 [leq sqr]].
    destruct leq; auto.
    rewrite <- H in sqr.
    contradict sqr.
    ring_simplify (real_0 * real_0).
    apply real_lt_neq.
    apply real_3_pos.
  Qed.

  Lemma sqrt_3_div_3_pos : sqrt_3 / real_3_neq_0 > real_0.
  Proof.
    unfold sqrt_3.
    destruct sqrt_3_exists as [s3 [leq sqr]].
    destruct leq. 
    unfold real_div.
    apply (real_lt_mult_pos_cancel (IZreal 3)).
    apply real_3_pos.
    rewrite real_mult_assoc.
    rewrite real_mult_inv.
    ring_simplify; auto.

    rewrite <- H in sqr.
    contradict sqr.
    ring_simplify (real_0 * real_0).
    apply real_lt_neq.
    apply real_3_pos.
  Qed.

  Lemma sqrt_3_lt_2 : sqrt_3 < real_2.
  Proof.
    apply real_pos_square_gt_gt.
    apply real_2_pos.
    apply sqrt_3_pos.
    unfold sqrt_3.
    destruct sqrt_3_exists as [s3 [leq sqr]].
    rewrite sqr.
    unfold real_2.
    rewrite <- IZreal_mult_hom.
    apply IZreal_strict_monotone.
    unfold z3.
    lia.
  Qed.

  Lemma sqrt_3_div_3_lt_2 : sqrt_3 / real_3_neq_0 < real_2.
  Proof.
    apply real_pos_square_gt_gt.
    apply real_2_pos.
    apply sqrt_3_div_3_pos.
    unfold sqrt_3.
    destruct sqrt_3_exists as [s3 [leq sqr]].
    unfold real_div.
    rewrite (real_mult_comm s3) at 1.
    rewrite real_mult_assoc.
    rewrite <- (real_mult_assoc s3).
    rewrite sqr.
    rewrite (real_mult_comm (IZreal 3)) at 1.
    rewrite real_mult_inv.
    apply (real_lt_mult_pos_cancel (IZreal 3)).
    apply real_3_pos.
    rewrite real_mult_comm.
    rewrite <- real_mult_assoc.
    rewrite (real_mult_comm (IZreal 3)) at 1.
    rewrite real_mult_inv.
    assert (T : real_1 * real_1 = IZreal 1). ring.
    rewrite T; clear T.
    assert (T : real_2 * real_2 * IZreal 3 = IZreal 12). ring.
    rewrite T; clear T.
    apply IZreal_strict_monotone.
    lia.
  Qed.

  Lemma sqrt_3_gt_1 : real_1 < sqrt_3.
  Proof.
    apply real_pos_square_gt_gt.
    apply sqrt_3_pos.
    apply real_1_gt_0.
    unfold sqrt_3.
    destruct sqrt_3_exists as [s3 [leq sqr]].
    rewrite sqr.
    assert (real_1 * real_1 = IZreal 1) as T.
    ring. rewrite T; clear T.
    apply IZreal_strict_monotone.
    unfold z3.
    lia.
  Qed.

  Lemma sqrt_3_div_3_le_1 : real_1 >= sqrt_3 / real_3_neq_0.
  Proof.
    unfold real_div.
    rewrite <- (real_mult_inv _ real_3_neq_0).
    rewrite (real_mult_comm sqrt_3).
    apply real_le_mult_pos_le.
    apply (real_le_mult_pos_cancel (IZreal 3)).
    apply real_3_pos.
    rewrite real_mult_inv.
    ring_simplify.
    left; apply real_1_gt_0.

    left;
    apply real_pos_square_gt_gt.
    apply real_3_pos.
    apply sqrt_3_pos.
    unfold sqrt_3.
    destruct sqrt_3_exists as [s3 [leq sqr]].
    rewrite sqr.
    replace (IZreal 3 * IZreal 3) with (IZreal 9) by ring.
    apply IZreal_strict_monotone.
    unfold z3.
    lia.
  Qed.
  

  Definition STE_v1 := make_euclidean2 (- real_1) (- real_1).
  Definition STE_v2 := make_euclidean2 (real_1) (- real_1).
  Definition STE_v3 := make_euclidean2 real_0 (sqrt_3 - real_1).

  Definition STE_vs := t3_new STE_v1 STE_v2 STE_v3.

  Lemma STE_initial_ball_radius_bound : snd STE_initial_ball <= real_1.
  Proof.
    unfold STR_initial_ball. 
    simpl. 
    apply real_le_triv.
  Qed.

  Definition STEn := STn _ STE_vs STE_initial_ball.

  (* bits needed for verification *)

  Lemma STE_initial_ball_contains_v1 : ball_to_subset n2 STE_initial_ball STE_v1.
  Proof.
    unfold STE_initial_ball, ball_to_subset, euclidean_max_dist, make_ball2, euclidean_max_norm, euclidean_minus, euclidean_opp, euclidean_plus. 
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
    left; apply real_lt_anti.
    apply real_1_gt_0.
  Qed.
  
  Lemma STE_initial_ball_contains_v2 : ball_to_subset n2 STE_initial_ball STE_v2.
  Proof.
    unfold STE_initial_ball, ball_to_subset, euclidean_max_dist, make_ball2, euclidean_max_norm, euclidean_minus, euclidean_opp, euclidean_plus. 
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
    left; apply real_lt_anti.
    apply real_1_gt_0.
    left. apply real_1_gt_0.
  Qed.
  
  Lemma STE_initial_ball_contains_v3 : ball_to_subset n2 STE_initial_ball STE_v3.
  Proof.
    unfold STE_initial_ball, ball_to_subset, euclidean_max_dist, make_ball2, euclidean_max_norm, euclidean_minus, euclidean_opp, euclidean_plus. 
    simpl.
    apply real_max_le_le_le.
    rewrite abs_pos_id.
    left.
    ring_simplify (real_0 + - real_0).
    apply real_1_gt_0.
    right.
    ring.

    ring_simplify (sqrt_3 - real_1 + - real_0). 
    apply real_max_le_le_le.
    rewrite abs_pos_id.
    apply (real_le_add_r real_1).
    left.
    ring_simplify; apply sqrt_3_lt_2.

    apply (real_le_add_r real_1).
    ring_simplify.
    left. apply sqrt_3_gt_1.

    left. apply real_1_gt_0.
  Qed.
  
  Lemma STE_initial_ball_contains_vs : 
    Forall (ball_to_subset n2 STE_initial_ball) STE_vs.
  Proof.
    unfold STE_vs.
    rewrite Forall_forall.
    intros.
    apply t3_in in H.
    destruct H.
    rewrite H.
    apply STE_initial_ball_contains_v1.
    destruct H.
    rewrite H.
    apply STE_initial_ball_contains_v2.
    rewrite H.
    apply STE_initial_ball_contains_v3.
  Qed.

  Definition STE_is_covert := 
    ST_is_covert _
      STE_vs STE_initial_ball
      STE_initial_ball_radius_bound
      STE_initial_ball_contains_vs
      .

  Definition STE_v4 := make_euclidean2 real_0 ((sqrt_3)/real_3_neq_0 - real_1).

  Definition STE4_vs := t4_new STE_v1 STE_v2 STE_v3 STE_v4.

  Definition STE4n := STn _ STE4_vs STE_initial_ball.

  Lemma STE_initial_ball_contains_v4 : ball_to_subset n2 STE_initial_ball STE_v4.
  Proof.
    unfold STE_initial_ball, ball_to_subset, euclidean_max_dist, make_ball2, euclidean_max_norm, euclidean_minus, euclidean_opp, euclidean_plus. 
    simpl.
    apply real_max_le_le_le.
    rewrite abs_pos_id.
    left.
    ring_simplify (real_0 + - real_0).
    apply real_1_gt_0.
    right.
    ring.

    ring_simplify (sqrt_3 / real_3_neq_0 - real_1 + - real_0). 
    apply real_max_le_le_le.
    rewrite abs_neg_id_neg.
    apply (real_le_add_r (- real_1)).
    assert (T : real_1 + - real_1 = - real_0). ring.
    rewrite T; clear T.
    replace (- (((sqrt_3 / real_3_neq_0) - real_1) + - real_0) + - real_1) with (-(sqrt_3 / real_3_neq_0)) by ring.
    left; apply real_lt_anti.
    apply sqrt_3_div_3_pos.

    apply (real_le_add_r real_1).
    ring_simplify.
    apply sqrt_3_div_3_le_1.

    left. apply real_1_gt_0.
  Qed.

  Lemma STE4_initial_ball_contains_vs : 
    Forall (ball_to_subset n2 STE_initial_ball) STE4_vs.
  Proof.
    unfold STE_vs.
    rewrite Forall_forall.
    intros.
    apply t4_in in H.
    destruct H.
    rewrite H.
    apply STE_initial_ball_contains_v1.
    destruct H.
    rewrite H.
    apply STE_initial_ball_contains_v2.
    destruct H.
    rewrite H.
    apply STE_initial_ball_contains_v3.
    rewrite H.
    apply STE_initial_ball_contains_v4.
  Qed.

  Definition STE4_is_covert := 
    ST_is_covert _
      STE4_vs STE_initial_ball
      STE_initial_ball_radius_bound
      STE4_initial_ball_contains_vs.

End ST_Equilateral.
