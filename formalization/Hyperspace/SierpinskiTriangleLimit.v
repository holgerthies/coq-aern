Require Import Real Hyperspace.Subsets Euclidean List Lia Minmax Simpletriangle SierpinskiTriangle.
Require Import Vector.
Require Import EuclideanSubsets RealAssumption.

Section SierpinskiLimit.

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
 (* Check ST. *)
 Definition sierpinski_approx (n : nat) : (@euclidean_subset n2).
 Proof.
   induction n.
   apply T.
   pose proof (scaling (prec n1) IHn) as T.
   apply union.
   apply union.
   apply T.
   apply (translation T (make_euclidean2 ((prec n1)) real_0)).
   apply (translation T (make_euclidean2 real_0 (prec n1))).
 Defined.

 Lemma sierpinski_approx_tbounded n : totally_bounded (sierpinski_approx n).
 Proof.
   induction n.
   apply T_tbounded.

   apply tbounded_union;[apply tbounded_union |];(try apply tbounded_translation;apply tbounded_scale_down;apply IHn).
 Defined.

 Lemma sierpinski_approx_contains_origin : forall n, (sierpinski_approx n (euclidean_zero 2)).
 Proof.
   intros.
   induction n.
   - split;[|split].
     apply real_eq_ge;auto.
     apply real_eq_ge;auto.
     rewrite real_plus_unit.
     apply real_lt_le;apply real_1_gt_0.
  -  
     left ;left.
     exists (euclidean_zero 2).
     split.
     rewrite <-(euclidean_scalar_mult_zero (euclidean_zero 2)).
     rewrite euclidean_scalar_mult_mult.
     f_equal; ring.
     apply IHn.
 Defined.

 Lemma sierpinski_approx_contains_STR_vs : forall n, Forall (sierpinski_approx n) STR_vs.
 Proof.
   intros.
   apply Forall_cons; [|apply Forall_cons].
   - induction n.
     split; [apply real_eq_le | split;[apply real_lt_le;apply real_1_gt_0 |apply real_eq_le;ring ]];auto.
     right.
     unfold translation.
     exists STR_v1.
     split; auto.
     unfold STR_v1.
     unfold make_euclidean2,euclidean_minus, euclidean_plus, euclidean_scalar_mult;simpl.
     f_equal.
     ring.
     f_equal.
     replace real_2_neq_0 with d2 by auto.
     replace (real_1 + - (real_1 / d2)) with (real_1 - (real_1 / d2)) by ring.
     rewrite real_minus_half.
     ring.
  - apply sierpinski_approx_contains_origin.
  - apply Forall_cons;[|apply Forall_nil].
    induction n.
    split; [apply real_lt_le;apply real_1_gt_0 | split;[apply real_eq_le |apply real_eq_le;ring ]];auto.
    left; right.
    exists STR_v3.
    split;auto.
    unfold make_euclidean2,euclidean_minus, euclidean_plus, euclidean_scalar_mult;simpl.
    f_equal.
     replace real_2_neq_0 with d2 by auto.
     replace (real_1 + - (real_1 / d2)) with (real_1 - (real_1 / d2)) by auto.
     rewrite real_minus_half.
     ring.
     f_equal.
     ring.
 Defined.

 Lemma sierpinski_approx_ppm n x v : In v STR_vs -> sierpinski_approx n x -> sierpinski_approx (S n) (point_point_mid v x). 
 Proof.
   intros.
   unfold STR_vs in H.
   rewrite to_list_In in H.
   apply in_inv in H.
   destruct H; [| apply in_inv in H;destruct H; [| apply in_inv in H; destruct H; [|contradict H]]].
   - rewrite <-H.
     right.
     unfold translation, scaling.
     exists x.
     split;auto.
     destruct (dim_succ_destruct x); destruct s as [xr ->].
     destruct (dim_succ_destruct xr) as [x1 s]; destruct s as [xn ->].
     rewrite (dim_zero_destruct xn).
     unfold STR_v1.
     unfold point_point_mid,euclidean_minus,make_euclidean2.
     simpl.
     unfold one_half, real_div.
     f_equal;[ring | f_equal; ring].
  - rewrite <- H.
    left;left.
    unfold translation, scaling.
    exists x.
    split;auto.
    destruct (dim_succ_destruct x); destruct s as [xr ->].
    destruct (dim_succ_destruct xr) as [x1 s]; destruct s as [xn ->].
    rewrite (dim_zero_destruct xn).
    unfold STR_v1.
    unfold point_point_mid,euclidean_minus,make_euclidean2.
    simpl.
    unfold one_half, real_div.
    f_equal;[ring | f_equal; ring].
  - rewrite <- H.
    left;right.
    unfold translation, scaling.
    exists x.
    split;auto.
    destruct (dim_succ_destruct x); destruct s as [xr ->].
    destruct (dim_succ_destruct xr) as [x1 s]; destruct s as [xn ->].
    rewrite (dim_zero_destruct xn).
    unfold STR_v1.
    unfold point_point_mid,euclidean_minus,make_euclidean2.
    simpl.
    unfold one_half, real_div.
    f_equal;[ring | f_equal; ring].
 Qed.

 Lemma point_point_away_spec x v : point_point_away v x = euclidean_minus (euclidean_scalar_mult real_2 x) v.
   destruct (dim_succ_destruct x); destruct s as [xr ->].
   destruct (dim_succ_destruct xr) as [x1 s]; destruct s as [xn ->].
   rewrite (dim_zero_destruct xn).
   destruct (dim_succ_destruct v); destruct s as [vr ->].
   destruct (dim_succ_destruct vr) as [v1 s]; destruct s as [vn ->].
   rewrite (dim_zero_destruct vn).
   unfold point_point_away, make_euclidean2, euclidean_minus.
   simpl.
   unfold real_2.
   f_equal; [ | f_equal];ring.
 Qed.

 Lemma sierpinski_approx_ppa n x :  sierpinski_approx (S n) x -> exists v, In v STR_vs /\ sierpinski_approx n (point_point_away v x).
 Proof.
   assert (In STR_v1 STR_vs /\ In STR_v2 STR_vs /\ In STR_v3 STR_vs) as I.
   {
     split; [|split].
     apply In_cons_hd.
     apply In_cons_tl;apply In_cons_hd.
     apply In_cons_tl;apply In_cons_tl;apply In_cons_hd.
   }
   assert (forall (x : euclidean 2), euclidean_scalar_mult real_2 (euclidean_scalar_mult (prec 1) x) = x) as mult_simpl.
   {
     intros.
     rewrite euclidean_scalar_mult_mult.
     replace (real_2 * prec 1) with real_1.
     apply euclidean_scalar_mult_unit.
     simpl;unfold real_div.
     rewrite real_mult_comm, real_mult_assoc.
     rewrite real_mult_inv.
     ring.
   }
   intros H.
   destruct H as [H1 | H1] ; [destruct H1 as [[y [P1 P2]] | [y [P1 P2]]]  | destruct H1 as [y [P1 P2]]].
   - exists STR_v2.
     rewrite point_point_away_spec.
     split;[apply I|].
     unfold STR_v2.
     rewrite P1.
     rewrite mult_simpl.
    destruct (dim_succ_destruct y); destruct s as [yr ->].
    destruct (dim_succ_destruct yr) as [y1 s]; destruct s as [yn ->].
    rewrite (dim_zero_destruct yn) in *.
    unfold euclidean_minus; simpl.
    assert (forall x, x + (- real_0) = x) as L by (intros;ring).
    rewrite !L.
    apply P2.
   - exists STR_v3.
    split;[apply I|].
    rewrite point_point_away_spec.
    replace x with (euclidean_scalar_mult (prec 1) (euclidean_plus y STR_v3)).
    rewrite mult_simpl.
    rewrite euclidean_minus_plus.
    apply P2.
    destruct (dim_succ_destruct x); destruct s as [xr ->].
    destruct (dim_succ_destruct xr) as [x1 s]; destruct s as [xn ->].
    rewrite (dim_zero_destruct xn).
    destruct (dim_succ_destruct y); destruct s as [yr ->].
    destruct (dim_succ_destruct yr) as [y1 s]; destruct s as [yn ->].
    rewrite (dim_zero_destruct yn).
    simpl.
    injection P1.
    intros.
    f_equal.
    rewrite real_mult_plus_distr.
    apply (real_eq_plus_cancel (- (real_1 / real_2_neq_0))).
    ring_simplify in H1.
    ring_simplify.
    rewrite <-H1.
    ring.
    f_equal;auto.
    rewrite real_mult_plus_distr.
    ring_simplify.
    ring_simplify in H0.
    rewrite H0.
    ring.
  - exists STR_v1.
    split;[apply I|].
    rewrite point_point_away_spec.
    replace x with (euclidean_scalar_mult (prec 1) (euclidean_plus y STR_v1)).
    rewrite mult_simpl.
    rewrite euclidean_minus_plus.
    apply P2.
    destruct (dim_succ_destruct x); destruct s as [xr ->].
    destruct (dim_succ_destruct xr) as [x1 s]; destruct s as [xn ->].
    rewrite (dim_zero_destruct xn).
    destruct (dim_succ_destruct y); destruct s as [yr ->].
    destruct (dim_succ_destruct yr) as [y1 s]; destruct s as [yn ->].
    rewrite (dim_zero_destruct yn).
    simpl.
    injection P1.
    intros.
    f_equal.
    ring_simplify in H1.
    ring_simplify.
    rewrite H1;auto.
    f_equal;auto.
    ring_simplify in H0.
    rewrite real_mult_plus_distr.
    apply (real_eq_plus_cancel (- (real_1 / real_2_neq_0))).
    ring_simplify.
    rewrite <-H0.
    ring.
 Qed.
 Lemma sierpinski_approx_next n x : sierpinski_approx (S n) x <-> exists y, (sierpinski_approx n y) /\ Exists (fun v => y = point_point_away v x) STR_vs.
 Proof.
  split.
  intros.
  destruct (sierpinski_approx_ppa _ _ H) as [v [V1 V2]].
  exists (point_point_away v x).
  split;auto.
  apply to_list_Exists, List.Exists_exists.
  exists v.
  split;[apply to_list_In |];auto.

  intros.
  destruct H as [y [P1 P2]].
  rewrite to_list_Exists, List.Exists_exists in P2.
  destruct P2 as [v [V1 V2]].
  rewrite (point_point_away_mid_id v).
  apply sierpinski_approx_ppm; [apply to_list_In | ];auto.
  rewrite <- V2;auto.
  Defined.

 Lemma point_point_away_dist x y v : In v STR_vs -> (euclidean_max_dist (point_point_away v x) (point_point_away v y)) = real_2 * (euclidean_max_dist x y). 
 Proof.
   intros.
   rewrite to_list_In in H.
   destruct (dim_succ_destruct x); destruct s as [xr ->].
   destruct (dim_succ_destruct xr) as [x1 s]; destruct s as [xn ->].
   destruct (dim_succ_destruct y) as [y0 s]; destruct s as [yr ->].
   destruct (dim_succ_destruct yr) as [y1 s]; destruct s as [yn ->].
   rewrite (dim_zero_destruct xn), (dim_zero_destruct yn).
   unfold point_point_away, make_euclidean2.
   destruct H;[ | destruct H; [ |destruct H]];auto; try rewrite <-H.
   - unfold STR_v1.
     rewrite <-euclidean_max_dist_scalar_mult.
     simpl.
     rewrite !euclidean_max_dist_cons.
     f_equal; [f_equal;unfold real_2;ring | ].
     f_equal.
     unfold RealMetric.dist.
     f_equal.
     unfold real_2; ring.
     apply real_lt_le;apply real_lt_0_2.
   - unfold STR_v2.
     rewrite <-euclidean_max_dist_scalar_mult.
     simpl.
     rewrite !euclidean_max_dist_cons.
     f_equal; [f_equal;unfold real_2;ring | ].
     f_equal.
     unfold RealMetric.dist.
     f_equal.
     unfold real_2; ring.
     apply real_lt_le;apply real_lt_0_2.
   - unfold STR_v3.
     rewrite <-euclidean_max_dist_scalar_mult.
     simpl.
     rewrite !euclidean_max_dist_cons.
     f_equal.
     unfold RealMetric.dist.
     f_equal.
     unfold real_2; ring.
     f_equal; f_equal; unfold real_2; ring.
     apply real_lt_le;apply real_lt_0_2.
  - contradict H.
 Qed.
 
 Lemma inside_hull_unfold x : ST_inside_hull_pt _ STR_vs x <-> exists l1 l2 l3, x = euclidean_plus (euclidean_scalar_mult l1 STR_v1) (euclidean_plus (euclidean_scalar_mult l2 STR_v2) (euclidean_scalar_mult l3 STR_v3)) /\ l1 + l2 + l3 = real_1 /\ l1 >= real_0 /\ l2 >= real_0 /\ l3 >= real_0.
 Proof.
   split; intros.
   - destruct H as [z [P1 [P2 P3]]].
     unfold ST_weighted_pt,weighted_pt in P1.
     exists (hd z); exists (hd (tl z)); exists (hd (tl (tl z))).
     split.
     rewrite P1.
     unfold STR_vs.
     rewrite (eta z), (eta (tl z)), (eta (tl (tl z))).
     replace (tl (tl (tl z))) with (nil ^Real) by (apply case0;auto).
     simpl;f_equal; [ring | f_equal; ring].
     rewrite Forall_forall in P2.
     split.
     revert P3.
     rewrite (eta z), (eta (tl z)), (eta (tl (tl z))).
     replace (tl (tl (tl z))) with (nil ^Real) by (apply case0;auto).
     unfold sum.
     simpl; intros <-.
     ring.
     split;[|split];apply P2; rewrite (eta z); rewrite (eta (tl z));rewrite (eta (tl (tl z)));simpl.
     apply In_cons_hd.
     apply In_cons_tl;apply In_cons_hd.
     apply In_cons_tl;apply In_cons_tl;apply In_cons_hd.
  -  destruct H as [l1 [l2 [l3 [P1 [P2 P3]]]]].
     exists (cons _ l1 _ (cons _ l2 _ (cons _ l3 _ (nil ^Real)))).
     split.
     unfold ST_weighted_pt,weighted_pt.
     rewrite P1.
     simpl.
     f_equal;[ | f_equal];ring.
     split.
     apply Forall_cons;[ |apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]];apply P3.
     unfold sum;simpl.
     rewrite <-P2;ring.
 Defined.

 Lemma inside_hull_T x : ST_inside_hull_pt _ STR_vs x -> T x.
 Proof.
   rewrite inside_hull_unfold.
   intros.
   destruct H as [l1 [l2 [l3 [P1 P2]]]].
   rewrite P1.
   unfold T.
   simpl.
   replace (l1 * real_0 + (l2* real_0 + l3*real_1)) with l3 by ring.
   replace (l1 * real_1 + (l2* real_0 + l3*real_0)) with l1 by ring.
   split;[| split]; try apply P2.
   apply (real_le_le_le _ (l1 + l2 + l3)); [|apply real_eq_le;apply P2].
   replace (l3 + l1) with (l1 + l3 + real_0) by ring.
   replace (l1 + l2 + l3) with (l1 + l3 + l2) by ring.
   apply real_le_plus_le.
   apply P2.
 Qed.

 Lemma triangle_max_dist : forall x, T x -> (euclidean_max_dist x STR_v1 <= real_1).
 Proof.
   intros.   
   destruct (dim_succ_destruct x) as [x0 [tx ->]].
   destruct (dim_succ_destruct tx) as [y0 [tx' ->]].
   destruct H as [Hx0 [Hy0 Hxy0]].
   rewrite (dim_zero_destruct tx').
   unfold STR_v1, make_euclidean2;simpl.
   rewrite euclidean_max_dist_cons.
   apply real_max_le_le_le.
   unfold RealMetric.dist.
   replace (x0 - real_0) with x0 by ring.
   rewrite abs_pos_id;auto.
   apply (real_le_add_r y0).
   apply (real_le_le_le _ _ _ Hxy0).
   replace real_1 with (real_1 + real_0) at 1 by ring.
   apply real_le_plus_le;auto.
   rewrite euclidean_max_dist_cons.
   unfold euclidean_max_dist; simpl.
   apply real_max_le_le_le.
   rewrite dist_symm.
   unfold RealMetric.dist.
   rewrite abs_pos_id.
   apply (real_le_add_r y0).
   apply (real_le_add_r (- real_1)).
   ring_simplify;auto.
   apply (real_le_le_le _ _ _ Hx0).
   apply (real_le_add_r y0).
   ring_simplify;auto.
   apply real_lt_le;apply real_1_gt_0.
 Qed.

 Lemma triangle_max_dist_half : forall x, T x -> (euclidean_max_dist x STR_v1 <= one_half
 \/ euclidean_max_dist x STR_v2 <= one_half
 \/ euclidean_max_dist x STR_v3 <= one_half
 ).
 Proof.
   intros.   
   destruct (dim_succ_destruct x) as [x0 [tx ->]].
   destruct (dim_succ_destruct tx) as [y0 [tx' ->]].
   destruct H as [Hx0 [Hy0 Hxy0]].
   rewrite (dim_zero_destruct tx'); clear tx'.
   unfold STR_v1, STR_v2, STR_v3, make_euclidean2;simpl.
   rewrite euclidean_max_dist_cons.

   destruct (real_total_order one_half x0);
   destruct (real_total_order one_half y0).
   - contradict Hxy0.
     apply real_gt_nle.
     rewrite <- one_half_plus_one_half.
     apply real_lt_lt_plus_lt; auto.

   - right; right. 
     apply real_max_le_le_le; simpl.

     rewrite abs_neg_id_neg.
     rewrite <- one_half_plus_one_half.
     apply (real_le_add_r (x0 - one_half)).
     replace (- (x0 + - (one_half + one_half)) + (x0 - one_half)) with one_half by ring.
     replace (one_half + (x0 - one_half)) with x0 by ring.
     left; auto.
     apply (real_le_add_r (real_1)).
     pose proof (real_le_le_plus_le _ _ _ _ Hy0 (real_le_triv x0)).
     ring_simplify in H1.
     pose proof (real_le_le_le _ _ _ H1 Hxy0).
     ring_simplify; auto.

     replace (y0 + - real_0) with y0 by ring.
     rewrite abs_pos_id;auto.
     apply real_max_le_le_le.
     destruct H0; [right| left]; auto.
     left; apply one_half_pos.

   - left.  
     apply real_max_le_le_le; simpl.
     unfold RealMetric.dist.
     replace (x0 - real_0) with x0 by ring.
     rewrite abs_pos_id;auto.
     destruct H; [right| left]; auto.
     apply real_max_le_le_le; simpl.
     rewrite abs_neg_id_neg.
     rewrite <- one_half_plus_one_half.
     apply (real_le_add_r (y0 - one_half)).
     replace (- (y0 + - (one_half + one_half)) + (y0 - one_half)) with one_half by ring.
     replace (one_half + (y0 - one_half)) with y0 by ring.
     left; auto.
     apply (real_le_add_r (real_1)).
     pose proof (real_le_le_plus_le _ _ _ _ Hx0 (real_le_triv y0)).
     ring_simplify in H1.
     rewrite real_plus_comm in H1.
     pose proof (real_le_le_le _ _ _ H1 Hxy0).
     ring_simplify; auto.
     left; apply one_half_pos.

   - right; left. 
     apply real_max_le_le_le; simpl.
     replace (x0 + - real_0) with x0 by ring.
     rewrite abs_pos_id;auto.
     destruct H; [right| left]; auto.
     apply real_max_le_le_le; simpl.
     replace (y0 + - real_0) with y0 by ring.
     rewrite abs_pos_id;auto.
     destruct H0; [right| left]; auto.
     left; apply one_half_pos.
  Qed.

 Lemma point_point_mid_in X x  v : (STR X) -> X x -> In v STR_vs -> X (point_point_mid v x).
 Proof.
   intros S Xx vP.
   destruct S as [H1 [H2 H3]].
   unfold ST_equal_union in H3.
   rewrite (H3 (point_point_mid v x)).
   rewrite to_list_Exists.
   rewrite List.Exists_exists.
   exists v.
   split.
   apply to_list_In;auto.
   rewrite <-point_point_mid_away_id;auto.
 Defined.

 Lemma sierpinski_approx_dist n : forall X, (STR X) -> (Hausdorff_dist_bound (sierpinski_approx (pred n)) X (prec n)).
 Proof.
   intros X S.
   destruct S as [H1 [H2 H3]].
   destruct n.
   (* case n = 0 *)
   { pose proof (sierpinski_approx_contains_STR_vs 0).
     rewrite Forall_forall in H.
     split.
     + exists STR_v1.
       unfold ST_has_vs, STR_vs in H1.
       rewrite Forall_forall in H1.
       split; [apply H1;apply VectorDef.In_cons_hd |].
       apply triangle_max_dist;auto.
    + intros.
      exists STR_v1.
      split;[apply H; unfold STR_vs; apply VectorDef.In_cons_hd |].
      rewrite euclidean_max_dist_sym.
      apply triangle_max_dist.
      apply inside_hull_T.
      apply H2;auto.
   }
   simpl.
   induction n.
   (* case n = 1 *)
   - pose proof (sierpinski_approx_contains_STR_vs 0).
     rewrite Forall_forall in H.
     split; simpl.
     intros.
     destruct (triangle_max_dist_half x H0) as [N|[N|N]].
     + exists STR_v1.
       unfold ST_has_vs, STR_vs in H1.
       rewrite Forall_forall in H1.
       split; [apply H1;apply VectorDef.In_cons_hd |].
       unfold real_div.
       rewrite real_mult_unit.
       auto.
     + exists STR_v2.
       unfold ST_has_vs, STR_vs in H1.
       rewrite Forall_forall in H1.
       split; [apply H1;apply VectorDef.In_cons_tl;apply VectorDef.In_cons_hd |].
       unfold real_div.
       rewrite real_mult_unit.
       auto.
     + exists STR_v3.
       unfold ST_has_vs, STR_vs in H1.
       rewrite Forall_forall in H1.
       split; [apply H1;apply VectorDef.In_cons_tl;apply VectorDef.In_cons_tl;apply VectorDef.In_cons_hd |].
       unfold real_div.
       rewrite real_mult_unit.
       auto.
    + intros.

      exists y.
      split.
      apply inside_hull_T; auto.
      pose proof (euclidean_max_dist_id y y) as [_ ->]; auto.
      unfold real_div.
      rewrite real_mult_unit.
      left;apply one_half_pos.
   - split; unfold n2; intros.
     + pose proof (sierpinski_approx_next n x ) as [S _].
       destruct (S H) as [x' [P1 P2]].
       destruct IHn as [IH1 IH2].
       destruct (IH1 _ P1) as [x2 [Xx2 D]].
       rewrite to_list_Exists in P2.
       rewrite List.Exists_exists in P2.
       destruct P2 as [v [L1 L2]].
       assert (exists z, X z /\ x2 = point_point_away v z) as [z [zP1 zP2]].
       {
         exists (point_point_mid v x2).
         split.
         apply (point_point_mid_in X);auto.
         split;auto.
         apply to_list_In;auto.
         rewrite <-point_point_mid_away_id;auto.
       }
       exists z;split;auto.
       apply (real_le_mult_pos_cancel real_2).
       apply real_lt_0_2.
       rewrite !(real_mult_comm _ real_2).
       rewrite <- (point_point_away_dist x z v); [| apply to_list_In;auto].
       rewrite <-L2, <-zP2.
       simpl.
       unfold real_div.
       rewrite real_mult_comm, real_mult_assoc, real_mult_inv.
       ring_simplify;auto.
    + destruct IHn as [_ IH].
      rewrite H3 in H.
      rewrite to_list_Exists, List.Exists_exists in H.
      destruct H as [v [P1' P2']].
      destruct (IH _ P2') as [x1 [P1 P2]].
      exists (point_point_mid v x1).
      pose proof (sierpinski_approx_next n (point_point_mid v x1)) as [_ S].
      split.
      apply S.
      exists x1;split;auto.
     apply to_list_Exists; apply List.Exists_exists.
     exists v.
     split;auto.
     rewrite <-point_point_mid_away_id;auto.
     apply (real_le_mult_pos_cancel real_2).
     apply real_lt_0_2.
     rewrite !(real_mult_comm _ real_2).
     rewrite <- (point_point_away_dist _ _ v); [| apply to_list_In;auto].
     rewrite <-point_point_mid_away_id.
     simpl.
     unfold real_div.
     rewrite real_mult_comm, real_mult_assoc, real_mult_inv.
     ring_simplify;auto.
  Defined.


 Lemma tbounded_sierpinski : forall X, (STR X) -> totally_bounded X.
 Proof.
   intros.
   apply located_lim.
   intros.
   exists (sierpinski_approx (pred n)).
   split.
   apply sierpinski_approx_tbounded.
   apply sierpinski_approx_dist.
   exact H.
 Defined.
 End SierpinskiLimit.
