Require Import Real Subsets Euclidean List Lia Minmax simpletriangle SierpinskiTriangle.
Section SierpinskiLimit.

Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).
#[local] Definition sofReal := @sofReal types casofReal.
#[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).
#[local] Notation "^euclidean" := (@euclidean types) (at level 0).
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
 Check ST.
 Definition sierpinski_approx (n : nat) : (@euclidean_subset types 2).
 Proof.
   induction n.
   apply T.
   pose proof (scaling 2 (prec 1) IHn) as T.
   apply union.
   apply union.
   apply T.
   apply (translation 2 T (make_euclidean2 ((prec 1)) real_0)).
   apply (translation 2 T (make_euclidean2 real_0 (prec 1))).
 Defined.

 Lemma sierpinski_approx_is_covert n : is_covert 2 (sierpinski_approx n).
 Proof.
   induction n.
   apply T_is_covert.

   apply is_covert_union;[apply is_covert_union |];(try apply is_covert_translation;apply is_covert_scale_down;apply IHn).
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
 Require Import Vector.

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
 Lemma sierpinski_approx_next n x : sierpinski_approx (S n) x <-> exists y, (sierpinski_approx n y) /\ Exists (fun v => y = point_point_away v x) STR_vs.
 Proof.
   induction n.
   Admitted.
 Print point_point_away.

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
     unfold dist.
     f_equal.
     unfold real_2; ring.
     apply real_lt_le;apply real_lt_0_2.
   - unfold STR_v2.
     rewrite <-euclidean_max_dist_scalar_mult.
     simpl.
     rewrite !euclidean_max_dist_cons.
     f_equal; [f_equal;unfold real_2;ring | ].
     f_equal.
     unfold dist.
     f_equal.
     unfold real_2; ring.
     apply real_lt_le;apply real_lt_0_2.
   - unfold STR_v3.
     rewrite <-euclidean_max_dist_scalar_mult.
     simpl.
     rewrite !euclidean_max_dist_cons.
     f_equal.
     unfold dist.
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

 Lemma triangle_max_dist : forall x y, T x -> T y -> euclidean_max_dist x y <= real_1.
 Proof.
 Admitted.

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

 Lemma sierpinski_approx_dist n : forall X, (STR X) -> (Hausdorff_dist_bound 2 (sierpinski_approx n) X (prec n)).
 Proof.
   intros X S.
   destruct S as [H1 [H2 H3]].
   induction n.
   - pose proof (sierpinski_approx_contains_STR_vs 0).
     rewrite Forall_forall in H.
     split.
     + exists STR_v1.
       unfold ST_has_vs, STR_vs in H1.
       rewrite Forall_forall in H1.
       split; [apply H1;apply VectorDef.In_cons_hd |].
       apply triangle_max_dist;auto.
       apply H.
       unfold STR_vs.
       apply VectorDef.In_cons_hd.
    + intros.
      exists STR_v1.
      split;[apply H; unfold STR_vs; apply VectorDef.In_cons_hd |].
      apply triangle_max_dist.
      apply inside_hull_T.
      exists (cons _ (real_1) _ ((cons _ real_0) _ ((cons _ real_0 _ (nil ^Real))))).
      unfold ST_weighted_pt,weighted_pt.
      unfold STR_v1, make_euclidean2.
      simpl.
      split.
      f_equal;[ | f_equal];ring.
      split.
     apply Forall_cons;[ |apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; try (apply real_eq_le; reflexivity).
     apply real_lt_le.
     apply real_1_gt_0.
     unfold sum;simpl; ring.
     apply  inside_hull_T;auto.
   - split; intros.
     + pose proof (sierpinski_approx_next n x ) as [S S'].
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
 End SierpinskiLimit.
