Require Import Real.

Section Minmax.
Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).

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


  
  Definition real_is_max (x y z : Real)
    := (x > y -> z = x) /\ (x = y -> z = x) /\ (x < y -> z = y).

  Lemma real_is_max_or : forall x y z, real_is_max x y z -> (x = z) \/ (y = z).
  Proof.
    intros x y z m.
    destruct m as [a [b c]].
    destruct (real_total_order x y) as [p1 | [p2 | p3]].
    right; rewrite (c p1); exact eq_refl.
    left; rewrite (b p2); exact eq_refl.
    left; rewrite (a p3); exact eq_refl.
  Qed.
  
  Lemma real_is_max_Or : forall x y z, real_is_max x y z -> (x=z /\ x>=y) \/ (y=z /\ y>=x).
  Proof.
    intros x y z m.
    destruct m as [a [b c]].
    destruct (real_total_order x y) as [p1 | [p2 | p3]].
    right; rewrite (c p1); split; auto with real.
    left; rewrite (b p2); split; auto with real.
    left; rewrite (a p3); split; auto with real.
  Qed.

  Lemma real_W_max_prop : forall x y, (exists z, real_is_max x y z).
  Proof.
    intros x y.
    destruct (real_total_order x y) as [c1 | [c2 | c3]]; unfold real_is_max.

    exists y.
    split; auto.
    intro H; contradict H; apply real_lt_nlt; auto.

    exists x.
    split; auto.

    exists x.
    split; auto.
    split; auto.
    intro H; contradict c3; apply real_lt_nlt; auto.
  Qed.
  Local Hint Resolve real_is_max_or real_is_max_Or real_W_max_prop: real.

  (***************************************************************)
  (** ** min                                                     *)
  (***************************************************************)
  Definition real_is_min (x y z : Real)
    := (x > y -> z = y) /\ (x = y -> z = x) /\ (x < y -> z = x).

  Lemma real_is_min_or : forall x y z, real_is_min x y z -> (x = z) \/ (y = z).
  Proof.
    intros x y z m.
    destruct m as [a [b c]].
    destruct (real_total_order x y) as [p1 | [p2 | p3]].
    left; rewrite (c p1); exact eq_refl.
    left; rewrite (b p2); exact eq_refl.
    right; rewrite (a p3); exact eq_refl.
  Qed.

  Lemma real_is_min_Or : forall x y z, real_is_min x y z -> (x=z /\ y>=x) \/ (y=z /\ x>=y).
  Proof.
    intros x y z m.
    destruct m as [a [b c]].
    destruct (real_total_order x y) as [p1 | [p2 | p3]].
    left; rewrite (c p1); split; auto with real.
    left; rewrite (b p2); split; auto with real.
    right; rewrite (a p3); split; auto with real.
  Qed.

  Lemma real_is_min_whatever_r : forall x y z, real_is_min x y z -> (z <= y).
  Proof.
    intros.
    destruct (real_is_min_Or x y z H).
    destruct H0.
    rewrite H0 in H1; auto with real.
    destruct H0; right; rewrite H0;  exact eq_refl.
  Qed.

  Lemma real_is_min_whatever_l : forall x y z, real_is_min x y z -> (z <= x).
  Proof.
    intros.
    destruct (real_is_min_Or x y z H).
    destruct H0.
    destruct H0; right; exact eq_refl.
    destruct H0.
    
    rewrite H0 in H1; auto with real.
  Qed.

  Lemma real_W_min_prop : forall x y, (exists z, real_is_min x y z).
  Proof.
    intros x y.
    destruct (real_total_order x y) as [c1 | [c2 | c3]]; unfold real_is_min.

    exists x.
    split; auto.
    intro Hl; contradict c1; apply real_lt_nlt; auto.

    exists x.
    split; auto.

    exists y.
    split; auto.
    split; auto.
    intro H; contradict c3; apply real_lt_nlt; auto.
  Qed.
  Local Hint Resolve real_is_min_or  real_W_min_prop: real.


  Lemma real_max_prop : forall x y, {z | real_is_max x y z}.
  Proof.
    intros.
    apply real_mslimit_P_lt.
    + (* max is single valued predicate *)
      unfold unique.
      pose proof (real_W_max_prop x y).
      destruct H as [m H].
      exists m.
      split; auto.
      intros m' H'.
      destruct (real_is_max_Or x y m H) as [[H11 H12]|[H11 H12]];
        destruct (real_is_max_Or x y m' H') as [[H11' H12']|[H11' H12']];
        try rewrite <- H11; try rewrite <- H11'; auto with real.
      apply real_ge_ge_eq; auto.
      apply real_ge_ge_eq; auto.
    + (* construct limit *)
      intros.
      apply (mjoin (x>y - prec n) (y > x - prec n)).
      ++ intros [c1|c2].
         +++ (* when x>y-2ⁿ *)
           exists x.
           destruct (real_W_max_prop x y).
           exists x0.
           constructor; auto.
           destruct (real_is_max_Or x y x0 H) as [[H1 _]|[H1 H2]].
           ++++ rewrite H1.
                destruct (dist_zero x0 x0) as [o t]; rewrite (t eq_refl).
                apply prec_pos.
                
           ++++ rewrite <- H1.
                pose proof (prec_pos n) as P.
                apply (real_lt_plus_lt y real_0 (prec n)) in P; ring_simplify in P.
                apply (real_ge_le) in H2.
                apply (real_le_lt_lt x y (y+prec n) H2) in P.
                assert (y-prec n < x < y+prec n) by auto.
                pose proof (prec_pos n) as Q.
                rewrite (dist_symm).
                apply (real_metric_gtgt_sand y x (prec n) Q H0).
                
         +++ (* when x<y-2ⁿ *)
           exists y.
           destruct (real_W_max_prop x y).
           exists x0.
           constructor; auto.
           destruct (real_is_max_Or x y x0 H) as [[H1 H2]|[H1 _]].
           ++++ rewrite <- H1.
                pose proof (prec_pos n) as P.
                apply (real_lt_plus_lt x real_0 (prec n)) in P; ring_simplify in P.
                apply (real_ge_le) in H2.
                apply (real_le_lt_lt y x (x+prec n) H2) in P.
                assert (x-prec n < y < x+prec n) by auto.
                pose proof (prec_pos n) as Q.
                rewrite (dist_symm).
                apply (real_metric_gtgt_sand x y (prec n) Q H0).
           ++++ rewrite H1.
                destruct (dist_zero x0 x0) as [o t]; rewrite (t eq_refl).
                apply @prec_pos.
                
      ++ apply M_split.
         apply @prec_pos.       
  Defined.

  Lemma real_min_prop : forall x y, {z | real_is_min x y z}.
  Proof.
    intros x y.
    pose proof (real_max_prop (-x) (-y)) as [m rel].
    exists (-m).
    destruct rel as [a [b c]].
    split.
    intro
    + apply (real T_lt_plus_lt (-x-y)) in H.
    apply (real_lt_plus_lt (- x - y)) in H; 
    ring_simplify in H.
      apply c in H.
      rewrite H; ring.

    + split.
    ++
        intro.
        rewrite H in b at 1.
        rewrite (b eq_refl); ring.

      ++
        intro.
        apply (real_lt_plus_lt (-x-y)) in H.
        ring_simplify in H.
        apply a in H.
        rewrite H; ring.
  Defined.

  Definition real_max (x y : Real) := projP1 _ _ (real_max_prop x y).
  Definition real_min (x y : Real) := projP1 _ _ (real_min_prop x y).


  Lemma real_min_real_max x y : real_min x y = - real_max (-x) (-y).
  Proof.
    unfold real_min, real_max.
    destruct (real_max_prop (-x) (-y)).
    destruct (real_min_prop x y).
    simpl.
    destruct r as [r1 [r2 r3]].
    destruct r0 as [m1 [m2 m3]].
    destruct (real_total_order x y) as [H | [H | H]].

    rewrite m3;auto.
    rewrite r1; [ring|].
    apply real_lt_anti_anti.
    ring_simplify;auto.

    rewrite m2;auto.
    rewrite r2; [ring|].
    rewrite H;auto.

    rewrite m1;auto.
    rewrite r3;auto.
    ring_simplify;auto.
    apply real_lt_anti_anti.
    ring_simplify.
    auto.
 Qed.
  (* properties of max function *)


  Lemma real_max_eq_fst_le : forall x y z, (real_max x y) = z -> x <= z.
  Proof.
    intros.
    unfold real_max in H.
    destruct (real_max_prop x y).
    destruct r.
    destruct a.
    simpl in H.
    destruct (real_total_order x y).
    pose proof (e1 H0).
    induction (eq_sym H1).
    induction (eq_sym H).

    left; exact H0.
    destruct H0.
    induction H0.
    induction (e0 eq_refl).
    right; exact H.
    induction (e H0).
    induction (eq_sym H).
    right; exact (eq_refl).
  Qed.

  Lemma real_max_sym : forall x y, (real_max x y) = (real_max y x).
  Proof.
    intros.
    unfold real_max.
    destruct (real_max_prop x y).
    destruct (real_max_prop y x).
    simpl.
    destruct r.
    destruct H0.
    destruct r0.
    destruct H3.
    destruct (real_total_order x y).
    rewrite (H1 H5).
    rewrite (H2 H5).
    auto.
    destruct H5.
    rewrite (H0 H5).
    rewrite (H3 (eq_sym H5)).
    auto.
    rewrite (H H5).
    rewrite (H4 H5).
    auto.
  Qed.

  Lemma real_max_cand : forall x y, (real_max x y) =  x \/ (real_max x y) =  y.
  Proof.
    intros.
    unfold real_max.
    destruct (real_max_prop x y).
    simpl.
    destruct r as [p [q r]].
    destruct (real_total_order x y).
    right; apply r; exact H.
    destruct H.
    left; apply q; exact H.
    left; apply p; exact H.
  Qed.

  Lemma real_min_cand : forall x y, (real_min x y) =  x \/ (real_min x y) =  y.
  Proof.
    intros.
    unfold real_min.
    destruct (real_min_prop x y).
    simpl.
    destruct r as [p [q r]].
    destruct (real_total_order x y).
    left; apply r; exact H.
    destruct H.
    left; apply q; exact H.
    right; apply p; exact H.
  Qed.

  Lemma real_max_eq_snd_le : forall x y z, (real_max x y) = z -> y <= z.
  Proof.
    intros.
    rewrite real_max_sym in H.
    apply (real_max_eq_fst_le y x).
    exact H.
  Qed.


  Lemma real_max_fst_ge_ge : forall x y z, x >= z -> (real_max x y) >= z.
  Proof.
    intros.
    unfold real_max.
    destruct (real_max_prop x y).
    destruct r.
    destruct a.
    simpl.
    destruct (real_total_order x y).
    pose proof (e1 H0).
    induction (eq_sym H1).
    destruct H.
    left; apply (real_lt_lt_lt _ _ _ H H0).
    left; rewrite H; exact H0.
    destruct H0.
    induction H0.
    rewrite (e0 eq_refl).
    exact H.
    rewrite (e H0).
    exact H.
  Qed.

  Lemma real_max_snd_ge_ge : forall x y z, y >= z -> (real_max x y) >= z.
  Proof.
    intros.
    rewrite real_max_sym.
    apply (real_max_fst_ge_ge y x).
    exact H.
  Qed.

  
  Lemma real_max_fst_ge : forall x y, (real_max x y) >= x.
  Proof.
    intros.
    apply (real_max_fst_ge_ge _ _ x).
    right; auto.
  Qed.

  
  Lemma real_max_snd_ge : forall x y, (real_max x y) >= y.
  Proof.
    intros.
    apply (real_max_snd_ge_ge _ _ y).
    right; auto.
  Qed.
  
  Lemma real_min_fst_le : forall x y, (real_min x y) <= x.
  Proof.
    intros.
    rewrite real_min_real_max.
    add_both_side_by (real_max (-x) (- y) - x).
    apply real_max_fst_ge.
  Qed.

  
  Lemma real_min_snd_le : forall x y, (real_min x y) <= y.
  Proof.
    intros.
    rewrite real_min_real_max.
    add_both_side_by (real_max (-x) (- y) - y).
    apply real_max_snd_ge.
  Qed.

  Lemma real_max_le_fst_le : forall x y z, (real_max x y) <= z -> x <= z.
  Proof.
    unfold real_max.
    intros.
    destruct (real_max_prop x y).
    simpl in H.
    destruct r as [p [q r]].
    destruct (real_total_order x y).
    induction (eq_sym (r H0)).

    left; apply (real_lt_le_lt _ _ _ H0 H).
    destruct H0.
    induction H0.
    induction (eq_sym (q eq_refl)).
    exact H.
    induction (eq_sym (p H0)).
    exact H.
  Qed.

  Lemma real_max_le_snd_le : forall x y z, (real_max x y) <= z -> y <= z.
  Proof.
    intros.
    rewrite real_max_sym in H.
    apply (real_max_le_fst_le y x).
    exact H.
  Qed.

  Lemma real_max_le_le_le : forall x y z, x<= z -> y <= z -> (real_max x y) <= z.
  Proof.
    intros.
    destruct (real_max_cand x y).
    rewrite H1; auto.
    rewrite H1; auto.
  Qed.

  Lemma real_max_lt_lt_lt : forall x y z, x < z -> y < z -> (real_max x y) < z.
  Proof.
    intros.
    destruct (real_max_cand x y).
    rewrite H1; auto.
    rewrite H1; auto.
  Qed.

  Lemma real_le_ge_eq : forall x y  : Real, x <= y -> x >= y -> x = y.
  Proof.
    intros.
    destruct H, H0.
    induction (real_lt_nlt _ _ H H0).
    rewrite H0 in H; induction (real_nlt_triv _ H).
    rewrite H in H0 ; induction (real_nlt_triv _ H0).
    exact H.
  Qed.

  

  Lemma real_abs_le0_eq0 : forall x : Real, abs x <= real_0 -> x = real_0.
  Proof.
    intros.
    pose proof (abs_pos x).
    destruct H, H0.
    induction (real_lt_nlt _ _ H H0).
    rewrite H0 in H; induction (real_nlt_triv _ H).
    rewrite H in H0 ; induction (real_nlt_triv _ H0).
    exact (proj1 (abs_zero x) H ). 
  Qed.  

  Lemma real_abs_le_le_le : forall a b : Real, a <= b -> -a <= b -> abs a <= b.
  Proof.
    intros a b a_le_b nega_le_b.
    destruct (real_total_order a real_0).
    rewrite abs_neg_id_neg. auto. left; auto.
    rewrite abs_pos_id; auto.
    destruct H; auto.
    rewrite <- (eq_sym H). apply real_le_triv. 
    left. auto.
  Qed.
  
  Lemma real_abs_le_pos_le : forall a b : Real, abs a <= b -> a <= b.
  Proof.
    intros a b absa_le_b.
    destruct (real_total_order a real_0).
    - left.
      apply (real_lt_le_lt _ real_0); auto.
      apply (real_le_le_le _ (abs a)); auto.
      apply abs_pos.
    - destruct H. 
      rewrite H. 
      apply (real_le_le_le _ (abs a)); auto. apply abs_pos.
      rewrite abs_pos_id in absa_le_b; auto.
      left; auto.
  Qed.
  
  Lemma real_abs_le_neg_le : forall a b : Real, abs a <= b -> -a <= b.
  Proof.
    intros a b absa_le_b.
    destruct (real_total_order a real_0).
    - 
      apply (real_le_le_le _ (abs a)); auto.
      rewrite abs_neg_id_neg.
      apply real_le_triv. left; auto.
    - destruct H.
      rewrite H. 
      apply (real_le_le_le _ (abs a)); auto.
      ring_simplify; apply abs_pos.
      apply (real_le_le_le _ real_0); auto.
      left. apply real_lt_anti in H. ring_simplify in H; auto.
      apply (real_le_le_le _ (abs a)); auto. apply abs_pos.
  Qed.
  
  Lemma real_abs_cand : forall a b : Real, abs a <= b -> a <= b /\ -a <= b.
  Proof.
    intros a b H1.
    pose proof H1 as H2.
    apply real_abs_le_pos_le in H1.
    apply real_abs_le_neg_le in H2.
    split; auto.
  Qed.
  
  Lemma real_max_plus_eq : forall a b c : Real, c + real_max a b = real_max (a + c) (b + c).
  Proof.
    intros.
    unfold real_max.
    destruct (real_max_prop (a + c) (b + c)),  (real_max_prop a b).
    destruct r.
    destruct a0.
    destruct r0.
    destruct a0.
    simpl.
    destruct (real_total_order a b).
    rewrite (e4 H).
    rewrite real_plus_comm; apply eq_sym, e1.
    apply (real_lt_plus_r_lt c) in H; exact H.
    destruct H.
    induction H.
    rewrite (e3 eq_refl).
    rewrite (e0 eq_refl); ring.
    rewrite (e2 H).
    rewrite (real_plus_comm); apply eq_sym, e.
    apply (real_lt_plus_r_lt c) in H; exact H.
  Qed.

  Lemma real_max_fst_le_le : forall a b c , a <= b -> a <= real_max b c.
  Proof.
    intros.
    unfold real_max.
    destruct (real_max_prop b c).
    simpl.
    destruct r.
    destruct H1.
    destruct (real_total_order b c).
    rewrite (H2 H3).
    left; apply (real_le_lt_lt _ _ _ H H3).
    destruct H3.
    induction H3.
    rewrite (H1 eq_refl); auto.
    rewrite (H0 H3); auto.
  Defined.

  Lemma real_max_snd_le_le : forall a b c , a <= b -> a <= real_max c b.
  Proof.
    intros.
    rewrite (real_max_sym).
    apply real_max_fst_le_le.
    exact H.
  Qed.


  Lemma real_max_compwise_le : forall a b c d, a <= b -> c <= d -> (real_max a c) <= (real_max b d).
  Proof.
    intros.
    pose proof (real_max_fst_le_le _ _ d H).
    pose proof (real_max_snd_le_le _ _ b H0).
    apply (real_max_le_le_le _ _ _ H1 H2).
  Qed.

End Minmax.
(*  Hint Resolve real_is_max_or real_is_max_Or real_W_max_prop_prop: real. *)
(* Global Hint Resolve real_is_min_or  real_W_real_min_prop: real. *)
