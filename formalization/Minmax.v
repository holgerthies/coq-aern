Require Import Real.



Definition W_M (x y z : Real)
  := (x > y -> z = x) /\ (x = y -> z = x) /\ (x < y -> z = y).
Lemma W_M_or : forall x y z, W_M x y z -> (x = z) \/ (y = z).
Proof.
  intros x y z m.
  destruct m as [a [b c]].
  destruct (Realtotal_order x y) as [p1 | [p2 | p3]].
  right; rewrite (c p1); exact eq_refl.
  left; rewrite (b p2); exact eq_refl.
  left; rewrite (a p3); exact eq_refl.
Qed.
Lemma W_M_Or : forall x y z, W_M x y z -> (x=z /\ x>=y) \/ (y=z /\ y>=x).
Proof.
  intros x y z m.
  destruct m as [a [b c]].
  destruct (Realtotal_order x y) as [p1 | [p2 | p3]].
  right; rewrite (c p1); split; auto with Realiny.
  left; rewrite (b p2); split; auto with Realiny.
  left; rewrite (a p3); split; auto with Realiny.
Qed.

Lemma W_max : forall x y, (exists z, W_M x y z).
Proof.
  intros x y.
  destruct (Realtotal_order x y) as [c1 | [c2 | c3]]; unfold W_M.

  exists y.
  split; auto.
  intro H; contradict H; apply Reallt_nlt; auto.

  exists x.
  split; auto.

  exists x.
  split; auto.
  split; auto.
  intro H; contradict c3; apply Reallt_nlt; auto.
Qed.
Global Hint Resolve W_M_or W_M_Or W_max: Realiny.

(***************************************************************)
(** ** min                                                     *)
(***************************************************************)
Definition W_m (x y z : Real)
  := (x > y -> z = y) /\ (x = y -> z = x) /\ (x < y -> z = x).

Lemma W_m_or : forall x y z, W_m x y z -> (x = z) \/ (y = z).
Proof.
  intros x y z m.
  destruct m as [a [b c]].
  destruct (Realtotal_order x y) as [p1 | [p2 | p3]].
  left; rewrite (c p1); exact eq_refl.
  left; rewrite (b p2); exact eq_refl.
  right; rewrite (a p3); exact eq_refl.
Qed.

Lemma W_m_Or : forall x y z, W_m x y z -> (x=z /\ y>=x) \/ (y=z /\ x>=y).
Proof.
  intros x y z m.
  destruct m as [a [b c]].
  destruct (Realtotal_order x y) as [p1 | [p2 | p3]].
  left; rewrite (c p1); split; auto with Realiny.
  left; rewrite (b p2); split; auto with Realiny.
  right; rewrite (a p3); split; auto with Realiny.
Qed.

Lemma W_m_whatever_r : forall x y z, W_m x y z -> (z <= y).
Proof.
  intros.
  destruct (W_m_Or x y z H).
  destruct H0.
  rewrite H0 in H1; auto with Realiny.
  destruct H0; right; rewrite H0;  exact eq_refl.
Qed.

Lemma W_m_whatever_l : forall x y z, W_m x y z -> (z <= x).
Proof.
  intros.
  destruct (W_m_Or x y z H).
  destruct H0.
  destruct H0; right; exact eq_refl.
  destruct H0.
    
  rewrite H0 in H1; auto with Realiny.
Qed.

Lemma W_min : forall x y, (exists z, W_m x y z).
Proof.
  intros x y.
  destruct (Realtotal_order x y) as [c1 | [c2 | c3]]; unfold W_m.

  exists x.
  split; auto.
  intro Hl; contradict c1; apply Reallt_nlt; auto.

  exists x.
  split; auto.

  exists y.
  split; auto.
  split; auto.
  intro H; contradict c3; apply Reallt_nlt; auto.
Qed.
Global Hint Resolve W_m_or  W_min: Realiny.


Lemma Realmax : forall x y, {z | W_M x y z}.
Proof.
  intros.
  apply Real_mslimit_P_lt.
  + (* max is single valued predicate *)
    unfold unique.
    pose proof (W_max x y).
    destruct H as [m H].
    exists m.
    split; auto.
    intros m' H'.
    destruct (W_M_Or x y m H) as [[H11 H12]|[H11 H12]];
      destruct (W_M_Or x y m' H') as [[H11' H12']|[H11' H12']];
      try rewrite <- H11; try rewrite <- H11'; auto with Realiny.   
  + (* construct limit *)
    intros.
    apply (mjoin (x>y - prec n) (y > x - prec n)).
    ++ intros [c1|c2].
       +++ (* when x>y-2ⁿ *)
         exists x.
         destruct (W_max x y).
         exists x0.
         constructor; auto.
         destruct (W_M_Or x y x0 H) as [[H1 _]|[H1 H2]].
         ++++ rewrite H1.
              destruct (dist_zero x0 x0) as [o t]; rewrite (t eq_refl).
                apply prec_pos.
                
         ++++ rewrite <- H1.
              pose proof (prec_pos n) as P.
              apply (Reallt_plus_lt y Real0 (prec n)) in P; ring_simplify in P.
              apply (Realge_le) in H2.
              apply (Realle_lt_lt x y (y+prec n) H2) in P.
              assert (y-prec n < x < y+prec n) by auto.
              pose proof (prec_pos n) as Q.
              rewrite (dist_symm).
              apply (Realmetric_gtgt_sand y x (prec n) Q H0).
              
       +++ (* when x<y-2ⁿ *)
         exists y.
         destruct (W_max x y).
         exists x0.
         constructor; auto.
         destruct (W_M_Or x y x0 H) as [[H1 H2]|[H1 _]].
         ++++ rewrite <- H1.
              pose proof (prec_pos n) as P.
              apply (Reallt_plus_lt x Real0 (prec n)) in P; ring_simplify in P.
              apply (Realge_le) in H2.
              apply (Realle_lt_lt y x (x+prec n) H2) in P.
              assert (x-prec n < y < x+prec n) by auto.
              pose proof (prec_pos n) as Q.
              rewrite (dist_symm).
              apply (Realmetric_gtgt_sand x y (prec n) Q H0).
           ++++ rewrite H1.
                destruct (dist_zero x0 x0) as [o t]; rewrite (t eq_refl).
                apply prec_pos.
                
    ++ apply M_split.
       apply prec_pos.       
Defined.

Lemma Realmin : forall x y, {z | W_m x y z}.
Proof.
  intros x y.
  pose proof (Realmax (-x) (-y)) as [m rel].
  exists (-m).
  destruct rel as [a [b c]].
  split.
  intro.

  + apply (Reallt_plus_lt (-x-y)) in H.
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
      apply (Reallt_plus_lt (-x-y)) in H.
      ring_simplify in H.
      apply a in H.
      rewrite H; ring.
Defined.



(* properties of max function *)


Lemma Realmax_eq_fst_le : forall x y z, projP1 _ _ (Realmax x y) = z -> x <= z.
Proof.
  intros.
  destruct (Realmax x y).
  destruct w.
  destruct a.
  simpl in H.
  destruct (Realtotal_order x y).
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

Lemma Realmax_sym : forall x y, projP1 _ _ (Realmax x y) = projP1 _ _ (Realmax y x).
Proof.
  intros.
  destruct (Realmax x y).
  destruct (Realmax y x).
  simpl.
  destruct w.
  destruct H0.
  destruct w0.
  destruct H3.
  destruct (Realtotal_order x y).
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

Lemma Realmax_cand : forall x y, projP1 _ _ (Realmax x y) =  x \/ projP1 _ _ (Realmax x y) =  y.
Proof.
  intros.
  destruct (Realmax x y).
  simpl.
  destruct w as [p [q r]].
  destruct (Realtotal_order x y).
  right; apply r; exact H.
  destruct H.
  left; apply q; exact H.
  left; apply p; exact H.
Qed.


Lemma Realmax_eq_snd_le : forall x y z, projP1 _ _ (Realmax x y) = z -> y <= z.
Proof.
  intros.
  rewrite Realmax_sym in H.
  apply (Realmax_eq_fst_le y x).
  exact H.
Qed.


Lemma Realmax_fst_ge_ge : forall x y z, x >= z -> projP1 _ _ (Realmax x y) >= z.
Proof.
  intros.
  destruct (Realmax x y).
  destruct w.
  destruct a.
  simpl.
  destruct (Realtotal_order x y).
  pose proof (e1 H0).
  induction (eq_sym H1).
  destruct H.
  left; apply (Reallt_lt_lt _ _ _ H H0).
  left; rewrite <- H; exact H0.
  destruct H0.
  induction H0.
  rewrite (e0 eq_refl).
  exact H.
  rewrite (e H0).
  exact H.
Qed.

Lemma Realmax_snd_ge_ge : forall x y z, y >= z -> projP1 _ _ (Realmax x y) >= z.
Proof.
  intros.
  rewrite Realmax_sym.
  apply (Realmax_fst_ge_ge y x).
  exact H.
Qed.

  
Lemma Realmax_fst_ge : forall x y, projP1 _ _ (Realmax x y) >= x.
Proof.
  intros.
  apply (Realmax_fst_ge_ge _ _ x).
  right; auto.
Qed.

  
Lemma Realmax_snd_ge : forall x y, projP1 _ _ (Realmax x y) >= y.
Proof.
  intros.
  apply (Realmax_snd_ge_ge _ _ y).
  right; auto.
Qed.
  

Lemma Realmax_le_fst_le : forall x y z, projP1 _ _ (Realmax x y) <= z -> x <= z.
Proof.
  intros.
  destruct (Realmax x y).
  simpl in H.
  destruct w as [p [q r]].
  destruct (Realtotal_order x y).
  induction (eq_sym (r H0)).

  left; apply (Reallt_le_lt _ _ _ H0 H).
  destruct H0.
  induction H0.
  induction (eq_sym (q eq_refl)).
  exact H.
  induction (eq_sym (p H0)).
  exact H.
Qed.

Lemma Realmax_le_snd_le : forall x y z, projP1 _ _ (Realmax x y) <= z -> y <= z.
Proof.
  intros.
  rewrite Realmax_sym in H.
  apply (Realmax_le_fst_le y x).
  exact H.
Qed.

Lemma Realmax_le_le_le : forall x y z, x<= z -> y <= z -> projP1 _ _ (Realmax x y) <= z.
Proof.
  intros.
  destruct (Realmax_cand x y).
  rewrite H1; auto.
  rewrite H1; auto.
Qed.


Lemma Real_le_ge_eq : forall x y, x <= y -> x >= y -> x = y.
Proof.
  intros.
  destruct H, H0.
  induction (Reallt_nlt _ _ H H0).
  rewrite H0 in H; induction (Realnlt_triv _ H).
  rewrite H in H0 ; induction (Realnlt_triv _ H0).
  exact H.
Qed.

  

Lemma Realabs_le0_eq0 : forall x, abs x <= Real0 -> x = Real0.
Proof.
  intros.
  pose proof (abs_pos x).
  destruct H, H0.
  induction (Reallt_nlt _ _ H H0).
  rewrite H0 in H; induction (Realnlt_triv _ H).
  rewrite H in H0 ; induction (Realnlt_triv _ H0).
  exact (proj1 (abs_zero x) H ). 
Qed.  



Definition Realmaxf x y := projP1 _ _ (Realmax x y).
Lemma Realmax_plus_eq : forall a b c, c + Realmaxf a b = Realmaxf (a + c) (b + c).
Proof.
  intros.
  unfold Realmaxf.
  destruct (Realmax (a + c) (b + c)),  (Realmax a b).
  destruct w.
  destruct a0.
  destruct w0.
  destruct a0.
  simpl.
  destruct (Realtotal_order a b).
  rewrite (e4 H).
  rewrite Realplus_comm; apply eq_sym, e1.
  apply (Reallt_plus_r_lt c) in H; exact H.
  destruct H.
  induction H.
  rewrite (e3 eq_refl).
  rewrite (e0 eq_refl); ring.
  rewrite (e2 H).
  rewrite (Realplus_comm); apply eq_sym, e.
  apply (Reallt_plus_r_lt c) in H; exact H.
Qed.

Lemma Realmax_fst_le_le : forall a b c , a <= b -> a <= Realmaxf b c.
Proof.
  intros.
  unfold Realmaxf.
  destruct (Realmax b c).
  simpl.
  destruct w.
  destruct H1.
  destruct (Realtotal_order b c).
  rewrite (H2 H3).
  left; apply (Realle_lt_lt _ _ _ H H3).
  destruct H3.
  induction H3.
  rewrite (H1 eq_refl); auto.
  rewrite (H0 H3); auto.
Defined.

Lemma Realmax_snd_le_le : forall a b c , a <= b -> a <= Realmaxf c b.
Proof.
  intros.
  unfold Realmaxf.
  rewrite (Realmax_sym).
  apply Realmax_fst_le_le.
  exact H.
Qed.


Lemma Realmax_compwise_le : forall a b c d, a <= b -> c <= d -> projP1 _ _ (Realmax a c) <= projP1 _ _ (Realmax b d).
Proof.
  intros.
  pose proof (Realmax_fst_le_le _ _ d H).
  pose proof (Realmax_snd_le_le _ _ b H0).
  apply (Realmax_le_le_le _ _ _ H1 H2).
Qed.
