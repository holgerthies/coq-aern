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
  apply mslimit.
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
