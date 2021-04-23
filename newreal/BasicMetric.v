Require Import BasicAxioms.
Require Import BasicRing.
Require Import BasicArith.
Open Scope T_scope.


Lemma Tmetric_sand : forall z1 z2 z3, z1-z3<=z2<=z1+z3 -> dist z1 z2 <= z3.
Proof.
  intros z1 z2 z3 p.
  destruct p as [p1 p2].
  destruct (dist_prop z1 z2) as [q1 [q2 q3]];
    destruct (Ttotal_order z1 z2) as [r1 | [r2 | r3]].
  rewrite (q3 r1).
  destruct p2.
  apply (Tlt_plus_lt (-z1) z2 (z1+z3)) in H.
  ring_simplify in H.
  replace (-z1+z2) with (z2-z1) in H by ring; left; exact H.
  rewrite H.
  ring_simplify; right; exact eq_refl.

  rewrite (q2 r2); rewrite r2 in p2.
  destruct p2.
  apply (Tlt_plus_lt (-z2) z2 (z2+z3)) in H.
  ring_simplify in H; left; exact H.
  apply (Teq_plus_eq z2 (z2+z3) (-z2)) in H.
  ring_simplify in H; right; exact H.

  rewrite (q1 r3).
  apply (Tle_plus_le (z1-z3) z2 (z3-z2)) in p1.
  ring_simplify in p1.
  exact p1.
Qed.
Hint Resolve Tmetric_sand: Tiny.


Lemma Tmetric_plus_inv : forall z1 z2 z3, dist z1 z2 = dist (z3 + z1) (z3 + z2).
Proof.
  intros z1 z2 z3;
    replace (z3+z1) with (z1+z3) by ring;
    replace (z3+z2) with (z2+z3) by ring; exact (Tmetric_inv z1 z2 z3).
Qed.
Hint Resolve Tmetric_plus_inv: Tiny.


Lemma Tmetric_or : forall z1 z2, dist z1 z2 = z1 - z2 \/ dist z1 z2 = z2 - z1.
Proof.
  intros z1 z2.
  destruct (Ttotal_order z1 z2) as [r1 | [r2 | r3]];
    destruct (dist_prop z1 z2) as [l1 [l2 l3]].
  right; rewrite (l3 r1); exact eq_refl.
  rewrite r2 at 2.
  left; ring_simplify.
  exact (l2 r2).
  left; rewrite (l1 r3); exact eq_refl.
Qed.
Hint Resolve Tmetric_or: Tiny.

Lemma Tmetric_Or : forall z1 z2, (dist z1 z2 = z1-z2 /\ z1 >= z2) \/
                                (dist z1 z2 = z2-z1 /\ z2 >= z1).
Proof.
  intros z1 z2.
  destruct (Ttotal_order z1 z2) as [r1 | [r2 | r3]];
    destruct (dist_prop z1 z2) as [l1 [l2 l3]].
  right; rewrite (l3 r1); exact (conj eq_refl (Tgt_ge  z2 z1 r1)).
  rewrite r2 at 2.
  left; split; ring_simplify.
  exact (l2 r2).
  right; exact r2.
  left; rewrite (l1 r3); exact (conj eq_refl (Tgt_ge z1 z2 r3)).
Qed.
Hint Resolve Tmetric_Or: Tiny.

Lemma Tmetric_gtgt_sand : forall z1 z2 z3, z3> T0 -> z1-z3<z2<z1+z3 -> dist z1 z2 < z3.
Proof.
  intros z1 z2 z3 q p.
  destruct p as [p1 p2].
  destruct (Tmetric_Or z1 z2) as [[a b] | [a b]]; rewrite a.
  apply (Tlt_plus_lt (z3-z2) (z1-z3) z2) in p1.
  ring_simplify in p1.
  replace (-z2+z1) with (z1-z2) in p1 by ring.
  exact p1.
  apply (Tlt_plus_lt (-z1) z2 (z1+z3)) in p2.
  ring_simplify in p2.
  replace (-z1+z2) with (z2-z1) in p2 by ring.
  exact p2.
Qed.
Hint Resolve Tmetric_gtgt_sand: Tiny.


Lemma Tmetric_minus_inv : forall z1 z2 z3, dist z1 z2 = dist (z1 - z3) (z2 - z3).
Proof.
  intros z1 z2 z3;
  pose proof (Tmetric_inv z1 (z2) (-z3)) as H;
  replace (z1-z3) with (z1+-z3) by ring;
  replace (z2-z3) with (z2+-z3) by ring; exact H.    
Qed.
Hint Resolve Tmetric_minus_inv: Tiny.


Lemma lt_metric : forall x y, x < y -> dist x y = y - x.
Proof.
  intros x y p.
  destruct (Tmetric_Or x y) as [[P Q] | [P Q]].
  contradict Q; auto with Tiny.
  exact P.
Qed.
Hint Resolve lt_metric: Tiny.

Lemma le_metric : forall x y, x <= y -> dist x y = y - x.
Proof.
  intros x y p.
  destruct p.
  apply lt_metric; exact H.
  rewrite H.
  ring_simplify.
  rewrite (dist_zero y y); exact eq_refl.
Qed.
Hint Resolve le_metric: Tiny.

Lemma dist_0_1 : dist T0 T1 = T1.
Proof.
  rewrite (lt_metric T0 T1 T1_gt_T0).
  ring.
Qed.
Hint Resolve dist_0_1: Tiny.

Lemma dist_1_0 : dist T1 T0 = T1.
Proof.
  rewrite (dist_symm T1 T0).
  exact dist_0_1.
Qed.
Hint Resolve dist_1_0: Tiny.

(***************************************************************)
(** * Max and Min                                              *)
(***************************************************************)
(***************************************************************)
(** ** Max                                                     *)
(***************************************************************)
Definition W_M (x y z : T)
  := (x > y -> z = x) /\ (x = y -> z = x) /\ (x < y -> z = y).
Lemma W_M_or : forall x y z, W_M x y z -> (x = z) \/ (y = z).
Proof.
  intros x y z m.
  destruct m as [a [b c]].
  destruct (Ttotal_order x y) as [p1 | [p2 | p3]].
  right; rewrite (c p1); exact eq_refl.
  left; rewrite (b p2); exact eq_refl.
  left; rewrite (a p3); exact eq_refl.
Qed.
Lemma W_M_Or : forall x y z, W_M x y z -> (x=z /\ x>=y) \/ (y=z /\ y>=x).
Proof.
  intros x y z m.
  destruct m as [a [b c]].
  destruct (Ttotal_order x y) as [p1 | [p2 | p3]].
  right; rewrite (c p1); split; auto with Tiny.
  left; rewrite (b p2); split; auto with Tiny.
  left; rewrite (a p3); split; auto with Tiny.
Qed.

Lemma W_max : forall x y, (exists z, W_M x y z).
Proof.
  intros x y.
  destruct (Ttotal_order x y) as [c1 | [c2 | c3]]; unfold W_M.

  exists y.
  split; auto.
  intro H; contradict H; apply Tlt_nlt; auto.

  exists x.
  split; auto.

  exists x.
  split; auto.
  split; auto.
  intro H; contradict c3; apply Tlt_nlt; auto.
Qed.
Hint Resolve W_M_or W_M_Or W_max: Tiny.

(***************************************************************)
(** ** min                                                     *)
(***************************************************************)
Definition W_m (x y z : T)
  := (x > y -> z = y) /\ (x = y -> z = x) /\ (x < y -> z = x).

Lemma W_m_or : forall x y z, W_m x y z -> (x = z) \/ (y = z).
Proof.
  intros x y z m.
  destruct m as [a [b c]].
  destruct (Ttotal_order x y) as [p1 | [p2 | p3]].
  left; rewrite (c p1); exact eq_refl.
  left; rewrite (b p2); exact eq_refl.
  right; rewrite (a p3); exact eq_refl.
Qed.

Lemma W_m_Or : forall x y z, W_m x y z -> (x=z /\ y>=x) \/ (y=z /\ x>=y).
Proof.
  intros x y z m.
  destruct m as [a [b c]].
  destruct (Ttotal_order x y) as [p1 | [p2 | p3]].
  left; rewrite (c p1); split; auto with Tiny.
  left; rewrite (b p2); split; auto with Tiny.
  right; rewrite (a p3); split; auto with Tiny.
Qed.

Lemma W_m_whatever_r : forall x y z, W_m x y z -> (z <= y).
Proof.
  intros.
  destruct (W_m_Or x y z H).
  destruct H0.
  rewrite H0 in H1; auto with Tiny.
  destruct H0; right; rewrite H0;  exact eq_refl.
Qed.

Lemma W_m_whatever_l : forall x y z, W_m x y z -> (z <= x).
Proof.
  intros.
  destruct (W_m_Or x y z H).
  destruct H0.
  destruct H0; right; exact eq_refl.
  destruct H0.
    
  rewrite H0 in H1; auto with Tiny.
Qed.

Lemma W_min : forall x y, (exists z, W_m x y z).
Proof.
  intros x y.
  destruct (Ttotal_order x y) as [c1 | [c2 | c3]]; unfold W_m.

  exists x.
  split; auto.
  intro Hl; contradict c1; apply Tlt_nlt; auto.

  exists x.
  split; auto.

  exists y.
  split; auto.
  split; auto.
  intro H; contradict c3; apply Tlt_nlt; auto.
Qed.
Hint Resolve W_m_or  W_min: Tiny.
