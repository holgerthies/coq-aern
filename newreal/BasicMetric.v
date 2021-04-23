Require Import BasicAxioms.
Require Import BasicRing.
Require Import BasicArith.
Open Scope T_scope.



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
