(* this file proves various properties of subsets of real numbers *)
Require Import Lia.
Require Import Real Euclidean List Minmax ClassicalSubsets Sierpinski testsearch Dyadic.

Section Open.

Context {X : Type}.
Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.
#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).

Definition open (A : (@csubset X)) := forall x, {s : sierp | (sierp_up s)  <-> A x}. 

Definition open_cf {A} (P : open A) : X -> sierp.
Proof.
  intros x.
  destruct (P x).
  apply x0.
Defined.

Lemma open_cf_exists {A} : open A -> {f : X -> sierp | forall x, (sierp_up (f x)) <-> A x}.
Proof.
  intros P.
  exists (open_cf P).
  intros x.
  unfold open_cf.
  destruct P.
  apply i.
Defined.

Lemma open_countable_union {A} : (forall n, open (A n)) -> open (countable_union A).
Proof.
  intros.
  intro x.
  Check eventually_true.
  destruct (eventually_true (fun n => (proj1_sig (X0 n x)))) as [s P].
  exists s.
  rewrite P.
  split;intros.
  - destruct H as [n H].
    pose proof (proj2_sig (X0 n x)).
    exists n.
    apply H0.
    exact H.
  - destruct H as [n H].
    pose proof (proj2_sig (X0 n x)).
    exists n.
    apply H0.
    exact H.
Defined.

Lemma open_intersection {A B}: open A -> open B -> open (intersection A B).
Proof.
  intros openA openB x.
  destruct (openA x) as [s1 S1].
  destruct (openB x) as [s2 S2].
  exists (proj1_sig (sierp_and s1 s2)).
  rewrite (proj2_sig (sierp_and s1 s2)).
  unfold intersection.
  rewrite S1, S2.
  split;auto.
Defined.
End Open.

Section Closed.

Context {X : Type}.
Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.
#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).

Definition closed (A : (@csubset X)) := open (complement A).

Lemma closed_union {A B} : closed A -> closed B -> closed (union A B).
Proof.
  intros cA cB x.
  pose proof (open_intersection cA cB).
  destruct (X0 x) as [s H].
  exists s.
  rewrite H.
  split;intros.
  destruct H0.
  intros P.
  destruct P;auto.
  unfold complement, union in H0.
  split;intros P;apply H0;auto.
Defined.

Lemma closed_countable_intersection {A} : (forall n, closed (A n)) -> closed (countable_intersection A).
Proof.
  intros H x.
  destruct (open_countable_union H x) as [s P].
  exists s.
  rewrite P.
  split;intros.
  intros Q.
  destruct H0 as [n H0].
  apply H0.
  apply Q.
  apply Classical_Pred_Type.not_all_ex_not.
  apply H0.
Defined.

Section Compact.

Context {X : Type}.
Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.
#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).

Definition compact (A : (@csubset X)) := forall B, open B -> {k : ^K | (k = lazy_bool_true) <-> (@is_subset X A B)}. 

Lemma is_compact_union M1 M2 : compact M1 -> compact M2 -> compact (union M1 M2).
Proof.
    intros H1 H2 A Aopen.
    destruct (H1 A Aopen) as [k1 P1].
    destruct (H2 A Aopen) as [k2 P2].
    exists (lazy_bool_and k1 k2).
    split; intros.
    rewrite lazy_bool_and_up in H.
    intros x P.
    destruct P; [apply P1| apply P2];auto;apply H;auto.
    rewrite lazy_bool_and_up.
    rewrite union_subset in H.
    split;[apply P1 | apply P2];apply H.
Defined.

End Compact.

Section Overt.

Context {X : Type}.
Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.
#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).

Definition overt (A : (@csubset X)) := forall B, open B -> {k : ^K | (k = lazy_bool_true) <-> (@intersects X A B)}. 

End Overt.

