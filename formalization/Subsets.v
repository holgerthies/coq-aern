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

End Open.

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

