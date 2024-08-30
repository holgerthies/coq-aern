(* this file proves various prperties of subsets of real numbers *)
Require Import Lia.
Require Import Real Euclidean List Minmax Classical.Subsets Sierpinski Testsearch Dyadic.
Require Import RealAssumption.
Require Import List.
Require Import Hyperspace.Continuity.

Import ListNotations.
Section Open.

Context {X : Type}.

Definition open (A : (@csubset X)) := forall x, {s : sierp | (sierp_up s)  <-> A x}. 

Lemma open_semidec A : open A -> forall x, semidec (A x).
Proof.
  unfold open.
  intros.
  destruct (X0 x).
  destruct x0.
  exists x0.
  apply i.
Defined.

Lemma semidec_open A : (forall x, semidec (A x)) -> open A.
Proof.
  intros.
  intros x.
  destruct (sierp_from_semidec (X0 x)).
  exists x0;auto.
Defined.

Definition open_cf {A} (P : open A) : X -> sierp.
Proof.
  intros x.
  destruct (P x).
  apply x0.
Defined.

Lemma open_emptyset : open (fun x => False).
Proof.
  apply semidec_open.
  intros.
  exists lazy_bool_false.
  split;unfold lazy_bool_up;intros;contradict H;auto.
  apply lazy_bool_distinct.
Qed.

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

Lemma open_union A B : open A -> open B -> open (union A B).
Proof.
  assert (union A B = countable_union (fun n => match n with | 0 => A | _ => B end)).
  {
    apply fun_ext.
    intros x.
    unfold union,countable_union.
    apply Prop_ext.
    intros [].
    exists 0%nat;auto.
    exists 1%nat;auto.
    intros [].
    destruct x0; [left|right];auto.
  }
  intros.
  rewrite H.
  apply open_countable_union.
  intros n.
  destruct n; simpl;auto.
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

Lemma open_to_testfun U : open U -> (forall (x : X), ^M {f : nat -> bool | U x <-> exists n, f n = true  }).
Proof.
  intros.
  intros.
  destruct (X0 x).
  pose proof (sierp_to_nat_sequence x0).
  revert X1.
  apply M_lift.
  intros [f F].
  exists (fun n => if ((f n) =? 1)%nat then true else false).
  rewrite <-i.
  rewrite F.
  split;intros [n N]; exists n.
   rewrite N;auto.
  destruct (f n =? 1) eqn:E;try (contradict N;apply Bool.diff_false_true).
  apply Nat.eqb_eq;auto.
Defined.

End Open.

Section Closed.

Context {X : Type}.
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

Lemma closed_intersection A B : closed A -> closed B -> closed (intersection A B).
Proof.
  intros.
  unfold closed.
  intros x.
  destruct (open_union _ _ X0 X1 x).
  exists x0.
  rewrite i.
  unfold complement, union,intersection.
  rewrite classical_tautology_neg_and;split;auto.
Qed.
 Lemma points_closed_ineq_semidec x : (closed (singleton x) -> (forall y, semidec (x <> y))).
 Proof.
   intros.
   destruct (X0 y).
   unfold sierp_up in i.
   destruct x0.
   simpl in i.
   exists x0.
   rewrite i.
   split;auto.
 Defined.
 Lemma ineq_semidec_points_closed x :  (forall y, semidec (x <> y)) -> (closed (singleton x)).
   intros H y.
   destruct (sierp_from_semidec (H y)).
   exists x0.
   rewrite i.
   split;auto.
 Defined.
End Closed.

Section Compact.

Context {X : Type}.

Definition compact (A : (@csubset X)) := forall B, open B -> {k : sierp | sierp_up k <-> (@is_subset X A B)}. 

Lemma is_compact_union M1 M2 : compact M1 -> compact M2 -> compact (union M1 M2).
Proof.
    intros H1 H2 A Aopen.
    destruct (H1 A Aopen) as [k1 P1].
    destruct (H2 A Aopen) as [k2 P2].
    destruct (sierp_and k1 k2) as [x [X1 X2]].
    exists x.
    split; intros.
    intros a P.
    destruct P; [apply P1| apply P2];auto;apply X1;auto.
    apply X2.
    rewrite union_subset in H.
    split;[apply P1 | apply P2];apply H.
Defined.
Lemma subset_intersection A B C : is_subset (intersection A B) C <-> is_subset A (@union X (complement B) C).
Proof.
  unfold is_subset, union, complement, intersection.
  split;intros.
  apply Classical_Prop.imply_to_or.
  intros.
  apply H;auto.
  destruct H0.
  destruct (H x H0);auto.
  contradict H1;auto.
Qed.

Lemma is_compact_intersection M1 M2 : compact M1 -> closed M2 -> compact (intersection M1 M2).
Proof.
  intros H1 H2 A Aopen.
  destruct (H1 (union (complement M2) A)).
  apply open_union;auto.
  exists x.
  rewrite subset_intersection.
  apply i.
Qed.

Lemma singleton_compact x : compact (singleton x). 
Proof.
  unfold compact, singleton, open.
  intros.
  destruct (X0 x).
  exists x0.
  rewrite i.
  unfold is_subset.
  split;intros;auto.
  rewrite <-H0;auto.
Qed.

Lemma compact_closed_ineq_semidec : (forall A,  compact A -> closed A) -> (forall (x y : X), semidec (x <> y)). 
Proof.
  intros.
  apply points_closed_ineq_semidec.
  apply X0.
  apply singleton_compact.
Qed.
Lemma compact_closed A : (forall (x y : X), semidec (x <> y)) -> compact A -> closed A.
Proof.
  intros T1 H x.
  pose proof (ineq_semidec_points_closed _ (T1 x)).
  destruct (H _ X0).
    exists x0.
    rewrite i.
    unfold is_subset, complement, singleton.
    split.
    intros H2 Ax.
    specialize (H2 x Ax).
    contradict H2;auto.

    intros.
    contradict H1.
    rewrite <-H1;auto.
 Defined.


Lemma is_compact_countable_intersection A : (forall (x y : X), semidec (x <> y)) -> (forall n, compact (A n)) -> compact (countable_intersection A).
Proof.
  intros.
  assert (closed (countable_intersection A)).
  {
    apply closed_countable_intersection.
    intros.
    apply compact_closed;auto.
  }
  assert (countable_intersection A = intersection (A 0%nat) (countable_intersection A)) as ->.
  {
    apply fun_ext.
    intros; apply Prop_ext;intros; [split;auto|].
    intros n.
    apply H.
  }
  apply is_compact_intersection;auto.
Qed.

  Lemma compact_fin_cover K U : compact K -> (forall n, (open (U n))) -> is_subset K (countable_union U) -> ^M { m | forall x, K x -> exists n, (n < m)%nat /\ (U n x)}.
  Proof.
    intros.
    assert {T : (nat -> X -> sierp) -> (X -> sierp) | forall x y, sierp_up ((T x) y) <-> (countable_union (fun n y =>  sierp_up (x n y)) y)  } as [T H0].
    {
       assert (forall (x : nat -> X -> sierp) n, open (fun y => sierp_up (x n y))) by (unfold open;intros;exists (x n x0);split;auto).
       exists (fun x => (fun y => (pr1 _ _ (open_countable_union (X2 x) y)))).
       intros.
       destruct (open_countable_union (X2 x) y);auto.
    } 
    assert {g : (nat -> X -> sierp) -> sierp | forall x, sierp_up (g x) <-> is_subset K (countable_union (fun n => (fun y => sierp_up (x n y))))  } as [g G].
    {
      assert (forall x, open (fun y => sierp_up (T x y))) by (unfold open;intros;exists (T x x0);split;auto).
      exists (fun x => (pr1 _ _ (X0 _ (X2 x)))).
      intros.
      destruct (X0 _ (X2 x));simpl;auto.
      split;auto.
      - intros.
        unfold is_subset, countable_union.
        intros.
        apply H0.
        apply i;auto.
     - intros.
       apply i.
       unfold is_subset.
       intros.
       apply H0.
       apply H1;auto.
    }
    assert (sierp_up (g (fun n => (fun y => (pr1 _ _ (X1 n y)))))).
    {
      apply G.
      unfold is_subset.
      intros.
      unfold countable_union.
      destruct (H x H1).
      exists x0.
      destruct (X1 x0 x);simpl;apply i;auto.
    }
    pose proof (continuity _ _ H1).
    revert X2.
    apply M_lift.
    intros [m M].
    exists m.
    intros.
    assert {y : nat -> X -> sierp | (forall n, (n < m)%nat -> (fun a=> (pr1 _ _ (X1 n a))) = y n) /\ forall n x, sierp_up (y n x) -> (n < m)%nat} as [y Y].
    {
      exists (fun n => if (n <? m)%nat then (fun a => (pr1 _ _ (X1 n a))) else (fun a => pr1 _ _ (open_emptyset a))).
      split.
      intros.
      apply fun_ext.
      intros.
      rewrite ((proj2 (Nat.ltb_lt n m)) H3);auto.
      intros.
      destruct (lt_dec n m);auto.
      contradict H3.
      rewrite (proj2 (Nat.ltb_nlt n m) n0).
      destruct (open_emptyset x0).
      simpl.
      rewrite i;auto.
    }
    assert (sierp_up (g y)).
    {
      apply M.
      intros.
      apply Y;auto.
    }
    destruct (proj1 (G y) H3 x H2).
    exists x0.
    assert (x0 < m)%nat.
    apply (proj2 Y x0 x);auto.
    split;auto.
    assert (sierp_up (pr1 _ _ (X1 x0 x))) by (destruct (proj1 Y _ H5);auto).
    destruct (X1 x0 x);apply i;auto.
 Qed.

End Compact.

Section Overt.

  Context {X : Type}.
  Definition overt (A : (@csubset X)) := forall B, open B -> {k : sierp | sierp_up k <-> (@intersects X A B)}. 

  Lemma singleton_overt x : overt (singleton x).
  Proof.
    intros A openA.
    destruct (openA x).
    exists x0.
    rewrite i.
    unfold intersects, intersection, singleton.
    split;intros.
    exists x;split;auto.
    destruct H as [x' [-> H]];auto.
  Defined.

  Lemma overt_nonempty_semidec A : overt A -> semidec (exists x, A x).
  Proof.
    intros.
    destruct (X0 (fun x => True)).
    exists (sierp_from_kleenean (neq_sym _ _ _ lazy_bool_distinct)).
    unfold sierp_up, sierp_from_kleenean;split;auto.
    destruct x.
    exists x.
    rewrite i.
    unfold intersects, intersection;split; intros [];exists x0;auto;apply H.
  Defined.

  Lemma overt_open_intersection : (forall A B, overt A -> open B -> overt (intersection A B)).
  Proof.
    intros.
    unfold overt, intersection.
    intros.
    pose proof (open_intersection X1 X2).
    destruct (X0 _ X3).
    exists x.
    rewrite i.
    unfold intersects, intersection.
    split.
    intros [a [P1 [P2 P3]]];exists a;auto.
    intros [a [[P1 P2] P3]];exists a;auto.
  Qed.
  Lemma overt_intersection_eq_semidec : (forall A B, overt A -> overt B -> overt (intersection A B)) -> (forall (x y : X), semidec (x = y)).
  Proof.
    intros.
    specialize (X0 _ _ (singleton_overt x) (singleton_overt y)).
    apply overt_nonempty_semidec in X0.
    destruct X0.
    exists x0.
    rewrite i.
    unfold intersection, singleton.
    split;intros.
    destruct H as [x' [-> ->]];auto.
    exists x;split;auto.
 Qed.
End Overt.

