(* this file proves various prperties of subsets of real numbers *)
Require Import Lia.
Require Import Real Euclidean List Minmax Classical.Subsets Sierpinski Testsearch Dyadic.
Require Import RealAssumption.
Require Import List.


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

Axiom continuity : forall {X} (f : (nat -> X) -> sierp) (x : (nat -> X)), sierp_up (f x) -> ^M {m | forall y, (forall n, (n < m)%nat -> x n = y n) -> sierp_up (f y)}.

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

Section Metric.
  Context {X : Type}.
  
  Definition metric := {d : X -> X -> ^Real |  (forall x y, d x y = 0 <-> x = y) /\ (forall x y, d x y = d y x) /\ forall x y z, d x y <= d x z + d z y}.

  Definition d_X (H : metric):= pr1 _ _ H.  

  Definition dense (A : (@csubset X)) := forall x U, open U -> U x -> exists y, A y /\ U y.

  Definition separable := {e : nat -> X | dense (fun x => exists n, e n = x)}. 

  Definition D (s : separable):= (pr1 _ _ s).

  Definition metric_is_fast_cauchy (H : metric) (f: nat -> X):= forall n m, (d_X H (f n) (f m)) <= prec n + prec m.
  Definition metric_is_fast_limit (H : metric) (f : nat -> X) x := forall n, (d_X H (f n) x) <= prec n.
  Definition has_limit (H : metric) := forall f, (metric_is_fast_cauchy H f) -> {x | metric_is_fast_limit H f x}.
   

  Definition second_countable := {B : nat -> (@csubset X) & forall n, open (B n) & forall U, open U -> ^M {c : nat -> nat | countable_union (fun n => B (c n)) = U }}. 

  Definition open_choice (U : (@csubset X)) := open U -> (exists x, U x) -> ^M {x | U x}.

  Lemma separable_exists U (s : separable) : open U -> (exists x, U x) -> exists n, U (D s n).
  Proof.
    intros.
    destruct s.
    simpl.
    destruct H.
    specialize (d _ _ X0 H).
    destruct d.
    destruct H0 as [[n H0] H1].
    exists n;rewrite H0;auto.
  Qed.

  Lemma separable_choice (s : separable): forall U, open U -> (exists x, U x) -> ^M {n | U (D s n) }.
  Proof.
    intros U H N.
    pose proof (separable_exists _ s H N).
    assert (forall n, {k : ^K | k = lazy_bool_true <-> U (D s n)}).
    {
      intros.
      destruct (H (D s n)).
      destruct x.
      exists x.
      rewrite i;split;auto.
    }
    remember (fun n => pr1 _ _ (X0 n)) as f.
    assert (exists n, f n = lazy_bool_true).
    {
      destruct H0.
      exists x.
      rewrite Heqf.
      destruct (X0 x).
      simpl.
      rewrite i;auto.
    }
    pose proof (multivalued_countable_choice f H1).
    revert X1.
    apply M_lift.
    intros [n P].
    exists n.
    destruct (X0 n) eqn:E.
    rewrite <-i.
    rewrite <- P.
    rewrite Heqf.
    rewrite E.
    simpl;auto.
  Qed.

  Lemma separable_open_choice : separable -> forall U, open_choice U.
  Proof.
    intros.
    intros H N.
    pose proof (separable_choice X0 U H N).
    revert X1.
    apply M_lift.
    intros [n P].
    exists (D X0 n);auto.
  Qed.

  Lemma choice_separable : second_countable -> (forall U, open_choice U) -> separable.
  Proof.
    intros.
  Abort.

  Definition ball (H: metric) x n := (fun y => (d_X H x y < prec n)) : csubset.
  Lemma metric_open (H : metric) : forall x n, open (ball H x n). 
  Proof.
    intros.
    apply semidec_open.
    intros y.
    apply real_lt_semidec.
  Qed.


  Lemma separable_metric_approx_inside (H : metric) (s : separable) U x :open U -> U x -> forall n,  ^M {m | (d_X H x (D s m)) < prec n /\ U (D s m)}.
  Proof.
    intros.
    pose proof (metric_open H x n).
    pose proof (separable_choice s _ (open_intersection X0 X1)).
    enough (exists x0, (intersection U (ball H x n) x0)).
    specialize (X2 H1).
    revert X2.
    apply M_lift.
    intros [m M].
    exists m.
    split;apply M.
    exists x.
    split;auto.
    unfold ball.
    replace (d_X H x x) with 0.
    apply prec_pos.
    apply eq_sym.
    destruct H.
    apply a;auto.
  Qed.

  Lemma separable_metric_approx (H : metric) (s : separable) : forall x n, ^M {m | (d_X H x (D s m)) < prec n}.
  Proof.
    intros.
    pose proof (separable_choice s _ (metric_open H x n)).
    enough ( (exists x0 : X, (fun y : X => d_X H x y < prec n) x0) );auto.
    exists x.
    replace (d_X H x x) with 0.
    apply prec_pos.
    apply eq_sym.
    destruct H.
    apply a;auto.
 Qed.


  Lemma fast_cauchy_simpl H : forall x, {y | metric_is_fast_cauchy H x -> (forall n, d_X H (y n) (y (S n)) <= prec (S (S n))) /\ (forall p, metric_is_fast_limit H x p -> metric_is_fast_limit H y p) }.
  Proof.
    intros.
    exists (fun n => x (S (S (S n)))).
    intros.
    split.
    intros.
    apply (real_le_le_le _ (prec (S (S (S n))) + prec (S (S (S ( S n)))))).
    apply H0.
    rewrite <-(prec_twice (S (S n))).
    apply real_le_le_plus_le; [right;f_equal;lia|apply real_lt_le;apply prec_monotone;lia].

    intros.
    intros n.
    apply (real_le_le_le _ (prec (S (S (S n))))).
    apply H1.
    apply real_lt_le.
    apply prec_monotone.
    lia.
  Qed.

  Lemma fast_cauchy_neighbor M x: (forall n, (d_X M (x n) (x (S n))) <= prec (S n)) -> metric_is_fast_cauchy M x.
  Proof.
    intros H.
    intros n1 m1.
    destruct M as [d [M1 [M2 M3]]].
    simpl d_X in *.
    assert (forall n m k,  (n <= m)%nat -> (k = m - n)%nat ->  d (x n) (x m) <= prec n + prec m).
    intros n m k H0 e.
    assert (m  = k + n)%nat by (rewrite e; lia).
    induction (eq_sym H1).
    assert (d (x n)  (x (k + n)%nat) <= prec n - prec (n + k)). 
    induction k.
    replace (n + 0)%nat with n by lia; replace (0 + n)%nat with n by lia. 
    replace (prec n - prec n) with real_0 by ring.
    replace (d (x n) (x n)) with 0 by (rewrite (proj2 (M1 (x n) (x n)));auto).
    apply real_eq_le;auto.

    assert ( k = (k + n - n)%nat) by lia.
    assert ((k + n)%nat = (k + n)%nat) by apply eq_refl.
    assert (n <= k + n)%nat by lia.
    pose proof (IHk H4 H2 H3).
    clear e H1 H0 IHk H2 H3 H4.
    pose proof (H (k + n)%nat).

    apply (real_le_le_le _ _ _ (M3 _ _ (x (k+n)%nat))).
    pose proof (real_le_le_plus_le _ _ _ _ H0 H5).
    rewrite real_plus_comm.

    apply (real_le_le_le _ _ _ H1 ).
    ring_simplify.
    replace (n + S k)%nat with ((n+k)+1)%nat by lia.
    replace (S (k+n))%nat with ((n+k)+1)%nat by lia.
    add_both_side_by (-prec n + prec (n+k) ).
    rewrite <-(prec_twice (n+k)).
    ring_simplify.
    right;auto.

    pose proof (H (k + n)%nat).
    apply (real_le_le_le _ _ _ H2).
    add_both_side_by (- prec n).
    apply (real_le_le_le _ real_0);apply real_lt_le.
    add_both_side_by (prec (n+k)).
    apply prec_pos.
    apply prec_pos.
    assert (J : (n1 <= m1 \/ m1 <= n1)%nat) by lia; destruct J.

    apply (H0 _ _ (m1 - n1)%nat H1  eq_refl).
    pose proof (H0 _ _  (n1 - m1)%nat H1 eq_refl).
    rewrite M2.
    rewrite real_plus_comm.
    apply H2.
  Qed.

  Definition XX2X (x : X+X) := match x with
                                  | inl a => a 
                                  | inr a => a
                                  end.

  Definition to_convergent (H : metric) (x : nat -> X) :^M {y : nat -> X | metric_is_fast_cauchy H y /\ ((metric_is_fast_cauchy H x) -> forall p, metric_is_fast_limit H x p -> metric_is_fast_limit H y p)}.
  Proof.
    destruct (fast_cauchy_simpl H x) as [x' X'].

    assert ({k : nat -> K | forall n, k n = lazy_bool_true <-> d_X H (x' n) (x' (S n)) > prec (S (S n)) }) as [k1 K1].
    {
      enough (forall n, {k | k = lazy_bool_true <-> d_X H (x' n) (x' (S n)) > prec (S (S n))}).
      exists (fun n => pr1 _ _ (X0 n)).
      intros.
      destruct (X0 n);auto.
      intros.
      destruct (real_lt_semidec (prec (S (S n))) (d_X H (x' n) (x' (S n)))).
      exists x0.
      rewrite i;split;auto.
    }
    assert ({k : nat -> K | forall n, k n = lazy_bool_true <-> d_X H (x' n) (x' (S n)) < prec (S n) }) as [k2 K2].
    {
      enough (forall n, {k | k = lazy_bool_true <-> d_X H (x' n) (x' (S n)) < prec (S n)}).
      exists (fun n => pr1 _ _ (X0 n)).
      intros.
      destruct (X0 n);auto.
      intros.
      destruct (real_lt_semidec (d_X H (x' n) (x' (S n))) (prec ((S n))) ).
      exists x0.
      rewrite i;split;auto.
    }

    assert (forall n, (k1 n = lazy_bool_true \/ k2 n = lazy_bool_true)).
    {
      intros.
      rewrite K1,K2.
      destruct (lem   (d_X H (x' n) (x' (S n)) < prec (S n))).
      right;auto.
      left.
      apply real_nge_le in H0.
      apply (real_lt_le_lt _ (prec (S n)) _);auto.
      apply prec_S.
    }

    assert (forall n yp, ^M {y : X+X |  (y = inr (XX2X yp) \/ y = (inl (x' (S n)))) /\ (n = O -> y = inl (x' (S n))) /\ ((yp = inl (x' n) /\ d_X H (x' n) (x' (S n)) <= prec (S (S n))) -> y = (inl (x' (S n)))) /\  ( (n > 0)%nat /\ (d_X H (x' n) (x' (S n)) > prec (S n)) -> y = inr (XX2X yp)) /\ ((n > 0)%nat /\ yp = inr (XX2X yp) -> y = yp)}).
    {
      intros.
      destruct n.

      apply M_unit.
      exists (inl (x' 1%nat)).
      split;[|split;[|split; [|split]]];auto; try lia.
      destruct yp.
      - pose proof (M_choice _ _ (H0 (S n))).
        revert X0.
        apply M_lift.
        intros [].
        + exists (inr x0).
          split.
          left;simpl;auto.
          split;try lia.
          split.
          intros.
          destruct H1.
          contradict H2.
          apply real_gt_nle.
          apply K1;auto.
          split.
          intros;simpl;auto.
          intros.
          destruct H1.
          discriminate H2.
      +  exists (inl (x' (S (S n)))).
         split.
         right;simpl;auto.
         split;try lia.
         split.
         intros;auto.
         split.
         intros.
         destruct H1.
         contradict H2.
         apply real_gt_ngt.
         apply K2;auto.
         intros [].
         discriminate H2.
      - apply M_unit.
        exists (inr x0).
        split;[|split; [|split;[| split ]]];auto;try lia.
        intros [];auto.
        contradict H1.
        discriminate.
    }

    pose proof (M_paths _ _ (M_unit _ (inl (x' 0%nat))) X0 ).
    revert X1.
    apply M_lift.
    intros [f0 P].
    remember (fun n => f0 (S n)) as f.
    assert (forall n, f (S n) = inr (XX2X (f (S n))) -> d_X H (XX2X (f n)) (XX2X (f (S n))) = 0).
    {
      intros.
      specialize (P (S n)).
      destruct P as [P [_ _]].
      destruct P.
      rewrite Heqf.
      rewrite H2.
      simpl XX2X.
      destruct H.
      simpl in *.
      rewrite (proj1 a);auto.
      contradict H1.
      rewrite Heqf.
      simpl.
      rewrite H2.
      discriminate.
    }

    assert (forall n, f (S n) = inl (x' (S (S n))) -> f n = inl (x' (S n))).
    {
      intros.
      rewrite Heqf in *.
      destruct (P n) as [P1 [P2 [P3 [P4 P5]]]].
      destruct P1;auto.
      contradict H2.
      destruct (P ((S n))) as [_ [_ [_ [_ P5']]]].
      rewrite P5';auto.
      rewrite H3.
      discriminate.
      split;try lia.
      rewrite H3.
      simpl;auto.
    }
    
    assert (forall n, f (S n) = inl (x' (S (S n))) -> d_X H (XX2X (f n)) (XX2X (f (S n))) <= prec (S (S n))).
    {
      intros.
      rewrite H3.
      rewrite H2;auto.
      simpl d_X.
      apply real_nge_le.
      intros A.
      destruct (P (S n)) as [_ [_ [_ [P4 P5]]]].
      assert ((S n > 0)%nat /\  prec (S (S n)) < d_X H (x' (S n)) (x' (S (S n)))
).
      split;try lia;auto.

      specialize (P4 H4).
      contradict H3.
      rewrite Heqf.
      rewrite P4.
      discriminate.
    }

    assert ((forall n, d_X H (x' n) (x' (S n)) <= prec (S (S n))) -> forall n, (f n) = inl (x' (S n))).
    {
      intros.
      induction n.
      destruct (P 0%nat).
      rewrite Heqf.
      destruct H6.
      rewrite H6;auto.
      destruct (P (S n)) as [P1 [P2 [P3 [P4 P5]]]].
      rewrite Heqf.
      rewrite P3;auto.
      split;auto.
      rewrite <-IHn.
      rewrite Heqf;auto.
    }

    exists (fun n => XX2X (f n)).
    split.
    - apply fast_cauchy_neighbor.
      intros.
      apply (real_le_le_le _ (prec (S (S n)))); [|apply real_lt_le;apply prec_S].
      destruct (P (S n)) as [P1 [P2 [P3 [P4 P5]]]].
      destruct P1.
      + rewrite H1;auto.
        apply real_lt_le;apply prec_pos.
        rewrite Heqf.
        rewrite H5.
        simpl;auto.
      + apply H3;auto.
        rewrite Heqf;auto.
   - intros.
     intros n.
     rewrite H4.
     simpl.
      apply (real_le_le_le _ (prec (S n))); [|apply real_lt_le;apply prec_S].
     apply X';auto.
     intros m.
     apply X';auto.
  Qed.
  
  Lemma metric_limit_unique (H : metric) x x1 x2 : metric_is_fast_limit H x x1 -> metric_is_fast_limit H x x2 -> x1 = x2. 
    destruct H as [d [D1 [D2 D3]]].
    unfold metric_is_fast_limit;simpl.
    intros.
    enough (d x1 x2 <= 0).
    - destruct H1;try (apply D1;auto).
      contradict H1.
      intros H1.
      pose proof (D3 x1 x1 x2).
      contradict H2.
      apply real_gt_nle.
      assert ((d x1 x1) = 0) as -> by (apply D1;auto).
      replace 0 with (0+real_0) by ring.
      apply real_lt_lt_plus_lt;[|rewrite D2];auto.
    - enough (forall n, d x1 x2 <= prec n).
      apply real_nge_le.
      intros H2.
     destruct (real_Archimedean _ H2).
     contradict H3.
     apply real_lt_nlt.
     apply (real_le_lt_lt _ _ _  (D3 _ _ (x (S (x0 + 1))))).
     rewrite <-prec_twice.
     apply real_lt_lt_plus_lt;[rewrite D2;apply (real_le_lt_lt _ _ _ (H (S (x0+1))%nat)) |apply (real_le_lt_lt _ _ _ (H0 (S (x0+1))%nat))];apply prec_S.

     intros.
     apply (real_le_le_le _ _ _ (D3 _ _ (x (n+1)%nat))).
     rewrite <-prec_twice.
     apply real_le_le_plus_le;[rewrite D2|];auto.
  Qed.

  Definition extended_limit H (l : has_limit H) x  : ^M {p | metric_is_fast_cauchy H x -> metric_is_fast_limit H x p}.
  Proof.
    pose proof (to_convergent H x).
    revert X0.
    apply M_lift.
    intros [y [Y1 Y2]].
    destruct (l y Y1).
    exists x0;auto.
    intros.
    destruct (l x H0).
    specialize (Y2 H0 _ m0).
    replace x0 with x1;auto.
    apply (metric_limit_unique H y);auto.
  Qed.

  Lemma sierp_id : forall s1 s2, (sierp_up s1 <-> sierp_up s2) -> s1 = s2.
 Admitted.

  Lemma not_fast_cauchy_semidec (H : metric) x : {s | sierp_up s <-> (~ metric_is_fast_cauchy H x)}.
  Proof.
    assert ({s | sierp_up s <-> (exists n m, d_X H (x n) (x m) > prec n + prec m)}) as [s S].
    {
      enough (forall n, {s | sierp_up s <-> exists m, d_X H (x n) (x m) > prec n + prec m}).
      pose proof (eventually_true (fun n=> (pr1 _ _ (X0 n)))).
      destruct X1.
      exists x0.
      rewrite i.
      split; intros [].
      destruct (X0 x1);simpl in *.
      exists x1.
      rewrite <-i0;auto.
      destruct H0.
      exists x1.
      destruct (X0 x1);simpl in *.
      rewrite i0.
      exists x2;auto.

      intros.
      enough (forall m, {s | sierp_up s <-> d_X H (x n) (x m) > prec n + prec m}).
      destruct (eventually_true (fun m=> (pr1 _ _ (X0 m)))).
      exists x0.
      rewrite i.
      split;intros [];exists x1;destruct (X0 x1);simpl in *;apply i0;auto.
      intros m.
      destruct (real_lt_semidec (prec n + prec m) (d_X H (x n) (x m))).
      apply sierp_from_semidec.
      exists x0;auto.
    }
    exists s.
    rewrite S.
    unfold metric_is_fast_cauchy.
    rewrite classical_tautology_neg_all.
    split.
    intros [n [m H0]].
    exists n;rewrite classical_tautology_neg_all;exists m;apply real_gt_nle;auto.
    intros [n N].
    exists n.
    rewrite classical_tautology_neg_all in N.
    destruct N.
    exists x0.
    apply real_nle_ge;auto.
  Qed.

  Lemma sierp_or s1 s2 : {s | sierp_up s <-> sierp_up s1 \/ sierp_up s2}. 
  Proof.
    destruct s1;destruct s2.
    apply sierp_from_semidec.
    exists (lazy_bool_or x x0).
    unfold lazy_bool_up, sierp_up;simpl.
    rewrite lazy_bool_or_up;split;auto.
  Qed.

  Lemma separable_metric_continuous (H : metric) (s : separable) (l : has_limit H) U x : open U ->  U x -> ^M {m | is_subset (ball H x m) U  }.
  Proof.
    intros.
    pose proof (extended_limit H l).
    
    assert (forall (x : nat -> X), {s : sierp | ((not (metric_is_fast_cauchy H x)) -> sierp_up s) /\ (metric_is_fast_cauchy H x -> (sierp_up s <-> exists p, metric_is_fast_limit H x p /\ U p))}).
    {
      intros.
      specialize (X1 x0).
      apply M_hprop_elim.
      intros a b.
      destruct a; destruct b.
      enough (x1 = x2) by  (apply sigma_eqP2;auto).
      apply sierp_id.
      destruct a; destruct a0.
      destruct (lem (metric_is_fast_cauchy H x0)).
      rewrite H2, H4;auto;split;auto.
      split;intros.
      apply H3;auto.
      apply H1;auto.
      revert X1.
      apply M_lift.
      intros [p P].
      destruct (not_fast_cauchy_semidec H x0).      
      destruct (X0 p).
      destruct (sierp_or x1 x2).
      exists x3.
      split.
      intros.
      rewrite i1.
      left.
      apply i;auto.
      intros.
      rewrite i1.
      split.
      intros.
      exists p;split;auto.
      apply i0.
      destruct H2;auto.
      contradict H1.
      apply i;auto.
      intros [p' [P1 P2]].
      right.
      apply i0.
      replace p with p';auto.
      specialize (P H1).
      apply (metric_limit_unique H x0);auto.
    }
    remember (fun n => (pr1 _ _ (X2 n))) as f.
    assert (forall xn, (forall n, (d_X H (xn n) x <= prec n)) -> sierp_up (f xn)).
    {
      intros.
      rewrite Heqf.
      destruct (X2 xn).
      destruct a.
      simpl.
      apply i.
      intros n m.
      destruct H as [d [D1 [D2 D3 ]]].
      simpl d_X in *.
      apply (real_le_le_le _ _ _ (D3 _ _ x)).
      apply real_le_le_plus_le;try apply H1.
      rewrite D2;apply H1.
      exists x.
      split;auto.
    }
    pose proof (separable_metric_approx_inside H s U x X0 H0).
    apply M_countable_lift in X3.
    revert X3.
    apply M_lift_dom.
    intros.
    remember (fun n => (D s (pr1 _ _ (H2 (S (S n)))))) as x0.
    assert (forall n, d_X H (x0 n) (x0 (S n)) <= prec (S n)).
    {
      intros.
      rewrite Heqx0.
      destruct (H2 (S (S (S n)))).
      destruct (H2 (S (S n))).
      simpl d_X.
      destruct H as [d [D1 [D2 D3 ]]].
      simpl d_X in *.
      destruct a; destruct a0.
      apply (real_le_le_le _ _ _ (D3 _ _ x)).
      rewrite <-prec_twice.
      apply real_le_le_plus_le;apply real_lt_le.
      replace (S n + 1)%nat with (S (S n)) by lia.
      rewrite D2.
      apply H4.
      apply (real_lt_lt_lt _ _ _ H).
      apply prec_monotone.
      lia.
    }
    assert (sierp_up (f x0)).
    {
      apply H1.
      intros.
      rewrite Heqx0.
      destruct (H2 (S (S n))).
      simpl.
      destruct a.
      destruct H.
      simpl d_X in *.
      destruct a.
      destruct a.
      rewrite e.
      apply real_lt_le.
      apply (real_lt_lt_lt _ _ _ H4).
      apply prec_monotone.
      lia.
    }
    pose proof (continuity f _ H4).
    revert X3.
    apply M_lift.
    intros [m M].
    exists (S m).
    intros y By.
    remember (fun n => if (n <? m)%nat then (x0 n) else y) as yn.
    assert (metric_is_fast_cauchy H yn).
    {
      apply fast_cauchy_neighbor.
      intros.
      rewrite Heqyn.
      destruct (S n <?  m)%nat eqn:E.
      - assert ((n <? m)%nat = true).
        apply Nat.ltb_lt;apply Nat.ltb_lt in E;lia.
        rewrite H5.
        apply H3.
     - destruct (n <?  m)%nat eqn:E'.
       unfold ball in By.
       destruct H as [d [D1 [D2 D3 ]]].
       simpl d_X in *.
       apply (real_le_le_le _ _ _ (D3 _ _ x)).
       rewrite <-prec_twice.
       apply real_le_le_plus_le.
       rewrite Heqx0.
       destruct (H2 (S (S n))).
       simpl D.
       destruct a.
       rewrite D2.
       apply real_lt_le.
       replace (S n + 1)%nat with (S (S n)) by lia.
       apply H.
       apply real_lt_le.
       apply (real_lt_le_lt _ _ _ By).
       enough (m = S n)%nat.
       right;rewrite H;auto.
       replace (S (S n)) with (S n +1)%nat by lia;auto.
       apply Nat.ltb_ge in E.
       apply Nat.ltb_lt in E'.
       lia.
       destruct H as [d [D1 [D2 D3 ]]].
       simpl d_X.
       replace (d y y) with 0.
       apply real_lt_le;apply prec_pos.
       apply eq_sym.
       apply D1;auto.
    }
    assert (forall p, metric_is_fast_limit H yn p -> p = y).
    {
      intros.
      apply (metric_limit_unique H (fun n => (yn (S n))));auto.
      intros n.
      apply (real_le_le_le _ _ _ (H6 (S n))).
      apply real_lt_le.
      apply prec_S.
      intros n.
      rewrite Heqyn.
      unfold ball in By.
      destruct H as [d [D1 [D2 D3 ]]].
      simpl d_X in *.
      destruct (S n <?  m)%nat eqn:E.
      apply (real_le_le_le _ _ _ (D3 _ _ x)).
      apply (real_le_le_le _ (prec (S n) + prec (S n))).
      apply real_le_le_plus_le.
      rewrite Heqx0.
      destruct (H2 (S (S (S n)))).
      simpl D.
      destruct a.
      apply real_lt_le.
      rewrite D2.
      apply (real_lt_lt_lt _ _ _ H).
      apply prec_monotone;lia.
      apply real_lt_le.
      apply (real_lt_le_lt _ _ _ By).
      apply Nat.ltb_lt in E.
      apply real_lt_le.
      apply prec_monotone;lia.
      replace (S n) with (n+1)%nat by lia.
      rewrite prec_twice.
      right;auto.
      replace (d y y) with 0.
      apply real_lt_le;apply prec_pos.
      apply eq_sym.
      apply D1;auto.
    }
    assert (forall z, (metric_is_fast_cauchy H z /\ sierp_up (f z)) -> exists p, (metric_is_fast_limit H z p /\ U p)).
    {
      rewrite Heqf.
      intros z [].
      destruct (X2 z).
      simpl in *.
      destruct a.
      apply H10;auto.
    }
    assert (sierp_up (f yn)).
    {
      apply M.
      intros.
      rewrite Heqyn.
      apply Nat.ltb_lt in H8.
      rewrite H8;auto.
    }
    destruct (H7 yn).
    split;auto.
    destruct H9.
    rewrite <- (H6 x1);auto.
 Qed.

  Lemma ball_contains_center H x m : (ball H x m) x.
  Proof.
    unfold ball.
    destruct H;destruct a.
    simpl.
    replace (x0 x x) with 0.
    apply prec_pos.
    apply eq_sym;apply i;auto.
  Qed.


  Lemma open_basis (H : metric) (s : separable) (l : has_limit H) U x : open U -> U x -> ^M {xm : nat * nat | is_subset (ball H  (D s (fst xm)) (snd xm)) U /\ (ball H (D s (fst xm)) (snd xm)) x}.
  Proof.
    intros.
    pose proof (separable_metric_continuous H s l U x X0 H0).
    revert X1.
    apply M_lift_dom.
    intros [m Hm].
    pose proof (separable_metric_approx_inside H s _ _ (metric_open H x m) (ball_contains_center H x m) (m+1)%nat).
    revert X1.
    apply M_lift.
    intros [n [Hn1 Hn2]].
    exists (n,(m+1)%nat).
    simpl.
    clear l.
    destruct H as [d [D1 [D2 D3]]].
    unfold ball in *;simpl in *.
    split; try (rewrite D2;auto).
    intros y.
    intros.
    apply Hm.
    apply (real_le_lt_lt _ _ _ (D3 _ _ (D s n))).
    rewrite <-prec_twice.
    apply real_lt_lt_plus_lt;auto.
  Qed.
    
  Definition base H s n m:= ball H (D s n) m.

  Lemma separable_suff (H :metric) (s : separable) (l : has_limit H) U1 U2 : open U1 -> open U2 -> (forall n, U1 (D s n) <-> U2 (D s n)) -> U1 = U2.
  Proof.
    revert U1 U2.
    enough (forall U1 U2 : csubset, open U1 -> open U2 -> (forall n : nat, U1 (D s n) <-> U2 (D s n)) -> forall x, U1 x -> U2 x).
    - intros.
      apply fun_ext.
      intros.
      apply Prop_ext.
      apply H0;auto.
      apply H0;auto.
      intros n;split; apply H1.
    - intros U1 U2 HU1 HU2 Hs.
      enough (forall n, exists m, is_subset (ball H (D s n) m) (intersection U1 U2)).
      intros.
      (* pose proof (open_basis H s l _ _ X0 H1). *)
      (* apply M_hprop_elim; [(intros a b;apply irrl)|]. *)
      (* revert X2. *)
      (* apply M_lift_dom. *)
      (* intros [[n m] [Hnm1 Hnm2]]. *)
      (* simpl in *. *)
      (* pose proof (open_intersection (metric_open H (D s n) m) X1). *)
      (* assert ((intersection (ball H (D s n) m) U2) (D s n)). *)
      (* { *)
      (*   split. *)
      (*   apply ball_contains_center. *)
      (*   apply H0. *)
      (*   apply Hnm1;apply ball_contains_center. *)
      (* } *)
      (* pose proof (separable_metric_continuous H s l _ _ X2 H2). *)
      (* revert X3. *)
      (* apply M_lift_dom. *)
      (* intros [m' Hnm']. *)
      (* pose proof (separable_metric_approx_inside H s _ _ X0 H1 (m'+1)%nat). *)
Abort.
End Metric.
Section Examples.
  
  Example cantor_exists_open : open (fun (n : (nat -> bool)) => exists m, (n m) = true).
  Proof.
    apply open_countable_union.
    intros n x.
    apply sierp_from_semidec.
    unfold lazy_bool_up.
    destruct (x n).
    exists lazy_bool_true;split;auto.
    exists lazy_bool_false;split;intros;contradict H;auto.
    apply lazy_bool_distinct.
 Qed.

  Definition extends (a : list bool) (x : (nat -> bool)) := forall n, (n < length a)%nat -> x n = nth n a true.

  Lemma one_point_fixed_clopen n b : open (fun (x : (nat -> bool)) => x n = b) * closed (fun (x : (nat -> bool)) => x n = b).
  Proof.
    assert (forall b', {k | (lazy_bool_up _ k) <-> b' = b}).
    {
      intros.
      exists (if (bool_eq b' b) then lazy_bool_true else lazy_bool_false).
      destruct b; destruct b';simpl;unfold lazy_bool_up;split;auto;intros;contradict H; try apply lazy_bool_distinct; try apply Bool.diff_false_true.
      apply Bool.diff_true_false.
    }
    split;intros x.
    destruct (X (x n));apply sierp_from_semidec.
    exists x0;auto.
    destruct (X (negb (x n)));apply sierp_from_semidec.
    exists x0.
    unfold complement.
    rewrite i.
    split;intros.
    rewrite <-H.
    apply neq_sym.
    apply Bool.no_fixpoint_negb.
    unfold lazy_bool_up.
    destruct (x n); destruct b;simpl;auto.
    contradict H;auto.
 Qed.
    

 Lemma extends_intersection a0 a x : extends (a0 :: a) x <-> (x 0%nat) = a0 /\ extends a (fun n => x (S n)).  
  Proof.
    revert a0 x.
    induction a.
    - unfold extends.
      simpl.
      split.
      intros H.
      split.
      destruct (H 0%nat);try lia;auto.
      intros;lia.
      intros [H1 H2] n N.
      rewrite Nat.lt_1_r in N.
      rewrite N;auto.
   - intros.
     rewrite IHa.
     unfold extends.
     split.
     intros.
     split; [|split].
     apply (H 0%nat);simpl;lia.
     apply (H 1%nat);simpl;lia.
     intros.
     apply (H (S (S n))).
     simpl;lia.
     intros [H1 [H2 H3]] n N.
     destruct n;simpl;auto.
     destruct n;simpl;auto.
     apply H3;simpl in *;lia.
  Qed.

  Lemma extends_intersection' a0 a : extends (a0 :: a) = intersection (fun (x : (nat -> bool)) => x O = a0) (fun x => (extends a (fun n => x (S n)))).
  Proof.
    apply fun_ext.
    intros.
    unfold intersection.
    apply Prop_ext;apply extends_intersection.
  Qed.

  Example cantor_base_clopen a : open (extends a) * closed (extends a). 
  Proof.
    induction a.
    - unfold extends.
      split;intros x;apply sierp_from_semidec.
      exists (lazy_bool_true);unfold lazy_bool_up;split;simpl;auto;lia.
      exists (lazy_bool_false);unfold lazy_bool_up.
      split;intros.
      contradict H.
      apply lazy_bool_distinct.
      unfold complement in H.
      contradict H;simpl;lia.
   - rewrite extends_intersection'.
     split.
     apply open_intersection.
     apply one_point_fixed_clopen.
     intros x.
     destruct IHa.
     destruct (o (fun n => x (S n))).
     exists x0;auto.
     apply closed_intersection.
     apply one_point_fixed_clopen.
     destruct IHa.
     intros x.
     destruct (c (fun n => (x (S n)))).
     exists x0;auto.
  Qed.

  (* Cantor space closed => WKL *)

  Definition prefix (L1 L2 : list bool) := exists (L3 : (list bool)), L2 = L1 ++ L2.
  
  Definition binary_tree T := (T []) /\ forall a b, T b -> prefix a b -> T a.

  Definition infinite (T : (list bool -> Prop)) := forall n, exists a, T a /\ (length a >= n)%nat.
  Definition path (T : list bool -> Prop) (p : nat -> bool)  := forall a, extends a p -> T a. 

  Definition decidable (T : (list bool -> Prop)) := forall x, {b : bool | b = true <-> T x}.

  Lemma extends_decidable x : decidable (fun a => (extends a x)).
  Proof.
    intros a.
    revert x.
    induction a.
    exists true.
    split;auto;unfold extends;intros _;simpl;lia.
    intros.
    destruct (IHa (fun n => x (S n))).
    exists (andb (bool_eq (x 0%nat) a) x0).
    rewrite Bool.andb_true_iff.
    rewrite ((extends_intersection a a0 x)).
    rewrite i.
    split;intros [H1 H2];split;auto.
    apply bool_eq_ok;auto.
    rewrite H1;destruct a;auto.
  Qed.

  Definition WKL := forall T, decidable T -> binary_tree T -> infinite T -> exists p,  path T p.

  Lemma enumerable_lists : enumerable (list bool).
  Admitted.

  Lemma path_closed T : (decidable T) -> closed (path T).
  Proof.
    intros H x.
    assert (decidable (fun a => extends a x /\ not (T a))).
    {
      intros a.
      destruct (extends_decidable x a).
      destruct (H a).
      exists (andb x0 (negb x1)).
      rewrite Bool.andb_true_iff.
      rewrite <-i, <-i0.
      rewrite Bool.negb_true_iff.
      rewrite Bool.not_true_iff_false;split;auto.
    }
    destruct (enumerable_lists) as [l L].
    destruct (cantor_exists_open (fun n => (pr1 _ _ (H0 (l n))))).
    exists x0.
    rewrite i.
    split.
    - intros [m M].
      destruct (H0 (l m));simpl in *.
      intros P.
      specialize (P (l m)).
      contradict M.
      rewrite i0.
      intros [H1 H2].
      apply H2;auto.
   - intros.
     unfold complement, path in H1.
     rewrite classical_tautology_neg_all in H1.
     destruct H1.
     destruct (L x1).
     exists x2.
     destruct (H0 (l x2));simpl.
     apply i0.
     apply Classical_Prop.imply_to_and;rewrite e;auto.
  Qed.
  Lemma dense_enumeration_exists : {e : nat -> (nat -> bool) | forall x U,  (open U) -> U x -> exists n, U (e n)}.
  Proof.
     destruct enumerable_lists.
     exists (fun n => (fun m => nth m (x n) false)).
     intros.
  Admitted.

 Definition dense_enumeration := pr1 _ _ dense_enumeration_exists.

 Lemma extends_last a an x : extends (a ++ [an]) x <->  extends a x /\ x (length a) = an.  
 Proof.
   revert x;induction a.
   - simpl.
     split;unfold extends;simpl;intros;try lia.
     split;try lia;auto.
      assert (n = 0)%nat as -> by lia;auto.
      apply H.
   - intros.
     rewrite <-app_comm_cons.
     rewrite !extends_intersection.
     rewrite !IHa.
     simpl.
     split;intros [H1 H2];split;try split;auto;destruct H2;destruct H1;auto.
  Qed.

  Lemma first_n_extends x n  : extends (map x (seq 0 n)) x.
  Proof.
    induction n; [unfold extends;simpl;lia|].
    rewrite seq_S, map_app.
    simpl.
    rewrite extends_last.
    split;auto.
    rewrite map_length, seq_length;auto.
  Qed.

  Definition base : nat -> (@csubset (nat -> bool)).
  Proof.
    intros n.
    destruct enumerable_lists.
    pose proof (extends (x n)) : csubset.
    apply X.
  Defined.

  Lemma base_open : forall n, open (base n).
  Proof.
    intros.
    unfold base.
    destruct enumerable_lists.
    apply cantor_base_clopen.
  Qed.

  Lemma open_nbhd U x : open U -> U x -> ^M ({n | (base n) x /\ is_subset (base n) U}).
  Proof.
    intros.
    remember (fun x => (pr1 _ _ (X x))) as f.
    assert (forall y, sierp_up (f y) <-> U y).
    {
      intros.
      rewrite Heqf.
      destruct (X y).
      simpl;auto.
    }
    assert (sierp_up (f x)) by (apply H0;auto).
    pose proof (continuity  f _ H1).
    revert X0.
    apply M_lift.
    intros [m Hm].
    destruct enumerable_lists eqn:E.
    destruct (s (map x (seq 0 m))).
    exists x1.
    unfold base.
    rewrite E.
    rewrite e.
    split; [apply first_n_extends|].
    intros y Hy.
    apply H0.
    apply Hm.
    intros.
    rewrite Hy; [ | rewrite map_length,seq_length];auto.
    rewrite (nth_indep _  _ (x 0%nat)); [|rewrite map_length,seq_length;auto].
    rewrite map_nth, seq_nth;auto.
  Qed.

  Lemma base_to_list n : {l | base n = extends l}.
  Proof.
    unfold base.
    destruct enumerable_lists.
    exists (x n);auto.
  Qed.

  Lemma contains_lazy_check U : open U -> ^M {t : nat -> nat -> bool | forall m, (exists n, t m n = true) <-> U (dense_enumeration m)}.
  Proof.
    intros.
    unfold dense_enumeration.
    destruct (dense_enumeration_exists).
    assert (^M (forall m, {f : nat -> bool |  (U (x m)) <-> (exists n, f n = true)})).
    {
      apply M_countable_lift.
      intros.
      pose proof (open_to_testfun _ X (x n)).
      apply X0.
    }
    revert X0.
    apply M_lift.
    intros.
    exists (fun m => (pr1 _ _ (H m))).
    intros.
    destruct (H m).
    simpl.
    rewrite i;split; intros[];exists x1;auto.
  Qed.

  Lemma dense_enumeration_base n : (base n) (dense_enumeration n).
  Proof.
    unfold base, dense_enumeration.
    destruct enumerable_lists.
  Admitted.

  Lemma interval_extension U : open U -> ^M {I : nat -> bool | (forall n, I n = true -> is_subset (base n) U) /\ forall x, U x -> exists n, (base n x) /\ (I n) = true}.
  Proof.
    intros.
    pose proof (contains_lazy_check _ X).
    revert X0.
    apply M_lift.
    intros [t T].
  Abort.   
  Lemma dense_covers U x:  open U -> U x -> exists n m, is_subset (base n) U /\ ((base n (dense_enumeration m)) /\ (base n x)).
  Proof.
    intros.
    unfold dense_enumeration.
    destruct (dense_enumeration_exists).
    simpl.
    specialize (e x).
    pose proof (open_nbhd U x X H).
    apply M_hprop_elim_f.
    intros a b.
    apply irrl.
    revert X0.
    apply M_lift.
    intros [n [N1 N2]].
    destruct (e (base n));auto;try apply base_open.
    exists n; exists x1;auto.
  Qed. 

  Definition base_to_subset (n : nat) := match n with
                                       | 0%nat => (fun _ => True)
                                       | (S n') => (base n')
                                       end.

  Lemma open_dense_suffices U1 U2: open U1 -> open U2 -> (forall n, U1 (dense_enumeration n) <-> U2 (dense_enumeration n)) -> (forall x, U1 x <-> U2 x). 
  Proof.
    unfold dense_enumeration.
    destruct (dense_enumeration_exists) eqn:E;simpl.
    intros.
    split.
    intros.
    destruct (dense_covers _ _ X H0) as [n [m [H1 [H2 H3]]]].
    unfold dense_enumeration in *;rewrite E in *;simpl in *.
    
  Abort.
  Lemma cantor_second_countable U : open U -> ^M {c : nat -> option nat | (forall n m, (c n) = Some m -> is_subset (base m) U) /\ (forall x, U x -> exists n m, (c n) = Some m /\ (base m) x)}.
  Proof.
    intros.
    pose proof (contains_lazy_check U X).
    revert X0.
    apply M_lift_dom.
    intros [t T].
    assert (^M (forall m n,  {i | t m n = true -> is_subset (base i) U /\ (base i) (dense_enumeration m)})).
    {
      apply M_countable_lift;intros m;apply M_countable_lift;intros n.
      intros.
      destruct (t m n) eqn:E.
      assert (U (dense_enumeration m)) by (apply T;exists n;auto).
      pose proof (open_nbhd _ _  X H).
      revert X0.
      apply M_lift.
      intros [i [I1 I2]];exists i;auto.
      apply M_unit.
      exists 0%nat.
      intros;contradict H.
      apply Bool.diff_false_true.
    }
    revert X0.
    apply M_lift.
    intros.
   Abort.
   (*  assert (forall x, U x -> exists m n, base (pr1 _ _ (H m n)) x). *)
   (*  { *)
   (*    intros. *)
   (*    destruct (dense_covers _ _ X H0). *)
      
   (*  } *)
   (*  destruct (enumerable_pair _ _ enumerable_nat enumerable_nat). *)
   (*  exists (fun n => match (t (fst (x n)) (snd (x n))) with | true => Some (pr1 _ _ (H (fst (x n)) (snd (x n)))) | false => None end). *)
   (*  split. *)
   (*  - intros. *)
   (*    destruct (H (fst (x n)) (snd (x n))). *)
   (*    destruct (t (fst (x n)) (snd (x n))) eqn:E. *)
   (*    simpl in *. *)
   (*    intros. *)
   (*    destruct a;auto. *)
   (*    injection H0. *)
   (*    intros <-;auto. *)
   (*    discriminate H0. *)
   (*  - intros. *)
   (*    destruct (dense_covers _ _ X H0) as [i [m H1]]. *)
   (*    assert (exists n, t m n = true) as [n N]. *)
   (*    { *)
   (*      apply T. *)
   (*      destruct H1. *)
   (*      apply H1;apply H2. *)
   (*    } *)
   (*    destruct (s (m,n)). *)
   (*    exists x1. *)
   (*    destruct (H m n) eqn:H'. *)
   (*    exists x2. *)
   (*    rewrite e;simpl. *)
   (*    rewrite H'. *)
   (*    simpl. *)
   (*    rewrite N. *)
   (*    split;auto. *)
      
   (*  assert (^M (forall m n, {b : option (list bool) | (f m n = false -> b = None) /\ (f m n = true ->  exists l, b = Some l /\ (extends l (x m)) /\ is_subset (extends l) U)})). *)
   (*  { *)
   (*    apply M_countable_lift;intros m;apply M_countable_lift;intros n. *)
   (*    destruct (f m n) eqn:E. *)
   (*    admit. *)
   (*    - apply M_unit. *)
   (*      exists None. *)
   (*      split;auto. *)
   (*      intros;contradict H0. *)
   (*      apply Bool.diff_false_true. *)
   (*  } *)
   (*  revert X0. *)
   (*  apply M_lift. *)
   (*  intros. *)
   (*  exists (fun n => (pr1 _ _ (H0 (fst (x0 n)) (snd (x0 n))))). *)
   (*  split. *)
   (*  - intros. *)
   (*    destruct (H0 (fst (x0 n)) (snd (x0 n))). *)
   (*    simpl in *. *)
   (*    destruct a. *)
   (*    destruct (f (fst (x0 n)) (snd (x0 n))). *)
   (*    destruct H3;auto. *)
   (*    replace b with x2. *)
   (*    apply H3. *)
   (*    destruct H3. *)
   (*    assert (Some x2 = Some b) by (rewrite <- H1, <- H3;auto). *)
   (*    inversion H5;auto. *)

   (*    contradict H1. *)
   (*    rewrite H2;auto. *)
   (*    discriminate. *)
   (* -  intros. *)
   (*    assert ({b | (extends b) x1 /\ is_subset (extends b) U}). *)
   (*    admit. *)
   (*    destruct H2. *)
   (*    destruct (cantor_base_clopen x2). *)
   (*    destruct a. *)
   (*    destruct (e x1 _ o);auto. *)
   (*    assert (U (x x3)). *)
   (*    admit. *)
   (*    destruct (F2 _ H5). *)
   (*    destruct (e0 (x3,x4)). *)
   (*    exists x5. *)
   (*    rewrite H7;simpl. *)
   (*    destruct (H0 x3 x4). *)
   (*    simpl in *. *)
   (*    destruct a. *)
   (*    destruct (H9 H6). *)
   (*    exists x7;split;try apply H7. *)
      
  (* Lemma cantor_space_compact : (@compact (nat -> bool) (fun x => True)). *)
  (* Proof. *)
  (*   intros U H. *)
  (*   destruct  *)
  (* Axiom continuity : forall X (f : (nat -> X) -> sierp) (x : (nat -> X)),   *)

  (* Definition pair_nat : nat -> nat -> nat. *)
  (* Proof. *)
  (*   intros n m. *)
  (*   destruct (enumerable_pair _ _ enumerable_nat enumerable_nat). *)
  (*   specialize (e (n,m)). *)
  (*   Search (exists _ , _) ({_ | _}). *)
  (*   apply ConstructiveEpsilon.constructive_indefinite_ground_description_nat_direct in e. *)
  (*   destruct e. *)
  (*   apply x0. *)
  (*   intros. *)
  (*   destruct (x n0). *)
  (*   simpl. *)
  (*   destruct (Nat.eq_dec n1 n)  as [-> |];auto. *)
  (*   destruct (Nat.eq_dec n2 m)  as [-> |];auto. *)
  (*   right. *)
  (*   rewrite pair_equal_spec;intros [];auto. *)
  (*   right. *)
  (*   rewrite pair_equal_spec;intros [];auto. *)
  (* Defined. *)

  (* Lemma continuous_sequence_to_sierp X (f : (nat -> X) -> sierp) (x : nat -> X) : is_totally_represented_space X -> sierp_up (f x) -> {m | forall y, (forall n, (n <= m)%nat -> x n = y n) -> sierp_up (f y)}. *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct (totally_represented_sequence _ X0) as [r R]. *)
  (*   assert {g : (nat -> nat) -> sierp | forall x, sierp_up (g x) <-> sierp_up (f (r x))} as [g G]. *)
  (*   admit. *)
  (*   destruct (R x) as [x0 [R1 R2]]. *)
  (*   destruct (continuous_baire_to_sierp g x0) as [m M]. *)
  (*   apply G;rewrite R1;auto. *)
  (*   exists m. *)
  (*   intros. *)
  (*   destruct (R y) as [y0 [R1' R2']]. *)
  (*   rewrite <- R1'. *)
  (*   apply G. *)
  (*   apply M. *)
  (*   intros. *)
  (*   intros. *)
    
  (* Lemma continuous_baire2_to_sierp (f : (nat -> nat -> nat) -> sierp) (x : nat -> (nat -> nat)) : sierp_up (f x) -> {m | forall y, (forall n, (n <= m)%nat -> x n = y n)  ->  sierp_up (f y) }. *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct (continuous_baire_to_sierp (fun (x : nat -> nat) => (f (fun n m => x (pair_nat n m)))) (fun n => x (unpair_nat1 n) (unpair_nat2 n))). *)
  (*   - replace (fun n m => x (unpair_nat1 (pair_nat n m)) (unpair_nat2 (pair_nat n m))) with x;auto. *)
  (*     apply fun_ext;intros;apply fun_ext;intros. *)
  (*     rewrite pair_unpair1, pair_unpair2;auto. *)
  (*   - exists x0. *)
  (*     intros. *)
  (*     specialize (s (fun n => (y (unpair_nat1 n) (unpair_nat2 n)))). *)
  (*   replace y with (fun n m => y (unpair_nat1 (pair_nat n m)) (unpair_nat2 (pair_nat n m))). *)
  (*   apply s. *)
  (*   intros. *)
  (*   rewrite H0;auto. *)
  (*   pose proof (unpair_le n). *)
  (*   lia. *)
  (*   apply fun_ext;intros;apply fun_ext;intros. *)
  (*   rewrite pair_unpair1, pair_unpair2;auto. *)
  (* Qed. *)


  (* Lemma continuity_baire : forall (f : ((nat -> nat) -> nat)) (x : (nat -> nat)), {m | forall y,  (forall n, (n <= m)%nat -> x n = y n) -> f x = f y}. *)
  (* Proof. *)
  (*   intros. *)
  (*   assert (forall n y, {s : sierp | sierp_up s <-> f y = n}). *)
  (*   { *)
  (*     intros. *)
  (*     apply sierp_from_semidec. *)
  (*     unfold lazy_bool_up. *)
  (*     destruct (Nat.eq_dec (f y) n); [exists lazy_bool_true | exists lazy_bool_false];split; auto. *)
  (*     intros. *)
  (*     contradict H;apply lazy_bool_distinct. *)
  (*     lia. *)
  (*   } *)
  (*   destruct (continuous_baire_to_sierp (fun y => (pr1 _ _ (X (f x) y))) x). *)
  (*   - destruct (X (f x) x). *)
  (*     apply i;auto. *)
  (*  - exists x0. *)
  (*    intros. *)
  (*    specialize (s y H). *)
  (*    destruct (X (f x) y). *)
  (*    apply eq_sym. *)
  (*    apply i. *)
  (*    apply s. *)
  (* Qed. *)

  (* (* Lemma continuity_baire2 (f : (nat -> nat -> nat) -> nat) (x : nat -> (nat -> nat)) : {m | forall y, (forall n, (n <= m)%nat -> x n = y n)  ->  f x = f y }. *) *)
  (* (* Proof. *) *)
  (* (*   destruct (continuity_baire (fun (x : nat -> nat) => (f (fun n m => x (pair_nat n m)))) (fun n => x (unpair_nat1 n) (unpair_nat2 n))). *) *)
  (* (*   exists x0. *) *)
  (* (*   intros. *) *)
  (* (*   specialize (e (fun n => (y (unpair_nat1 n) (unpair_nat2 n)))). *) *)
  (* (*   replace x with (fun n m => x (unpair_nat1 (pair_nat n m)) (unpair_nat2 (pair_nat n m))). *) *)
    
  (* (*   replace y with (fun n m => y (unpair_nat1 (pair_nat n m)) (unpair_nat2 (pair_nat n m))). *) *)
  (* (*   apply e. *) *)
  (* (*   intros. *) *)
  (* (*   rewrite H;auto. *) *)
  (* (*   pose proof (unpair_le n). *) *)
  (* (*   lia. *) *)
  (* (*   apply fun_ext;intros;apply fun_ext;intros. *) *)
  (* (*   rewrite pair_unpair1, pair_unpair2;auto. *) *)
  (* (*   apply fun_ext;intros;apply fun_ext;intros. *) *)
  (* (*   rewrite pair_unpair1, pair_unpair2;auto. *) *)
  (* (* Qed. *) *)

  (* Lemma sierp_from_nat_sequence : forall (f : (nat -> nat)), {s : sierp | sierp_up s <-> exists n, f n = 1%nat}. *)
  (* Proof. *)
  (*   intros. *)
  (*   assert (forall n, {s : sierp |  sierp_up s <-> f n = 1%nat}). *)
  (*   { *)
  (*     intros. *)
  (*     apply sierp_from_semidec. *)
  (*     unfold lazy_bool_up. *)
  (*     destruct (Nat.eq_dec (f n) 1%nat); [exists lazy_bool_true | exists lazy_bool_false];split; auto;intros;contradict H;auto. *)
  (*     apply lazy_bool_distinct. *)
  (*   } *)
  (*   destruct (eventually_true (fun n => (pr1 _ _ (X n)))). *)
  (*   exists x. *)
  (*   rewrite i. *)
  (*   split;intros [];exists x0;destruct (X x0);simpl;apply i0;auto. *)
  (* Qed. *)

  (* Axiom sierp_equality : forall s1 s2, sierp_up s1 <-> sierp_up s2 -> s1 = s2.  *)

  (* Lemma continuity_open : forall (f : (nat -> sierp) -> sierp) (x : nat -> sierp), sierp_up (f x) -> ^M {m | forall y, (forall n, (n <= m)%nat -> x n = y n) -> sierp_up (f y)}. *)
  (* Proof. *)
  (*   intros. *)
  (*   assert ({g : (nat -> nat -> nat) -> sierp | (forall y, sierp_up (g y) -> forall s, (forall n, sierp_up (s n) <-> exists m, (y n m) = 1%nat) -> sierp_up (f s)) /\ (forall s, sierp_up (f s) -> (forall y, (forall n, sierp_up (s n) <-> exists m, (y n m) = 1%nat) -> sierp_up (g y)))}) as [g [G1 G2]]. *)
  (*   { *)
  (*     exists (fun x => (f (fun n => (pr1 _ _ (sierp_from_nat_sequence (x n)))))). *)
  (*     split. *)
  (*     - intros. *)
  (*       replace s with (fun n => pr1 _ _ (sierp_from_nat_sequence (y n))). *)
  (*       apply H0. *)
  (*       apply fun_ext. *)
  (*       intros. *)
  (*       destruct (sierp_from_nat_sequence (y x0));simpl. *)
  (*       apply sierp_equality. *)
  (*       rewrite H1,i;split;intros [];exists x2;auto. *)
  (*     - intros. *)
  (*       replace (fun n => pr1 _ _ (sierp_from_nat_sequence (y n))) with s;auto. *)
  (*       apply fun_ext. *)
  (*       intros. *)
  (*       destruct (sierp_from_nat_sequence (y x0));simpl. *)
  (*       apply sierp_equality. *)
  (*       rewrite H1,i;split;intros [];exists x2;auto. *)
  (*     } *)
  (*   pose proof (continuous_baire2_to_sierp g). *)
  (*   assert (forall y, ^M ({x' : nat->nat -> nat | forall n, (sierp_up (y n) <-> exists m, (x' n m) = 1%nat)})).  *)
  (*   { *)
  (*     intros. *)
  (*     assert (forall n, ^M {x' : nat -> nat | sierp_up (y n) <-> exists m, (x' m) = 1%nat}). *)
  (*     - intros. *)
  (*       apply sierp_to_nat_sequence. *)
  (*     - apply M_countable_lift in X. *)
  (*       revert X. *)
  (*       apply M_lift. *)
  (*       intros. *)
  (*       exists (fun n => (pr1 _ _ (H1 n))). *)
  (*       intros. *)
  (*       destruct (H1 n);auto. *)
  (*   } *)
  (*   pose proof (X x). *)
  (*   revert X0. *)
  (*   apply M_lift. *)
  (*   intros [x' H1]. *)
  (*   assert (sierp_up (g x')) by (apply (G2 x);auto). *)
  (*   destruct (H0 _  H2) as [m M]. *)
  (*   exists m. *)
  (*   intros. *)
  (*   assert (^M ({y' : nat -> nat -> nat | (forall n, sierp_up (y n) <-> exists m, (y' n m) = 1%nat) /\ forall n, (n <= m)%nat -> x' n = y' n})). *)
  (*   { *)
  (*     pose proof (X y). *)
  (*     revert X0. *)
  (*     apply M_lift. *)
  (*     intros [y0 Y0]. *)
  (*     exists (fun p => if (p <=? m) then (x' p) else (y0 p)). *)
  (*     split. *)
  (*     - intros. *)
  (*       rewrite Y0. *)
  (*       split; intros [m0 M0]. *)
  (*       + destruct (le_gt_dec n m). *)
  (*         rewrite (leb_correct _ _ l). *)
  (*         rewrite <-H1. *)
  (*         rewrite H3;auto. *)
  (*         apply Y0. *)
  (*         exists m0;auto. *)
  (*         rewrite leb_correct_conv;try lia. *)
  (*         exists m0;auto. *)
  (*      + destruct (le_gt_dec n m). *)
  (*         rewrite (leb_correct _ _ l) in M0. *)
  (*        rewrite <-Y0. *)
  (*        rewrite <-H3;auto. *)
  (*        apply H1. *)
  (*        exists m0;auto. *)
  (*       rewrite leb_correct_conv in M0;try lia. *)
  (*       exists m0;auto. *)
  (*    - intros. *)
  (*      rewrite leb_correct;auto. *)
  (*   } *)
  (*   apply M_hprop_elim_f. *)
  (*   unfold is_hprop. *)
  (*   apply irrl. *)
  (*   revert X0. *)
  (*   apply M_lift. *)
  (*   intros [y' [Y1 Y2]]. *)
  (*   apply (G1 y'). *)
  (*   apply M. *)
  (*   apply Y2. *)
  (*   apply Y1. *)
  (* Qed. *)
  (* Example cantor_closed : closed (fun (x: (nat -> bool)) => forall n, (x n) = true -> forall m, (n <> m)%nat -> (x m) = false). *)
  (* Proof. *)
  (*   intros x. *)
  (*   unfold complement. *)
  (*   destruct (cantor_exists_open x). *)

End Examples.
