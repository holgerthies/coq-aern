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

Axiom baire_choice :
  forall (P : (nat -> nat) -> Type) (f : forall ϕ, ^M (P ϕ)),
    ^M {s : forall ϕ, P ϕ | forall ϕ, M_in (s ϕ) (f ϕ)}.

(*   Definition base H s n m:= ball H (D s n) m. *)

(*   Lemma x_to_name (H : metric) (s : separable) (l : has_limit H) x : ^M {y : nat -> nat | metric_is_fast_limit H (fun m => (D s (y m))) x /\ (forall n, d_X H (D s (y n)) (D s (S (y n))) <= prec (S n))}.   *)
(*   Proof. *)
(*   Admitted. *)

  Definition name_fun (H : metric) (s : separable) U t := (forall p, metric_is_fast_cauchy H (fun m => (D s (p m))) ->  (sierp_up (t p) <-> exists x, metric_is_fast_limit H (fun m => (D s (p  m))) x /\ U x)).
   Lemma open_to_name_fun (H : metric) (s : separable) (l : has_limit H) U : open U ->  {t : (nat -> nat) -> sierp | name_fun H s U t }.
    intros.
    pose proof (extended_limit H l).
    assert (forall (x : nat -> X), {s : sierp | ((not (metric_is_fast_cauchy H x)) -> sierp_up s) /\ (metric_is_fast_cauchy H x -> (sierp_up s <-> exists p, metric_is_fast_limit H x p /\ U p))}).
    {
      intros.
      specialize (X1 x).
      apply M_hprop_elim.
      intros a b.
      destruct a; destruct b.
      enough (x0 = x1) by  (apply sigma_eqP2;auto).
      apply sierp_id.
      destruct a; destruct a0.
      destruct (lem (metric_is_fast_cauchy H x)).
      rewrite H1, H3;auto;split;auto.
      split;intros.
      apply H2;auto.
      apply H0;auto.
      revert X1.
      apply M_lift.
      intros [p P].
      destruct (not_fast_cauchy_semidec H x).      
      destruct (X0 p).
      destruct (sierp_or x0 x1).
      exists x2.
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
      destruct H1;auto.
      contradict H0.
      apply i;auto.
      intros [p' [P1 P2]].
      right.
      apply i0.
      replace p with p';auto.
      specialize (P H0).
      apply (metric_limit_unique H x);auto.
    }
    
    remember (fun n => (pr1 _ _ (X2 n))) as f.
    exists (fun x => f (fun n => (D s (x n)))).
    unfold name_fun; intros.
    rewrite Heqf.
    destruct (X2 (fun n => D s (p n))).
    simpl in *.
    destruct a.
    specialize (H2 H0).
    rewrite H2;split;auto.
  Qed.
  Lemma M_sierp_to_lazy P t : (forall (x : (nat -> nat)), sierp_up (t x) -> ^M {m : nat | P m x}) -> ^M {m : (nat -> nat) -> nat -> nat | forall x,  (forall k, m x k = 0%nat \/ P (pred (m x k)) x) /\ (sierp_up (t x) -> exists k, (m x k) <> 0%nat)}.
  Proof.
    intros.
    enough (^M (forall x, {m : nat -> nat |(forall k, m k = 0%nat \/ P (pred (m k)) x) /\ (sierp_up (t x) -> exists k, (m k) <> 0%nat)})).
    {
    revert X1.
    apply M_lift.
    intros.
    exists (fun n => (pr1 _ _ (H n))).
    intros.
    destruct (H x);simpl in *;auto.
    }
    enough (forall ϕ : nat -> nat,
             ^M
               {m : nat -> nat
               | (forall k : nat, m k = 0%nat \/ P (Init.Nat.pred (m k)) ϕ) /\
                 (sierp_up (t ϕ) -> exists k : nat, m k <> 0%nat)}).
    {
    pose proof (baire_choice (fun x => {m : nat -> nat | (forall k, m k = 0%nat \/ P (pred (m k)) x) /\ (sierp_up (t x) -> exists k, (m k) <> 0%nat) }) X1).
    revert X2.
    apply M_lift.
    intros [].
    apply x.
    }
    intros Phi.
    specialize (sierp_to_nat_sequence  (t Phi)).
    apply M_lift_dom.
    intros [f F].
    enough (forall k, ^M {m | f k = 1%nat /\ (m <> 0)%nat /\ P (pred m) Phi \/ (f k <> 1)%nat /\ m = 0%nat}).
    {
      apply M_countable_lift in X1.
      revert X1.
      apply M_lift.
      intros H.
      exists (fun k => (pr1 _ _ (H k))).
      split.
      intros.
      destruct (H k).
      simpl.
      destruct o; destruct H0;[destruct H1;right|left];auto.
      intros.
      destruct F.
      destruct (H1 H0).
      exists x.
      destruct (H x).
      simpl in *.
      destruct o.
      destruct H4;destruct H5;auto.
      contradict H3.
      apply H4.
    }
    intros.
    destruct ((f k) =? 1%nat) eqn:E.
    destruct F.
    assert (sierp_up (t Phi)) by (apply H0; exists k; apply Nat.eqb_eq;auto).
    specialize (X0 _ H1).
    revert X0.
    apply M_lift; intros [].
    exists (S x).
    simpl.
    left;split.
    apply Nat.eqb_eq;auto.
    split;try lia;auto.
    apply M_unit.
    exists 0%nat.
    right.
    split;auto.
    apply Nat.eqb_neq;auto.
  Qed.

  Lemma M_sierp_to_lazy_unique P t : (forall (x : (nat -> nat)), sierp_up (t x) -> ^M {m : nat | P m x}) -> ^M {m : (nat -> nat) -> nat -> nat | forall x,  (forall k, m x k = 0%nat \/ P (pred (m x k)) x) /\ (sierp_up (t x) -> (exists k, (m x k) <> 0%nat) /\ (forall k, m x k <> 0%nat -> forall k', (k <> k') -> m x k' = 0%nat)) }.
  Proof.
    intros.
    specialize (M_sierp_to_lazy P t X0).
    apply M_lift.
    intros [m Pm].
    enough (forall x k, {n | ((n = 0%nat) \/ n = m x k) /\ (n <> 0%nat <-> ((m x k <> 0)%nat /\ forall i, (i < k)%nat -> m x i = 0%nat))}).
    {
      exists (fun x k => pr1 _ _ (H x k)).
      intros.
      split;intros.
      - destruct (H x k) as [n [N1 N2]];simpl.
        destruct N1.
        left;auto.
        destruct n.
        left;auto.
        right.
        destruct N2.
        rewrite H0.
        destruct (Pm x) as [Pm' _].
        specialize (Pm' k).
        destruct Pm';try lia;auto.
      - pose proof (proj2 (Pm x) H0).
        destruct (dec_inh_nat_subset_has_unique_least_element (fun k => m x k <> 0%nat)) as [k K];intros;try lia;try apply H1.
        split.
        + exists k.
          destruct (H x k) as [n [N1 N2]];simpl in *.
          apply N2.
          split; try apply K.
          intros.
          destruct K.
          destruct H3.
          specialize (H5 i).
          destruct (m x i);auto.
          contradict H2.
          apply Nat.nlt_ge.
          apply H5;auto.
       + intros.
          assert (k0 = k) as ->.
          {
          apply eq_sym.
          apply K.
          destruct (H x k0); simpl in *.
          destruct a.
          destruct H4;try lia.
          split;try lia.
          intros.
          destruct H5.
          specialize (H5 H2).
          destruct H5.
          apply Nat.nlt_ge.
          intros N.
          contradict H6.
          apply H8;auto.
          }
          destruct (H x k') as [n' [N1' N2']];simpl.
          simpl in *.
          destruct N1';auto.
          destruct n';auto.
          destruct N2'.
          clear H6.
          destruct K.
          destruct H6.
          destruct (Lt.nat_total_order_stt _ _ H3).
          contradict H6.
          apply H5;auto.
          assert (m x k' <> 0%nat) by lia.
          specialize (H8 _ H10).
          lia.
        }
        intros.
        enough ({b | b = true <-> forall i, (i < k)%nat -> m x i = 0%nat}) as [b B].
        exists (match (m x k) with 0%nat => 0%nat | (S n') => if b then (S n') else 0%nat end).
        destruct (m x k).
        split;auto;split;intros;[split|];try lia;auto.
        destruct b;split;auto;split;auto;try lia.
        intros;split;auto;intros;apply B;auto.
        intros [_ H2].
        destruct B.
        specialize (H0 H2).
        contradict H0;apply Bool.diff_false_true.

        induction k.
        exists true.
        split;auto;intros _; lia.
        destruct IHk.
        exists (andb x0 (m x k =? 0)%nat).
        split;intros.
        apply andb_prop in H.
        rewrite Nat.lt_succ_r in H0.
        destruct H.
        apply Nat.eqb_eq in H1.
        destruct (Lt.le_lt_or_eq_stt _ _ H0).
        apply i;auto.
        rewrite H2;auto.
        apply Bool.andb_true_iff.
        split.
        apply i;auto.
        apply Nat.eqb_eq.
        apply H;lia.
  Qed.
  Lemma baire_continuity (f : (nat->nat) -> nat -> nat) : ^M ( forall x n,  {m |forall y, (forall i, (i < m)%nat -> x i = y i) -> (forall i, (i < n)%nat -> f x i = f y i)}).
   Proof.
     assert (forall n m, {fn : (nat -> nat) -> sierp | forall x, sierp_up (fn x) <-> f x n = m}).
     {
         intros.
         enough (forall x, {s : sierp | sierp_up s <-> f x n = m}) as H. (exists (fun x => (pr1 _ _ (H x))); intros x; destruct (H x);auto).
         intros.
         apply sierp_from_semidec.
         unfold lazy_bool_up.
         destruct (f x n =? m) eqn:E.
         exists lazy_bool_true;rewrite <-Nat.eqb_eq;split;auto.
         exists lazy_bool_false.
         split;intros.
         contradict H;apply lazy_bool_distinct.
         rewrite Nat.eqb_neq in E;lia.
     }
     assert (forall x,  ^M (forall n, {k : nat | forall y, (forall i : nat, (i < k)%nat -> x i = y i) -> (forall i, (i < n)%nat ->  f x i = f y i)})).
     {
       intros.
       apply M_countable_lift.
       intros.
       induction n.
       - apply M_unit.
         exists 0%nat.
         intros;lia.
       - revert IHn.
         apply M_lift_dom.
         intros [k0 K0].
         destruct (X0 n (f x n)) as [fn F].
         assert (sierp_up (fn x)) by (apply F;auto).
         specialize (continuity fn _ H).
         apply M_lift.
         intros [k K].
         exists (max k k0).
         intros.
         assert (i < n \/ i = n)%nat by lia.
         destruct H2.
         apply K0;intros;auto.
         apply H0;lia.
         rewrite H2.
         apply eq_sym.
         apply F.
         apply K;auto.
         intros.
         apply H0;lia.
      }
      specialize (baire_choice _ X1).
      apply M_lift.
      intros [X2 _].
      apply X2.
   Qed.
  (* Lemma partial_baire_continuity P t : (forall (x : (nat -> nat)), sierp_up (t x) -> ^M {m : nat | P m x}) -> ^M {f: {x | sierp_up (t x)} -> nat | forall x, P (f x) (pr1 _ _ x) /\ forall y, (forall i, (i < (f x))%nat -> (pr1 _ _ x i) = (pr1 _ _ y i)) -> f x = f y}. *)
  (* Proof. *)
  (*   intros. *)
  (*   Search M. *)
  (*   assert (forall (x : (nat -> nat)), ^M ((sierp_up (t x)) -> {m : nat | P m x})). *)
  (*   intros. *)
  (*   specialize (X0 x). *)
  (*   pose proof (M_lift_dom (sierp_up (t x)) ({m | P m x}) X0). *)
  (*   Search M.      *)
  (*   apply M *)
  (*   revert X1. *)
  (*   Search (M _ -> M _). *)
  (*   apply M_lift in X0. *)
  (*   apply M_sierp_to_lazy in X0. *)
  (*   revert X0. *)
  (*   apply M_lift_dom. *)
  (*   intros [m Pm]. *)
  (*   specialize (baire_continuity m). *)
  (*   apply M_lift. *)
  (*   intros H. *)
  (*   assert ({mu | forall x n, forall y, (forall i, (i < mu x n)%nat -> x i = y i) -> (forall i, (i < n)%nat -> m x i  = m y i)}) as [mu M1]. *)
  (*   admit. *)
  (*   clear H. *)
  (*   assert (forall (y : {x | sierp_up (t x)}), {k | m (pr1 _ _ y) k <> 0%nat}). *)
  (*   admit. *)
  (*   assert ({g : {x : nat -> nat | sierp_up (t x)} -> nat | forall x, m (pr1 _ _ x) (g x) <> 0 %nat}) as [g G]. *)
  (*   { *)
  (*     exists (fun x => (pr1 _ _ (H x))). *)
  (*     intros. *)
  (*     destruct (H x). *)
  (*     destruct x. *)
  (*     simpl in *. *)
  (*     apply n. *)
  (*   } *)

  (*   exists (fun x => (max (pred (m (pr1 _ _ x) (g x))) (mu (pr1 _ _ x) (m (pr1 _ _ x) (g x))))). *)
  (*   intros. *)
  (*   specialize (G x). *)
  (*   destruct (H x). *)
  (*   destruct x. *)
  (*   simpl in *. *)
  (*   split. *)
  (*   - specialize (Pm x). *)
  (*     destruct Pm. *)
  (*     destruct (H0  (g (exist (fun x1 : nat -> nat => sierp_up (t x1)) x s))); try lia;auto. *)
  (*  - intros. *)
     
  Definition enumerates_subset s (s' : nat ->nat) U := (forall n, (s' n) = 0%nat \/ U (D s (pred (s' n)))) /\ forall m, U (D s m) -> exists k, (s' k) = (S m).

  Lemma enumerate_open (H : metric) (s : separable) U : open U -> ^M {s' : nat -> nat | enumerates_subset s s' U}.
  Proof.
    intros.
    assert (^M {f : nat -> nat -> nat | forall n,  U (D s n) <-> exists k, f n k = 1%nat}).
    {
      enough (^M (forall n, {g : nat -> nat | U (D s n) <-> exists k, g k = 1%nat})).
      revert X1.
      apply M_lift.
      intros.
      exists (fun n => pr1 _ _ (H0 n)).
      intros.
      destruct (H0 n);simpl in *;auto.
      apply M_countable_lift.
      intros.
      destruct (X0 (D s n)).
      specialize (sierp_to_nat_sequence x).
      apply M_lift.
      intros [g G].
      exists g.
      rewrite <-G.
      rewrite i;split;auto.
    }
    revert X1.
    apply M_lift.
    intros [f F].
    destruct (enumerable_pair _ _ enumerable_nat enumerable_nat).
    exists (fun n => if (f (fst (x n)) (snd (x n)) =? 1)%nat then (S (fst (x n))) else 0%nat).
    split.
    - intros.
      destruct (x n);simpl.
      destruct (f n0 n1 =? 1)%nat eqn:E; [|left;auto].
      right.
      apply F.
      exists n1;simpl.
      apply Nat.eqb_eq;auto.
   - intros.
     destruct (proj1 (F m));auto.
     destruct (s0 (m,x0)).
     exists x1.
     rewrite e;simpl;rewrite H1;auto.
  Qed.

  Lemma enumerable_list {A}  : enumerable A -> enumerable (list A).
  Proof.
   intros.
   enough (forall n, {f : nat -> list A & ( forall l, length l = n -> {m | f m = l})}).
   {
     destruct (enumerable_pair _ _ enumerable_nat enumerable_nat) as [e E].
     exists (fun n => (projT1 (X1 (fst (e n)))) (snd (e n))).
     intros.
     destruct (X1 (length x)) eqn:Ex.
     destruct (s x);auto.
     destruct (E (length x, x1)).
     exists x2.
     rewrite e1;simpl.
     rewrite Ex.
     simpl;auto.
   }
   intros.
   induction n.
   exists (fun n => []).
   intros.
   exists 0%nat;auto.
   rewrite length_zero_iff_nil in H.
   rewrite H;auto.
   
   destruct (enumerable_pair _ _ enumerable_nat X0) as [f F].
   destruct IHn.
   exists (fun n => cons (snd (f n)) (x (fst (f n)))).
   intros.
   destruct l;simpl in H; try lia.
   injection H.
   intros H'.
   destruct (s _ H').
   destruct (F (x0, a)).
   exists x1.
   rewrite e0.
   simpl.
   rewrite e;auto.
 Qed.
  Definition baire_base l := fun n => nth n l (last l 0%nat).

  Lemma enumerate_baire_open (P : (nat -> nat) -> sierp) : ^M {s' : nat -> option (list nat) |  (forall n, forall l, s' n = Some l -> sierp_up (P (baire_base l))) /\ (forall l, sierp_up (P (baire_base l)) -> exists n, s' n = Some l)}.
  Proof.
     destruct (enumerable_list enumerable_nat) as [e E].
     enough (^M (forall l, {f : nat -> nat | sierp_up (P (baire_base l)) <-> exists k, f k = 1%nat})).
     {
       revert X0.
       apply M_lift.
       intros.
       destruct (enumerable_pair _ _ enumerable_nat enumerable_nat) as [v V].
       remember (fun n m => pr1 _ _ (H n) m) as f.
       exists (fun n => if (f (e (fst (v n))) (snd (v n)) =? 1%nat) then Some (e (fst (v n))) else None).
       rewrite Heqf.
       split;simpl; intros;simpl.
       -
         replace l with  (e (fst (v n))).
         destruct (H (e (fst (v n))));simpl in *.
         rewrite i.
         destruct ( x (snd (v n)) =? 1 )%nat eqn:Eq;simpl;try discriminate;intros.
         exists (snd (v n)); apply Nat.eqb_eq;auto.
         destruct (H (e (fst (v n)))); simpl in *.
         destruct (x (snd (v n)) =? 1); simpl in *.
         injection H0;auto.
         discriminate H0.
      - destruct (E l) as [m M].
        destruct (H l) as [g [G1 G2]] eqn:El.
        simpl in *.
        destruct (G1 H0).
        destruct (V (m,x)) as [n N].
        exists n.
        rewrite N;simpl; rewrite M.
        rewrite El;simpl;rewrite H1;auto.
   }
   assert (^M (forall n, {f : nat -> nat | sierp_up (P (baire_base (e n))) <-> exists k, f k = 1%nat})).
     {
       apply M_countable_lift.
       intros.
       specialize (sierp_to_nat_sequence (P (baire_base (e n))));auto.
     }
     revert X0.
     apply M_lift.
     intros.
     destruct (E l).
     destruct (H x) as [f F].
     exists f.
     rewrite <-e0.
     apply F.
  Qed.
  
  Lemma fast_limit_fast_cauchy H xn x : metric_is_fast_limit H xn x -> metric_is_fast_cauchy H xn.
  Proof.
    intros H0 n m.
    destruct H as [d [D1 [D2 D3]]].
    unfold metric_is_fast_limit in H0.
    simpl in *.
    apply (real_le_le_le _ _ _ (D3 _ _ x )).
    apply (real_le_le_plus_le); [ |rewrite D2];apply H0.
  Qed.

  Lemma continuity_semidec_eq {A B : Type} (f : (nat -> A) -> B) : (forall (y y' : B), (semidec (y = y'))) -> forall x, ^M {k | forall x', (forall n, (n < k)%nat -> x n = x' n) -> f x = f x'}.  
  Proof.
    intros.
    assert ({e : B -> B -> sierp | forall y y', sierp_up (e y y') <-> y = y'}) as [e E].
    {
      enough (forall (y y' : B), {s | sierp_up s <-> y = y'}) by (exists (fun y y' => (pr1 _ _ (X1 y y')));intros;destruct (X1 y y');auto).
      intros.
      apply sierp_from_semidec.
      destruct (X0 y y').
      exists x0;auto.
    }
    assert (forall y, {g : (nat -> A) -> sierp | forall x, sierp_up (g x) <-> (f x) = y}).
    {
      intros.
      exists (fun x => e (f x) y).
      intros.
      rewrite E;split;auto.
    }
    destruct (X1 (f x)).
    assert (sierp_up (x0 x)) by (apply i;auto).
    specialize (continuity _ _ H).
    apply M_lift.
    intros [k K].
    exists k.
    intros.
    apply eq_sym.
    apply i.
    apply K;auto.
  Qed.
  Lemma semidec_to_sierp {A} (P: A -> Prop ): (forall x, semidec (P x)) -> {t | forall x, sierp_up (t x) <-> P x}.
  Proof.
      intros.
      enough (forall x, {s | sierp_up s <-> P x}) by (exists (fun x => pr1 _ _  (X1 x));intros;destruct (X1 x);simpl;auto).
      intros.
      destruct (X0 x).
      apply sierp_from_semidec.
      exists x0;auto.
  Qed.

  Lemma partial_baire_choice :
  forall  (P : (nat -> nat) -> Prop) (Q : nat -> (nat -> nat) -> Prop), (forall x, semidec (P x)) ->  (forall x, P x -> ^M {n | Q n x}) -> (^M (forall x, P x -> {n | Q n x})).
  Proof.
    intros.
    destruct (semidec_to_sierp P) as [t T];auto.
    assert (forall x, sierp_up (t x) -> ^M {n | Q n x}) as H by (intros; apply X1;apply T;auto).
    clear X0 X1.
    apply M_sierp_to_lazy_unique in H.
    revert H.
    apply M_lift.
    intros [m Pm] x Px.
    destruct (Pm x).
    apply T in Px.
    destruct (H0 Px).
    assert {k | m x k <> 0%nat} as [k K].
    apply ConstructiveEpsilon.constructive_indefinite_ground_description_nat;auto;intros; destruct (m x n);auto.
    exists (pred (m x k)).
    destruct (H k); try lia;auto.
  Qed.
  
  (* Lemma baire_modulus_exists (f : (nat -> nat) -> sierp) : ^M {mu : {x : (nat -> nat) | sierp_up (f x)} -> nat | forall x y, (forall n, (n < mu x)%nat -> pr1 _ _ x n =  y n) -> sierp_up (f y)}.   *)
  (* Proof. *)
  (*   pose proof (continuity f). *)
  (*   apply partial_baire_choice in X0. *)
  (*   revert X0. *)
  (*   apply M_lift. *)
  (*   intros. *)
  (* Admitted. *)

  Lemma continuity_partial P (f : ({x : nat -> nat | P x} -> nat)) : (forall x, semidec (P x)) -> forall x, ^M {k | forall x', (forall n, (n < k)%nat -> (pr1 _  _ x) n = (pr1 _ _ x') n) -> f x = f x'}.  
    intros.
    assert (^M {g : (nat -> nat) -> nat -> nat | (forall x, P x -> exists k,  g x k <> 0%nat ) /\ forall x  (H : P x) k, g x k <> 0%nat -> g x k = S (f (exist _ x H))}).
    {
      destruct (semidec_to_sierp P) as [t T];auto.
      enough (forall x, ^M {s : nat -> nat | (sierp_up (t x) -> exists k, s k <> 0%nat) /\ (forall H k, s k <> 0%nat -> s k = S (f (exist _ x H)))}).
      {
      pose proof (baire_choice _ X1).
      simpl in X2.
      revert X2.
      apply M_lift.
      intros [H S].
      exists (fun x => pr1 _ _ (H x)).
      split; intros;try rewrite <-T;destruct (H x0);destruct a;simpl in *;auto.
      apply e;apply T;auto.
      }
      intros.
      specialize (sierp_to_nat_sequence (t x0)).
      apply M_lift.
      intros [s Ps].
      assert (forall (n:nat), {m | ((s n) = 1%nat -> forall (H : P x0), m = S (f (exist _ x0 H))) /\ ((m <> 0)%nat -> (s n=1)%nat)}).
      {
        intros.
        destruct (Nat.eq_dec (s n) 1%nat).
        assert (sierp_up (t x0)) by (apply Ps; exists n;auto).
        assert (P x0) by (apply T;auto).
        exists (S (f (exist _ x0 H0))).
        split.
        intros.
        apply f_equal; apply f_equal.
        apply sigma_eqP2;auto.
        intros;auto.
        exists 0%nat;intros;lia.
      }
      exists (fun n => (pr1 _ _ (H n))).
      split.
      - intros.
        destruct Ps.
        destruct (H1 H0).
        exists x1. destruct (H x1);simpl in *.
        assert (P x0) by (apply T;auto).
        destruct a.
        rewrite (H5 H3 H4);lia.
     - intros.
       destruct (H k); simpl in *.
       destruct a.
       assert (P x0) by (apply T;apply Ps;exists k;auto).
       rewrite (H2 (H3 H1) H4).
       apply f_equal;apply f_equal.
       apply sigma_eqP2;auto.
    }
    revert X1.
    apply M_lift_dom.
    intros [g G].
    specialize  (baire_continuity g).
    apply M_lift.
    intros.
    destruct x.
    simpl in *.
    destruct G.
    assert {k | g x k <> 0%nat} as [k K].
    apply ConstructiveEpsilon.constructive_indefinite_ground_description_nat;auto;intros; destruct (g x n);auto.
    destruct (H x (S k)) as [m Pm].
    exists m.
    intros.
    destruct x'.
    simpl in *.
    enough (g x0 k <> 0%nat).
    apply Nat.succ_inj.
    rewrite <- (H1 x p k K).
    rewrite <-(H1 x0 _ k H3).
    apply Pm;try lia.
    intros.
    apply H2;auto.
    rewrite <-Pm;try lia;auto.
  Qed.
  Lemma semidec_sierp_up s : semidec (sierp_up s).
  Proof.
     destruct s.
     unfold sierp_up, semidec, lazy_bool_up.
     simpl.
     exists x;split;auto.
  Qed.

  Lemma initial_sequence x n : {l | (forall i, (i < n)%nat -> x i = (baire_base l i)) /\ length l = n}.
  Proof.
    induction n; [exists [];split;try lia;auto|].
    destruct IHn as [l [IH1 IH2]].
    exists (l ++ [x n]).
    intros.
    assert (length (l ++ [x n]) = S n) by (rewrite app_length;simpl;lia).
    split;auto.
    intros.
    rewrite Nat.lt_succ_r in H0.
    apply Lt.le_lt_or_eq_stt in H0.
    destruct H0;unfold baire_base.
    rewrite app_nth1;try lia.
    rewrite (nth_indep _ _ (last l 0%nat));try lia.
    apply IH1;auto.
    rewrite H0.
    replace n with (length l) at 2.
    rewrite nth_middle;auto.
  Qed.


  (* Lemma initial_sequence_close H s x x' n : metric_is_fast_limit H (fun i => (D s (x i))) x' -> metric_is_fast_limit H (fun i => (D s (baire_base (pr1 _ _ (initial_sequence x (S n))) i))) (D s (x n)). *)
  (* Proof. *)
  (* Admitted. *)
 (*  Lemma baire_continuous_modulus (P : (nat -> nat) -> sierp) : ^M {m : {x | sierp_up (P x)} -> nat | (forall x y, (forall n, (n < m x)%nat -> pr1 _ _ x n = y n) ->  (sierp_up (P y)))  /\ forall x, exists y, (exists M, forall i,  (i >= M)%nat -> pr1 _ _ y i = 0%nat) /\  m y = m x}.  *)
 (*  Proof. *)
 (*    pose proof (continuity P). *)
 (*    apply partial_baire_choice in X0; [|intros;apply semidec_sierp_up]. *)
 (*    revert X0. *)
 (*    apply M_lift. *)
 (*    intros. *)
 (*    assert (forall (x : {x | sierp_up (P x)}), sierp_up (P (pr1 _ _ x))) by (intros [x Hx];auto). *)
 (*    remember (fun x => pr1 _ _ (H _ (H0 x))) as f. *)
 (*    assert (forall x, semidec (sierp_up (P x))) by (intros; apply semidec_sierp_up). *)
 (*    pose proof (continuity_partial _ f X0). *)
 (*    exists f;simpl. *)
 (*    rewrite Heqf in *; simpl in *;split; intros. *)
 (*    destruct (H _ (H0 x)); simpl in *. *)
 (*    apply s. *)
 (*    intros;auto. *)
 (*    apply M_hprop_elim. *)
 (*    intros a b; apply irrl. *)
 (*    specialize (X1 x). *)
 (*    revert X1. *)
 (*    apply M_lift. *)
 (*    intros [k K]. *)
 (*    destruct (H _ (H0 x)) as [m Pm];simpl in *. *)
 (*    assert (exists y, (forall i, (((i < k) \/ (i < m))%nat -> y i = pr1 _ _ x i) /\ ((i >= max k m)%nat -> y i = 0%nat))) as [y Py]. *)
 (*    { *)
 (*      exists (fun i => if ((i <? k)%nat || (i <? m)%nat)%bool then pr1 _ _ x i else 0%nat). *)
 (*      intros. *)
 (*      split;intros. *)
 (*      -  rewrite <-!Nat.ltb_lt in H1. *)
 (*         apply Bool.orb_true_intro in H1. *)
 (*         rewrite H1;auto. *)
 (*     - pose proof (Nat.max_lub_r _ _ _ H1). *)
 (*       pose proof (Nat.max_lub_l _ _ _ H1). *)
 (*       apply Nat.ltb_ge in H2. *)
 (*       apply Nat.ltb_ge in H3. *)
 (*       rewrite H2, H3;auto. *)
 (*    } *)
 (*    assert (sierp_up (P y)). *)
 (*    { *)
 (*      apply Pm. *)
 (*      intros. *)
 (*      destruct x;simpl in *. *)
 (*      destruct (Py n). *)
 (*      apply eq_sym;apply H2;auto. *)
 (*    } *)
 (*    exists (exist _ y H1). *)
 (*    simpl. *)
 (*    split; [exists (max k m);intros;apply Py;auto|]. *)
 (*    specialize (K (exist _ y H1)). *)
 (*    apply eq_sym. *)
 (*    apply K. *)
 (*    destruct x; simpl in *. *)
 (*    intros. *)
 (*    apply eq_sym. *)
 (*    apply Py;auto. *)
 (* Qed. *)

  Definition to_initial_sequence x n := baire_base (pr1 _ _ (initial_sequence x n)).

  Lemma baire_continuous_modulus (P : (nat -> nat) -> sierp) : ^M {m : {x | sierp_up (P x)} -> nat | (forall x y, (forall n, (n < m x)%nat -> pr1 _ _ x n = y n) ->  (sierp_up (P y)))  /\ forall x, exists n0, forall n, (n > n0)%nat -> exists (H : sierp_up (P (to_initial_sequence (pr1 _ _ x) n))), m (exist _ (to_initial_sequence (pr1 _ _ x) n) H) = m x}.
  Proof.
    pose proof (continuity P).
    apply partial_baire_choice in X0; [|intros;apply semidec_sierp_up].
    revert X0.
    apply M_lift.
    intros.
    assert (forall (x : {x | sierp_up (P x)}), sierp_up (P (pr1 _ _ x))) by (intros [x Hx];auto).
    remember (fun x => pr1 _ _ (H _ (H0 x))) as f.
    assert (forall x, semidec (sierp_up (P x))) by (intros; apply semidec_sierp_up).
    pose proof (continuity_partial _ f X0).
    exists f;simpl.
    rewrite Heqf in *; simpl in *;split; intros.
    destruct (H _ (H0 x)); simpl in *.
    apply s.
    intros;auto.
    apply M_hprop_elim.
    intros a b; apply irrl.
    specialize (X1 x).
    revert X1.
    apply M_lift.
    intros [k K].
    destruct (H _ (H0 x)) as [m Pm];simpl in *.
    assert (exists n0, n0 > k /\ n0 > m)%nat as [n0 [Hn0 Hn0']].
    {
      exists (S (max k m)).
      split;lia.
    }
    exists n0.
    intros.
    assert (sierp_up (P (to_initial_sequence (pr1 _ _ x) n))).
    {
      apply Pm.
      intros.
      destruct x;simpl in *.
      unfold to_initial_sequence.
      destruct (initial_sequence x n).
      simpl.
      apply a.
      lia.
    }
    exists H2.
    simpl.
    specialize (K (exist _ (to_initial_sequence (pr1 _ _ x) n) H2)).
    apply eq_sym.
    apply K.
    destruct x; simpl in *.
    intros.
    unfold to_initial_sequence.
    destruct (initial_sequence x n).
    simpl.
    apply a;lia.
 Qed.

 (*  Lemma separable_metric_continuous_strong (H : metric) (s : separable) (l : has_limit H) U d0 : open U -> U (D s d0) ->  ^M {mu: nat -> nat*nat  | (forall n, is_subset (ball H (D s (fst (mu n))) (snd (mu n))) U) /\ (forall x, U x -> exists n, (ball H (D s (fst (mu n))) (snd (mu n))) x)}. *)
  Lemma enumerate_nonempty_open (H : metric) s U d0 : open U -> U (D s d0) -> ^M {s' : nat -> nat | (forall n, U (D s (s' n))) /\ forall m, U (D s m) -> exists k, s' k = m}.
  Proof.
    intros.
    specialize (enumerate_open H s U X0).
    apply M_lift.
    intros [s0 S0].
    destruct S0.
    exists (fun n => match (s0 n) with 0%nat => d0 | S n' => n' end).
    split;intros.
    destruct (s0 n) eqn:E;auto.
    destruct (H1 n);try lia.
    rewrite E in H3.
    simpl in H3;auto.

    destruct (H2 _ H3).
    exists x.
    rewrite H4;auto.
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
  Lemma has_name H s x : ^M {phi : nat -> nat | metric_is_fast_limit H (fun n => D s (phi n)) x}.
  Proof.
      pose proof (separable_metric_approx H s x).
      apply M_countable_lift in X0.
      revert X0.
      apply M_lift.
      intros.
      exists (fun n => (pr1 _ _ (H0 n))).
      intros n.
      apply real_lt_le.
      destruct (H0 n);simpl in *.
      destruct H as [d [D1 [D2 D3]]]; simpl in *; rewrite D2;auto.
 Qed.

   
  Lemma has_fast_name H s x k : ^M {phi : nat -> nat | metric_is_fast_limit H (fun n => D s (phi n)) x /\ forall n, d_X H (D s (phi n)) x < prec (n + k)%nat}.
  Proof.
    specialize (has_name H s x).
    apply M_lift.
    intros [phi Phi].
    exists (fun n => (phi (n+k+1)%nat)).
    split.
    intros n.
    apply (real_le_le_le _ _ _ (Phi (n+k+1)%nat)).
    apply real_lt_le.
    apply prec_monotone.
    lia.
    intros n.
    apply (real_le_lt_lt _ _ _ (Phi (n+k+1)%nat)).
    apply prec_monotone.
    lia.
  Qed.

  Lemma last_nth T (l : list T) d : last l d = nth (pred (length l)) l (last l d).
  Proof.
      destruct l;auto.
      assert (t :: l <> []) by discriminate.
      destruct (exists_last H).
      destruct s.
      rewrite e.
      rewrite last_last.
      rewrite app_length.
      simpl.
      replace (pred (length x + 1))%nat with  (length x) by lia.
      rewrite nth_middle;auto.
  Qed.

 Lemma rev_ind_T {T} : forall (P : list T  -> Type),
  P [] -> (forall (x : T) (l : list T), P l -> P (l ++ [x])) -> forall l : list T, P l.
 Proof.
   intros.
   replace l with (rev (rev l)) by (apply rev_involutive).
   induction (rev l).
   simpl.
   apply X0.
   simpl.
   apply X1;auto.
 Qed.
  (* Lemma baire_base_to_ball H s : forall l, metric_is_fast_limit H (fun n => (D s (nth n l (last l 0%nat)))) (D s (last l 0%nat)) -> forall x,  *)
  Lemma separable_metric_second_countable H s (l : has_limit H) U : open U -> ^M {f : nat -> option (nat * nat) | U = countable_union (fun n => match f n with | None => (fun x => False) | Some nm => ball H (D s (fst nm)) (snd nm) end)}.
  Proof.
    intros.
    destruct (open_to_name_fun H s l _ X0) as [phi Phi]. 
    assert (^M { fc | (forall l (n : nat), (fc l n) = true -> forall i, d_X H (D s (baire_base l i)) (D s (baire_base l (pred (length l)))) < prec (i+1)%nat) /\ (forall l, (forall i, d_X H (D s (baire_base l i)) (D s (baire_base l (pred (length l)))) < prec (i+1)%nat) -> exists n, (fc l n) = true)  }).
    {
    enough (^M {fc | (forall l , sierp_up (fc l)<-> forall i, d_X H (D s (baire_base l i)) (D s (baire_base l (pred (length l)))) < prec (i+1)%nat) }).
    {
      revert X1.
      apply M_lift_dom.
      intros [fc Fc].
      destruct (enumerable_list enumerable_nat).
      assert (forall n, ^M ({f : nat -> nat | sierp_up (fc (x n)) <-> exists k, f k = 1%nat})) by (intros;apply  (sierp_to_nat_sequence (fc (x n)))).
      apply M_countable_lift in X1.
      revert X1.
      apply M_lift.
      intros.
      exists (fun l n => ((pr1 _ _ (H0 (pr1 _ _ (s0 l)))) n =? 1)%nat).
      split.
      intros.
      destruct (H0 (pr1 _ _ (s0 l0)));simpl in *.
      destruct (s0 l0);simpl in *.
      apply Fc.
      rewrite <-e.
      apply i0.
      exists n.
      apply Nat.eqb_eq;auto.
      intros.
      destruct (H0 (pr1 _ _ (s0 l0)));simpl in *.
      destruct (s0 l0);simpl in *.
      enough (exists n, (x0 n = 1%nat)).
      destruct H2;exists x2.
      apply Nat.eqb_eq;auto.
      apply i.
      apply Fc.
      intros .
      rewrite e.
      apply H1.
    }
    apply M_unit.

    enough {fc | forall l, sierp_up (fc l) <-> forall i, (i < length l)%nat ->  d_X H (D s (baire_base l i)) (D s (baire_base l (pred (length l)))) < prec (i+1)%nat} as [fc Fc].
    {  exists fc.
      intros.
      split.
      intros.
      assert (i < length l0 \/ i >= length l0)%nat by lia.
      destruct H1; [apply Fc;auto|].
      unfold baire_base.
      rewrite <-last_nth.
      rewrite nth_overflow;try lia.
      destruct H as [d [D1 [D2 D3]]].
      simpl in *.
      apply (real_le_lt_lt _ 0).
      right;apply D1;auto.
      apply prec_pos.
      intros.
      apply Fc.
      intros.
      apply H0.
   } 
    enough (forall l x, {sp | sierp_up sp <-> forall i, (i < length l)%nat ->  d_X H (D s (baire_base l i)) x < prec (i+1)%nat}) by (exists (fun l => pr1 _ _ (X1 l (D s (baire_base l (pred (length l))))));intros;destruct (X1 l0);auto).
    intros.
    apply sierp_from_semidec.
    induction l0 using rev_ind_T.
    exists lazy_bool_true; unfold lazy_bool_up;simpl;split;intros;try lia;auto.
    destruct (real_lt_semidec (d_X H (D s x0) x) (prec (length l0+1)%nat)).
    destruct IHl0.
    exists (lazy_bool_and x1 x2).
    unfold lazy_bool_up.
    rewrite lazy_bool_and_up.
    split.
    - intros [B1 B2].
      intros k.
      rewrite app_length;simpl.
      intros.
      assert (k = length l0 \/ k < length l0)%nat by lia.
      destruct H1.
      rewrite H1.
      unfold baire_base.
      rewrite nth_middle.
      apply i;auto.
      unfold baire_base.
      rewrite app_nth1; try lia.
      rewrite (nth_indep _ _ (last l0 0%nat));try lia.
      apply i0;auto.
    - intros.
      split.
      apply i.
      rewrite <-(nth_middle l0 [] x0 (last (l0++[x0]) 0%nat)).
      apply H0.
      rewrite app_length; simpl;lia.
      apply i0.
      intros.
      unfold baire_base.
      rewrite <-(app_nth1 l0 [x0]);auto.
      rewrite (nth_indep _ _ (last (l0++[x0]) 0%nat));[apply H0|];rewrite app_length;simpl;lia.
    }
    revert X1.
    apply M_lift_dom.
    intros [fc Fc].
    specialize (enumerate_baire_open phi).
    apply M_lift_dom.
    intros [f0 [F0 F1]].
    specialize (baire_continuous_modulus phi).
    apply M_lift.
    intros [m [M1 M2]].
    assert {f : nat -> option  (nat*nat) | (forall n dm, (f n) = Some dm -> exists l (Hu: sierp_up (phi  (baire_base l))), (forall i, d_X H (D s (baire_base l i)) (D s (fst dm)) < prec (i+1)%nat ) /\ (fst dm) = baire_base l (pred (length l)) /\ (snd dm) = (S (m (exist _ (baire_base l) Hu)))) /\ forall l (Hu: sierp_up (phi  (baire_base l))), (forall i, d_X H (D s (baire_base l i)) (D s (baire_base l (pred (length l)))) < prec (i+1)%nat ) ->  exists n, (f n) = Some (baire_base l (pred (length l)), (S (m (exist _ (baire_base l) Hu)))) }.
    {
      assert (forall n, {m' | forall l, f0 n = Some l -> forall H: sierp_up (phi (baire_base l)), m' = (m (exist _ (baire_base l) H))}).
      {
        intros.
        destruct (f0 n) eqn:E.
        specialize (F0 _ _ E).
        exists (m (exist _ (baire_base l0) F0)). 
        intros.
        injection H0.
        intros ->.
        replace F0 with H1;auto.
        apply irrl.
        exists 0%nat.
        intros.
        discriminate H0.
      }
      
    enough {f : nat -> nat -> option  (nat*nat) | (forall n k dm, (f n k) = Some dm -> exists l (Hu: sierp_up (phi  (baire_base l))), (forall i, d_X H (D s (baire_base l i)) (D s (fst dm)) < prec (i+1)%nat ) /\ (fst dm) = baire_base l (pred (length l)) /\ (snd dm) = (S (m (exist _ (baire_base l) Hu)))) /\ forall l (Hu: sierp_up (phi  (baire_base l))), (forall i, d_X H (D s (baire_base l i)) (D s (baire_base l (pred (length l)))) < prec (i+1)%nat ) ->  exists n k, (f n k) = Some (baire_base l (pred (length l)), (S (m (exist _ (baire_base l) Hu)))) } as [f F].
      {
        destruct (enumerable_pair _ _ enumerable_nat enumerable_nat).
        exists (fun n => (f (fst (x n)) (snd (x n)))).
        split;intros.
        destruct F.
        destruct (H2 _ _ _ H1) as [l0 [Hl1 Hl2]].
        exists l0;exists Hl1.
        apply Hl2.
        destruct F.
        specialize (H3 l0 Hu H1).
        destruct H3 as [n [k K]].
        destruct (s0 (n,k)).
        exists x0.
        rewrite e;simpl;auto.
     }
      exists (fun n k => match (f0 n) with Some l => if (fc l k) then Some (baire_base l (pred (length l)), (S (pr1 _ _ (H0 n)))) else None | _ => None end).
      split; intros.
      - destruct (H0 n).
        simpl in *.
        destruct (f0 n) eqn:F0n; [|discriminate H1].
        destruct (fc l0) eqn:Fc0; [|discriminate H1].
        simpl in *.
        destruct dm.
        simpl in *.
        exists l0.
        specialize (F0 _ _ F0n).
        exists F0.
        split.
        intros.
        pose proof ((proj1 Fc) l0 k).
        specialize (H2 Fc0).
        injection H1;intros.
        rewrite H4 in H2.
        apply H2.
        injection H1.
        intros _ ->;split;auto.
        injection H1.
        intros <-.
        intros.
        apply f_equal.
        apply e;auto.
      - 
        destruct (F1 l0 Hu).
        exists x.
        destruct (H0 x).
        simpl in *.
        rewrite H2.
        destruct ((proj2 Fc) l0 H1).
        exists x1.
        rewrite H3.
        apply f_equal.
        enough (S x0 = (S (m (exist _ (baire_base l0) Hu)))) by auto.
        apply f_equal.
        apply e;auto.
    }
    
    clear fc Fc f0 F0 F1.
    destruct H0 as [f [F0 F1]].
    exists f.
    apply fun_ext.
    intros x.
    apply Prop_ext.
    - intros.
      unfold countable_union.
      intros.
      apply M_hprop_elim; [intros a b; apply irrl|].
      specialize  (has_fast_name H s x 2%nat).
      apply M_lift.
      intros [p [P Pfast]].
      assert (metric_is_fast_cauchy H (fun n => D s (p n))) by (apply (fast_limit_fast_cauchy _ _ x);auto).
      assert (sierp_up (phi p)).
      {
        apply Phi;auto.
        exists x;split;auto.
      }
      destruct (M2 (exist _ p H2)) as [k K].
      simpl in *.
      assert (exists n, S n > k /\ n > (S (m (exist _ p H2))))%nat as [k0 [K0 K1]].
      {
        exists (max k (S (S (m (exist _ p H2)))))%nat.
        split;try lia.
      }
      destruct (K _ K0).
      destruct (F1 _ x0) as [n N].
      {
        intros.
        unfold to_initial_sequence in *.
        destruct (initial_sequence p (S k0)).
        simpl in *.
        assert (i < length x1 \/ i >= length x1)%nat by lia.
        destruct H4.
        - destruct a.
          rewrite <-H5;try lia.
          rewrite H6.
          simpl.
          rewrite <-H5;try lia.
          destruct H as [d [D1 [D2 D3]]].
          simpl in *.
          apply (real_le_lt_lt _ _ _ (D3 _ _ x)).
          rewrite <- prec_twice.
          replace (i+1+1)%nat with (i+2)%nat by lia.
          apply real_lt_lt_plus_lt.
          apply Pfast.
          rewrite D2.
          apply (real_lt_le_lt _ _ _ (Pfast _)).
          assert (i = k0 \/ i < k0)%nat by lia.
          destruct H.
          rewrite H;right;auto.
          apply real_lt_le.
          apply prec_monotone.
          lia.
       - simpl.
         unfold baire_base.
         rewrite nth_overflow;try lia.
         replace (nth (pred (length x1)) x1 (last x1 0%nat)) with (last x1 0%nat).
         destruct H as [d [D1 [D2 D3]]];simpl in *.
         apply (real_le_lt_lt _ 0); [|apply prec_pos].
         right.
         apply D1;auto.
         destruct x1;auto.
         rewrite <-last_nth;auto.
      }
      exists n.
      rewrite N.
      simpl.
      unfold ball.
      assert (baire_base (pr1 _ _ (initial_sequence p (S k0))) (pred (length (pr1 _ _ (initial_sequence p (S k0))))) = p k0) as ->.
      {
        unfold to_initial_sequence in *.
        destruct (initial_sequence p (S k0)).
        simpl in *.
        destruct a.
        rewrite <- H4.
        rewrite H5.
        simpl;auto.
        lia.
      }
      apply (real_le_lt_lt _ _ _ (P _)).
      apply prec_monotone.
      unfold to_initial_sequence in H3.
      rewrite H3.
      lia.
   - unfold countable_union.
     intros.
     destruct H0.
     destruct (f x0) eqn:F;[|contradict H0].
     destruct (F0 _ _ F) as [a [Ha [P1 P2]]].
     destruct p as [d n]; simpl in *.
     unfold ball in H0.
     specialize (M1 (exist _ (baire_base a) Ha)).
     remember (m (exist _ (baire_base a) Ha)) as m0.
     pose proof (has_name H s x).
     apply M_hprop_elim; [intros u v; apply irrl|].
     revert X1.
     apply M_lift.
     intros [p P].
     remember (fun i => if (i <? n)%nat then (baire_base a i) else p i) as p'.
     assert (sierp_up (phi p')).
     {
       apply M1.
       intros.
       rewrite Heqp'.
       simpl.
       assert (n0 < n)%nat by lia.
       apply Nat.ltb_lt in H2.
       rewrite H2;auto.
     }
     assert (metric_is_fast_limit H (fun n => (D s (p' n))) x).
     {
       intros i.
       rewrite Heqp'.
       destruct (i <? n)%nat eqn:E.
       destruct H as [dist [D1 [D2 D3]]].
       simpl in *.
       apply real_lt_le.
       apply (real_le_lt_lt _ _ _ (D3 _ _ (D s d))).
       rewrite <-prec_twice.
       apply real_lt_lt_plus_lt.
       apply P1.
       apply (real_lt_le_lt _ _ _ H0).
       apply Nat.ltb_lt in E.
       assert (i + 1 < n \/ i+1 = n)%nat by lia.
       destruct H.
       apply real_lt_le;apply prec_monotone;auto.
       rewrite H;right;auto.
       apply P.
         
     }
     destruct (Phi p' (fast_limit_fast_cauchy _ _ _ H2) ).
     destruct (H3 H1) as [x1 [Hx1 Hx1']].
     replace x with x1; auto.
     apply (metric_limit_unique _ _ _ _ Hx1 H2).
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
  (* Definition totally_bounded (H : metric) (U : (@csubset X)) := forall n, {L : list X | (forall x, In x L -> U x) /\  *)
  (*               forall x,  U x ->  Exists  (ball H x n) L}. *)

  Definition totally_bounded (H : metric) (U : (@csubset X)) := forall n, {L : list X | (forall x, In x L -> intersects (ball H x n) U) /\ forall x,  U x ->  Exists  (ball H x n) L}.
  Definition complete (H : metric) (U : (@csubset X)) := forall f, (forall n, U (f n)) ->  (metric_is_fast_cauchy H f)  -> {x | metric_is_fast_limit H f x /\ U x}.
  Lemma d_sym H : forall x y, d_X H x y = d_X H y x.
  Proof.
    destruct H as [d [D1 [D2 D3]]];auto.
  Qed.

  Lemma closed_complete0 (H : metric) (l : has_limit H) U  : closed U -> complete H U.
  Proof.
     unfold complete.
     intros.
     destruct (l f);auto.
     exists x.
     split;auto.
     unfold closed in X0.
     destruct (lem (U x));auto.
     assert ({h : (nat -> X) -> sierp | forall a, metric_is_fast_cauchy H a -> (sierp_up (h a)) <-> exists x, metric_is_fast_limit H a x /\ not (U x)}).
     {
        enough (forall a, {s : sierp | (metric_is_fast_cauchy H a -> (sierp_up s) <-> exists x, metric_is_fast_limit H a x /\ not (U x)) /\ ((not (metric_is_fast_cauchy H a)) -> sierp_up s)} ).
         exists (fun a => pr1 _ _ (X1 a)).
         intros; destruct (X1 a);simpl in *.
         apply a0;auto.
         intros.
         apply M_hprop_elim.
         intros [] [].
         apply sigma_eqP2.
         apply sierp_id.
         destruct a0,a1.
         destruct (lem (metric_is_fast_cauchy H a)).
         rewrite H3, H5;auto.
         split;auto.
         split;intros;auto.
         pose proof (extended_limit H l a).
         revert X1.
         apply M_lift.
         intros [p P].
         destruct (not_fast_cauchy_semidec H a).
         destruct (X0 p).
         destruct (sierp_or x0 x1).
         exists x2.
         rewrite i1.
         split.
         intros.
         split.
         intros.
         destruct H4.
         contradict H3.
         apply i;auto.
         exists p.
         split;auto.
         apply i0;auto.
         intros [p0 [P0 P1]].
         right.
         apply i0.
         replace p with p0;auto.
         apply (metric_limit_unique _ _ _ _ P0);auto.
         intros.
         left.
         apply i;auto.
       }
     destruct X1 as [h P].
     destruct (fast_cauchy_simpl H f) as [f' F'].
     assert (sierp_up (h f')).
     {
       apply P;auto.
       apply (fast_limit_fast_cauchy _ _ x).
       apply F';auto.
       exists x;split;auto.
       apply F';auto.

     }
     apply M_hprop_elim;[intros a b;apply irrl|].
     specialize (continuity _ _ H3).
     apply M_lift.
     intros [k Pk].
     enough (complement U (f k)) by (specialize (H0 k);contradict H0;auto).
     assert (metric_is_fast_cauchy H (fun n => if (n <? k)%nat then (f' n) else (f' k))).
     {
       apply fast_cauchy_neighbor.
       intros.
       destruct (S n <? k)%nat eqn:E.
       assert ((n <? k)%nat = true) as -> by admit.
       apply real_lt_le.
       apply (real_le_lt_lt _ (prec (S (S n)))); [|apply prec_monotone;lia].
       apply F';auto.
       admit.
     }
     admit.
  Admitted.
  Lemma closed_complete (H : metric) (s : separable) (l : has_limit H) U  : closed U -> complete H U.
  Proof.
     unfold complete.
     intros.
     destruct (l f);auto.
     exists x.
     split;auto.
     unfold closed in X0.
     destruct (lem (U x));auto.
     apply M_hprop_elim;[intros a b;apply irrl|].
     specialize (separable_metric_continuous H s l _ _ X0 H2).
     apply M_lift.
     intros [k Pk].
     enough (complement U (f (k+1)%nat)) by (specialize (H0 (k+1)%nat);contradict H0;auto).
     apply Pk.
     unfold ball.
     rewrite d_sym.
     apply (real_le_lt_lt _ _ _ (m _)).
     apply prec_monotone;lia.
  Qed.

  Lemma first_n {A} (f : nat -> A) n : {l | forall x, In x l <-> exists m, (m < n)%nat /\ x = f m}.
  Proof.
    induction n.
    exists [].
    simpl;split;intros.
    contradict H.
    destruct H;lia.
    destruct IHn.
    exists (x ++ [f n]).
    intros.
    split.
    intros.
    apply in_app_or in H.
    destruct H.
    destruct (i x0).
    destruct (H0 H) as [x1 [H21 H22]].
    exists x1;split;try lia;auto.
    destruct H;[|contradict H].
    exists n.
    split;try lia;auto.
    intros [m [H1 H2]].
    apply in_or_app.
    rewrite Nat.lt_succ_r in H1.
    apply Lt.le_lt_or_eq_stt in H1.
    destruct H1.
    left.
    rewrite H2.
    apply i.
    exists m;split;auto.
    right.
    rewrite H2.
    rewrite H.
    left;auto.
  Qed.
  Lemma compact_empty_semidec (U : (@csubset X)) : compact U -> semidec (forall x, (not (U x))).
  Proof.
    intros.
    destruct (X0 _ open_emptyset).
    destruct x;unfold lazy_bool_up, sierp_up in *;simpl in *.
    exists x; rewrite i;split;unfold is_subset.
    intros H x0 Hx0.
    apply (H x0);auto.
    intros.
    contradict H0.
    apply H.
  Qed.


  Lemma compact_overt_empty_dec (U : (@csubset X)) : compact U -> overt U -> dec (exists x, (U x)).
  Proof.
    intros.
    apply semidec_dec.
    apply overt_nonempty_semidec;auto.
    rewrite classical_tautology_neg_some.
    apply compact_empty_semidec;auto.
  Qed.

  Lemma multivalued_countable_choice_sequence (f : nat -> ^K) : (exists n, (f n) = lazy_bool_true) -> ^M {g : nat -> nat | (forall n, (f (g n)) = lazy_bool_true) /\ (forall n, (f n) = lazy_bool_true -> exists m, g m = n)}.
  Proof.
    intros.
    specialize (multivalued_countable_choice f H).
    apply M_lift_dom.
    intros [d D].
    assert (^M (forall n, {f' : nat -> nat | f n = lazy_bool_true <-> exists m, f' m = 1%nat  })).
    {
      apply M_countable_lift.
      intros.
      apply (kleenean_to_nat_sequence (f n)).
    }
    revert X0.
    apply M_lift.
    intros.
    destruct (enumerable_pair _ _ enumerable_nat enumerable_nat).
    exists (fun n => if (pr1 _ _ (H0 (fst (x n))) (snd (x n))) =? 1%nat then (fst (x n)) else d).
    split.
    - intros; destruct (H0 (fst (x n)));simpl in *.
      destruct (x0 (snd (x n)) =? 1)%nat eqn:E;auto.
      apply Nat.eqb_eq in E.
      apply i.
      exists (snd (x n));auto.
   - intros.
     destruct (H0 n) eqn:E;simpl in *.
     destruct (proj1 i);auto. 
     destruct (s (n, x1)).
     exists x2.
     rewrite e;simpl.
     rewrite E;simpl.
     apply Nat.eqb_eq in H2.
     rewrite H2;simpl;auto.
  Qed.

  Lemma intersects_sym (A : (@csubset X)) B : intersects A B <-> intersects B A.
  Proof.
    split; intros [x [H1 H2]];exists x;split;auto.
  Qed.

  Lemma compact_overt_totally_bounded (H: metric) (s : separable) (l : has_limit H) U :  compact U -> overt U -> ^M (totally_bounded H U).
  Proof.
    intros.
    destruct (compact_overt_empty_dec _ X0 X1).
    - unfold totally_bounded.
      apply M_countable_lift.
      intros.

      assert (^M {f : nat -> X |  (forall m, intersects (ball H (f m) n) U) /\ is_subset U (countable_union (fun m => (ball H (f m) n)))}).
      {
        enough ({g : nat -> ^K | forall m, g m = lazy_bool_true <-> intersects (ball H (D s m) n) U}) as [g G].
        assert (exists n, g n = lazy_bool_true).
        {
          destruct e.
          apply M_hprop_elim;[intros a b; apply irrl|].
          specialize (separable_metric_approx H s x n).
          apply M_lift.
          intros [m M].
          exists m.
          apply G.
          exists x.
          split;auto.
          unfold ball; rewrite d_sym;auto.
        }
        specialize (multivalued_countable_choice_sequence g H0).
        apply M_lift.
        intros [f [F1 F2]].
        exists (fun n => D s (f n)).
        split.
        intros.
        apply G;auto.
        intros x Ux.
        apply M_hprop_elim;[intros a b; apply irrl|].
        specialize (separable_metric_approx H s x n).
        apply M_lift.
        intros [m M].
        assert (g m = lazy_bool_true).
        {
          apply G.
          exists x.
          split;auto.
          unfold ball;rewrite d_sym;auto.
        }
        destruct (F2 _ H1).
        exists x0.
        rewrite H2.
        unfold ball; rewrite d_sym;auto.
        enough (forall m, {k | k = lazy_bool_true <-> intersects (ball H (D s m) n) U}).
        exists (fun m => pr1 _ _ (X2 m)); intros; destruct (X2 m);auto.
        intros.
        destruct (X1 (ball H (D s m) n)).
        apply metric_open.
        unfold sierp_up in i.
        destruct x; simpl in *.
        exists x.
        rewrite i.
        rewrite intersects_sym;split;auto.
      }
      revert X2.
      apply M_lift_dom.
      intros [f [F1 F2]].
      pose proof (compact_fin_cover U).
      assert (forall m, open (ball H (f m) n)) by (intros; apply metric_open).
      specialize (compact_fin_cover U _ X0 X3 F2).
      apply M_lift.
      intros [m Pm].
      destruct (first_n f m) as [L PL].
      exists L.
      split.
      intros.
      destruct ((proj1 (PL x))  H0) as [k [K1 ->]].
      apply F1.
      intros.
      destruct (Pm _ H0) as [k [K1 K2]].
      apply Exists_exists.
      exists (f k).
      split;[apply PL; exists k;split |];auto.
      unfold ball.
      rewrite d_sym.
      apply K2.
   -  apply M_unit.
      intros m.
      exists [].
      split.
      intros;contradict H0;auto.
      intros.
      contradict n.
      exists x;auto.
  Qed.
  Definition closure H A := fun x => A x \/ exists (f : nat -> X), metric_is_fast_limit H f x /\ forall n, A (f n).
  Definition cball H x n y := d_X H x y <= prec n.


  Definition totally_bounded_cball (H : metric) (U : (@csubset X)) := forall n, {L : list X | (forall x, In x L -> intersects (cball H x n) U) /\ forall x,  U x ->  Exists  (cball H x n) L}.

  Lemma totally_bounded_whichever1 H U : totally_bounded H U -> totally_bounded_cball H U. 
  Proof.
    unfold totally_bounded, totally_bounded_cball.
    intros.
    destruct (X0 n) as [l [L1 L2]].
    exists l.
    split;intros.
    destruct (L1 _ H0).
    exists x0.
    destruct H1.
    split;auto.
    apply real_lt_le;auto.
    apply Exists_exists.
    specialize (L2 x H0).
    rewrite Exists_exists in L2.
    destruct L2 as [y [L21 L22]].
    exists y.
    split;auto.
    apply real_lt_le;auto.
  Qed.
  Lemma totally_bounded_whichever2 H U : totally_bounded_cball H U -> totally_bounded H U. 
  Proof.
    unfold totally_bounded, totally_bounded_cball.
    intros.
    destruct (X0 (S n)) as [l [L1 L2]].
    exists l.
    split;intros.
    - destruct (L1 _ H0).
      exists x0.
      destruct H1.
      split;auto.
      apply (real_le_lt_lt _ (prec (S n)));auto.
      apply prec_monotone;lia.
   - apply Exists_exists.
     specialize (L2 x H0).
     rewrite Exists_exists in L2.
     destruct L2 as [y [L21 L22]].
     exists y.
     split;auto.
      apply (real_le_lt_lt _ (prec (S n)));auto.
      apply prec_monotone;lia.
 Qed.

  Definition nth_cover H A (B : totally_bounded_cball H A) (n : nat) : (@csubset X).
  Proof.
    unfold totally_bounded_cball in B.
    destruct (B n) as [l L].
    apply ((fun x => exists c, In c l /\ cball H c n x) : (@csubset X)).
  Defined.
  
  Lemma nth_cover_spec H A B n x : nth_cover H A B n x <-> exists c, In c (pr1 _ _ (B n)) /\ cball H c n x.
  Proof.
    unfold nth_cover.
    destruct (B n);simpl;split;auto.
  Qed.   

  Lemma cball_sym H x y n : cball H x n y <-> cball H y n x.
  Proof.
    split;unfold cball;intros; rewrite d_sym;auto.
  Qed.

  Lemma dx_triangle H x y z: d_X H x y <= d_X H x z + d_X H z y.
  Proof.
    destruct H as [d [D1 [D2 D3]]];auto.
  Qed.
  Lemma totally_bounded_id_intersection H A (B : totally_bounded_cball H A) : complete H A -> A = countable_intersection (nth_cover H A B).
  Proof.
    intros.
    apply fun_ext.
    intros.
    apply Prop_ext.
    - intros.
      intros n.
      rewrite nth_cover_spec.
      destruct (B n);simpl in *.
      destruct a.
      specialize (H2 _ H0).
      apply Exists_exists in H2.
      destruct H2.
      rewrite cball_sym in H2.
      exists x1;auto.
    - intros.
      assert (forall n, exists y, d_X H x y <= prec n /\ A y).
      {
        intros.
        specialize (H0 (S n)).
        rewrite nth_cover_spec in H0.
        destruct (B (S n)); simpl in *.
        destruct H0.
        destruct a.
        destruct H0.
        destruct (H1 _ H0).
        exists x2.
        destruct H4.
        split;auto.
        rewrite <-prec_twice.
        replace (n+1)%nat with (S n) by lia.
        apply (real_le_le_le _ _ _ (dx_triangle H _ _  x1)).
        apply real_le_le_plus_le;auto.
        rewrite d_sym;auto.
      }
      apply countable_choice in H1.
      destruct H1.
      destruct (X0 x0).
      apply H1.
      apply (fast_limit_fast_cauchy _ _ x).
      intros n.
      rewrite d_sym;apply H1.
      destruct a.
      replace x with x1;auto.
      apply (metric_limit_unique _ _ _ _ H2);auto.
      intros n.
      rewrite d_sym.
      apply H1.
   Qed.

  Lemma metric_space_ineq_semidec (H : metric) : (forall (x y : X), semidec (x <> y)).
  Proof.
    intros.
    destruct H as [d [D1 [D2 D3]]].
    destruct (real_lt_semidec 0 (d x y)).
    exists x0.
    rewrite i.
    split.
    rewrite <-D1.
    intros.
    apply real_gt_neq;auto.
    intros.
    destruct (real_total_order 0 (d x y)) as [t | [t | t]];auto.
    contradict H.
    apply D1.
    apply eq_sym;auto.
    replace 0 with (d x x) by (rewrite D1;auto).
    apply (real_le_lt_lt _ _ _ (D3 _ _ y)).
    add_both_side_by (- d x y).
    rewrite D2;auto.
  Qed.


  Definition dist H (A : csubset) (x : X) r :=  (forall y, A y -> d_X H x y >= r) /\ forall s, (forall y, A y -> d_X H x y >= s) -> s <= r.
  Lemma dist_unique H A x r1 r2 :  (dist H A x r1 -> dist H A x r2 -> r1 = r2).
  Proof.
    unfold dist.
    intros [H1 H2] [H1' H2'].
    apply real_le_le_eq.
    apply H2'.
    apply H1.
    apply H2.
    apply H1'.
  Defined.

  Definition located H A := forall x, {r : Real | dist H A x r}.

  Definition uniformly_continuous H U (f : X -> Real) := forall n,  {m | forall x y, U x -> U y -> d_X H x y < prec m ->  RealMetric.dist (f x) (f y) < prec n}.

  Lemma dist_helper H x y y' : abs (d_X H x y - d_X H x y') <= d_X H y' y.
  Proof.
    destruct H as [d [D1 [D2 D3]]]; simpl in *.
    apply real_abs_le_le_le.
    apply (real_le_le_le _ (d x y' + d y' y  - d x y')); [|ring_simplify;apply real_le_triv].
    add_both_side_by (d x y').
    apply D3.
    ring_simplify.
    apply (real_le_le_le _ (-d x y + d x y  + d y y')); [|ring_simplify;rewrite D2;apply real_le_triv].
    ring_simplify.
    add_both_side_by (d x y).
    apply D3.
  Qed.

  Lemma uniformly_continuous_dist H  A :  forall x, uniformly_continuous H A (d_X H x).
  Proof.
    intros.
    intros n.
    exists n.
    intros.
    unfold RealMetric.dist.
    apply (real_le_lt_lt _ _ _ (dist_helper _ _ _ _));auto.
    rewrite d_sym;auto.
  Qed.

  Definition W_is_inf P s := W_is_sup (fun x => (P (- x))) (-s). 

  Lemma dist_inf H A x r: ((dist H A x r) <-> W_is_inf (fun r' =>  exists y, A y /\ d_X H x y = r') r).
  Proof.
    split.
    - intros [D1 D2].
      split.

      unfold W_is_upper_bound.
      intros z P.
      destruct P as [y [P1 P2]].
      add_both_side_by (r-z).
      rewrite <-P2.
      apply D1;auto.

      intros.
      unfold W_is_upper_bound in H.
      add_both_side_by (r-s').
      apply D2.
      intros.
      add_both_side_by (s'-d_X H x y).
      apply H0.
      exists y;split;auto;ring.
  - intros [H1 H2].
    split.

    intros.
    unfold W_is_upper_bound in H2.
    add_both_side_by (-r -d_X H x y).
    apply H1.
    exists y;split;auto;ring.

    intros.
    add_both_side_by (-r -s).
    apply H2.
    unfold W_is_upper_bound;intros.
    destruct H3 as [y [My Dy]].
    add_both_side_by (s-z).
    rewrite <-Dy.
    apply H0;auto.
  Defined.

  Lemma d_nonneg H : forall x y, real_0 <= d_X H x y .
  Proof.
    intros.
    apply (real_le_mult_pos_cancel real_2).
    apply real_lt_0_2.
    replace (real_0 * real_2) with (d_X H x x).
    replace (d_X H x y * real_2) with (d_X H x y + d_X H x y) by (unfold real_2;ring).
    apply (real_le_le_le _ _ _ (dx_triangle H _ _ y)).
    rewrite d_sym.
    apply real_le_triv.
    destruct H.
    destruct a;simpl.
    replace (real_0 * real_2) with (real_0) by ring.
    apply i;auto.
  Qed.
  Lemma classical_dist_exists H A x : (exists y, A y) -> exists! r, dist H A x r.
  Proof.
    intros.
    rewrite <-unique_existence.
    split; [|intros a b Hab Hab'; apply (dist_unique H A x);auto].
    assert ((exists r, dist H A x r) <-> (exists r, W_is_inf (fun r' =>  exists y, A y /\ d_X H x y = r') r)).
    {
      split;intros H1;destruct H1 as [y H1];exists y;apply dist_inf;auto.
    }
    apply H1.
    assert (forall P, ((exists r, W_is_sup P r) -> exists r, W_is_sup P (- r))).
    {
      intros.
      destruct H2.
      exists (-x0).
      assert ((- - x0) = x0) as -> by ring.
      exact H2.
    }
    unfold W_is_inf.
    
    apply H2.
    apply W_complete.
    destruct H0 as [y H0].
    exists (-d_X H x y);exists y.
    split;auto;ring.
    unfold W_is_bounded_above.
    exists real_0.
    unfold W_is_upper_bound.
    intros.
    destruct H3 as [y [_ H3]].
    add_both_side_by (-z).
    rewrite <- H3.
    apply d_nonneg. 
  Defined.

  Lemma nth_cover_close H A x n (B : totally_bounded_cball H A): nth_cover H A B n x -> exists y, A y /\ d_X H x y <= prec n + prec n.
  Proof.
    intros.
    apply nth_cover_spec in H0.
    destruct H0 as [c H0].
    destruct (B n);simpl in *.
    destruct a.
    destruct H0.
    destruct (H1 _ H0).
    exists x1.
    destruct H4.
    split;auto.
    apply (real_le_le_le _ _ _ (dx_triangle H _ _ c)).
    apply (real_le_le_plus_le);auto.
    rewrite d_sym;auto.
  Qed.

  Lemma dist_bounded_exists_gt H A x r: (dist H A x r) -> exists y, A y /\ d_X H y x >= r.
  Proof.
    intros.
    destruct (lem (exists x, A x)).
    destruct H1.
    destruct H0.
    exists x0.
    split;auto.
    rewrite d_sym.
    apply H0;auto.
    destruct H0.
    contradict H2.
    rewrite classical_tautology_neg_all.
    assert (exists r', r' > r) as [r' R'].
    {
        exists (r + real_1).
        apply (real_gt_add_r (-r)).
        ring_simplify.
        apply real_1_gt_0.
    }
    exists r'.
    intros H2.
    assert (forall y, A y -> d_X H x y >= r').
    {
      intros.
      contradict H1.
      exists y;auto.
    }
    specialize (H2 H3).
    contradict H2.
    apply real_gt_nge;auto.
  Qed.
  Lemma dist_bounded_exists_lt H A x r: (dist H A x r) -> forall n, exists y, A y /\ d_X H y x < r + prec n.
  Proof.
    intros.
    apply Classical_Pred_Type.not_all_not_ex.
    intros H1.
    destruct H0.
    assert (forall y, A y -> d_X H x y >= r + prec n).
    {
      intros.
      specialize (H1 y).
      rewrite classical_tautology_neg_and in H1.
      destruct H1;[contradict H1|];auto.
      apply real_nge_le in H1;auto.
      rewrite d_sym;auto.
    }
    specialize (H2 _ H3).
    contradict H2.
    apply real_gt_nle.
    apply (real_gt_add_r (-r)).
    ring_simplify.
    apply prec_pos.
  Qed.


  Lemma dist_bounded_complete_contained H A x: complete H A -> (dist H A x 0) -> A x.
  Proof.
    intros.
    pose proof (dist_bounded_exists_lt H A x real_0 H0).
    apply countable_choice in H1.
    destruct H1 as [f F].
    destruct (X0 f); try apply F.
    - intros n m.
      apply (real_le_le_le _ _ _ (dx_triangle _ _ _ x)).
      rewrite (d_sym _ x).
      apply real_le_le_plus_le; apply real_lt_le; try apply (real_lt_le_lt _ _ _ (proj2 (F _)));ring_simplify;apply real_le_triv.
  - destruct a.
    replace x with x0; auto.
    apply (metric_limit_unique H f);auto.
    intros n.
    destruct (F n).
    apply real_lt_le.
    apply (real_lt_le_lt _ _ _ H4).
    ring_simplify;apply real_le_triv.
  Qed.

  Lemma compact_intersection_classical (K : (@csubset X)) D : compact K -> (forall (n : nat), closed (D n)) -> (forall n, is_subset (D (S n)) (D n)) -> (forall n, exists x, K x /\ (D n x)) -> exists x, countable_intersection D x /\ K x.
  Proof.
    intros.
    apply Classical_Pred_Type.not_all_not_ex.
    intros Hi.
    assert (forall i j, (i < j)%nat -> is_subset (D j) (D i)).
    {
      intros.
      induction j;try lia.
      rewrite Nat.lt_succ_r in H1.
      apply Lt.le_lt_or_eq_stt in H1.
      destruct H1.
      specialize (IHj H1).
      intros x Dx.
      apply IHj.
      apply H;auto.
      rewrite H1.
      apply H.
    }
    assert (is_subset K (countable_union (fun n => complement (D n)))).
    {
       intros x Kx.
       unfold countable_union, complement.
       pose proof (Hi x).
       apply Classical_Pred_Type.not_all_not_ex.
       intros H'.
       contradict H2.
       split;auto.
       intros n.
       apply Classical_Prop.NNPP.
       apply H'.
    }
    
    apply M_hprop_elim; [intros a b;apply irrl|].
    specialize (compact_fin_cover _ _  X0 X1 H2).
    apply M_lift.
    intros [m Hm].
    destruct (H0 m).
    destruct H3.
    destruct (Hm _ H3).
    destruct H5.
    specialize (H1 _ _ H5 x H4). 
    contradict H1;auto.
  Qed.

  Lemma totally_bounded_dist1 H A x n (B : totally_bounded_cball H A) r1 r2: dist H (nth_cover H A B n) x r1 -> dist H A x r2 -> r2 <= r1 + prec n + prec n + prec n.
  Proof.
    intros.
    destruct (dist_bounded_exists_lt _ _ _ _ H0 n) as [y [H1y H2y]].
    destruct (nth_cover_close _ _ _ _ _ H1y) as [z [Hz1 Hz2]].
    destruct H1.
    apply (real_le_le_le _ _ _ (H1 _ Hz1)).
    apply (real_le_le_le _ _ _ (dx_triangle _ _ _ y)).
    rewrite d_sym.
    replace (r1 + prec n + prec n + prec n) with ((r1 + prec n) + (prec n + prec n)) by ring.
    apply real_le_le_plus_le;auto.
    apply real_lt_le;auto.
  Qed.

  Lemma nth_cover_superset H A x n (B : totally_bounded_cball H A) : A x -> nth_cover H A B n x.
  Proof.
    intros.
   rewrite nth_cover_spec.
   destruct (B n) as [l [L1 L2]];simpl in *.
   specialize (L2 _ H0).
   apply Exists_exists in L2.
    destruct L2.
    exists x0;split;try apply H1.
    rewrite cball_sym;apply H1.
  Qed.
  
  Lemma lim_zero_eq_zero x : (forall n, abs x <= prec n) -> x = real_0.
  Proof.
    intros.
    apply abs_zero.
    destruct (real_total_order (abs x) real_0) as [T | [T | T]];auto.
    apply real_gt_nle in T;contradict T;apply abs_pos.
    destruct (real_Archimedean _ T).
    apply real_gt_nle in H0.
    contradict H0.
    apply H.
  Qed.


  Lemma lim_le_le x y : (forall n, x < y + prec n) -> x <= y.
  Proof.
    intros.
    destruct (real_total_order x y) as [T | [T |T]]; [apply real_lt_le| apply real_eq_le | ];auto.
    add_both_side_by (-y).
    apply real_eq_le.
    apply lim_zero_eq_zero.
    intros.
    rewrite abs_pos_id; add_both_side_by y; [|apply real_lt_le;auto].
    apply real_lt_le.
    apply H;auto.
  Qed.

  Lemma lim_le_le' x y : (forall n, x <= y + prec n) -> x <= y.
  Proof.
    intros.
    destruct (real_total_order x y) as [T | [T |T]]; [apply real_lt_le| apply real_eq_le | ];auto.
    add_both_side_by (-y).
    apply real_eq_le.
    apply lim_zero_eq_zero.
    intros.
    rewrite abs_pos_id; add_both_side_by y; [|apply real_lt_le;auto].
    apply H;auto.
  Qed.

  Lemma dist_bounded_exists_complete_lt H A x r: compact A -> (dist H A x r) -> exists y, A y /\ d_X H y x <= r.
  Proof.
     intros.
     pose proof (dist_bounded_exists_lt H A x r H0).
     apply countable_choice in H1.
     destruct H1 as [f F].
     remember (fun n y => d_X H x y  <= r + prec n) as D.
     destruct (compact_intersection_classical A D X0).
     - intros.
       rewrite HeqD.
       intros y.
       apply sierp_from_semidec.
       destruct (real_lt_semidec (r+prec n) (d_X H x y)).
       exists x0.
       rewrite i.
       unfold complement.
       split.
       intros.
       apply real_gt_nle;auto.
       intros.
       apply real_nle_ge;auto.
     - intros.
       rewrite HeqD.
       intros y Dy.
       apply (real_le_le_le _ _ _ Dy).
       add_both_side_by (-r).
       apply real_lt_le.
       apply prec_monotone;lia.
    -  intros.
       exists (f n).
       split; try apply F.
       rewrite HeqD.
       apply real_lt_le.
       rewrite d_sym;apply F.
   - exists x0.
     destruct H1.
     split;auto.
     apply lim_le_le'.
     intros.
     rewrite d_sym.
     specialize (H1 n).
     rewrite HeqD in H1.
     apply H1.
  Qed.

  Lemma totally_bounded_dist2 H A x n (B : totally_bounded_cball H A) r1 r2: dist H (nth_cover H A B n) x r1 -> dist H A x r2 -> r1 <= r2.
  Proof.
    intros.
    apply lim_le_le.
    intros m.
    destruct (dist_bounded_exists_lt _ _ _ _ H1 m) as [y [P1 P2]].
    apply (real_le_lt_lt _ (d_X H y x));auto.
    destruct H0.
    rewrite d_sym.
    apply H0.
    apply nth_cover_superset;auto.
  Qed.

  Lemma closed_ball_dist_approx H x c n : {r | forall r', dist H (cball H c n) x r' -> abs (r-r') <= real_2*prec n}.
  Proof.
     exists (d_X H c x).
     intros.
     apply real_abs_le_le_le.
     add_both_side_by r'.
     destruct (dist_bounded_exists_lt _ _ _ _ H0 n).
     destruct H1.
     apply (real_le_le_le _ _ _ (dx_triangle _ _ _ x0)).
     replace (r' + real_2 * prec n) with (prec n + (r' + prec n)) by (unfold real_2; ring_simplify;ring).
     apply (real_le_le_plus_le);auto.
     apply real_lt_le;auto.
     add_both_side_by (d_X H c x).
     destruct (dist_bounded_exists_gt _ _ _ _ H0).
     destruct H1.
     apply (real_le_le_le _ _ _ H2).
     apply (real_le_le_le _ _ _ (dx_triangle _ _ _ c)).
     add_both_side_by (-d_X H c x).
     rewrite d_sym.
     apply (real_le_le_le _ _ _ H1).
     unfold real_2.
     add_both_side_by (-prec n).
     apply real_lt_le;apply prec_pos.
  Qed.
  Lemma dist_union H x A B r1 r2: dist H A x r1 -> dist H B x r2 -> dist H (union A B) x (real_min r1 r2).
  Proof.
    intros.
    split.
    - intros.
      destruct H2.
      apply (real_le_le_le _ _ _ (real_min_fst_le _ _)).
      apply H0;auto.
      apply (real_le_le_le _ _ _ (real_min_snd_le _ _)).
      apply H1;auto.
   - intros.
     destruct (real_min_cand r1 r2); rewrite H3; apply lim_le_le.
     intros n.
     destruct (dist_bounded_exists_lt _ _ _ _ H0 n).
     destruct H4.
     apply (real_le_lt_lt _ (d_X H x0 x));auto.
     rewrite d_sym.
     apply H2;left;auto.
     
     intros n.
     destruct (dist_bounded_exists_lt _ _ _ _ H1 n).
     destruct H4.
     apply (real_le_lt_lt _ (d_X H x0 x));auto.
     rewrite d_sym.
     apply H2;right;auto.
  Qed.
  Lemma abs_le_dist x y : x <= y + abs (x - y).
  Proof.
    destruct (real_total_order x y) as [H | [H | H]].
    apply (real_lt_le).
    apply (real_lt_le_lt _ y);auto.
    add_both_side_by (-y).
    apply abs_pos.
    rewrite H.
    add_both_side_by (-y).
    apply abs_pos.
    rewrite abs_pos_id.
    ring_simplify.
    apply real_le_triv.
    add_both_side_by y.
    apply real_lt_le;auto.
  Qed.

  Lemma real_min_sym x y : real_min x y = real_min y x.
  Proof.
      rewrite !real_min_real_max.
      rewrite real_max_sym;auto.
  Qed.

  Lemma min_approx  r0 r0' r1 r1' eps : abs (r0 - r0') <= eps -> abs (r1 - r1') <= eps -> abs (real_min r1 r0 - real_min r1' r0') <= eps.
  Proof.
    intros.
    assert (forall x y, real_min x y = x -> x <= y) as R.
    {
      intros x y H1.
      rewrite real_min_real_max in H1.
      add_both_side_by (-x-y).
      apply (real_max_eq_fst_le _ (-x)).
      rewrite real_max_sym.
      rewrite <-H1 at 2;ring.
    }
    destruct (real_min_cand r1 r0); destruct (real_min_cand r1' r0'); rewrite H1, H2; auto.
    pose proof (R _ _ H1) as R1.
    rewrite real_min_sym in H2.
    pose proof (R _ _ H2) as R2.
    apply real_abs_le_le_le.
    add_both_side_by r0'.
    apply (real_le_le_le _ _ _ R1).
    apply (real_le_le_le _ _ _ (abs_le_dist _ r0' )).
    add_both_side_by (-r0');auto.
    replace (-(r1 -r0')) with (r0' - r1) by ring.
    add_both_side_by r1.
    apply (real_le_le_le _ _ _ R2).
    apply (real_le_le_le _ _ _ (abs_le_dist r1' r1 )).
    add_both_side_by (-r1);auto.
    rewrite abs_symm.
    replace (- (r1' - r1)) with (r1 - r1') by ring.
    apply H0.

    rewrite real_min_sym in H1.
    pose proof (R _ _ H1) as R1.
    pose proof (R _ _ H2) as R2.
    apply real_abs_le_le_le.
    add_both_side_by r1'.
    apply (real_le_le_le _ _ _ R1).
    apply (real_le_le_le _ _ _ (abs_le_dist _ r1' )).
    add_both_side_by (-r1');auto.
    replace (-(r0 -r1')) with (r1' - r0) by ring.
    add_both_side_by r0.
    apply (real_le_le_le _ _ _ R2).
    apply (real_le_le_le _ _ _ (abs_le_dist _ r0 )).
    add_both_side_by (-r0);auto.
    rewrite abs_symm.
    replace (- (r0' - r0)) with (r0 - r0') by ring.
    apply H.
  Qed.
  Lemma list_ball_dist_approx H l x n : {r | forall r', dist H (fun y => exists c, In c l /\ cball H c n y) x r' -> abs (r-r') <= real_2*prec n}.
  Proof.
    induction l.
    - exists 0.
      intros.
      destruct H0.
      assert  (forall y, (exists c, In c [] /\ cball H c n y) -> d_X H x y >= r'+real_1).
      {
        intros.
        destruct H2.
        destruct H2.
        contradict H2.
      }
      specialize (H1 _ H2).
      contradict H1.
      apply real_gt_nle.
      apply (real_gt_add_r (-r')).
      ring_simplify.
      apply real_1_gt_0.
    - destruct l.
      + destruct (closed_ball_dist_approx H x a n) as [r1 R1].
        exists r1.
        replace (fun y => exists c, In c [a] /\ cball H c n y) with (cball H a n).
        apply R1.
        apply fun_ext;intros;apply Prop_ext;simpl;intros.
        exists a;auto.
        destruct H0 as [a' []].
        destruct H0;[rewrite H0|contradict H0];auto.
     + destruct IHl as [r0 R0].
       destruct (closed_ball_dist_approx H x a n) as [r1 R1].
       exists (real_min r1 r0).
       destruct (classical_dist_exists H (cball H a n) x) as [r1' R1'].
       exists a;apply real_lt_le;apply ball_contains_center.
       destruct (classical_dist_exists H (fun y => exists c, In c (x0 :: l) /\ cball H c n y) x) as [r0' R0'].
       exists x0; exists x0;split; [left;auto|apply real_lt_le;apply ball_contains_center].
       replace (fun y => exists c, In c (a :: x0 :: l) /\ cball H c n y) with (union (cball H a n) (fun y => exists c, In c (x0 :: l) /\ cball H c n y)).
       intros.
       destruct R0', R1'.
       pose proof (dist_union H x (cball H a n) (fun y => exists c, In c (x0 :: l) /\ cball H c n y) _ _ H3 H1).
       rewrite (dist_unique _ _ _ _ _ H0 H5).
       apply min_approx;auto.
       apply fun_ext; intros; apply Prop_ext;intros.
       destruct H0.
       exists a.
       split;simpl;auto.
       destruct H0.
       exists x2.
       destruct H0.
       split;simpl;auto.
       destruct H0.
       destruct H0.
       destruct H0.
       left.
       rewrite H0;auto.
       right.
       exists x2;split;auto.
  Qed.
  Lemma totally_bounded_dist H A x n (B : totally_bounded_cball H A) r1 r2: dist H (nth_cover H A B n) x r1 -> dist H A x r2 -> abs (r1 - r2) <= prec n + prec n + prec n.
  Proof.
    intros.
    apply real_abs_le_le_le.
    add_both_side_by r2.
    apply (real_le_le_le _ _ _ (totally_bounded_dist2 _ _ _ _ _ _ _ H0 H1)).
    add_both_side_by (-r2).
    apply real_lt_le.
    apply real_lt_pos_mult_pos_pos; try apply prec_pos.
    apply real_gt0_gt0_plus_gt0; try apply real_1_gt_0.
    apply real_gt0_gt0_plus_gt0; try apply real_1_gt_0.
    add_both_side_by r1.
    apply (real_le_le_le _ _ _ (totally_bounded_dist1 _ _ _ _ _ _ _ H0 H1)).
    ring_simplify.
    apply real_le_triv.
  Qed.

    Lemma totally_bounded_located H A : (exists x, A x) -> totally_bounded H A -> located H A.
  Proof.
    intros.
    apply totally_bounded_whichever1 in X0.
    intros x.
    apply real_limit_P.
    apply classical_dist_exists;auto.
    enough (forall n, {r | forall r', dist H (nth_cover H A X0 n) x r' -> abs (r-r') <= real_2 * prec n}).
    {
      intros.
      destruct (X1 (n+3)%nat) as [r R].
      replace (real_2 * prec (n+3)) with (prec (n+2)) in R by (unfold real_2;rewrite <-prec_twice; replace (n+2+1)%nat with (n+3)%nat by lia; ring).
      exists r.
      destruct (classical_dist_exists H A x H0) as [r0 R0].
      exists r0.
      split.
      apply R0.
      destruct (classical_dist_exists H (nth_cover H A X0 (n+3)) x) as [r1 R1].
      - destruct H0.
        exists x0.
        apply nth_cover_superset;auto.
     -  destruct R1.
        specialize (R _ H1).
        apply (real_le_le_le _ _ _ (RealMetric.dist_tri _ r1 _)).
        rewrite <-prec_twice.
        rewrite <-prec_twice at 1.
        rewrite real_plus_assoc.
        apply (real_le_le_plus_le).
        replace (n+1+1)%nat with (n+2)%nat by lia.
        apply R.
        destruct R0.
        pose proof (totally_bounded_dist H _ _ _ _ _ _  H1 H3).
        rewrite <-(prec_twice (n+1)%nat).
        replace (n+1+1)%nat with (n+2)%nat by lia.
        rewrite <-real_plus_assoc.
        apply (real_le_le_le _ _ _ H5).
        apply (real_le_le_plus_le);try apply real_le_le_plus_le; try (apply real_lt_le;apply prec_monotone;lia).
    }
    intros.
    unfold nth_cover.
    destruct (X0 n) as [l [L1 L2]].
    apply list_ball_dist_approx.
 Qed.
  Lemma located_dist_fun H A : located H A -> {f | forall x, exists r, dist H A x r /\ (f x) = r}.
  Proof.
    intros.
    exists (fun x=> pr1 _ _ (X0 x)).
    intros.
    destruct (X0 x);simpl;auto.
    exists x0;auto.
  Qed.
  Lemma choice_constr (T T' : Type) P : (forall (n :T'), {x : T | P x }) -> {f : T' -> T | forall n, P (f n)}.
  Proof.
    intros.
    exists (fun x => pr1 _ _ (X0 x)).
    intros.
    destruct (X0 n);simpl;auto.
  Qed.

  Lemma located_nonempty H (s : separable) A  : located H A -> exists x, A x.
  Proof.
    intros.
    specialize (X0 (D s 0)).
    destruct X0.
    apply dist_bounded_exists_gt in d.
    destruct d as [y []];auto.
    exists y;auto.
  Qed.
  Lemma dist_zero H x : d_X H x x = real_0.
  Proof.
    destruct H as [d [D1 D2]];simpl.
    apply D1;auto.
  Qed.

  Lemma prec_monotone_eq n m : (m <= n)%nat -> prec n <= prec m.
  Proof.
    intros.
    apply Lt.le_lt_or_eq_stt in H.
    destruct H.
    apply real_lt_le.
    apply prec_monotone;auto.
    rewrite H.
    apply real_le_triv.
  Qed.

  Lemma located_refinement H (s : separable) (l : has_limit H)  A c0 n0: complete H A -> located H A -> (exists r, dist H A c0 r /\ r < prec (S (S n0))%nat) -> ^M {x | A x /\ d_X H c0 x <= prec n0}.
  Proof.
    intros.
    destruct (located_dist_fun _ _ X1) as [d Hd].
    assert (d c0 < prec (S (S n0))) as Hdc0.
    {
      destruct H0 as [r [R1 R2]].
      destruct (Hd c0) as [_ [R <-]].
      replace (d c0) with r;auto.
      apply (dist_unique _ _ _ _ _ R1 R).
    }
    enough (^M {f : nat -> X | metric_is_fast_cauchy H f /\ (forall n, d (f n) <= prec n) /\ (forall m, (m <= n0)%nat -> f m = c0)}).
    {
      revert X2.
      apply M_lift.
      intros [f [F1 [F2 F3]]].
      destruct (l _ F1).
      exists x.
      split.
      apply (dist_bounded_complete_contained H);auto.
      split.
      intros.
      apply d_nonneg.
      intros.
      apply lim_le_le.
      intros.
      replace (0+prec n) with (prec n) by ((replace 0 with real_0 by auto);ring).
      destruct (Hd (f (n+2)%nat)) as [d0 [D0 <-]].
      destruct (dist_bounded_exists_lt _ _ _ _ D0 (n+2)%nat) as [y [Hy1 Hy2]].
      apply (real_le_lt_lt _ _ _ (H1 _ Hy1)).
      apply (real_le_lt_lt  _ _ _ (dx_triangle _ _ _ (f (n+2)%nat))).
      rewrite <-prec_twice.
      apply (real_lt_lt_plus_lt).
      rewrite d_sym.
      apply (real_le_lt_lt _ _ _ (m _)).
      apply prec_monotone;lia.
      rewrite d_sym.
      apply (real_lt_le_lt _ _ _ Hy2).
      rewrite <-(prec_twice (n+1)).
      replace (n+1+1)%nat with (n+2)%nat by lia.
      apply (real_le_le_plus_le).
      apply F2.
      apply real_le_triv.
      replace c0 with (f n0) by (apply F3;lia).
      apply m.
    }
    
    enough (^M {x0 | d x0 < prec 0 /\ ((0 <= (S (S n0)))%nat -> x0 = c0)} * forall n (x : {y | d y < prec n /\ ((n <= (S (S n0)))%nat -> y = c0)}),  ^M {y : {y | d y < prec (S n)%nat /\ (((S n) <= (S (S  n0)))%nat -> y = c0)} | d_X H (pr1 _ _ x) (pr1 _ _ y) < real_2*(prec n)%nat }).
    {
      destruct X2.
      pose proof M_paths.
      pose proof (M_paths _ _ m m0).
      revert X3.
      apply M_lift.
      intros [f Hf].
      exists (fun x => pr1 _ _ (f (S (S x)))).
      split.
      apply fast_cauchy_neighbor.
      intros.
      specialize (Hf (S (S n))).
      apply real_lt_le.
      replace (prec (S n)) with (real_2 * (prec (S (S n)))).
      apply Hf.
      rewrite <-(prec_twice (S n)).
      replace (S n +1)%nat with (S (S n)) by lia.
      unfold real_2;ring.
      split.
      intros.
      destruct (f ((S  (S n)))).
      destruct a;simpl.
      apply real_lt_le;apply (real_lt_lt_lt _ _ _ r).
      apply prec_monotone;lia.
      intros.
      destruct (f (S (S m1)));simpl.
      destruct a.
      apply H3.
      lia.
    }
    split.
    - apply M_unit.
      exists c0.
      split;intros;auto.
      apply (real_lt_lt_lt _ _ _ Hdc0).
      apply prec_monotone;lia.
   - intros.
     destruct x;simpl pr1.
     enough (^M {y : X | (d y < (prec (S n)) /\ ((S n <= (S (S n0)))%nat -> y =c0)) /\  d_X H x y < real_2*prec n}) by (revert X2;apply M_lift; intros [y [Y1 Y2]];exists (exist _ y Y1);simpl;auto).
     destruct (le_gt_dec (S n) (S (S n0))).
     apply M_unit.
     exists c0.
     split.
     split;intros;auto.
     apply (real_lt_le_lt _ _ _ Hdc0).
     apply prec_monotone_eq;lia.
     destruct a.
     rewrite H2; try lia.
     rewrite dist_zero.
     replace real_0 with (real_2 * real_0) by ring.
     apply real_lt_mult_pos_lt.
     apply real_lt_0_2.
     apply prec_pos.

     enough (^M {y : X | d y < prec (S n) /\  d_X H x y < real_2*prec n}).
     revert X2;apply M_lift; intros [y [Y1 Y2]];exists y;simpl;auto;split;auto;split;auto;lia.
     apply (separable_open_choice s).
     apply open_intersection;apply semidec_open;intros;apply real_lt_semidec.
     destruct (Hd x) as [_ [R <-]].
     pose proof (dist_bounded_exists_lt _ _ _ _ R n).
     destruct H1 as [y [Y1 Y2]].
     exists y.
     split.
     destruct (Hd y) as [_ [Ry <-]].
     destruct Ry.
     apply (real_le_lt_lt _ _ _ (H1 _ Y1)).
     rewrite dist_zero.
     apply prec_pos.
     rewrite d_sym.
     apply (real_lt_le_lt _ _ _ Y2).
     replace (real_2 * prec n) with (prec n + prec n) by (unfold real_2;ring).
     apply (real_le_le_plus_le);[apply real_lt_le|apply real_le_triv];auto.
     apply a.
  Qed.

  Lemma located_choice H (s : separable) (l : has_limit H)  A : complete H A -> located H A -> ^M {x | A x}.
  Proof.
    intros.
    destruct (located_dist_fun _ _ X1) as [d Hd].
    enough (^M {x0 | d x0 < prec 2}).
    {
      revert X2.
      apply M_lift_dom.
      intros [c0 Hc0].
      assert (exists r, dist H A c0 r /\ r < prec 2).
      {
        exists (d c0);split;auto.
        destruct (Hd c0) as [_ [R <-]];auto.
      }
      specialize (located_refinement H s l A c0 0%nat X0 X1 H0).
      apply M_lift.
      intros [x [Hx _]].
      exists x;auto.
    }
    apply (separable_open_choice s).
    apply semidec_open.
    intros.
    apply real_lt_semidec.
    destruct (located_nonempty _ s _ X1).
    exists x.
    destruct (Hd x) as [r [[R1 R2] <-]].
    apply (real_le_lt_lt _ _ _ (R1 _ H0)).
    rewrite dist_zero;apply prec_pos.
  Qed.
  Definition totally_bounded_strong (H : metric) (U : (@csubset X)) := forall n, {L : list X | (forall x, In x L -> U x) /\ forall x,  U x ->  Exists  (ball H x n) L}.
  

  Definition bishop_compact_centered H (s : separable) (lm : has_limit H) A : totally_bounded H A -> complete H A -> ^M (totally_bounded_strong H A).
  Proof.
    
    intros.
    apply M_countable_lift.
    intros.
    enough (forall l,  ((forall x, In x l -> intersects (ball H x (n+3)) A)) -> ^M {l' | (forall x, In x l' -> A x) /\ is_subset (fun x => Exists (ball H x (n+3)) l) (fun x => Exists (ball H x n) l') }) . 
    {
      destruct (X0 (n+3)%nat) as [l [L1 L2]].
      specialize (X2 _ L1).
      revert X2.
      apply M_lift.
      intros [l' [L1' L2']].
      exists l'.
      split;auto.
    }
    intros.
    induction l.
    apply M_unit.
    exists [].
    split;intros;simpl.
    contradict H1;auto.
    intros x0 Hx0.
    apply Exists_nil in Hx0.
    contradict Hx0.

    assert (forall x, In x l -> intersects (ball H x (n+3)%nat) A).
    {
      intros.
      apply H0.
      right;auto.
    }
    specialize (IHl H1).
    revert IHl.
    apply M_lift_dom.
    intros [l' L'].
    assert (exists x, A x).
    destruct  (H0 a);[left;auto|];destruct H2; exists x;auto.
    pose proof (totally_bounded_located H A H2 X0).
    assert (exists r, dist H A a r /\ r < prec (S (S (S n)))).
    {
      destruct (X2 a).
      exists x.
      split;auto.
      destruct d.
      destruct (H0 a); [left;auto|].
      destruct H5.
      apply (real_le_lt_lt _ (d_X H a x0)).
      apply H3;auto.
      replace (S (S (S n))) with (n+3)%nat by lia.
      apply H5.
    }
    specialize (located_refinement H s lm A a _ X1 X2 H3).
    apply M_lift.
    intros [a0 [Ha1 Ha2]].
    exists  (a0 :: l').
    split.
    - intros.
      destruct H4.
      rewrite <-H4;auto.
      apply L';auto.
    - replace (fun x => Exists (ball H x (n+3)) (a :: l)) with (union (fun x => ball H x (n+3) a) (fun x => (Exists (ball H x (n+3)%nat) l) )).
      + apply union_subset.
        split.
        intros x0 Hx0.
        apply Exists_exists.
        exists a0.
        split;[try  left|];auto.
        unfold ball.
        apply (real_le_lt_lt _ _ _ (dx_triangle H _ _ a)).
        rewrite <- prec_twice.
        rewrite real_plus_comm.
        apply (real_le_lt_plus_lt).
        replace (n+1)%nat with (S n) by lia.
        apply Ha2.
        apply (real_lt_lt_lt _ _ _ Hx0).
        apply prec_monotone;lia.
        intros x0 Hx0.
        apply Exists_cons_tl.
        apply L';auto.
     + apply fun_ext; intros.
       apply Prop_ext;intros.
       destruct H4.
       apply Exists_cons_hd;auto.
       apply Exists_cons_tl;auto.
       apply Exists_cons in H4.
       destruct H4.
       left;auto.
       right;auto.
  Qed.
  Lemma totally_bounded_strong_impl H A : totally_bounded_strong H A -> totally_bounded H A.
  Proof.
    intros.
    intros n.
    destruct (X0 n).
    exists x.
    destruct a.
    split;auto.
    intros.
    exists x0.
    split;auto.
    apply ball_contains_center.
  Qed.

  Lemma close_enough_contained H x c n m : d_X H x c < prec m - prec n -> is_subset (ball H x n) (ball H c m).
  Proof.
    intros.
    intros y By.
    apply (real_le_lt_lt _ _ _ (dx_triangle H _ _ x)).
    apply (real_lt_lt_lt _ (d_X H c x + prec n)).
    add_both_side_by (-d_X H c x);auto.
    rewrite d_sym.
    add_both_side_by (-prec n).
    apply (real_lt_le_lt _ _ _ H0).
    add_both_side_by (prec n);apply real_le_triv.
  Qed.

    Lemma separable_metric_nonempty_second_countable (H : metric) (s : separable) (l : has_limit H) U : (exists x, U x) -> open U -> ^M {f : nat -> (nat * nat) | U = countable_union (fun n => ball H (D s (fst (f n))) (snd (f n)))}.
    Proof.
      intros.
    specialize (separable_metric_second_countable H s l _ X0).
    apply M_lift.
    intros [f F].
    assert ({n : nat | exists fn, f n = Some fn }) as [m N].
    {
      apply ConstructiveEpsilon.constructive_indefinite_ground_description_nat.
      - intros.
        destruct (f n) eqn: Fn.
        left; exists  p;auto.
        right.
        intros H1.
        destruct H1.
        discriminate H1.
      - rewrite F in H0.
        destruct H0.
        destruct H0.
        exists x0.
        destruct (f x0);auto.
        exists p;auto.
        contradict H0.
    }
    assert {fm | f m = Some fm } as [fm Fm].
    { destruct (f m).
      exists p;auto.
      exists (0,0)%nat.
      destruct N.
      discriminate H1.
    }
    exists (fun n => match (f n) with | Some nm => nm | None => fm  end).
    rewrite F.
    apply fun_ext; intros; apply Prop_ext;intros.
    destruct H1.
    exists x0.
   destruct (f x0);auto.
   contradict H1.
   destruct H1.
   destruct (f x0) eqn:F0;simpl.
   exists x0;rewrite F0;auto.
   exists m.
   rewrite Fm;auto.
 Qed.

  Definition countable_union_base H s (b : nat -> (option (nat * nat))) := countable_union (fun n => match (b n) with (Some mn) => (ball H (D s (fst mn)) (snd mn)) | None => (fun _ => False) end).

  Definition finite_union_base H s (b : nat -> (option (nat * nat))) N x := exists n, (n < N)%nat /\ exists mn, (b n) = (Some mn) /\ (ball H (D s (fst mn)) (snd mn) x).  

 (*  Lemma fin_cover_compact (H : metric) (s :separable) (l : has_limit H) (K : (@csubset X)) :  (forall b, is_subset K (countable_union_base H s b) -> (exists m, is_subset K (finite_union_base H s b m)))  -> (forall b m, {s0 : sierp | sierp_up s0 <-> is_subset K (finite_union_base H s b m)})  -> compact K. *)
 (*  Proof. *)
 (*    intros. *)
 (*    intros U Hu. *)
 (*    apply M_hprop_elim. *)
 (*    intros a b;destruct a,b;apply sigma_eqP2;apply sierp_id;split;rewrite i0;rewrite i;auto. *)
 (*    specialize (separable_metric_second_countable H s l _ Hu). *)
 (*    apply M_lift. *)
 (*    intros [f F]. *)
 (*    assert ({f' : nat -> nat*nat | U = countable_union (fun n x => ((snd (f' n)) > 0)%nat /\ (ball H (D s (fst (f' n))) (snd (f' n)) x))}). *)
 (*    { *)

 (*    }   *)
 (*    destruct f as [f F0];simpl in *. *)
 (*    specialize (H0 f F0). *)
 (*    specialize (X0 f F0). *)
 (*    remember (fun n => (pr1 _ _ (X0 n))) as g. *)
 (*    destruct (eventually_true g). *)
 (*    exists x. *)
 (*    rewrite i. *)
 (*    split. *)
 (*    rewrite Heqg; intros [n N]; destruct (X0 n);simpl in *. *)
 (*    destruct i0. *)
 (*    specialize (H1 N). *)
 (*    intros y Hy. *)
 (*    destruct (H1 _ Hy). *)
 (*    rewrite F. *)
 (*    exists x1;apply H3. *)
 (*    rewrite F. *)
 (*    intros HK. *)
 (*    destruct (H0 HK). *)
 (*    rewrite Heqg. *)
 (*    exists x0. *)
 (*    destruct (X0 x0);simpl. *)
 (*    apply i0;auto. *)
 (* Qed. *)

  (* Definition is_base_element (H : metric) (s : separable) (U : (@csubset X))  := {bi : option (nat * nat) | (forall nm, bi = Some nm -> U = ball H (D s (fst nm)) (snd nm)) /\ (bi = None -> U = (fun _ => False))} . *)

  (* Definition is_base_sequence H s (U : nat -> (@csubset X))  := forall n, is_base_element H s (U n). *)
 (*    Lemma separable_metric_second_countable_base (H : metric) (s : separable) (l : has_limit H) U :  open U -> ^M {fb : {f : nat -> (@csubset X) & (is_base_sequence H s f)} | U = countable_union (projT1 fb)}. *)
 (*    Proof. *)
 (*      intros. *)
 (*      specialize (separable_metric_second_countable H s l _ X0). *)
 (*      apply M_lift. *)
 (*      intros [f F]. *)
 (*      remember  *)
 (*      (fun n : nat => *)
 (*         match f n with *)
 (*         | Some nm => ball H (D s (fst nm)) (snd nm) *)
 (*         | None => fun _ : X => False *)
 (*         end) as f0. *)
 (*      assert (is_base_sequence H s f0). *)
 (*      rewrite Heqf0. *)
 (*      intros n;  exists (f n);split;intros. *)
 (*      destruct (f n);auto. *)
 (*      injection H0. *)
 (*      intros. *)
 (*      rewrite H1;auto. *)
 (*      discriminate H0. *)
 (*      rewrite H0;auto. *)
 (*      exists (existT _ f0 H0). *)
 (*      simpl;auto. *)
 (* Qed. *)

  Lemma fin_cover_compact (H : metric) (s :separable) (l : has_limit H) (K : (@csubset X)) : (forall b, is_subset K (countable_union_base H s b) -> (exists N, (is_subset K (finite_union_base H s b N)))) -> (forall b m, {s0 : sierp | sierp_up s0 <-> is_subset K (finite_union_base H s b m)})  -> compact K.
  Proof.
    intros.
    intros U Hu.
    apply M_hprop_elim.
    intros a b;destruct a,b;apply sigma_eqP2;apply sierp_id;split;rewrite i0;rewrite i;auto.
    specialize (separable_metric_second_countable H s l _ Hu).
    apply M_lift.
    intros [f F].
    specialize (H0 f).
    specialize (X0 f).
    remember (fun n => (pr1 _ _ (X0 n))) as g.
    destruct (eventually_true g).
    exists x.
    rewrite i.
    split.
    rewrite Heqg; intros [n N]; destruct (X0 n);simpl in *.
    destruct i0.
    specialize (H1 N).
    intros y Hy.
    destruct (H1 _ Hy).
    rewrite F.
    destruct H3.
    destruct H4.
    destruct H4.
    exists x1.
    rewrite H4;auto.
    rewrite F.
    intros HK.
    destruct (H0 HK).
    rewrite Heqg.
    exists x0.
    destruct (X0 x0);simpl.
    apply i0;auto.
 Qed.
 (*  Lemma fin_cover_compact (H : metric) (s :separable) (l : has_limit H) (K : (@csubset X)) : (forall b, is_base_sequence H s b ->  is_subset K (countable_union b) -> (exists m, (forall x, K x -> exists n, (n < m)%nat /\ ((b n) x)))) -> (forall b, is_base_sequence H s b ->  forall m, {s : sierp | sierp_up s <-> (forall x, K x -> exists n, (n < m)%nat /\ ((b n) x))})  -> compact K. *)
 (*  Proof. *)
 (*    intros. *)
 (*    intros U Hu. *)
 (*    apply M_hprop_elim. *)
 (*    intros a b;destruct a,b;apply sigma_eqP2;apply sierp_id;split;rewrite i0;rewrite i;auto. *)
 (*    specialize (separable_metric_second_countable_base H s l _ Hu). *)
 (*    apply M_lift. *)
 (*    intros [f F]. *)
 (*    destruct f as [f F0];simpl in *. *)
 (*    specialize (H0 f F0). *)
 (*    specialize (X0 f F0). *)
 (*    remember (fun n => (pr1 _ _ (X0 n))) as g. *)
 (*    destruct (eventually_true g). *)
 (*    exists x. *)
 (*    rewrite i. *)
 (*    split. *)
 (*    rewrite Heqg; intros [n N]; destruct (X0 n);simpl in *. *)
 (*    destruct i0. *)
 (*    specialize (H1 N). *)
 (*    intros y Hy. *)
 (*    destruct (H1 _ Hy). *)
 (*    rewrite F. *)
 (*    exists x1;apply H3. *)
 (*    rewrite F. *)
 (*    intros HK. *)
 (*    destruct (H0 HK). *)
 (*    rewrite Heqg. *)
 (*    exists x0. *)
 (*    destruct (X0 x0);simpl. *)
 (*    apply i0;auto. *)
 (* Qed. *)
  
Lemma bot_exists : ({s : sierp | (not (sierp_up s))}).
  Proof.
     enough {s : sierp | sierp_up s <-> False}.
     destruct X0.
     exists x.
     rewrite i;auto.
     apply sierp_from_semidec.
     exists lazy_bool_false.
     unfold lazy_bool_up.
     split; intros.
     contradict H.
     apply lazy_bool_distinct.
     destruct H.
 Qed.

  Definition ball_in_base_finseq H s (c : X) n b N :=  (exists (i : nat) x m, (i < N)%nat /\ (b i) = Some (x,m) /\ d_X H c (D s x) < prec m - prec n).

  

  Lemma ball_in_base_sequence_semidec H s c n b N : semidec (ball_in_base_finseq H s c n b N).
  Proof.
    intros.
    induction N.
    exists lazy_bool_false.
    unfold lazy_bool_up; split;intros;[contradict H0;apply lazy_bool_distinct|].
    destruct H0 as [n' [x [m M]]];lia.
    destruct IHN as [k K].
    unfold semidec.
    enough ({k' | lazy_bool_up _ k' <->  exists x m, (b N) = Some (x,m) /\ (d_X H c (D s x) < prec m - prec n)}).
    {
      destruct X0.
      unfold lazy_bool_up in *.
      exists (lazy_bool_or k x).
      rewrite lazy_bool_or_up.
      split; intros.
      destruct H0.
      destruct K.
      destruct (H1 H0) as [i0 [x1 [m0 M]]].
      exists i0; exists x1;exists m0.
      split;try apply M;lia.
      destruct i.
      destruct (H1 H0) as [x1 [m0 M]].
      exists N; exists x1; exists m0.
      split;auto;lia.
      destruct H0 as [i0 [x1 [m1 [M1 M2]]]].
      assert (i0 < N \/ i0 = N)%nat by lia.
      destruct H0.
      left.
      apply K.
      exists i0; exists x1; exists m1;split;auto.
      right.
      apply i.
      destruct M2.
      exists x1; exists m1;rewrite <-H1;auto.
   }
    destruct (b N).
    destruct p;simpl in *.
    destruct (real_lt_semidec (d_X H c (D s n0)) (prec n1 - prec n)).  
    exists x.
    rewrite i.
    split;intros.
    exists n0; exists n1;auto.
    destruct H0 as [x0 [m0 [M1 M2]]].
    injection M1.
    intros -> ->;auto.

    exists lazy_bool_false.
    unfold lazy_bool_up; split;intros;[contradict H0;apply lazy_bool_distinct|].
    destruct H0 as [x [m [M1 _]]].
    discriminate M1.
  Qed.
  Lemma ball_in_base_finseq_contained H s c n b N : ball_in_base_finseq H s c n b N -> is_subset (ball H c n) (finite_union_base H s b N).
  Proof.
    intros.
    destruct H0 as [i [n1 [n2 [H2 [H3 H4]]]]].
    intros y Hy.
    exists i;split;auto.
    exists (n1,n2);split;auto;simpl.
    pose proof (close_enough_contained H _ _ _ _ H4 ).
    apply H0;auto.
  Qed.

  Lemma Exists_semidec {T: Type} f l : (forall (x : T), semidec (f x)) -> semidec (Exists f l).
  Proof.
     intros.
     induction l.
     exists lazy_bool_false.
    unfold lazy_bool_up; split;intros;[contradict H;apply lazy_bool_distinct|].
    apply Exists_nil in H;contradict H.
    destruct IHl.
    destruct (X0 a).
    exists (lazy_bool_or x0 x).
    unfold lazy_bool_up in *.
    rewrite lazy_bool_or_up.
    rewrite Exists_cons.
    rewrite i0, i;split;auto.
  Qed.

  Lemma Forall_semidec {T: Type} f l : (forall (x : T), semidec (f x)) -> semidec (Forall f l).
  Proof.
     intros.
     induction l.
     exists lazy_bool_true.
     unfold lazy_bool_up; split;intros;auto.
     destruct IHl.
     destruct (X0 a).
     exists (lazy_bool_and x0 x).
     unfold lazy_bool_up in *.
     rewrite lazy_bool_and_up.
     rewrite Forall_cons_iff.
    rewrite i0, i;split;auto.
  Qed.
Search compact.
Lemma bishop_compact_classically_seqcompact H (s : separable) (l : has_limit H) K : totally_bounded H K -> complete H K -> forall (f : nat -> X), (forall n, K (f n)) -> exists (g : nat -> nat), (forall n, (g (n+1) > g n)%nat /\ (g n >= n)%nat) /\ exists y, K y /\ metric_is_fast_limit H (fun n => (f (g n))) y.
                                                                                    Proof.

    intros.
    enough (forall x n, (forall m, exists i, (i > m)%nat /\ d_X H (f i) x < prec n) -> (exists j, (j > n)%nat /\ d_X H x (f j) < prec n /\  forall m, exists i, (i > m)%nat /\ d_X H (f i) (f j) < prec (n+1)%nat)).
    
  Admitted.

  Lemma bishop_compact_compact H (s : separable) (l : has_limit H) K : totally_bounded H K -> complete H K -> compact K.
  Proof.
    intros.
    apply (fin_cover_compact H s);auto.

    - admit.
    - intros.
      apply M_hprop_elim.
      intros x0 x1;destruct x0,x1;apply sigma_eqP2;apply sierp_id;split;rewrite i0;rewrite i;auto.
      specialize (bishop_compact_centered H s l K X0 X1).
      apply M_lift;intros.
      enough ({f : nat -> sierp | (forall k, sierp_up (f k) -> Forall (fun x => is_subset (ball H x k) (finite_union_base H s b m)) (pr1 _ _ (X2 k))) /\ (is_subset K (finite_union_base H s b m) -> (exists k, sierp_up (f k)))}).
      {
        destruct X3 as [f [F1 F2]].
        pose proof (eventually_true f).
        destruct X3.
        exists x.
        rewrite i.
        split.
        - intros [k Pk].
          intros y Ky.
          specialize (F1 _ Pk).
          destruct (X2 k);simpl in *.
          destruct a.
          specialize (H1 _ Ky).
          rewrite Forall_forall in F1.
          apply Exists_exists in H1.
          destruct H1 as [y1 [Py1 Qy1]].
          apply (F1 _ Py1).
          unfold ball.
          rewrite d_sym;auto.
       - intros.
         destruct (F2  H0).
         exists x0;auto.
      }
        assert ({f : nat -> sierp | forall k, sierp_up (f k) <-> (Forall (fun x =>  (ball_in_base_finseq H s x k b m)) (pr1 _ _ (X2 k)))}) as [f F].
        {
          enough (forall k, {s0 |sierp_up s0 <-> (Forall (fun x =>  (ball_in_base_finseq H s x k b m)) (pr1 _ _ (X2 k)))}).
          exists (fun k => pr1 _ _ (X3 k));intros k;destruct (X3 k);simpl;auto.
          intros.
          apply sierp_from_semidec.
          destruct (X2 k);simpl.
          apply Forall_semidec.
          intros x0.
          apply ball_in_base_sequence_semidec.
        }
        exists f.
        split.
        + intros; destruct (F k), (X2 k);simpl in *.
          specialize (H1 H0).
          apply Forall_forall.
          intros.
          rewrite Forall_forall in H1.
          specialize (H1 _ H3).
          apply ball_in_base_finseq_contained;auto.
       + intros.
         enough (exists k, Forall (fun x =>  (ball_in_base_finseq H s x k b m)) (pr1 _ _ (X2 k))) by (destruct H1;exists x;apply F;auto).
         apply Classical_Pred_Type.not_all_not_ex.
         intros H1.
         enough (exists f x, (forall n, K (f n)) /\  metric_is_fast_limit H f x /\ (not (K x))).
         destruct H2 as [ff [x [Hf1 [Hf2 Hf3]]]].
         contradict Hf3.
         destruct (X1 ff Hf1 (fast_limit_fast_cauchy _ _ _ Hf2)) as [x' [Px1 Px2]].
         rewrite (metric_limit_unique H ff _ x');auto.
         assert (forall n, exists x, K x /\ (forall i, (i < m)%nat -> forall n0 n1, (b i) = Some (n0,n1) -> d_X H x (D s n0) >= prec n1 - prec n)).
         {
           intros n.
           specialize (H1 n).
           apply Exists_Forall_neg in H1; [|intros;apply lem].
           destruct (X2 n); simpl in *.
           apply Exists_exists in H1.
           destruct H1 as [x0 [Hx0 Hx1]].
           exists x0.
           destruct a.
           split; [apply H1;auto|].
           intros.
           unfold ball_in_base_finseq in Hx1.
           apply real_nge_le.
           intros H5.
           contradict Hx1.
           exists i; exists n0; exists n1;split;auto;split;auto.
         }
         apply countable_choice in H2.
         destruct H2 as [f0 F0].
         destruct (bishop_compact_classically_seqcompact H s l _ X0 X1 f0) as [g [G1 G2]]; try apply F0.
         exists (fun n => f0 (g n)).
         destruct G2.
         exists x.
         destruct H2.
         split.
         intros.
         apply F0.
         split;auto.
         intros Hk.
         specialize (H0 _ Hk).
         destruct H0 as [m1 [M0 M1]].
         destruct M1 as [[n0 n1] [A1 A2]].
         simpl in *.

         assert (forall n, d_X H (D s n0) x >= prec n1 - prec n).
         {
           enough (forall n, d_X H (D s n0) x >= prec n1 - prec (n+1)%nat - prec (g (n+1)%nat)).
           intros.
           apply (real_le_le_le _ (prec n1 - prec (n+1) - prec (g (n+1)%nat)));try apply H0.
           rewrite <-(prec_twice n).
           add_both_side_by (prec (n+1) - prec n1 + prec (n+1) + (prec (g (n+1)%nat))).
           apply prec_monotone_eq.
           apply G1.
           intros.
           destruct (F0 (g (n+1))%nat).
           add_both_side_by (prec (n+1)).
           specialize (H4 _ M0 _ _ A1).
           apply (real_le_le_le _ _ _ H4).
           apply (real_le_le_le _ _ _ (dx_triangle _ _ _ x)).
           rewrite (d_sym _ x).
           add_both_side_by (- d_X H (D s n0) x).
           apply H3.
         }
         assert (prec n1 <= d_X H (D s n0) x) by (apply lim_le_le';intros n;add_both_side_by (-prec n);apply H0).
         contradict H4.
         apply real_gt_nle;auto.
   Admitted.       
  Lemma bishop_compact_overt H (s : separable) (l : has_limit H) A : totally_bounded H A -> complete H A -> overt A.
  Proof.
    intros.
    intros U Uopen.
    apply M_hprop_elim.
    {
      intros a b.
      destruct a,b;simpl in *.
      apply sigma_eqP2.
      apply sierp_id.
      rewrite i, i0;split;auto.
    }
    specialize (separable_metric_second_countable H s l _ Uopen).
    assert ({s : sierp | sierp_up s <-> intersects A (fun _ => False)}) as [bot B].
    {
        apply sierp_from_semidec.
        exists lazy_bool_false.
        unfold lazy_bool_up.
        split; intros.
        contradict H0.
        apply lazy_bool_distinct.
        destruct H0.
        destruct H0.
        contradict H1.
    }
    apply M_lift.
    intros [f F].
    enough (forall c n, {k : sierp | sierp_up k <-> intersects A (ball H c n)}).
    {
      assert ({t : nat -> sierp | forall n, sierp_up (t n) <-> intersects A (match f n with
                                                              | Some nm => ball H (D s (fst nm)) (snd nm)
                                                              | None => fun _ => False
                                                              end)}) as [t T].
      
      exists (fun n => match (f n) with
               | Some nm => pr1 _ _ (X2 (D s (fst nm)) (snd nm))
               | None => bot
               end).
      intros.
      destruct (f n);auto.
      destruct (X2 (D s (fst p)) (snd p));simpl in *.
      rewrite i;split;auto.
      destruct (eventually_true t).
      exists x.
      rewrite i.
      split;intros.
      destruct H0.
      rewrite F.
      destruct (T x0).
      destruct (H1 H0).
      exists x1.
      destruct H3.
      split;auto.
      exists x0;auto.
      rewrite F in H0.
      destruct H0.
      destruct H0.
      destruct H1.
      exists x1.
      apply T.
      exists x0.
      split;auto.
    }
    intros.
    assert (dec (exists x, (A x))).
    {
      destruct (X0 0%nat).
      destruct x;destruct a.
      right.
      intros Hx.
      destruct Hx.
      specialize (H1 _ H2).
      apply Exists_exists in H1.
      destruct H1.
      destruct H1.
      contradict H1.
      left.
      assert (In x (x :: x0)) by (left;auto).
      specialize (H0 _ H2).
      destruct H0.
      destruct H0.
      exists x1;auto.
    }
    destruct H0; [|exists bot; rewrite B;split;intros [];destruct H0;[contradict H1|contradict n0;exists x;auto]].
    destruct (totally_bounded_located _ _ e X0 c) as [r R].
    apply sierp_from_semidec.
    destruct (real_lt_semidec r (prec n)).
    exists x.
    rewrite i.
    split; intros.
    destruct (dist_bounded_exists_complete_lt _ _ _ _ (bishop_compact_compact _ s l _ X0 X1) R) as [a [A1 A2]].
    exists a.
    split;auto.
    unfold ball.
    rewrite d_sym.
    apply (real_le_lt_lt _ _ _ A2);auto.
    destruct H0 as [a [A1 A2]].
    destruct R.
    apply (real_le_lt_lt _ (d_X H c a));auto.
    apply H0;auto.
  Qed.

  Definition M_test H A := forall x n, ^M ({exists r', r' < real_2*prec n /\ dist H A x r'} + {exists r', r' >  prec n /\ dist H A x r'}).

  Lemma M_test_nonempty H (s : separable) A  : M_test H A -> exists x, A x.
  Proof.
    intros.
    specialize (X0 (D s 0) 0%nat).
    apply M_hprop_elim.
    intros a b; apply irrl.
    revert X0.
    apply M_lift.
    intros [];destruct e;destruct H0;destruct (dist_bounded_exists_gt _ _ _ _ H1);exists x0;apply H2.
  Qed.

  Lemma located_Mtest H A : located H A -> M_test H A.
  Proof.
    intros.
    intros x n.
    destruct (X0 x).
    specialize (M_split x0 (prec n + prec (n+1)%nat) (prec (n+1)%nat) (prec_pos _)).
    apply M_lift.
    intros [].
    right.
    ring_simplify in r.
    exists x0;split;auto.
    left.
    exists x0;split;auto.
    replace (real_2 * prec n) with (prec n + ((prec (n+1)%nat) + (prec (n+1)%nat))).
    add_both_side_by (-prec (n+1));auto.
    rewrite real_plus_comm.
    apply r.
    rewrite prec_twice.
    unfold real_2;ring.
  Qed.
  (* Lemma Mtest_located H A : M_test H A -> located H A. *)
  (* Admitted. *)

  (* Lemma test : (0 = 1)%nat. *)
  (* Proof. *)
  (*    destruct (cont (fun x => 0%nat) (fun n => 0%nat)) as [m M] eqn: E. *)
  (*    remember (fun b => (pr1 _ _ (cont (fun a => (b (a m)) ) (fun n => 0%nat) ))) as f. *)
  (*    assert (f (fun n=> 0%nat) = m). *)
  (*    { *)
  (*      rewrite Heqf. *)
  (*      rewrite E. *)
  (*      simpl;auto. *)
  (*    } *)
  (*    destruct (cont f (fun n => 0%nat)) as [mf Mf] eqn: Emf. *)
  (*    remember (fun n => if (n <? (mf+1))%nat then 0%nat else 1 %nat ) as b. *)
  (*    assert (f b = m). *)
  (*    { *)
  (*      rewrite <- H. *)
  (*      rewrite <- Mf;auto. *)
  (*      intros;rewrite Heqb. *)
  (*      admit. *)
  (*    } *)
  (*    remember (fun n => if (n <=? m)%nat then 0%nat else (mf+1)%nat) as a. *)
  (*    replace 0%nat with (b 0%nat) at 1. *)
  (*    replace (b 0%nat) with (b (a m)). *)
  (*    replace (b (a m)) with (b (mf +1)%nat). *)
  (*    rewrite Heqb. *)
  (*     rewrite Nat.ltb_irrefl;auto. *)
  (*    admit. *)
  (*    rewrite Heqa, Heqb;simpl. *)
  (*    admit. *)
  (* Lemma wrong_continuity (f : (nat -> nat) -> sierp) (x : nat -> nat): sierp_up (f x) -> {k | forall y, (forall n, (n <= k)%nat -> x n = y n) -> sierp_up (f y)}.  *)
  (* Admitted. *)

  (* Lemma cont_nat (f : (nat -> nat) -> nat) (x : nat -> nat) : {k | forall y, (forall n, (n <= k)%nat -> x n = y n) -> f x = f y}. *)
  (* Proof. *)
  (*    assert (forall n,{g : (nat -> nat) -> sierp | forall x, sierp_up (g x) <-> (f x) = n}). *)
  (*    admit. *)
     
  (*    destruct (wrong_continuity ) *)
  (* Lemma name_fun_extension H s U t : name_fun H s U t -> ^M {g : nat -> nat -> nat | (forall n, (U (D s n) -> exists m, ((g n m) > 0)%nat /\ forall x, ball H (D s n) (g n m) x -> U x)) /\ forall x, U x -> exists n m, ((g n m) > 0)%nat /\ ball H (D s n) (g n m) x}. *)
  (* Proof. *)
  (*   intros. *)
  (*   pose proof (continuity t). *)
  (*   assert ( ^M {k : nat -> nat -> nat | forall n, U (D s n) -> (exists m, (k n m > 0)%nat /\ forall x, (forall j,(j < (k n m))%nat -> x j = n) -> sierp_up (t x))}). *)
  (*   { *)
      

      (* intros. *)
      (* assert (sierp_up (t (fun m => n))). *)
      (* { *)
      (*   apply H0. *)
      (*   apply fast_cauchy_neighbor. *)
      (*   intros k1. *)
      (*   left. *)
      (*   apply (real_le_lt_lt _ 0);[right|apply prec_pos]. *)
      (*   destruct H;destruct a;apply i;auto. *)
      (*   exists (D s n). *)
      (*   split;auto. *)
      (*   intros k. *)
      (*   left. *)
      (*   apply (real_le_lt_lt _ 0);[right|apply prec_pos]. *)
      (*   destruct H;destruct a;apply i;auto. *)
      (* } *)
      (* specialize (continuity t _ H2). *)
      (* apply M_lift. *)
      (* intros [m M]. *)
      (* exists m. *)
      (* intros. *)
      (* apply M;intros;rewrite H3;auto. *)
    (*   admit. *)
    (* } *)
    (* revert X1. *)
    (* apply M_lift. *)
    (* intros [k K]. *)
    (* exists k. *)
    (* split. *)
   (* intros. *)
    (* specialize (K n H1). *)
    (* destruct K as [m [M1 M2]]. *)
    (* exists m. *)
    (* split;auto. *)
    (* intros. *)
    (* unfold name_fun in H0. *)
    (* admit. *)
    (* intros. *)
    (* unfold name_fun in H0. *)
    (* assert {x0 : nat -> nat | metric_is_fast_cauchy H (fun m => D s (x0 m)) /\ metric_is_fast_limit H (fun m => D s (x0 m)) x} as [p P]. *)
    (* admit. *)
    
  
(*   Lemma separable_suff (H :metric) (s : separable) (l : has_limit H) U1 U2 : open U1 -> open U2 -> (forall n, U1 (D s n) <-> U2 (D s n)) -> U1 = U2. *)
(*   Proof. *)
(*     revert U1 U2. *)
(*     enough (forall U1 U2 : csubset, open U1 -> open U2 -> (forall n : nat, U1 (D s n) <-> U2 (D s n)) -> forall x, U1 x -> U2 x). *)
(*     - intros. *)
(*       apply fun_ext. *)
(*       intros. *)
(*       apply Prop_ext. *)
(*       apply H0;auto. *)
(*       apply H0;auto. *)
(*       intros n;split; apply H1. *)
(*     - intros U1 U2 HU1 HU2 Hs. *)
(*       enough (forall n, exists m, is_subset (ball H (D s n) m) (intersection U1 U2)). *)
(*       intros. *)
(*       (* pose proof (open_basis H s l _ _ X0 H1). *) *)
(*       (* apply M_hprop_elim; [(intros a b;apply irrl)|]. *) *)
(*       (* revert X2. *) *)
(*       (* apply M_lift_dom. *) *)
(*       (* intros [[n m] [Hnm1 Hnm2]]. *) *)
(*       (* simpl in *. *) *)
(*       (* pose proof (open_intersection (metric_open H (D s n) m) X1). *) *)
(*       (* assert ((intersection (ball H (D s n) m) U2) (D s n)). *) *)
(*       (* { *) *)
(*       (*   split. *) *)
(*       (*   apply ball_contains_center. *) *)
(*       (*   apply H0. *) *)
(*       (*   apply Hnm1;apply ball_contains_center. *) *)
(*       (* } *) *)
(*       (* pose proof (separable_metric_continuous H s l _ _ X2 H2). *) *)
(*       (* revert X3. *) *)
(*       (* apply M_lift_dom. *) *)
(*       (* intros [m' Hnm']. *) *)
(*       (* pose proof (separable_metric_approx_inside H s _ _ X0 H1 (m'+1)%nat). *) *)
(* Abort. *)
End Metric.
(* Section Examples. *)
  
(*   Example cantor_exists_open : open (fun (n : (nat -> bool)) => exists m, (n m) = true). *)
(*   Proof. *)
(*     apply open_countable_union. *)
(*     intros n x. *)
(*     apply sierp_from_semidec. *)
(*     unfold lazy_bool_up. *)
(*     destruct (x n). *)
(*     exists lazy_bool_true;split;auto. *)
(*     exists lazy_bool_false;split;intros;contradict H;auto. *)
(*     apply lazy_bool_distinct. *)
(*  Qed. *)

(*   Definition extends (a : list bool) (x : (nat -> bool)) := forall n, (n < length a)%nat -> x n = nth n a true. *)

(*   Lemma one_point_fixed_clopen n b : open (fun (x : (nat -> bool)) => x n = b) * closed (fun (x : (nat -> bool)) => x n = b). *)
(*   Proof. *)
(*     assert (forall b', {k | (lazy_bool_up _ k) <-> b' = b}). *)
(*     { *)
(*       intros. *)
(*       exists (if (bool_eq b' b) then lazy_bool_true else lazy_bool_false). *)
(*       destruct b; destruct b';simpl;unfold lazy_bool_up;split;auto;intros;contradict H; try apply lazy_bool_distinct; try apply Bool.diff_false_true. *)
(*       apply Bool.diff_true_false. *)
(*     } *)
(*     split;intros x. *)
(*     destruct (X (x n));apply sierp_from_semidec. *)
(*     exists x0;auto. *)
(*     destruct (X (negb (x n)));apply sierp_from_semidec. *)
(*     exists x0. *)
(*     unfold complement. *)
(*     rewrite i. *)
(*     split;intros. *)
(*     rewrite <-H. *)
(*     apply neq_sym. *)
(*     apply Bool.no_fixpoint_negb. *)
(*     unfold lazy_bool_up. *)
(*     destruct (x n); destruct b;simpl;auto. *)
(*     contradict H;auto. *)
(*  Qed. *)
    

(*  Lemma extends_intersection a0 a x : extends (a0 :: a) x <-> (x 0%nat) = a0 /\ extends a (fun n => x (S n)).   *)
(*   Proof. *)
(*     revert a0 x. *)
(*     induction a. *)
(*     - unfold extends. *)
(*       simpl. *)
(*       split. *)
(*       intros H. *)
(*       split. *)
(*       destruct (H 0%nat);try lia;auto. *)
(*       intros;lia. *)
(*       intros [H1 H2] n N. *)
(*       rewrite Nat.lt_1_r in N. *)
(*       rewrite N;auto. *)
(*    - intros. *)
(*      rewrite IHa. *)
(*      unfold extends. *)
(*      split. *)
(*      intros. *)
(*      split; [|split]. *)
(*      apply (H 0%nat);simpl;lia. *)
(*      apply (H 1%nat);simpl;lia. *)
(*      intros. *)
(*      apply (H (S (S n))). *)
(*      simpl;lia. *)
(*      intros [H1 [H2 H3]] n N. *)
(*      destruct n;simpl;auto. *)
(*      destruct n;simpl;auto. *)
(*      apply H3;simpl in *;lia. *)
(*   Qed. *)

(*   Lemma extends_intersection' a0 a : extends (a0 :: a) = intersection (fun (x : (nat -> bool)) => x O = a0) (fun x => (extends a (fun n => x (S n)))). *)
(*   Proof. *)
(*     apply fun_ext. *)
(*     intros. *)
(*     unfold intersection. *)
(*     apply Prop_ext;apply extends_intersection. *)
(*   Qed. *)

(*   Example cantor_base_clopen a : open (extends a) * closed (extends a).  *)
(*   Proof. *)
(*     induction a. *)
(*     - unfold extends. *)
(*       split;intros x;apply sierp_from_semidec. *)
(*       exists (lazy_bool_true);unfold lazy_bool_up;split;simpl;auto;lia. *)
(*       exists (lazy_bool_false);unfold lazy_bool_up. *)
(*       split;intros. *)
(*       contradict H. *)
(*       apply lazy_bool_distinct. *)
(*       unfold complement in H. *)
(*       contradict H;simpl;lia. *)
(*    - rewrite extends_intersection'. *)
(*      split. *)
(*      apply open_intersection. *)
(*      apply one_point_fixed_clopen. *)
(*      intros x. *)
(*      destruct IHa. *)
(*      destruct (o (fun n => x (S n))). *)
(*      exists x0;auto. *)
(*      apply closed_intersection. *)
(*      apply one_point_fixed_clopen. *)
(*      destruct IHa. *)
(*      intros x. *)
(*      destruct (c (fun n => (x (S n)))). *)
(*      exists x0;auto. *)
(*   Qed. *)

(*   (* Cantor space closed => WKL *) *)

(*   Definition prefix (L1 L2 : list bool) := exists (L3 : (list bool)), L2 = L1 ++ L2. *)
  
(*   Definition binary_tree T := (T []) /\ forall a b, T b -> prefix a b -> T a. *)

(*   Definition infinite (T : (list bool -> Prop)) := forall n, exists a, T a /\ (length a >= n)%nat. *)
(*   Definition path (T : list bool -> Prop) (p : nat -> bool)  := forall a, extends a p -> T a.  *)

(*   Definition decidable (T : (list bool -> Prop)) := forall x, {b : bool | b = true <-> T x}. *)

(*   Lemma extends_decidable x : decidable (fun a => (extends a x)). *)
(*   Proof. *)
(*     intros a. *)
(*     revert x. *)
(*     induction a. *)
(*     exists true. *)
(*     split;auto;unfold extends;intros _;simpl;lia. *)
(*     intros. *)
(*     destruct (IHa (fun n => x (S n))). *)
(*     exists (andb (bool_eq (x 0%nat) a) x0). *)
(*     rewrite Bool.andb_true_iff. *)
(*     rewrite ((extends_intersection a a0 x)). *)
(*     rewrite i. *)
(*     split;intros [H1 H2];split;auto. *)
(*     apply bool_eq_ok;auto. *)
(*     rewrite H1;destruct a;auto. *)
(*   Qed. *)

(*   Definition WKL := forall T, decidable T -> binary_tree T -> infinite T -> exists p,  path T p. *)


(*   Lemma path_closed T : (decidable T) -> closed (path T). *)
(*   Proof. *)
(*     intros H x. *)
(*     assert (decidable (fun a => extends a x /\ not (T a))). *)
(*     { *)
(*       intros a. *)
(*       destruct (extends_decidable x a). *)
(*       destruct (H a). *)
(*       exists (andb x0 (negb x1)). *)
(*       rewrite Bool.andb_true_iff. *)
(*       rewrite <-i, <-i0. *)
(*       rewrite Bool.negb_true_iff. *)
(*       rewrite Bool.not_true_iff_false;split;auto. *)
(*     } *)
(*     destruct (enumerable_lists) as [l L]. *)
(*     destruct (cantor_exists_open (fun n => (pr1 _ _ (H0 (l n))))). *)
(*     exists x0. *)
(*     rewrite i. *)
(*     split. *)
(*     - intros [m M]. *)
(*       destruct (H0 (l m));simpl in *. *)
(*       intros P. *)
(*       specialize (P (l m)). *)
(*       contradict M. *)
(*       rewrite i0. *)
(*       intros [H1 H2]. *)
(*       apply H2;auto. *)
(*    - intros. *)
(*      unfold complement, path in H1. *)
(*      rewrite classical_tautology_neg_all in H1. *)
(*      destruct H1. *)
(*      destruct (L x1). *)
(*      exists x2. *)
(*      destruct (H0 (l x2));simpl. *)
(*      apply i0. *)
(*      apply Classical_Prop.imply_to_and;rewrite e;auto. *)
(*   Qed. *)
(*   Lemma dense_enumeration_exists : {e : nat -> (nat -> bool) | forall x U,  (open U) -> U x -> exists n, U (e n)}. *)
(*   Proof. *)
(*      destruct enumerable_lists. *)
(*      exists (fun n => (fun m => nth m (x n) false)). *)
(*      intros. *)
(*   Admitted. *)

(*  Definition dense_enumeration := pr1 _ _ dense_enumeration_exists. *)

(*  Lemma extends_last a an x : extends (a ++ [an]) x <->  extends a x /\ x (length a) = an.   *)
(*  Proof. *)
(*    revert x;induction a. *)
(*    - simpl. *)
(*      split;unfold extends;simpl;intros;try lia. *)
(*      split;try lia;auto. *)
(*       assert (n = 0)%nat as -> by lia;auto. *)
(*       apply H. *)
(*    - intros. *)
(*      rewrite <-app_comm_cons. *)
(*      rewrite !extends_intersection. *)
(*      rewrite !IHa. *)
(*      simpl. *)
(*      split;intros [H1 H2];split;try split;auto;destruct H2;destruct H1;auto. *)
(*   Qed. *)

(*   Lemma first_n_extends x n  : extends (map x (seq 0 n)) x. *)
(*   Proof. *)
(*     induction n; [unfold extends;simpl;lia|]. *)
(*     rewrite seq_S, map_app. *)
(*     simpl. *)
(*     rewrite extends_last. *)
(*     split;auto. *)
(*     rewrite map_length, seq_length;auto. *)
(*   Qed. *)

(*   Definition base : nat -> (@csubset (nat -> bool)). *)
(*   Proof. *)
(*     intros n. *)
(*     destruct enumerable_lists. *)
(*     pose proof (extends (x n)) : csubset. *)
(*     apply X. *)
(*   Defined. *)

(*   Lemma base_open : forall n, open (base n). *)
(*   Proof. *)
(*     intros. *)
(*     unfold base. *)
(*     destruct enumerable_lists. *)
(*     apply cantor_base_clopen. *)
(*   Qed. *)

(*   Lemma open_nbhd U x : open U -> U x -> ^M ({n | (base n) x /\ is_subset (base n) U}). *)
(*   Proof. *)
(*     intros. *)
(*     remember (fun x => (pr1 _ _ (X x))) as f. *)
(*     assert (forall y, sierp_up (f y) <-> U y). *)
(*     { *)
(*       intros. *)
(*       rewrite Heqf. *)
(*       destruct (X y). *)
(*       simpl;auto. *)
(*     } *)
(*     assert (sierp_up (f x)) by (apply H0;auto). *)
(*     pose proof (continuity  f _ H1). *)
(*     revert X0. *)
(*     apply M_lift. *)
(*     intros [m Hm]. *)
(*     destruct enumerable_lists eqn:E. *)
(*     destruct (s (map x (seq 0 m))). *)
(*     exists x1. *)
(*     unfold base. *)
(*     rewrite E. *)
(*     rewrite e. *)
(*     split; [apply first_n_extends|]. *)
(*     intros y Hy. *)
(*     apply H0. *)
(*     apply Hm. *)
(*     intros. *)
(*     rewrite Hy; [ | rewrite map_length,seq_length];auto. *)
(*     rewrite (nth_indep _  _ (x 0%nat)); [|rewrite map_length,seq_length;auto]. *)
(*     rewrite map_nth, seq_nth;auto. *)
(*   Qed. *)

(*   Lemma base_to_list n : {l | base n = extends l}. *)
(*   Proof. *)
(*     unfold base. *)
(*     destruct enumerable_lists. *)
(*     exists (x n);auto. *)
(*   Qed. *)

(*   Lemma contains_lazy_check U : open U -> ^M {t : nat -> nat -> bool | forall m, (exists n, t m n = true) <-> U (dense_enumeration m)}. *)
(*   Proof. *)
(*     intros. *)
(*     unfold dense_enumeration. *)
(*     destruct (dense_enumeration_exists). *)
(*     assert (^M (forall m, {f : nat -> bool |  (U (x m)) <-> (exists n, f n = true)})). *)
(*     { *)
(*       apply M_countable_lift. *)
(*       intros. *)
(*       pose proof (open_to_testfun _ X (x n)). *)
(*       apply X0. *)
(*     } *)
(*     revert X0. *)
(*     apply M_lift. *)
(*     intros. *)
(*     exists (fun m => (pr1 _ _ (H m))). *)
(*     intros. *)
(*     destruct (H m). *)
(*     simpl. *)
(*     rewrite i;split; intros[];exists x1;auto. *)
(*   Qed. *)

(*   Lemma dense_enumeration_base n : (base n) (dense_enumeration n). *)
(*   Proof. *)
(*     unfold base, dense_enumeration. *)
(*     destruct enumerable_lists. *)
(*   Admitted. *)

(*   Lemma interval_extension U : open U -> ^M {I : nat -> bool | (forall n, I n = true -> is_subset (base n) U) /\ forall x, U x -> exists n, (base n x) /\ (I n) = true}. *)
(*   Proof. *)
(*     intros. *)
(*     pose proof (contains_lazy_check _ X). *)
(*     revert X0. *)
(*     apply M_lift. *)
(*     intros [t T]. *)
(*   Abort.    *)
(*   Lemma dense_covers U x:  open U -> U x -> exists n m, is_subset (base n) U /\ ((base n (dense_enumeration m)) /\ (base n x)). *)
(*   Proof. *)
(*     intros. *)
(*     unfold dense_enumeration. *)
(*     destruct (dense_enumeration_exists). *)
(*     simpl. *)
(*     specialize (e x). *)
(*     pose proof (open_nbhd U x X H). *)
(*     apply M_hprop_elim_f. *)
(*     intros a b. *)
(*     apply irrl. *)
(*     revert X0. *)
(*     apply M_lift. *)
(*     intros [n [N1 N2]]. *)
(*     destruct (e (base n));auto;try apply base_open. *)
(*     exists n; exists x1;auto. *)
(*   Qed.  *)

(*   Definition base_to_subset (n : nat) := match n with *)
(*                                        | 0%nat => (fun _ => True) *)
(*                                        | (S n') => (base n') *)
(*                                        end. *)

(*   Lemma open_dense_suffices U1 U2: open U1 -> open U2 -> (forall n, U1 (dense_enumeration n) <-> U2 (dense_enumeration n)) -> (forall x, U1 x <-> U2 x).  *)
(*   Proof. *)
(*     unfold dense_enumeration. *)
(*     destruct (dense_enumeration_exists) eqn:E;simpl. *)
(*     intros. *)
(*     split. *)
(*     intros. *)
(*     destruct (dense_covers _ _ X H0) as [n [m [H1 [H2 H3]]]]. *)
(*     unfold dense_enumeration in *;rewrite E in *;simpl in *. *)
    
(*   Abort. *)
(*   Lemma cantor_second_countable U : open U -> ^M {c : nat -> option nat | (forall n m, (c n) = Some m -> is_subset (base m) U) /\ (forall x, U x -> exists n m, (c n) = Some m /\ (base m) x)}. *)
(*   Proof. *)
(*     intros. *)
(*     pose proof (contains_lazy_check U X). *)
(*     revert X0. *)
(*     apply M_lift_dom. *)
(*     intros [t T]. *)
(*     assert (^M (forall m n,  {i | t m n = true -> is_subset (base i) U /\ (base i) (dense_enumeration m)})). *)
(*     { *)
(*       apply M_countable_lift;intros m;apply M_countable_lift;intros n. *)
(*       intros. *)
(*       destruct (t m n) eqn:E. *)
(*       assert (U (dense_enumeration m)) by (apply T;exists n;auto). *)
(*       pose proof (open_nbhd _ _  X H). *)
(*       revert X0. *)
(*       apply M_lift. *)
(*       intros [i [I1 I2]];exists i;auto. *)
(*       apply M_unit. *)
(*       exists 0%nat. *)
(*       intros;contradict H. *)
(*       apply Bool.diff_false_true. *)
(*     } *)
(*     revert X0. *)
(*     apply M_lift. *)
(*     intros. *)
(*    Abort. *)
(*    (*  assert (forall x, U x -> exists m n, base (pr1 _ _ (H m n)) x). *) *)
(*    (*  { *) *)
(*    (*    intros. *) *)
(*    (*    destruct (dense_covers _ _ X H0). *) *)
      
(*    (*  } *) *)
(*    (*  destruct (enumerable_pair _ _ enumerable_nat enumerable_nat). *) *)
(*    (*  exists (fun n => match (t (fst (x n)) (snd (x n))) with | true => Some (pr1 _ _ (H (fst (x n)) (snd (x n)))) | false => None end). *) *)
(*    (*  split. *) *)
(*    (*  - intros. *) *)
(*    (*    destruct (H (fst (x n)) (snd (x n))). *) *)
(*    (*    destruct (t (fst (x n)) (snd (x n))) eqn:E. *) *)
(*    (*    simpl in *. *) *)
(*    (*    intros. *) *)
(*    (*    destruct a;auto. *) *)
(*    (*    injection H0. *) *)
(*    (*    intros <-;auto. *) *)
(*    (*    discriminate H0. *) *)
(*    (*  - intros. *) *)
(*    (*    destruct (dense_covers _ _ X H0) as [i [m H1]]. *) *)
(*    (*    assert (exists n, t m n = true) as [n N]. *) *)
(*    (*    { *) *)
(*    (*      apply T. *) *)
(*    (*      destruct H1. *) *)
(*    (*      apply H1;apply H2. *) *)
(*    (*    } *) *)
(*    (*    destruct (s (m,n)). *) *)
(*    (*    exists x1. *) *)
(*    (*    destruct (H m n) eqn:H'. *) *)
(*    (*    exists x2. *) *)
(*    (*    rewrite e;simpl. *) *)
(*    (*    rewrite H'. *) *)
(*    (*    simpl. *) *)
(*    (*    rewrite N. *) *)
(*    (*    split;auto. *) *)
      
(*    (*  assert (^M (forall m n, {b : option (list bool) | (f m n = false -> b = None) /\ (f m n = true ->  exists l, b = Some l /\ (extends l (x m)) /\ is_subset (extends l) U)})). *) *)
(*    (*  { *) *)
(*    (*    apply M_countable_lift;intros m;apply M_countable_lift;intros n. *) *)
(*    (*    destruct (f m n) eqn:E. *) *)
(*    (*    admit. *) *)
(*    (*    - apply M_unit. *) *)
(*    (*      exists None. *) *)
(*    (*      split;auto. *) *)
(*    (*      intros;contradict H0. *) *)
(*    (*      apply Bool.diff_false_true. *) *)
(*    (*  } *) *)
(*    (*  revert X0. *) *)
(*    (*  apply M_lift. *) *)
(*    (*  intros. *) *)
(*    (*  exists (fun n => (pr1 _ _ (H0 (fst (x0 n)) (snd (x0 n))))). *) *)
(*    (*  split. *) *)
(*    (*  - intros. *) *)
(*    (*    destruct (H0 (fst (x0 n)) (snd (x0 n))). *) *)
(*    (*    simpl in *. *) *)
(*    (*    destruct a. *) *)
(*    (*    destruct (f (fst (x0 n)) (snd (x0 n))). *) *)
(*    (*    destruct H3;auto. *) *)
(*    (*    replace b with x2. *) *)
(*    (*    apply H3. *) *)
(*    (*    destruct H3. *) *)
(*    (*    assert (Some x2 = Some b) by (rewrite <- H1, <- H3;auto). *) *)
(*    (*    inversion H5;auto. *) *)

(*    (*    contradict H1. *) *)
(*    (*    rewrite H2;auto. *) *)
(*    (*    discriminate. *) *)
(*    (* -  intros. *) *)
(*    (*    assert ({b | (extends b) x1 /\ is_subset (extends b) U}). *) *)
(*    (*    admit. *) *)
(*    (*    destruct H2. *) *)
(*    (*    destruct (cantor_base_clopen x2). *) *)
(*    (*    destruct a. *) *)
(*    (*    destruct (e x1 _ o);auto. *) *)
(*    (*    assert (U (x x3)). *) *)
(*    (*    admit. *) *)
(*    (*    destruct (F2 _ H5). *) *)
(*    (*    destruct (e0 (x3,x4)). *) *)
(*    (*    exists x5. *) *)
(*    (*    rewrite H7;simpl. *) *)
(*    (*    destruct (H0 x3 x4). *) *)
(*    (*    simpl in *. *) *)
(*    (*    destruct a. *) *)
(*    (*    destruct (H9 H6). *) *)
(*    (*    exists x7;split;try apply H7. *) *)
      
(*   (* Lemma cantor_space_compact : (@compact (nat -> bool) (fun x => True)). *) *)
(*   (* Proof. *) *)
(*   (*   intros U H. *) *)
(*   (*   destruct  *) *)
(*   (* Axiom continuity : forall X (f : (nat -> X) -> sierp) (x : (nat -> X)),   *) *)

(*   (* Definition pair_nat : nat -> nat -> nat. *) *)
(*   (* Proof. *) *)
(*   (*   intros n m. *) *)
(*   (*   destruct (enumerable_pair _ _ enumerable_nat enumerable_nat). *) *)
(*   (*   specialize (e (n,m)). *) *)
(*   (*   Search (exists _ , _) ({_ | _}). *) *)
(*   (*   apply ConstructiveEpsilon.constructive_indefinite_ground_description_nat_direct in e. *) *)
(*   (*   destruct e. *) *)
(*   (*   apply x0. *) *)
(*   (*   intros. *) *)
(*   (*   destruct (x n0). *) *)
(*   (*   simpl. *) *)
(*   (*   destruct (Nat.eq_dec n1 n)  as [-> |];auto. *) *)
(*   (*   destruct (Nat.eq_dec n2 m)  as [-> |];auto. *) *)
(*   (*   right. *) *)
(*   (*   rewrite pair_equal_spec;intros [];auto. *) *)
(*   (*   right. *) *)
(*   (*   rewrite pair_equal_spec;intros [];auto. *) *)
(*   (* Defined. *) *)

(*   (* Lemma continuous_sequence_to_sierp X (f : (nat -> X) -> sierp) (x : nat -> X) : is_totally_represented_space X -> sierp_up (f x) -> {m | forall y, (forall n, (n <= m)%nat -> x n = y n) -> sierp_up (f y)}. *) *)
(*   (* Proof. *) *)
(*   (*   intros. *) *)
(*   (*   destruct (totally_represented_sequence _ X0) as [r R]. *) *)
(*   (*   assert {g : (nat -> nat) -> sierp | forall x, sierp_up (g x) <-> sierp_up (f (r x))} as [g G]. *) *)
(*   (*   admit. *) *)
(*   (*   destruct (R x) as [x0 [R1 R2]]. *) *)
(*   (*   destruct (continuous_baire_to_sierp g x0) as [m M]. *) *)
(*   (*   apply G;rewrite R1;auto. *) *)
(*   (*   exists m. *) *)
(*   (*   intros. *) *)
(*   (*   destruct (R y) as [y0 [R1' R2']]. *) *)
(*   (*   rewrite <- R1'. *) *)
(*   (*   apply G. *) *)
(*   (*   apply M. *) *)
(*   (*   intros. *) *)
(*   (*   intros. *) *)
    
(*   (* Lemma continuous_baire2_to_sierp (f : (nat -> nat -> nat) -> sierp) (x : nat -> (nat -> nat)) : sierp_up (f x) -> {m | forall y, (forall n, (n <= m)%nat -> x n = y n)  ->  sierp_up (f y) }. *) *)
(*   (* Proof. *) *)
(*   (*   intros. *) *)
(*   (*   destruct (continuous_baire_to_sierp (fun (x : nat -> nat) => (f (fun n m => x (pair_nat n m)))) (fun n => x (unpair_nat1 n) (unpair_nat2 n))). *) *)
(*   (*   - replace (fun n m => x (unpair_nat1 (pair_nat n m)) (unpair_nat2 (pair_nat n m))) with x;auto. *) *)
(*   (*     apply fun_ext;intros;apply fun_ext;intros. *) *)
(*   (*     rewrite pair_unpair1, pair_unpair2;auto. *) *)
(*   (*   - exists x0. *) *)
(*   (*     intros. *) *)
(*   (*     specialize (s (fun n => (y (unpair_nat1 n) (unpair_nat2 n)))). *) *)
(*   (*   replace y with (fun n m => y (unpair_nat1 (pair_nat n m)) (unpair_nat2 (pair_nat n m))). *) *)
(*   (*   apply s. *) *)
(*   (*   intros. *) *)
(*   (*   rewrite H0;auto. *) *)
(*   (*   pose proof (unpair_le n). *) *)
(*   (*   lia. *) *)
(*   (*   apply fun_ext;intros;apply fun_ext;intros. *) *)
(*   (*   rewrite pair_unpair1, pair_unpair2;auto. *) *)
(*   (* Qed. *) *)


(*   (* Lemma continuity_baire : forall (f : ((nat -> nat) -> nat)) (x : (nat -> nat)), {m | forall y,  (forall n, (n <= m)%nat -> x n = y n) -> f x = f y}. *) *)
(*   (* Proof. *) *)
(*   (*   intros. *) *)
(*   (*   assert (forall n y, {s : sierp | sierp_up s <-> f y = n}). *) *)
(*   (*   { *) *)
(*   (*     intros. *) *)
(*   (*     apply sierp_from_semidec. *) *)
(*   (*     unfold lazy_bool_up. *) *)
(*   (*     destruct (Nat.eq_dec (f y) n); [exists lazy_bool_true | exists lazy_bool_false];split; auto. *) *)
(*   (*     intros. *) *)
(*   (*     contradict H;apply lazy_bool_distinct. *) *)
(*   (*     lia. *) *)
(*   (*   } *) *)
(*   (*   destruct (continuous_baire_to_sierp (fun y => (pr1 _ _ (X (f x) y))) x). *) *)
(*   (*   - destruct (X (f x) x). *) *)
(*   (*     apply i;auto. *) *)
(*   (*  - exists x0. *) *)
(*   (*    intros. *) *)
(*   (*    specialize (s y H). *) *)
(*   (*    destruct (X (f x) y). *) *)
(*   (*    apply eq_sym. *) *)
(*   (*    apply i. *) *)
(*   (*    apply s. *) *)
(*   (* Qed. *) *)

(*   (* (* Lemma continuity_baire2 (f : (nat -> nat -> nat) -> nat) (x : nat -> (nat -> nat)) : {m | forall y, (forall n, (n <= m)%nat -> x n = y n)  ->  f x = f y }. *) *) *)
(*   (* (* Proof. *) *) *)
(*   (* (*   destruct (continuity_baire (fun (x : nat -> nat) => (f (fun n m => x (pair_nat n m)))) (fun n => x (unpair_nat1 n) (unpair_nat2 n))). *) *) *)
(*   (* (*   exists x0. *) *) *)
(*   (* (*   intros. *) *) *)
(*   (* (*   specialize (e (fun n => (y (unpair_nat1 n) (unpair_nat2 n)))). *) *) *)
(*   (* (*   replace x with (fun n m => x (unpair_nat1 (pair_nat n m)) (unpair_nat2 (pair_nat n m))). *) *) *)
    
(*   (* (*   replace y with (fun n m => y (unpair_nat1 (pair_nat n m)) (unpair_nat2 (pair_nat n m))). *) *) *)
(*   (* (*   apply e. *) *) *)
(*   (* (*   intros. *) *) *)
(*   (* (*   rewrite H;auto. *) *) *)
(*   (* (*   pose proof (unpair_le n). *) *) *)
(*   (* (*   lia. *) *) *)
(*   (* (*   apply fun_ext;intros;apply fun_ext;intros. *) *) *)
(*   (* (*   rewrite pair_unpair1, pair_unpair2;auto. *) *) *)
(*   (* (*   apply fun_ext;intros;apply fun_ext;intros. *) *) *)
(*   (* (*   rewrite pair_unpair1, pair_unpair2;auto. *) *) *)
(*   (* (* Qed. *) *) *)

(*   (* Lemma sierp_from_nat_sequence : forall (f : (nat -> nat)), {s : sierp | sierp_up s <-> exists n, f n = 1%nat}. *) *)
(*   (* Proof. *) *)
(*   (*   intros. *) *)
(*   (*   assert (forall n, {s : sierp |  sierp_up s <-> f n = 1%nat}). *) *)
(*   (*   { *) *)
(*   (*     intros. *) *)
(*   (*     apply sierp_from_semidec. *) *)
(*   (*     unfold lazy_bool_up. *) *)
(*   (*     destruct (Nat.eq_dec (f n) 1%nat); [exists lazy_bool_true | exists lazy_bool_false];split; auto;intros;contradict H;auto. *) *)
(*   (*     apply lazy_bool_distinct. *) *)
(*   (*   } *) *)
(*   (*   destruct (eventually_true (fun n => (pr1 _ _ (X n)))). *) *)
(*   (*   exists x. *) *)
(*   (*   rewrite i. *) *)
(*   (*   split;intros [];exists x0;destruct (X x0);simpl;apply i0;auto. *) *)
(*   (* Qed. *) *)

(*   (* Axiom sierp_equality : forall s1 s2, sierp_up s1 <-> sierp_up s2 -> s1 = s2.  *) *)

(*   (* Lemma continuity_open : forall (f : (nat -> sierp) -> sierp) (x : nat -> sierp), sierp_up (f x) -> ^M {m | forall y, (forall n, (n <= m)%nat -> x n = y n) -> sierp_up (f y)}. *) *)
(*   (* Proof. *) *)
(*   (*   intros. *) *)
(*   (*   assert ({g : (nat -> nat -> nat) -> sierp | (forall y, sierp_up (g y) -> forall s, (forall n, sierp_up (s n) <-> exists m, (y n m) = 1%nat) -> sierp_up (f s)) /\ (forall s, sierp_up (f s) -> (forall y, (forall n, sierp_up (s n) <-> exists m, (y n m) = 1%nat) -> sierp_up (g y)))}) as [g [G1 G2]]. *) *)
(*   (*   { *) *)
(*   (*     exists (fun x => (f (fun n => (pr1 _ _ (sierp_from_nat_sequence (x n)))))). *) *)
(*   (*     split. *) *)
(*   (*     - intros. *) *)
(*   (*       replace s with (fun n => pr1 _ _ (sierp_from_nat_sequence (y n))). *) *)
(*   (*       apply H0. *) *)
(*   (*       apply fun_ext. *) *)
(*   (*       intros. *) *)
(*   (*       destruct (sierp_from_nat_sequence (y x0));simpl. *) *)
(*   (*       apply sierp_equality. *) *)
(*   (*       rewrite H1,i;split;intros [];exists x2;auto. *) *)
(*   (*     - intros. *) *)
(*   (*       replace (fun n => pr1 _ _ (sierp_from_nat_sequence (y n))) with s;auto. *) *)
(*   (*       apply fun_ext. *) *)
(*   (*       intros. *) *)
(*   (*       destruct (sierp_from_nat_sequence (y x0));simpl. *) *)
(*   (*       apply sierp_equality. *) *)
(*   (*       rewrite H1,i;split;intros [];exists x2;auto. *) *)
(*   (*     } *) *)
(*   (*   pose proof (continuous_baire2_to_sierp g). *) *)
(*   (*   assert (forall y, ^M ({x' : nat->nat -> nat | forall n, (sierp_up (y n) <-> exists m, (x' n m) = 1%nat)})).  *) *)
(*   (*   { *) *)
(*   (*     intros. *) *)
(*   (*     assert (forall n, ^M {x' : nat -> nat | sierp_up (y n) <-> exists m, (x' m) = 1%nat}). *) *)
(*   (*     - intros. *) *)
(*   (*       apply sierp_to_nat_sequence. *) *)
(*   (*     - apply M_countable_lift in X. *) *)
(*   (*       revert X. *) *)
(*   (*       apply M_lift. *) *)
(*   (*       intros. *) *)
(*   (*       exists (fun n => (pr1 _ _ (H1 n))). *) *)
(*   (*       intros. *) *)
(*   (*       destruct (H1 n);auto. *) *)
(*   (*   } *) *)
(*   (*   pose proof (X x). *) *)
(*   (*   revert X0. *) *)
(*   (*   apply M_lift. *) *)
(*   (*   intros [x' H1]. *) *)
(*   (*   assert (sierp_up (g x')) by (apply (G2 x);auto). *) *)
(*   (*   destruct (H0 _  H2) as [m M]. *) *)
(*   (*   exists m. *) *)
(*   (*   intros. *) *)
(*   (*   assert (^M ({y' : nat -> nat -> nat | (forall n, sierp_up (y n) <-> exists m, (y' n m) = 1%nat) /\ forall n, (n <= m)%nat -> x' n = y' n})). *) *)
(*   (*   { *) *)
(*   (*     pose proof (X y). *) *)
(*   (*     revert X0. *) *)
(*   (*     apply M_lift. *) *)
(*   (*     intros [y0 Y0]. *) *)
(*   (*     exists (fun p => if (p <=? m) then (x' p) else (y0 p)). *) *)
(*   (*     split. *) *)
(*   (*     - intros. *) *)
(*   (*       rewrite Y0. *) *)
(*   (*       split; intros [m0 M0]. *) *)
(*   (*       + destruct (le_gt_dec n m). *) *)
(*   (*         rewrite (leb_correct _ _ l). *) *)
(*   (*         rewrite <-H1. *) *)
(*   (*         rewrite H3;auto. *) *)
(*   (*         apply Y0. *) *)
(*   (*         exists m0;auto. *) *)
(*   (*         rewrite leb_correct_conv;try lia. *) *)
(*   (*         exists m0;auto. *) *)
(*   (*      + destruct (le_gt_dec n m). *) *)
(*   (*         rewrite (leb_correct _ _ l) in M0. *) *)
(*   (*        rewrite <-Y0. *) *)
(*   (*        rewrite <-H3;auto. *) *)
(*   (*        apply H1. *) *)
(*   (*        exists m0;auto. *) *)
(*   (*       rewrite leb_correct_conv in M0;try lia. *) *)
(*   (*       exists m0;auto. *) *)
(*   (*    - intros. *) *)
(*   (*      rewrite leb_correct;auto. *) *)
(*   (*   } *) *)
(*   (*   apply M_hprop_elim_f. *) *)
(*   (*   unfold is_hprop. *) *)
(*   (*   apply irrl. *) *)
(*   (*   revert X0. *) *)
(*   (*   apply M_lift. *) *)
(*   (*   intros [y' [Y1 Y2]]. *) *)
(*   (*   apply (G1 y'). *) *)
(*   (*   apply M. *) *)
(*   (*   apply Y2. *) *)
(*   (*   apply Y1. *) *)
(*   (* Qed. *) *)
(*   (* Example cantor_closed : closed (fun (x: (nat -> bool)) => forall n, (x n) = true -> forall m, (n <> m)%nat -> (x m) = false). *) *)
(*   (* Proof. *) *)
(*   (*   intros x. *) *)
(*   (*   unfold complement. *) *)
(*   (*   destruct (cantor_exists_open x). *) *)

(* End Examples. *)
