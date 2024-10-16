(* this file proves various properties of subsets of  metric spaces *)
Require Import Lia.
Require Import Real Euclidean List Minmax Classical.Subsets Sierpinski Testsearch Dyadic.
Require Import RealAssumption.
Require Import List.
Require Import Hyperspace.Continuity.
Require Import Hyperspace.Subsets.
Import ListNotations.

  Axiom sierp_id : forall s1 s2, (sierp_up s1 <-> sierp_up s2) -> s1 = s2.
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
    pose proof (M_countable_selection f H1).
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

  Lemma separable_open_overt  : separable -> forall V, open V -> (@overt X V).
  Proof.
    intros s V H U Hu.
    pose proof (open_intersection  H Hu).
    pose proof (separable_exists _ s X0 ).
    assert (forall n, {k : sierp | sierp_up k <-> intersection V U (D s n)}).
    {
      intros.
      destruct (X0 (D s n)).
      exists x;auto.
    }
    remember (fun n => pr1 _ _ (X1 n)) as f.
     destruct (eventually_true f).
     exists x.
     rewrite i.
     split.
     - intros [n N].
       exists (D s n).
       rewrite Heqf in N.
       destruct (X1 n);simpl in *;tauto.
    - intros.
      apply H0 in H1.
      rewrite Heqf.
      destruct H1 as [n N].
      exists n.
      destruct (X1 n);simpl;tauto.
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
  
  Definition totally_bounded (H : metric) (U : (@csubset X)) := forall n, {L : list X | (forall x, In x L -> intersects (ball H x n) U) /\ forall x,  U x ->  Exists  (ball H x n) L}.
  Definition complete (H : metric) (U : (@csubset X)) := forall f, (forall n, U (f n)) ->  (metric_is_fast_cauchy H f)  -> {x | metric_is_fast_limit H f x /\ U x}.
  Lemma d_sym H : forall x y, d_X H x y = d_X H y x.
  Proof.
    destruct H as [d [D1 [D2 D3]]];auto.
  Qed.


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

  Lemma M_countable_selection_sequence (f : nat -> ^K) : (exists n, (f n) = lazy_bool_true) -> ^M {g : nat -> nat | (forall n, (f (g n)) = lazy_bool_true) /\ (forall n, (f n) = lazy_bool_true -> exists m, g m = n)}.
  Proof.
    intros.
    specialize (M_countable_selection f H).
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
        specialize (M_countable_selection_sequence g H0).
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


  Lemma compact_complete H (s :separable) (l : has_limit H) K : compact K -> complete H K.
  Proof.
    intros.
    apply compact_closed in X0; [|apply metric_space_ineq_semidec;auto].
    apply closed_complete;auto.
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
  Lemma complete_intersection H A B : complete H A -> complete H B -> complete H (intersection A B).
  Proof.
    intros.
    intros f Hf1 Hf2.
    assert ((forall n, A (f n)) /\ (forall n, B (f n))) as [Ha Hb] by (split;apply Hf1).
    destruct (X0 f) as [x [Hx1 Hx2]];auto.
    exists x.
    split;auto.
    split;auto.
    destruct (X1 f) as [x' [Hx1' Hx2']];auto.
    replace x with x'; auto.
    apply (metric_limit_unique _ _ _ _ Hx1' Hx1).
 Qed.

  Lemma closed_ball_closed H x n : closed (cball H x n).
  Proof.
    intros y.
    unfold complement, cball.
    apply sierp_from_semidec.
    destruct (real_lt_semidec (prec n) (d_X H x y)).
    exists x0.
    rewrite i.
    split;intros.
    apply real_gt_nle;auto.
    apply real_nle_ge;auto.
  Qed.

  Lemma totally_bounded_nonempty_dec H K : totally_bounded H K -> ({exists x, K x} + {not (exists x, K x)}).
  Proof.
    intros.
    destruct (X0 0%nat).
    destruct x.
    - right.
      intros H0.
      destruct H0.
      destruct a.
      specialize (H2 _ H0).
      apply Exists_exists in H2.
      destruct H2.
      apply H2.
   - left.
     destruct a.
     destruct (H0 x);simpl;auto.
     exists x1;apply H2.
  Qed.

Lemma bishop_compact_subsequence_refinement H (s : separable) (l : has_limit H) K f m : totally_bounded H K -> complete H K -> (forall n, K (f n)) -> exists z, K z /\ (forall n, exists k, (k > n)%nat /\ d_X H z (f k) <= prec m).
  Proof.
    intros.
    apply M_hprop_elim.
    intros a b; destruct a, b ; apply irrl.
    specialize (bishop_compact_centered _ s l _ X0 X1).
    clear X0 X1.
    apply M_lift.
    intros.
    destruct (X0 m) as [p [Hp1 Hp2]].
    clear X0 .
    enough (exists z, In z p /\ forall n, exists k, (k > n)%nat /\ d_X H z (f k) <= prec m) as [z [Hz1 Hz2]] by (exists z; split;auto).
    assert (forall n, exists z,  In z p /\ d_X H z (f n) <= prec m).
    {
      intros.
       specialize (Hp2 _ (H0 n)).
       apply Exists_exists in Hp2.
       destruct Hp2 as [z [Hz1 Hz2]].
       exists z;split;auto.
       apply real_lt_le;rewrite d_sym;auto.
    }
    clear Hp1 Hp2 H0.
    revert dependent f.
    induction p.
    - intros.
      destruct (H1 0%nat).
      destruct H0;contradict H0.
   -  intros.
      destruct (lem (forall n, exists k, (k > n)%nat /\ d_X H a (f k)  <= prec m)).
      exists a;split;simpl;auto.
      assert (exists N, forall k, (k > N)%nat -> not ((d_X H a (f k)) <= prec m)).
      {
      apply Classical_Pred_Type.not_all_ex_not in H0.
      destruct H0.
      exists x.
      intros k Hk Hp.
      contradict H0.
      exists k.
      split;auto.
      }
      destruct H2 as [N HN].
      destruct (IHp (fun n =>  f (n+N+1)%nat )) as [z [Hz1 Hz2]].
      {
       intros.
       destruct (H1 (n+N+1)%nat) as [z [Hz1 Hz2]].
       exists z.
       split;auto.
       destruct Hz1;auto.
       contradict Hz2.
       rewrite <-H2.
       apply HN;lia.
     }
     exists z.
     split;[simpl;auto|].
     intros.
     destruct (Hz2 n) as [k [Hk1 Hk2]].
     exists (k+N+1)%nat.
     split;auto;lia.
   Qed.

  Lemma bishop_compact_classically_seqcompact H (s : separable) (l : has_limit H) K : totally_bounded H K -> complete H K -> forall (f : nat -> X), (forall n, K (f n)) -> exists (g : nat -> nat), (forall n, (g (n+1) > g n)%nat /\ (g n >= n)%nat) /\ exists y, K y /\ metric_is_fast_limit H (fun n => (f (g n))) y.
  Proof.
    intros.
    enough (exists (g : nat -> nat), (forall n, (g (n+1) > g n)%nat) /\ exists y, K y /\ metric_is_fast_limit H (fun n => (f (g n))) y).
    {
      destruct H1.
      exists x.
      split;[split|];try apply H1.
      destruct H1 as [H1 _].
      induction n.
      lia.
      enough (x (S n) > n)%nat by lia.
      replace (S n) with (n+1)%nat by lia.
      specialize (H1 n).
      lia.
    }

    enough (exists g : nat -> nat, (forall n, (g (n+1) > g n)%nat) /\ (forall n, d_X H (f (g n)) (f (g (S n))) <= prec (S n))).
    {
      destruct H1 as [g [G1 G2]].
      exists g.
      split;auto.
      destruct (X1 (fun n => (f (g n))));auto.
      apply fast_cauchy_neighbor;auto.
      exists x;split;apply a.
    }

    assert (forall x : nat * nat,
        exists y : nat * nat,
          (snd y) = (S (snd x)) /\ (fst y > fst x)%nat /\
          ((exists z, K z /\ d_X H (f (fst x)) z <=  prec (S (snd x)) /\ forall n, exists k, (k > n)%nat /\ d_X H z (f k) <= prec (S (snd x))) ->
                        
          d_X H (f (fst x)) (f (fst y)) <= prec (snd x) /\
           (exists z, K z /\ d_X H (f (fst y)) z <= prec (S (S (snd x))) /\ forall n, exists k, (k > n)%nat /\ d_X H z (f k) <= prec (S (S (snd x)))))).
       {
         intros [n m].
         destruct (lem ((exists z : X, K z /\
        d_X H (f n) z <= prec (S m) /\
        (forall n0 : nat,
         exists k : nat,  (k > n0)%nat /\ d_X H z (f k) <= prec (S m))))).
         - destruct H1 as [z [Kz [Hz1 Hz2]]].
           enough (exists z', K z' /\ forall n, exists k, (k > n)%nat /\ d_X H z' (f k) <= prec (S (S m)) /\ d_X H z (f k) <= prec (S m)).
           {
             destruct H1 as [z' [Kz' Hz']].
             destruct (Hz' n).
             destruct H1 as [H2 [H3 H4]].
             exists (x, S m).
             split;[|split];auto.
             intros _.
             split.
             simpl.
             rewrite <-prec_twice.
             replace (m+1)%nat with (S m) by lia.
             apply (real_le_le_le _ _ _ (dx_triangle _ _ _ z)).
             apply real_le_le_plus_le;auto.
             exists z'.
             split; [|split];auto.
             simpl fst; simpl snd.
             rewrite d_sym;auto.
             intros.
             destruct (Hz' n0).
             exists x0.
             split;apply H1.
           }
           pose proof (bishop_compact_centered _ s l _ X0 X1).
           apply M_hprop_elim.
           intros x0 x1;destruct x0,x1;apply irrl.
           revert X2.
           apply M_lift.
           intros.
           apply countable_choice in Hz2.
           destruct Hz2 as [g G].
           enough (exists z', K z' /\ (forall n, exists k, (k > n)%nat /\ d_X H z' (f (g k)) <= prec (S (S m)))).
           {
              destruct H1 as [z' [Kz' Hz']].
              exists z'.
              split;auto.
              intros.
              destruct (Hz' n0) as [k [K1 K2]].
              exists (g k).
              split.
              destruct (G k).
              lia.
              split;auto.
              apply G.
          }
           destruct (X2 (S (S m))) as [p [Hp1 Hp2]].
           clear dependent z.
           clear X0 X1 X2 n.
           enough (exists z, In z p /\ forall n, exists k, (k > n)%nat /\ d_X H z (f (g k)) <= (prec (S (S m)))) as [z [Hz1 Hz2]] by (exists z; split;auto).
           assert (forall n, exists z,  In z p /\ d_X H z (f (g n)) <= prec (S (S m))).
           {
             intros.
             specialize (Hp2 _ (H0 (g n))).
             apply Exists_exists in Hp2.
             destruct Hp2 as [z [Hz1 Hz2]].
             exists z;split;auto.
             apply real_lt_le;rewrite d_sym;auto.
           }
           clear Hp1 Hp2 H0.
           revert dependent g.
           induction p.
           + intros.
             destruct (H1 0%nat).
             destruct H0;contradict H0.
           + intros.
             destruct (lem (forall n, exists k, (k > n)%nat /\ d_X H a (f (g k))  <= (prec (S (S m))))).
             exists a;split;simpl;auto.
             assert (exists N, forall k, (k > N)%nat -> not ((d_X H a (f (g k))) <= prec (S (S m)))).
            {
             apply Classical_Pred_Type.not_all_ex_not in H0.
             destruct H0.
             exists x.
             intros k Hk Hp.
             contradict H0.
             exists k.
             split;auto.
            }
            destruct H2 as [N HN].
            destruct (IHp (fun n => g (n+N+1)%nat )) as [z [Hz1 Hz2]].
            {
              intros.
              destruct (H1 (n+N+1)%nat) as [z [Hz1 Hz2]].
              exists z.
              split;auto.
              destruct Hz1;auto.
              contradict Hz2.
              rewrite <-H2.
              apply HN;lia.
           }
           exists z.
            split;[simpl;auto|].
            intros.
            destruct (Hz2 n) as [k [Hk1 Hk2]].
            exists (k+N+1)%nat.
            split;auto;lia.
         - exists (S n, S m).
           split;[|split];simpl;auto.
           intros.
           contradict H2;auto.
       }
      assert (exists n0 z , K z /\ d_X H (f n0) z <= prec 1%nat /\ (forall n, exists k, (k> n)%nat /\ d_X H z (f k) <= prec 1%nat)) as [n0 N0].
       {
         pose proof (bishop_compact_subsequence_refinement _ s l K f 1%nat X0 X1 H0).
         destruct H2 as [z [Kz Hz]].
         destruct (Hz 0%nat).
         exists x; exists z.
         split;[|split];auto.
         rewrite d_sym;apply H2.
       }
      pose proof (dependent_choice _ _ H1 (n0, 0)%nat).
      destruct H2 as [g [G1 G2]].
      assert (forall n, (snd (g n) = n)).
      {
        induction n;[rewrite G1;simpl;auto|].
        destruct (G2 n).
        rewrite H2.
        rewrite IHn;auto.
      }
      assert (forall m, exists z, K z /\ d_X H (f (fst (g m))) z <= prec (S (snd (g m))) /\ (forall n, exists k, (k > n)%nat /\ d_X H z (f k)  <= prec (S (snd (g m))))).
      {
        intros m.
        induction m.
        rewrite G1.
        apply N0.
        rewrite H2.
        destruct (G2 m).
        destruct H4.
        rewrite H2 in H5.
        destruct H5.
        rewrite H2 in IHm.
        apply IHm.
        apply H6.
      }
      exists (fun n => (fst (g (S n)))).
      split;auto.
      intros.
      replace (n+1)%nat with (S n) by lia.
      apply G2.
      intros.
      rewrite <-(H2 n) at 3.
      destruct (G2 (S n)).
      destruct H5.
      destruct H6.
      apply H3.
      rewrite H2 in H6.
      rewrite H2;auto.
  Qed.

  Lemma bishop_compact_classical_fincover_compact H (s : separable) (l : has_limit H) K : totally_bounded H K -> complete H K -> (forall b, is_subset K (countable_union_base H s b) -> (exists N, (is_subset K (finite_union_base H s b N)))).
  Proof.
    intros.
    pose proof (bishop_compact_classically_seqcompact H s l K X0 X1).
    clear X0 X1.
    apply Classical_Pred_Type.not_all_not_ex.
    intros H2.
    assert (forall n, exists x, K x /\ not (finite_union_base H s b n x)).
    {
      intros.
      specialize (H2 n).
      apply Classical_Pred_Type.not_all_not_ex.
      intros H3.
      contradict H2.
      intros x Kx.
      specialize (H3 x).
      rewrite classical_tautology_neg_and in H3.
      destruct H3;[contradict H2 |];auto.
      rewrite classical_tautology_dneg in H2;auto.
    }
    clear H2.
    apply countable_choice in H3.
    destruct H3 as [f F].
    destruct (H1 f) as [g [G1 [x [Kx Lx]]]]; [apply F|].
    destruct (H0 _ Kx) as [n Hn].
    destruct (b n) as [[c r] | ] eqn:E;auto.
    simpl in Hn.
    enough (forall n, exists k, (k > n)%nat /\ ball H (D s c) r (f (g k))).
    {
      destruct (H2 n) as [k [Hk1 Hk2]].
      destruct (F (g k)).
      contradict H4.
      exists n.
      split.
      destruct (G1 k).
      lia.
      exists (c,r).
      split;auto.
    }
    intros.
    assert (exists m, d_X H (D s c) x < prec r - prec m).
    {
      destruct (real_Archimedean (prec r - d_X H (D s c) x)). 
      apply real_gt_minus_gt_zero;auto.
      exists x0.
      add_both_side_by (prec x0 - d_X H (D s c) x).
      rewrite real_plus_comm;auto.
    }
    destruct H2 as [m Hm].
    exists (n0 + m + 1)%nat.
    split;try lia.
    apply (real_le_lt_lt  _ _ _ (dx_triangle _ _ _ x)).
    replace (prec r) with ((prec r - prec m) + prec m) by ring.
    apply real_lt_lt_plus_lt;auto.
    rewrite d_sym.
    apply (real_le_lt_lt _ _ _ (Lx _)).
    apply prec_monotone;lia.
  Qed.

  Lemma bishop_compact_compact H (s : separable) (l : has_limit H) K : totally_bounded H K -> complete H K -> compact K.
  Proof.
    intros.
    apply (fin_cover_compact H s);auto.
    - apply bishop_compact_classical_fincover_compact;auto.
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
   Qed.       
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

  Definition fattening H U eps x := exists y, U y /\ d_X H x y <= eps.


  Lemma dist_pos H A x r : dist H A x r ->  (r >= real_0).
  Proof.
    intros.
    destruct H0.
    apply H1.
    intros.
    apply d_nonneg.
  Qed.
  
  Lemma inf_defined_exists P x : W_is_inf P x -> forall n, exists t, P t /\ t <= x + prec n.
  Proof.
    intros.
    apply Classical_Pred_Type.not_all_not_ex.
    intros H0.
    destruct H.
    assert ((not ( -x <= (-x - prec n)))) as Py.
    apply real_gt_nle.
    replace (-x) with (-x + real_0) at 1 by ring.
    unfold real_minus.
    apply real_lt_plus_lt.
    add_both_side_by (prec n).
    apply prec_pos.
    specialize (H1 (-x - prec n)).
    contradict Py.
    apply H1.
    intros p P'.
    specialize (H0 (-p)).
    rewrite classical_tautology_neg_and in H0.
    destruct H0.
    contradict H0;auto.
    apply real_nle_ge in H0.
    add_both_side_by (x + prec n - p).
    apply real_lt_le;apply H0.
  Qed.

  Definition Hausdorff_dist_one_sided H A B x:= W_is_inf (fun eps => eps >= real_0 /\ (is_subset A (fattening H B eps))) x.
  
  Lemma fattening_fatter H A r1 r2 : (r1 <= r2 ) -> is_subset (fattening H A r1) (fattening H A r2).
  Proof.
    intros.
    intros x Fx.
    destruct Fx as [x0 [P1 P2]].
    exists x0.
    split; auto.
    apply (real_le_le_le _ _ _ P2);auto.
  Qed.

  Lemma Hausdorff_dist_one_sided_contained H A B x : Hausdorff_dist_one_sided H A B x -> forall n, (is_subset A (fattening H B (x+prec n))).
  Proof.
    intros.
    pose proof (inf_defined_exists _ _ H0 n).
    destruct H1 as [r [[R1 R2] R3]].
    intros y Ay.
    destruct (R2 _ Ay) as [x0 [P1 P2]].
    exists x0;split;auto.
    apply (real_le_le_le _ _ _ P2);auto.
  Qed.

  Lemma Hausdorff_dist_os_add_pt H A B x e1 e2 : Hausdorff_dist_one_sided H A B e1 -> dist H B x e2 -> Hausdorff_dist_one_sided H (fun t => A t \/ t = x) B (real_max e1 e2). 
  Proof.
    intros.
    split.
    - intros r [P1 P2].
      destruct H0.
      add_both_side_by (real_max e1 e2 - r).
      apply real_max_le_le_le.
      + specialize (H0 r).
        simpl in H0.
        add_both_side_by (r - e1).
        apply H0.
        split;auto.
        intros y By.
        apply P2.
        left;auto.
      +  assert (fattening H B (-r) x).
         apply P2;right;auto.
         destruct H3 as [y [Y1 Y2]].
         destruct H1.
         apply (real_le_le_le _ (d_X H x y));auto.
         apply H1;auto.
    - intros.
      enough (forall n, -real_max e1 e2 - prec n <= s') by (apply lim_le_le'; intros n; add_both_side_by (-prec n);apply H3).
      intros.
      apply H2.
      replace (- (-real_max e1 e2 - prec n)) with (real_max e1 e2 + prec n) by ring.
      split.
      replace (real_0) with (real_0 + real_0) by ring.
      apply real_le_le_plus_le; [|apply real_lt_le;apply prec_pos].
      apply real_max_snd_le_le.
      apply dist_pos in H1;auto.
      intros y Py.
      destruct Py.
      enough (fattening H B (e1 + prec n) y).
      apply  (fattening_fatter H B  (e1 + prec n) (real_max e1 e2 + prec n));auto;add_both_side_by (-prec n); apply real_max_fst_ge.
      apply (Hausdorff_dist_one_sided_contained _ _ _ _ H0);auto.
      rewrite H3.
      unfold fattening.
      destruct (dist_bounded_exists_lt _ _ _ _ H1 n).
      destruct H4.
      exists x0.
      split;auto.
      apply real_lt_le.
      rewrite d_sym.
      apply (real_lt_le_lt _ _ _ H5).
      add_both_side_by (-prec n).
      apply real_max_snd_ge.
  Qed.      

  Lemma Hausdorff_dist_os_extend_left H A B x : located H B -> {r | Hausdorff_dist_one_sided H A B r} -> {r | Hausdorff_dist_one_sided H (fun t => A t \/ t = x) B r}.
  Proof.
    intros.
    destruct X1.
    destruct (X0 x).
    exists (real_max x0 x1).
    apply Hausdorff_dist_os_add_pt;auto.
  Qed.
    
  Lemma Hausdorff_dist_os_pt H x y: Hausdorff_dist_one_sided H (fun t => t = x) (fun t => t = y) (d_X H x y).
  Proof.
    split.
    -  intros r [Hr1 Hr2].
       destruct (Hr2 x) as [_ [->  H0]];auto.
       add_both_side_by (d_X H x y - r);auto.
    - intros s Hs.
      apply Hs.
      replace (- - d_X H x y) with (d_X H x y) by ring.
      split; try apply d_nonneg.
      exists y;split;auto.
      rewrite H0;apply real_le_triv.
  Qed.

  Lemma Hausdorff_dist_os_pos H A B r : Hausdorff_dist_one_sided H A B r -> r >= real_0.
  Proof.
    intros.
    destruct H0.
    enough (-r <= real_0) by (add_both_side_by (-r);auto).
    apply H1.
    unfold W_is_upper_bound.
    intros.
    add_both_side_by (-z).
    apply H2.
  Qed.

  Lemma Hausdorff_dist_os_pt_extend H A x y r1: Hausdorff_dist_one_sided H (fun t => t = x) A r1 ->  Hausdorff_dist_one_sided H (fun t => t = x) (fun t => A t \/ t = y) (real_min r1 (d_X H x y)).
  Proof.
    intros.
    split.
    - intros r [R1 R2].
      add_both_side_by (real_min r1 (d_X H x y) - r).
      destruct H0.
      destruct (R2 x);auto.
      destruct H2.
      destruct H2.
      + apply (real_le_le_le _ _ _ (real_min_fst_le _ _)).
        add_both_side_by (r - r1).
        apply H0;split;auto.
        exists x0.
        rewrite H4;split;auto.
      + apply (real_le_le_le _ _ _ (real_min_snd_le _ _)).
        rewrite <-H2;auto.
   - intros.
     enough (forall n, -real_min r1 (d_X H x y) - prec n <= s') by (apply lim_le_le'; intros n; add_both_side_by (-prec n);apply H2).
     intros n.
     apply H1.
     replace (-  (- real_min r1 (d_X H x y) - prec n)) with (real_min r1 (d_X H x y)+prec n) by ring.
     split.
     replace (real_0) with (real_0 + real_0) by ring.
     apply real_le_le_plus_le; [|apply real_lt_le;apply prec_pos].
     destruct (real_min_cand r1 (d_X H x y)) as [-> | ->]; try apply d_nonneg.
     apply (Hausdorff_dist_os_pos _ _ _ _ H0).
     intros _ ->.
     destruct (real_min_cand r1 (d_X H x y)) as [-> | ->].
     destruct (Hausdorff_dist_one_sided_contained _ _ _ _ H0 n x);auto.
     exists x0.
     split;[left|]; try apply H2.
     exists y.
     split;[right|];auto.
     add_both_side_by (-d_X H x y); apply real_lt_le;apply prec_pos.
   Qed.


  Lemma Hausdorff_dist_os_pt_extend_right H B x y:  {r | Hausdorff_dist_one_sided H (fun t => t = x) B r} -> {r | Hausdorff_dist_one_sided H (fun t => t = x) (fun t => B t \/ t = y) r}.
  Proof.
    intros [r R].
    exists (real_min r (d_X H x y)).
    apply Hausdorff_dist_os_pt_extend;auto.
  Qed.

  Lemma Hausdorff_dist_os_pt_pts_exists H x l y: {r | Hausdorff_dist_one_sided H (fun t => t = x) (fun t => In t (y :: l)) r}.
  Proof.
    induction l.
    - simpl.
      exists (d_X H x y).
      replace (fun t => y = t \/ False) with (fun t => t = y).
      apply Hausdorff_dist_os_pt.
      apply fun_ext;intros;apply Prop_ext;intros;destruct H0;auto;contradict H0.
   - replace (fun t => In t (y :: a :: l )) with (fun t => In t (y :: l) \/ t = a).
     apply Hausdorff_dist_os_pt_extend_right.
     apply IHl.
     apply fun_ext.
     intros.
     simpl.
     apply Prop_ext;intros;destruct H0;auto;destruct H0;auto.
  Qed.
  Lemma point_set_located H x l : located H  (fun t => In t (x :: l)).
  Proof.
    induction l.
    - intros y.
      exists (d_X H x y).
      simpl.
      split.
      intros.
      destruct H0; [|contradict H0].
      rewrite H0, d_sym;apply real_le_triv.
      intros.
      specialize (H0 x).
      rewrite d_sym;apply H0.
      left;auto.
   - replace (fun t => In t (x :: a :: l)) with (union (fun t => In t (x :: l)) (fun t => t = a)).
     intro y.
     destruct (IHl y).
     exists (real_min x0 (d_X H y a)).
     apply dist_union;auto.
     split;intros.
     rewrite H0;apply real_le_triv.
     apply H0;auto.
     apply fun_ext; intros;simpl;apply Prop_ext; intros.
     destruct H0;simpl;auto.
     destruct H0;simpl;auto.
     unfold union.
     destruct H0;simpl;auto.
     destruct H0;simpl;auto.
  Qed.

  Lemma Hausdorff_dist_one_sided_pts H x l1 y l2: {r | Hausdorff_dist_one_sided H (fun t => In t (x :: l1)) (fun t => In t (y :: l2)) r}.
  Proof.
    induction l1.
    - replace (fun t => In t [x]) with (fun t => t = x).
      apply Hausdorff_dist_os_pt_pts_exists.
      apply fun_ext;intros;apply Prop_ext;simpl;intros;destruct H0;auto;contradict H0.
    - replace (fun t => In t (x :: a :: l1)) with (fun t => In t (x :: l1) \/ t = a).
      apply Hausdorff_dist_os_extend_left;[apply point_set_located | apply IHl1].
      apply fun_ext; simpl; intros;apply Prop_ext; intros;destruct H0;auto;destruct H0;auto.
  Qed.

  Definition Hausdorff_dist H A B x:= W_is_inf (fun eps => eps >= real_0 /\ (is_subset A (fattening H B eps) /\ (is_subset B (fattening H A eps)))) x.

  Lemma Hausdorff_dist_pts_exists H x l1 y l2 : {r | Hausdorff_dist H (fun t => In t (x :: l1)) (fun t => In t (y :: l2)) r}.
  Proof.
    destruct (Hausdorff_dist_one_sided_pts H x l1 y l2) as [r1 R1].
    destruct (Hausdorff_dist_one_sided_pts H y l2 x l1) as [r2 R2].
    exists (real_max r1 r2).
    split.
    - intros r [P1 [P2 P3]].
      destruct (real_max_cand r1 r2) as [-> | ->].
      apply R1;split;auto.
      apply R2;split;auto.
   - intros.
     enough (forall n, -real_max r1 r2 - prec n <= s') by (apply lim_le_le'; intros n; add_both_side_by (-prec n);apply H1).
     intros n.
     apply H0.
     replace (- (-real_max r1 r2 - prec n)) with (real_max r1 r2 + prec n) by ring.
     split.
     + replace (real_0) with (real_0 + real_0) by ring.
       apply real_le_le_plus_le; [|apply real_lt_le;apply prec_pos].
       destruct (real_max_cand r1 r2) as [-> | ->].
       apply (Hausdorff_dist_os_pos _ _ _ _ R1 ).
       apply (Hausdorff_dist_os_pos _ _ _ _ R2 ).
    + split.
      intros z Z.
      apply (fattening_fatter _ _ (r1 + prec n)).
      add_both_side_by (-prec n).
      apply real_max_fst_ge.
      apply (Hausdorff_dist_one_sided_contained _ _ _ _ R1);auto.
      intros z Z.
      apply (fattening_fatter _ _ (r2 + prec n)).
      add_both_side_by (-prec n).
      apply real_max_snd_ge.
      apply (Hausdorff_dist_one_sided_contained _ _ _ _ R2);auto.
  Qed.

  Definition nth_centers H A (T : totally_bounded H A) (n : nat) : list X.
  Proof.
    destruct (T n).
    apply x.
  Defined.

  Lemma nth_centers_Hausdorff_dist H A (T : totally_bounded H A) :  forall n r, Hausdorff_dist H A (fun t => In t (nth_centers H A T n)) r -> r  <= prec n.  
  Proof.
    intros.
    destruct H0.
    add_both_side_by (-r - prec n).
    apply H0.
    replace (- - prec n) with (prec n) by ring.
    split;[apply real_lt_le; apply prec_pos |].
    split.
    - intros x Ax.
      unfold nth_centers.
      destruct (T n).
      destruct a.
      specialize (H3 _ Ax).
      apply Exists_exists in H3.
      destruct H3;destruct H3.
      exists x1.
      split;auto.
      apply real_lt_le;auto.
    - unfold nth_centers.
      destruct (T n) as [l L].
      intros x Px.
      destruct L.
      destruct (H2 _ Px).
      exists x0.
      destruct H4.
      split;auto.
      apply real_lt_le;auto.
  Qed.

  Lemma inf_to_sup : (forall P, ((exists r, W_is_sup P r) -> exists r, W_is_sup P (- r))).
  Proof.
      intros P H1.
      destruct H1.
      exists (-x).
      assert ((- - x) = x) as -> by ring.
      exact H.
  Qed.

  Lemma nth_centers_Hausdorff_dist_exists H A (T : totally_bounded H A) :  forall n, exists r, Hausdorff_dist H A (fun t => In t (nth_centers H A T n)) r.
  Proof.
    intros.
    unfold Hausdorff_dist.
    unfold W_is_inf.
    apply inf_to_sup.
    apply W_complete.
    - 
      exists (-prec n).
      replace (- - prec n) with (prec n) by ring.
      split; [apply real_lt_le;apply prec_pos |].
      split.
      + intros x Ax.
        unfold nth_centers.
        destruct (T n).
        destruct a.
        specialize (H1 _ Ax).
        apply Exists_exists in H1.
        destruct H1;destruct H1.
        exists x1.
        split;auto.
        apply real_lt_le;auto.
      + unfold nth_centers.
        destruct (T n) as [l L].
        intros x Px.
        destruct L.
        destruct (H0 _ Px).
        exists x0.
        destruct H2.
        split;auto.
        apply real_lt_le;auto.
   - exists real_0.
     intros a.
    intros.
    destruct H0.
    add_both_side_by (-a).
    apply H0.
  Qed.

  Lemma nth_centers_Hausdorff_bound_exists H A (T : totally_bounded H A) :   forall n, exists r, Hausdorff_dist H A (fun t => In t (nth_centers H A T n)) r /\ r <= prec n.
  Proof.
    intros.
    destruct (nth_centers_Hausdorff_dist_exists _ _ T n).
    exists x.
    split;auto.
    apply (nth_centers_Hausdorff_dist _ _ T);auto.
  Qed.

  Lemma Hausdorff_dist_contained H A B x : Hausdorff_dist H A B x -> forall n, (is_subset A (fattening H B (x+prec n)) /\ is_subset B (fattening H A (x + prec n))).
  Proof.
    intros.
    pose proof (inf_defined_exists _ _ H0 n).
    destruct H1 as [r [[R1 R2] R3]].
    destruct R2.
    split;intros y Ay.
    destruct (H1 _ Ay) as [x0 [P1 P2]];exists x0;split;auto;apply (real_le_le_le _ _ _ P2);auto.
    destruct (H2 _ Ay) as [x0 [P1 P2]];exists x0;split;auto; apply (real_le_le_le _ _ _ P2);auto.
  Qed.

  Lemma Hausdorff_dist_nonneg H A B r : Hausdorff_dist H A B r -> r >= real_0.
  Proof.
    intros.
    destruct H0.
    enough (-r <= real_0) by (add_both_side_by (-r);auto).
    apply H1.
    unfold W_is_upper_bound.
    intros.
    add_both_side_by (-z).
    apply H2.
   Qed.

  Lemma real_plus_plus_ge0 x y : x >= real_0 -> y >= real_0 -> x + y >= real_0.
  Proof.
    intros.
    replace (real_0) with (real_0 + real_0) by ring.
    apply real_le_le_plus_le;auto.
  Qed.

  Lemma real_plus_prec_ge0 x n : x >= real_0 ->  x + prec n >= real_0.
  Proof.
    intros.
    apply real_plus_plus_ge0;auto.
    apply real_lt_le.
    apply prec_pos.
  Qed.

  Lemma Hausdorff_dist_tri_exists {H A A' B r1 r2}: Hausdorff_dist H A A' r1 -> Hausdorff_dist H A' B r2 -> (exists r, Hausdorff_dist H A B r).
  Proof.
    intros.
    apply inf_to_sup.
    apply W_complete.
     - exists (-(r1 + (prec 1) + r2 + (prec 1))).
       replace (- - (r1+ prec 1 + r2 + prec 1)) with (r1 + prec 1 + (r2 + prec 1)) by ring.
       destruct (Hausdorff_dist_contained _ _ _ _ H0 1).
       destruct (Hausdorff_dist_contained _ _ _ _ H1 1).
       split.
       apply real_plus_plus_ge0;apply real_plus_prec_ge0.
       apply (Hausdorff_dist_nonneg _ _ _ _ H0).
       apply (Hausdorff_dist_nonneg _ _ _ _ H1).
       split.
       + intros x Ax.
         destruct (H2 _ Ax) as [y [A'y dy]].
         destruct (H4 _ A'y) as [z [A'z dz]].
         exists z.
         split;auto.
         apply (real_le_le_le _ _ _ (dx_triangle _ _ _ y)).
         apply (real_le_le_plus_le);auto.
       + intros x Bx.
         destruct (H5 _ Bx) as [y [A'y dy]].
         destruct (H3 _ A'y) as [z [A'z dz]].
         exists z.
         split;auto.
         rewrite real_plus_comm.
         apply (real_le_le_le _ _ _ (dx_triangle _ _ _ y)).
         apply (real_le_le_plus_le);auto.
    - exists real_0.
      intros a.
      intros.
      destruct H2.
      add_both_side_by (-a).
      apply H2.
  Qed.


  Lemma Hausdorff_dist_sym {H A B r}: Hausdorff_dist H A B r -> Hausdorff_dist H B A r.
  Proof.
    intros.
    destruct H0.
    split.
    intros r' [R1 R2].
    apply H0;split;auto.
    destruct R2.
    split;auto.
    intros.
    apply H1.
    intros r' [R1 R2].
    apply H2;split;auto.
    destruct R2;split;auto.
  Qed.

  Lemma nonempty_centers H A (T : totally_bounded H A) : (exists x, A x) -> (forall n , { a & {l | nth_centers H A T n = a :: l}}).
  Proof.
     intros.
     unfold nth_centers.
     destruct (T n).
     destruct x.
     - destruct a.
       contradict H0.
       intros H0.
       destruct H0.
       specialize (H2 _ H0).
       apply Exists_exists in H2.
       destruct H2.
       destruct H2.
       simpl in H2.
       contradict H2.
    - exists x.
      exists x0;auto.
  Qed.
  Lemma nth_centers_fattening H A (T : totally_bounded H A) : forall n, is_subset A (fattening H (fun t => In t (nth_centers H A T n)) (prec n)).
  Proof.
    intros.
    unfold nth_centers.
    destruct (T n) as [l [L1 L2]].
    intros x Ax.
    specialize (L2 _ Ax).
    apply Exists_exists in L2.
    destruct L2 as [y [Y1 Y2]].
    exists y.
    split;auto.
    apply real_lt_le;auto.
  Qed.

  Lemma is_subset_transitive (A B C : (@csubset X)) : is_subset A B -> is_subset B C -> is_subset A C.
  Proof.
    intros.
    intros y Ay.
    apply H0.
    apply H;auto.
  Qed.


  Lemma nth_centers_intersects H A (T : totally_bounded H A) : forall n z , In z (nth_centers H A T n) -> exists x, A x /\ (d_X H z x) <= prec n .
  Proof.
    unfold nth_centers.
    intros.
    destruct (T n).
    destruct a.
    destruct (H1 _ H0).
    exists x0.
    split;try apply H3.
    apply real_lt_le;apply H3.
  Qed.

  Lemma Hausdorff_dist_classical_exists H A B : totally_bounded H A -> totally_bounded H B -> (exists x, A x) -> (exists x, B x) -> exists r, Hausdorff_dist H A B r.
  Proof.
    intros.
    apply inf_to_sup.
    apply W_complete.
    - destruct (nonempty_centers H A X0 H0 0) as [a0 [l0 L0]].
      destruct (nonempty_centers H B X1 H1 0) as [a1 [l1 L1]].
      destruct (Hausdorff_dist_pts_exists H a0 l0 a1 l1).
      rewrite <-L0, <-L1 in h.
      exists (-x - prec 0 - prec 0 - prec 0).
      replace (- (-x - prec 0 - prec 0 - prec 0)) with (x+ prec 0 + prec 0 + prec 0) by ring.
      split.
      apply real_plus_prec_ge0.
      apply real_plus_prec_ge0.
      apply real_plus_prec_ge0.
      apply (Hausdorff_dist_nonneg _ _ _ _ h).
      destruct (Hausdorff_dist_contained _ _ _ _ h 0).
      split.
      + apply (is_subset_transitive _ _ _ (nth_centers_fattening H A X0 0)).
        apply (is_subset_transitive _ (fattening H (fun t => In t (nth_centers H B X1 0)) (x+prec 0+prec 0))).
        intros y Y.
        destruct Y.
        destruct H4.
        destruct (H2 _ H4) as [z [Z1 Z2]].
        exists z;split;auto.
        apply (real_le_le_le _ _ _ (dx_triangle H _ _ x0)).
        replace (x + prec 0 + prec 0) with (prec 0 + (x + prec 0)) by ring.
        apply real_le_le_plus_le;auto.
        intros y Y.
        destruct Y as [z [Z1 Z2]].
        destruct (nth_centers_intersects H B X1 _ _ Z1) as [b [Bb1 Bb2]].
        exists b;split;auto.
        apply (real_le_le_le _ _ _ (dx_triangle H _ _ z)).
        apply real_le_le_plus_le;auto.
      + apply (is_subset_transitive _ _ _ (nth_centers_fattening H B X1 0)).
        apply (is_subset_transitive _ (fattening H (fun t => In t (nth_centers H A X0 0)) (x+prec 0+prec 0))).
        intros y Y.
        destruct Y.
        destruct H4.
        destruct (H3 _ H4) as [z [Z1 Z2]].
        exists z;split;auto.
        apply (real_le_le_le _ _ _ (dx_triangle H _ _ x0)).
        replace (x + prec 0 + prec 0) with (prec 0 + (x + prec 0)) by ring.
        apply real_le_le_plus_le;auto.
        intros y Y.
        destruct Y as [z [Z1 Z2]].
        destruct (nth_centers_intersects H A X0 _ _ Z1) as [b [Bb1 Bb2]].
        exists b;split;auto.
        apply (real_le_le_le _ _ _ (dx_triangle H _ _ z)).
        apply real_le_le_plus_le;auto.
    - exists real_0.
      intros a.
      intros.
      destruct H2.
      add_both_side_by (-a).
      apply H2.
  Qed.

  Lemma Hausdorff_dist_unique H A B r1 r2 : Hausdorff_dist H A B r1 -> Hausdorff_dist H A B r2 -> r1 = r2.
  Proof.
    intros [H1 H2] [H1' H2'].
    apply real_le_le_eq;add_both_side_by (-r1 - r2).
    apply H2'.
    apply H1.
    apply H2.
    apply H1'.
  Qed.

  Lemma Hausdorff_dist_fattening H A B r r' eps : (eps >= 0) -> Hausdorff_dist H A B r -> Hausdorff_dist H (fattening H A eps) (fattening H B eps) r' -> abs (r-r') <= eps.
  Proof.
    intros.
    apply real_abs_le_le_le.
    - add_both_side_by (-r).
      apply H2.
      intros t [T1 [T2 T3]].
      add_both_side_by (-eps).
      apply H1.
      split.
      replace (- (t- eps)) with (-t + eps) by ring;apply real_plus_plus_ge0;auto.
      split.
      + intros x Ax.
        destruct (T2 x); [exists x;split;auto;rewrite dist_zero;auto|].
        destruct H3.
        destruct H3.
        destruct H3.
        exists x1;split;auto.
        apply (real_le_le_le _ _ _ (dx_triangle H _ _ x0)).
        replace (- (t - eps)) with (-t + eps) by ring.
        apply (real_le_le_plus_le);auto.
      + intros x Bx.
        destruct (T3 x); [exists x;split;auto;rewrite dist_zero;auto|].
        destruct H3.
        destruct H3.
        destruct H3.
        exists x1;split;auto.
        apply (real_le_le_le _ _ _ (dx_triangle H _ _ x0)).
        replace (- (t - eps)) with (-t + eps) by ring.
        apply (real_le_le_plus_le);auto.
  - add_both_side_by (-r').
    apply H1.
    intros t [T1 [T2 T3]].
    add_both_side_by (-eps).
    apply H2.
    split.
    replace (- (t- eps)) with (-t + eps) by ring;apply real_plus_plus_ge0;auto.
    split.
    + intros x Fx.
      destruct Fx as [y [Y1 Y2]].
      destruct (T2 _ Y1) as [z [Z1 Z2]].
      exists z.
      split.
      exists z;split;auto; rewrite dist_zero;auto.
      apply (real_le_le_le _ _ _ (dx_triangle H _ _ y)).
      replace (- (t - eps)) with (eps - t) by ring.
      apply (real_le_le_plus_le);auto.
    + intros x Fx.
      destruct Fx as [y [Y1 Y2]].
      destruct (T3 _ Y1) as [z [Z1 Z2]].
      exists z.
      split.
      exists z;split;auto; rewrite dist_zero;auto.
      apply (real_le_le_le _ _ _ (dx_triangle H _ _ y)).
      replace (- (t - eps)) with (eps - t) by ring.
      apply (real_le_le_plus_le);auto.
  Qed.

  Lemma Hausdorff_dist_exists H A B : totally_bounded H A -> totally_bounded H B -> (exists x, A x) -> (exists x, B x) -> {r | Hausdorff_dist H A B r}.
  Proof.
    intros.
    apply real_limit_P.
    - destruct (Hausdorff_dist_classical_exists _ _ _ X0 X1 H0 H1).
      exists x.
      split;auto.
      intros.
      apply (Hausdorff_dist_unique _ _ _ _ _ H2 H3).
    - intros.
      destruct (nonempty_centers H A X0 H0 (S n)) as [a0 [l0 L0]].
      destruct (nonempty_centers H B X1 H1 (S n)) as [a1 [l1 L1]].
      destruct (Hausdorff_dist_pts_exists H a0 l0 a1 l1).
      exists x.
      destruct (Hausdorff_dist_classical_exists _ _ _ X0 X1 H0 H1).
      exists x0.
      rewrite <-L0,<-L1 in *.
      split;auto.
      apply real_abs_le_le_le.
      + add_both_side_by (-x).
        apply H2.
        intros t [T1 [T2 T3]].
        add_both_side_by (-prec n).
        apply h.
        split.
        replace (-(t- prec n)) with (-t + prec n) by ring; apply real_plus_prec_ge0;auto.
        split.
        * intros y Y.
          destruct (nth_centers_intersects _ _ _ _ _ Y ) as [z [Z1 Z2]].
          destruct (T2 _ Z1) as [z' [Z1' Z2']].
          destruct (nth_centers_fattening  H B X1 (S n) _ Z1' ) as [z'' [Z1'' Z2'']].
          exists z'';split;auto.
          apply (real_le_le_le _ _ _ (dx_triangle H _ _ z)).
          rewrite <-prec_twice.
          replace (- (t - (prec (n+1) + prec (n+1)))) with (prec (S n) + (-t + prec (S n))) by (rewrite Nat.add_1_r;ring).
          apply real_le_le_plus_le;auto.
          apply (real_le_le_le _ _ _ (dx_triangle H _ _ z')).
          apply real_le_le_plus_le;auto.
        * intros y Y.
          destruct (nth_centers_intersects _ _ _ _ _ Y ) as [z [Z1 Z2]].
          destruct (T3 _ Z1) as [z' [Z1' Z2']].
          destruct (nth_centers_fattening  H A X0 (S n) _ Z1' ) as [z'' [Z1'' Z2'']].
          exists z'';split;auto.
          apply (real_le_le_le _ _ _ (dx_triangle H _ _ z)).
          rewrite <-prec_twice.
          replace (- (t - (prec (n+1) + prec (n+1)))) with (prec (S n) + (-t + prec (S n))) by (rewrite Nat.add_1_r;ring).
          apply real_le_le_plus_le;auto.
          apply (real_le_le_le _ _ _ (dx_triangle H _ _ z')).
          apply real_le_le_plus_le;auto.
    + add_both_side_by (-x0).
      apply h.
      intros t [T1 [T2 T3]].
      add_both_side_by (-prec n).
      apply H2.
      split.
      replace (-(t- prec n)) with (-t + prec n) by ring; apply real_plus_prec_ge0;auto.
      split.
      * intros y Y.
          destruct (nth_centers_fattening  H A X0 (S n) _ Y) as [z [Z1 Z2]].
          destruct (T2 z Z1) as [z' [Z1' Z2']].
          destruct (nth_centers_intersects _ _ _ _ _ Z1' ) as [z'' [Z1'' Z2'']].
          exists z''.
          split;auto.
          apply (real_le_le_le _ _ _ (dx_triangle H _ _ z)).
          rewrite <-prec_twice.
          replace (- (t - (prec (n+1) + prec (n+1)))) with (prec (S n) + (-t + prec (S n))) by (rewrite Nat.add_1_r;ring).
          apply real_le_le_plus_le;auto.
          apply (real_le_le_le _ _ _ (dx_triangle H _ _ z')).
          apply real_le_le_plus_le;auto.
      * intros y Y.
          destruct (nth_centers_fattening  H B X1 (S n) _ Y) as [z [Z1 Z2]].
          destruct (T3 z Z1) as [z' [Z1' Z2']].
          destruct (nth_centers_intersects _ _ _ _ _ Z1' ) as [z'' [Z1'' Z2'']].
          exists z''.
          split;auto.
          apply (real_le_le_le _ _ _ (dx_triangle H _ _ z)).
          rewrite <-prec_twice.
          replace (- (t - (prec (n+1) + prec (n+1)))) with (prec (S n) + (-t + prec (S n))) by (rewrite Nat.add_1_r;ring).
          apply real_le_le_plus_le;auto.
          apply (real_le_le_le _ _ _ (dx_triangle H _ _ z')).
          apply real_le_le_plus_le;auto.
  Qed.

  Definition Hausdorff_dist_bound H A B eps := exists r, Hausdorff_dist H A B r /\ r < eps.

  Lemma Hausdorff_dist_bound_spec H A B eps:  Hausdorff_dist_bound H A B eps -> (is_subset B (fattening H A eps)) /\ is_subset A (fattening H B eps).
   Proof.
     intros.
     destruct H0 as [r [R1 R2]].
     destruct (real_Archimedean (eps-r)) as [n N].
     apply real_gt_minus_gt_zero;auto.
     pose proof (Hausdorff_dist_contained _ _ _ _ R1 n).
     destruct H0.
     split; [apply (is_subset_transitive _ _ _ H1)|apply (is_subset_transitive _ _ _ H0)];apply fattening_fatter;apply real_lt_le;add_both_side_by (-r);replace (-r+eps) with (eps -r) by ring;auto.
  Qed.
      
  Lemma totally_bounded_lim H  :
    forall K,
      (forall n : nat, {X : csubset & prod (totally_bounded H X) (Hausdorff_dist_bound H X K (prec n))})
      -> totally_bounded H K.
  Proof.
    intros.
    intros n.
    destruct (X0 (n+1)%nat) as [A [H1 H2]].
    apply Hausdorff_dist_bound_spec in H2.
    destruct H2 as [H3 H4].
    destruct (H1 (n+1)%nat) as [l [L1 L2]].
    exists l.
    split.
    - intros.
      destruct (L1 _ H0) as [y Hy].
      destruct (H4 y);[apply Hy|].
      exists x0.
      split; try apply H5.
      destruct Hy,H2.
      apply (real_le_lt_lt _ _ _ (dx_triangle _ _ _ y)).
      rewrite <-prec_twice.
      rewrite real_plus_comm.
      apply real_le_lt_plus_lt;auto.
      apply H2.
   - intros.
     apply Exists_exists.
     destruct (H3 _ H0) as [y [Ha Hb]].
     specialize (L2 _ Ha).
     apply Exists_exists in L2.
     destruct L2 as [z [Hz Hz']].
     exists z.
     split;auto.
     apply (real_le_lt_lt _ _ _ (dx_triangle _ _ _ y)).
     rewrite <-prec_twice.
     apply real_le_lt_plus_lt;auto.
  Qed.
  Lemma Hausdorff_dist_bound_spec' H A B eps: eps >= real_0 /\  (is_subset B (fattening H A eps)) /\ is_subset A (fattening H B eps) -> (forall n, Hausdorff_dist_bound H A B (eps + prec n)).
  Proof.
    intros [H0 [H1 H2]] n.
    enough (exists r, Hausdorff_dist H A B r) as [r R].
    - exists r;split;auto.
      replace r with (r + real_0) by ring.
      apply real_le_lt_plus_lt; [| apply prec_pos].
      add_both_side_by (-r - eps).
      apply R.
      replace (- - eps) with eps by ring.
      split;auto.
   - apply inf_to_sup.
     apply W_complete.
     + exists (-eps).
       replace (- - eps) with eps by ring.
       split;auto.
    + exists real_0.
      intros z [Hz1 Hz2].
      add_both_side_by (-z);auto.
  Qed.


  Lemma fast_cauchy_limit_exist_helper H (l : has_limit H) K :  (forall n, Hausdorff_dist_bound H (K n) (K (n+1)%nat) (prec (n+1)%nat)) -> exists J, forall n k, Hausdorff_dist_bound H (K n) J ((prec n)+(prec k)).
  Proof.
    intros.
    exists (fun x => exists f, forall n, K n (f n) /\ d_X H (f n) x <= prec n).
    intros.

    apply Hausdorff_dist_bound_spec'.
    split;[apply real_lt_le;apply prec_pos |split].
    - intros x Hx.
      destruct Hx as [f F].
      exists (f n).
      split;try apply F.
      rewrite d_sym;apply F.
   - intros x Hx.
     
      enough (exists f, (forall m, (K m (f m))) /\ (forall n, (d_X H (f n) (f (S n))) <= prec (S n) ) /\ (f n) = x) as [f F].
      {
        destruct (l f).
        apply fast_cauchy_neighbor.
        apply F.
        exists x0.
        split.
        exists f.
        intros.
        split.
        apply F.
        apply m.
        apply lim_le_le'.
        intros.
        apply (real_le_le_le _ _ _ (dx_triangle _ _ _ (f (n0+1)%nat))).
        rewrite <-(prec_twice n0).
        rewrite <-real_plus_assoc.
        apply real_le_le_plus_le; try apply m.
        apply (real_le_le_le _ _ _ (dx_triangle _ _ _ (f n))).
        destruct F as [F1 [F2 F3]].
        rewrite F3 at 1.
        rewrite dist_zero.
        ring_simplify.
        apply fast_cauchy_neighbor in F2.
        apply F2.
      }
      
      enough (exists f, (forall m, (K (m+n)%nat (f m))) /\ (forall m, (d_X H (f m) (f (S m))) <= prec (S m + n)) /\ (f 0%nat) = x).
      {
        revert dependent x.
        induction n.
        - intros.
          destruct H1 as [f [F1 [F2 F3]]].
          exists f.
          split;[|split];auto.
          intros.
          replace m with (m+0)%nat at 1 by lia.
          apply F1.
          intros.
          replace (S n) with (S n +0)%nat at 2 by lia.
          apply F2.
       -  intros.
          assert (exists y, K n y /\ d_X H y x <= prec (S n)) as [y [Hy1 Hy2]].
          {
            specialize (H0 n).
            apply Hausdorff_dist_bound_spec in H0.
            destruct H0.
            replace (n+1)%nat with (S n)  in H0 by lia.
            destruct (H0 _ Hx).
            exists x0.
            split;[| rewrite d_sym];apply H3.
          }
          destruct H1 as [f [F1 [F2 F3]]].
          destruct (IHn _ Hy1) as [g [G1 [G2 G3]]].
          exists (fun n => match n with | 0 => y | (S n') => f n' end).
          split; [|split];auto.
          intros.
          destruct m;simpl;auto.
          replace (S (m+n)) with (m + S n)%nat by lia.
          apply F1.
          destruct m.
          replace (1+n)%nat with (S n) by lia.
          rewrite F3;auto.
          replace (S (S m) + n)%nat with (S m + S n)%nat by lia.
          apply F2.
          exists (fun m => if (m <=? n) then (g m) else (f (m - (S n))%nat)).
          split; [|split].
          intros.
          destruct (m <=? n) eqn:e;auto.
          apply leb_complete_conv in e.
          replace m with ((m - (S n)) + S n)%nat at 1 by lia.
          apply F1.
          intros.
          destruct (S n0 <=? n) eqn:e;auto.
          replace (n0 <=? n) with true by (apply eq_sym; apply leb_correct; apply Nat.leb_le in e;lia).
          apply G2.
          apply leb_complete_conv in e.
          destruct (n0 <=? n) eqn:e';auto.
          apply Nat.leb_le in e'.
          assert (n0 = n)%nat  as -> by lia.
          rewrite G3.
          replace (S n - S n)%nat with 0%nat by lia.
          rewrite F3.
          apply Hy2.
          apply leb_complete_conv in e'.
          replace ((S n0 - S n)%nat) with (S (n0 - S n)) by lia.
          apply (real_le_le_le _ _ _ (F2 _ )).
          replace (S (n0 - S n) + S n)%nat with (S n0) by lia.
          right;auto.
          assert (S n <=? n = false ) as -> by (apply leb_correct_conv;lia).
          replace (S n - S n)%nat with 0%nat by lia.
          apply F3.
      }
      enough (forall x0, exists y0,
           K (fst x0 + n)%nat (snd x0) ->
           fst y0 = (fst x0 + 1)%nat /\ K (fst y0 + n)%nat (snd y0) /\ d_X H (snd x0) (snd y0) <= prec (fst y0 + n)
           ).
      {
        destruct (dependent_choice _ _ H1 (0%nat , x)) as [f [F1 F2]].
        assert (forall m, (fst (f m)) = m /\ K (m +n)%nat (snd (f m))).
        {
          intros.
          induction m.
          split;rewrite F1;auto.
          destruct (F2 m).
          destruct IHm.
          rewrite H2.
          apply H3.
          destruct H3.
          destruct IHm.
          rewrite H2.
          split;auto;try lia.
          replace (S m)  with (fst (f (S m))) at 1 by lia.
          apply H3.
        }
        exists (fun n => (snd (f n))).
        split;[intros;apply H2|split;[|rewrite F1;auto]].
        intros.
        replace (S m) with (fst (f (S m))) at 2 by apply H2.
        apply F2.
        replace (fst (f m)) with m by  (apply eq_sym; apply H2).
        apply H2.
      }
      intros. 
      destruct (lem (K (fst x0 + n)%nat (snd x0))).
      destruct x0.
      simpl in *.
      specialize (H0 (n0+n)%nat).
      apply Hausdorff_dist_bound_spec in H0.
      destruct H0.
      destruct (H2 _ H1) as [y [Y1 Y2]].
      exists ((n0+1)%nat, y).
      intros _.
      split;simpl;auto.
      replace (n0+1+n)%nat with (n0 + n +1)%nat by lia.
      split;auto.
      exists (0%nat, x).
      intros; contradict H1;auto.
 Qed.
      
  Lemma hausdorff_fast_cauchy_limit_exists H (l : has_limit H) K :  (forall n, Hausdorff_dist_bound H (K n) (K (n+1)%nat) (prec (n+1)%nat)) -> exists J, forall n, exists r, Hausdorff_dist H (K n) J r /\ r <= prec n.
  Proof.
    intros.
    destruct (fast_cauchy_limit_exist_helper H l K H0) as [J H1].
    exists J.
    intros.
    specialize (H1 n).
    destruct (H1 0%nat).
    exists x.
    destruct H2 as [H2 _];split;auto.
    apply lim_le_le.
    intros.
    destruct (H1 n0) as [r' [H3 H4]].
    replace x with r';auto.
    apply (Hausdorff_dist_unique _ _ _ _ _ H3 H2).
  Qed.

  End Metric.

  Definition image {X Y} (f : X -> Y) (A : (@csubset X)) := fun x => (exists y, A y /\ f y = x).

   Definition uniformly_continuous_function {X Y} H1 H2 (U : (@csubset X)) (f : X -> Y) := forall n,  {m | forall (x y : X), U x -> U y -> d_X H1 x y < prec m ->  d_X H2 (f x) (f y) < prec n}.

   Lemma list_image {X Y} l (f : X -> Y) : {l' | forall x,  In x l' <-> exists y, In y l /\ x = f y}.
   Proof.
     induction l.
     - exists [].
       intros.
       split;intros.
       apply in_nil in H;contradict H.
       destruct H.
       destruct H;apply in_nil in H;contradict H.
     - destruct IHl.
       exists (f a :: x).
       intros.
       split;intros.
       destruct H.
       exists a;split;simpl;auto.
       destruct (i x0).
       destruct H0;auto.
       destruct H0.
       exists x1;split;simpl;auto.
       destruct H as [y [H1 H2]].
       destruct H1.
       rewrite H.
       left;auto.
       right;auto.
       apply i.
       exists y;auto.
  Qed.
  Lemma image_totally_bounded {X Y} H1 H2 (f : X -> Y) A : uniformly_continuous_function H1 H2 A f -> totally_bounded_strong H1 A -> (totally_bounded_strong H2 (image f A)).
  Proof.
    intros.
    intros n.
    destruct (H n) as [m P].
    destruct (X0 m) as [l [L1 L2]].
    destruct (list_image l f) as [l' L].
    exists l'.
    split.
    - intros.
      destruct (L x).
      destruct H3;auto.
      exists x0.
      destruct H3;split;auto.
   - intros.
     apply Exists_exists.
     destruct H0 as [y [Hy <-]].
     specialize (L2 _ Hy).
     apply Exists_exists in L2.
     destruct L2 as [x [Hx1 Hx2]].
     exists (f x).
     split; [apply L;exists x;auto|].
     apply P;auto.
  Qed.
  
