Require Import Base.
Require Import Monad.
Require Import ClassicalMonads.
Require Import Nabla.
Require Import Kleene.
Require Import MultivalueMonad.
Require Import RealAxioms.
Require Import RealRing.
Require Import RealOrder.
Require Export RealOrderTactic.
Require Export RealLimit0.
Require Import RealLimit1.



Require Import Psatz.
Require Import PeanoNat.

Require Import RealAssumption.

Section RealAbs.

  Definition is_abs x y := (x > real_0 -> y = x) /\ (x = real_0 -> y = real_0) /\ (x < real_0 -> y = - x).

  Lemma abs_unique : forall x : Real, exists ! z : ^Real, is_abs x z.
  Proof.
    intros x.
    destruct (real_total_order x real_0).
    exists (- x).
    split.
    repeat split.
    intro p; contradict p; auto with real.
    intro p; induction p; contradict H; auto with real.
    intros.
    destruct H0 as [_ [_ H0]].
    induction (H0 H); apply eq_refl.
    destruct H.
    exists real_0.
    repeat split; auto with real.
    intro p; induction H; contradict p; auto with real.
    intros.
    destruct H0 as [_ [H0 _]].
    induction (H0 H); apply eq_refl.
    exists x.
    repeat split; auto with real.
    intro p; contradict p; auto with real.
    intros.
    destruct H0 as [H0 [_ _]].
    induction (H0 H); apply eq_refl.
  Qed.

  Lemma approx_abs_little_positive x n : real_0 <= x < prec (n + 2) -> - prec n < - x - x < prec n.
  Proof.
    intros [H r].
    destruct H.

    (* x > 0 *)
    - split.

      (* - prec n < - x - x *)
      apply real_lt_anti_anti.
      replace (- (- x - x)) with (x + x) by ring.
      replace (- - prec n) with (prec n) by ring.
      apply (real_lt_lt_plus_lt _ _ _ _ r) in r.
      apply (real_lt_lt_lt _ _ _ r).
      replace (n + 2)%nat with (n + 1 + 1)%nat by lia.
      rewrite prec_twice.
      apply prec_monotone; lia.

      (* - x - x < prec n *)
      apply (real_lt_lt_plus_lt  _ _ _ _ H) in H.
      apply (real_lt_plus_lt (- x - x)) in H.
      replace ( - x - x + (real_0 + real_0)) with (- x - x) in H by ring.
      replace (- x - x + (x + x)) with real_0 in H by ring.
      apply (real_lt_lt_lt _ _ _ H).
      apply @prec_pos.

    (* x = 0 *)
    - apply eq_sym in H.
      split.

      (* - prec n < - x - x *)
      rewrite H; auto with real.
      apply real_lt_anti_anti.
      replace (- - prec n) with (prec n) by ring.
      replace (- (- real_0 - real_0)) with real_0 by ring.
      apply @prec_pos.

      (* - x - x < prec n *)
      rewrite H.
      replace (- real_0 - real_0) with real_0 by ring.
      apply @prec_pos.
  Qed.

  Lemma approx_abs_little_negative x n : - prec (n + 2) < x < real_0 -> - prec n < x - (- x) < prec n.
  Proof.
    intros [r H].
    replace (x - - x) with (x + x) by ring. 
    split.
    
    pose proof (real_lt_plus_r_lt x _ _ r).
    assert (- prec (n + 2) + x > - prec (n + 2) + - prec (n +2 )).
    apply (real_lt_plus_lt).
    exact r.
    assert (x + x > - prec (n + 2) + - prec (n + 2)).
    apply (real_lt_lt_lt _ _ _ H1 H0).
    assert (- prec n < - prec (n + 2) + - prec (n + 2)).
    apply real_lt_anti_anti.
    replace (  - (- prec (n + 2) + - prec (n + 2)))
      with (   prec (n + 2) + prec (n + 2)) by ring.
    replace (- - prec n) with (prec n) by ring.
    replace (n + 2)%nat with (n + 1 + 1)%nat by lia.
    rewrite prec_twice.
    apply prec_monotone; lia.
    apply (real_lt_lt_lt _ _ _ H3 H2).

    pose proof (real_lt_lt_plus_lt _ _ _ _ H H).
    rewrite real_plus_unit in H0.
    pose proof (prec_pos n).
    apply (real_lt_lt_lt _ _ _ H0 H1).
  Qed.


  Lemma approx_abs_negative x n : x < prec (n + 2) -> exists a : ^Real, is_abs x a /\ - prec n < - x - a < prec n.
  Proof.
      intro r.
      (* branch based on actual sign of x *)
      destruct (real_total_order x real_0).
    
      (* case when x < 0 *)
      exists (- x).
      replace (- x - - x) with real_0 by ring.        
      repeat split; try intro; try auto with real; try ring.
      contradict H0; auto with real.
      rewrite H0; ring.

      apply real_lt_anti_anti.
      replace (- real_0) with real_0 by ring.
      replace (- - prec n) with (prec n) by ring.
      apply prec_pos.
      apply prec_pos.

      (* case when 0 <= x *)
      exists x.
      split.

      (* is_abs x x *)
      repeat split; try intro; try auto with real; try ring.
      contradict H0.
      destruct H; auto with real.
      rewrite H; auto with real.

      (* - prec n < - x - x < prec n *)
      apply approx_abs_little_positive.
      repeat split; try auto with real.
      destruct H; auto with real.
  Qed.

  Lemma approx_abs_positive x n : - prec (n + 2) < x -> exists a : ^Real, is_abs x a /\ - prec n < x - a < prec n.
  Proof.
    intro.
    (* branch based on actual sign of x *)
    destruct (real_total_order x real_0).
    exists (- x).
    repeat split; auto with real.
    intro j. contradict j. auto with real.
    intro j. induction j. contradict H0. auto with real.

    (* case when -prec (n+2) < x < 0, returning -x *)
    apply approx_abs_little_negative; auto.
    apply approx_abs_little_negative; auto.

    (* case when 0 <= x *)
    exists x.
    replace (x - x) with real_0 by ring.  
    repeat split; auto; try intro; try ring.
    destruct H0.
    rewrite H0.
    replace (- real_0) with real_0 by ring.
    auto.

    contradict H0.
    auto with real.
    apply real_lt_anti_anti.
    replace (- - prec n) with (prec n) by ring.
    replace (- real_0) with real_0 by ring.
    apply prec_pos.
    apply prec_pos.
  Qed.


  Definition abs_prop : forall x : Real, {y : Real | is_abs x y}.
  Proof.
    intros x.

    (* the result is an M limit *)
    apply real_mslimit_P_lt_p.
    (* the limit converges *)
    apply abs_unique.

    (* n-th term of the limit is computed via a soft comparison of x and 0 *)
    intro n.
    pose proof (prec_pos (n + 2)) as posN2.
    pose proof ((M_split x real_0 (prec (n + 2))) posN2) as M_order.

    (* eliminate M *)
    revert M_order.
    apply M_lift.
    replace (real_0 - prec (n + 2)) with (- prec (n + 2)) by ring.
    intro order.

    destruct order as [xApprPos|xApprNeg].

    (* when x is determined to be approximately positive, return x *)
    - exists x.
      (* the result x is close enough to the exact (abs x) *)
      apply (approx_abs_positive x n). auto.

    (* when x is determined to be approximately negative, return -x *)
    - exists (-x).
      (* simplify hypothesis xApprNeg *)
      apply (real_lt_plus_lt (prec (n + 2))) in xApprNeg.
      replace (prec (n + 2) + (x - prec (n + 2))) with x in xApprNeg by ring.
      replace (prec (n + 2) + real_0) with (prec (n+2)) in xApprNeg by ring.
      (* the result -x is close enough to the exact (abs x) *)
      apply (approx_abs_negative x n). auto.
  Defined.

  
  Definition abs : ^Real -> ^Real.
  Proof.
    intros x.
    destruct (abs_prop x).
    exact x0.
  Defined.


  Lemma abs_pos : forall x, real_0 <= abs x.
  Proof.
    intros.
    unfold abs.
    destruct (abs_prop x) as [x0 a].
    destruct a as [a [b c]].
    destruct (real_total_order x real_0).
    pose proof (c H).
    rewrite H0.
    left.
    apply real_lt_anti_anti.
    replace (- - x) with x by ring.
    replace (- real_0) with real_0 by ring.
    exact H.
    destruct H.
    right.
    rewrite (b H); auto.

    left. rewrite( a H); auto.
  Qed.

End RealAbs.

Global Hint Resolve abs_pos: real.
