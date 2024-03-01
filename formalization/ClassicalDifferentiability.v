Require Import Real.
Require Import ClassicalMonads ClassicalPartiality ClassicalPartialReals ClassicalContinuity ClassicalContinuousPartialRealFunctions.
Require Import RealAssumption.
Require Import Minmax.

Open Scope Real_scope.

Section toMove.
  Definition uniformly_continuous (f: Real -> Real) r := forall eps, eps > real_0 -> {d : Real | d > real_0 /\ forall x y, abs x <= r -> abs y <= r -> dist x y <= d -> dist (f x) (f y) <= eps}.

End toMove.
Section ClassicalDerivatives.
  Definition uniform_derivative (f: Real -> pc Real) (f': Real -> pc Real) r := (forall x, abs x <= r -> defined (f x)) /\ (forall x, abs x <= r -> defined (f' x)) ->  forall eps, eps > real_0 -> exists delta, delta > real_0 /\ forall x y fx fy fx' , abs x <= r -> abs y <= r -> defined_to (f x) fx -> defined_to (f y) fy -> defined_to (f' x) fx' -> abs (fy - fx - fx' * (y-x)) <= eps * abs(y-x).

  
End ClassicalDerivatives.

Section ConstructiveDerivatives.
  Definition constructive_derivative (f: Real -> Real) (g : Real -> Real) r := forall eps, eps > real_0 -> {d : Real | d > real_0 /\ forall x y, abs x <= r -> abs y <= r -> dist x y <= d -> abs (f y - f x - g x * (y -x)) <= eps * abs(y-x) }.

  Lemma lbc_helper f f' r M : constructive_derivative f f' r -> (forall x, abs x <= r -> abs (f' x) <= M) ->forall eps, eps > real_0 -> {d | d > real_0 /\ forall x y, abs x <= r -> abs y <= r ->dist x y <= d -> dist (f x) (f y) <= eps*d + M *d}.
  Proof.
    intros.
    destruct (X eps) as [d [D1 D2]];auto.
    exists d;split;auto.
    intros.
    rewrite dist_symm.
    unfold dist.
    replace (f y - f x) with ((f y - f x - f' x * (y -x)) + f' x * (y - x)) by ring.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    apply real_le_le_plus_le.
    - apply (real_le_le_le _ (eps * abs (y-x)) _ ); [apply D2;auto|].
      apply real_le_mult_pos_le;auto.
      apply real_lt_le; auto.
      rewrite dist_symm in H3;auto.
   - rewrite abs_mult.
     apply (real_le_le_le _ (abs (f' x) * d)).
     apply real_le_mult_pos_le; [apply abs_pos |rewrite dist_symm in H3;auto].
     rewrite !(real_mult_comm _ d).
     apply real_le_mult_pos_le;[apply real_lt_le|];auto.
  Qed.

  Lemma interval_div_by_d x y d : (d > real_0) ->  exists (n : nat), dist x y <= Nreal n*d.
  Proof.
    destruct (real_total_order (dist x y) real_0).
    apply real_gt_nge in H.
    contradict H.
    apply dist_pos.
    destruct H.
    intros.
    exists 0.
    rewrite H.
    simpl.
    apply real_eq_le;ring.
    intros.
    assert  (dist x y / dg0 H0 > real_0).
    apply real_lt_mult_pos_move_rl.   
    ring_simplify;auto.
    destruct (nat_bound_above _ H1).
    exists x0.
    apply (real_le_mult_pos_cancel (/ dg0 H0)).
    apply real_pos_inv_pos;auto.
    rewrite real_mult_assoc, (real_mult_comm d), real_mult_inv.
    ring_simplify.
    apply real_lt_le.
    apply H2.
  Qed.
  Lemma interval_subdivision_step x y d n : (d > real_0) -> (dist x y <= Nreal (S n) * d) -> exists x1, dist x x1 <= d /\ dist x1 y <= Nreal n * d. 
  Proof.
    intros.
    destruct (real_total_order x y) as [T | [T | T]].
    - exists (x+(real_min d (dist x y))).
      split.
      + unfold dist.
        replace (x - (x + real_min d (abs (x-y)))) with (-real_min d (abs (x-y))) by ring.
        rewrite <-abs_symm.
        rewrite abs_pos_id; [|destruct (real_min_cand d (abs (x-y))) as [-> | ->]; try apply abs_pos; apply real_lt_le;auto].
      apply real_min_fst_le.
     + 
    Admitted.

  Lemma lbc_approx f f' r M :  constructive_derivative f f' r -> (forall x, abs x <= r -> abs (f' x) < M) -> forall x y eps , (real_0 < eps) -> abs x <= r -> abs y <= r -> dist (f x) (f y) <= (M + eps) * dist x y.
  Proof.
    intros.
    destruct (X eps) as [d [D1 D2]];auto.
    destruct (interval_div_by_d x y d) as [n N];auto.
    apply (real_le_le_le _ (Nreal N * eps)).
    revert dependent x.
    induction n.
    intros.
    replace y with x.
    admit.
    admit.
    intros.
    destruct (interval_subdivision_step _ _ _ _ D1 N) as [x' [P1 P2]].
    apply (real_le_le_le _ _ _ (dist_tri _ (f x') _)).
    apply (real_le_le_le _ (eps*dist x y + )
  Lemma lbc f f' r M :  constructive_derivative f f' r -> (forall x, abs x <= r -> abs (f' x) < M) -> forall x y, abs x <= r -> abs y <= r -> dist (f x) (f y) < M * dist x y.
  Proof.
    intros.
    destruct (X real_1).
  admit.
  
  Admitted.
  Definition derivative_sum f1 f2 g1 g2 r : constructive_derivative f1 g1 r -> constructive_derivative f2 g2 r -> constructive_derivative (fun x => (f1 x + f2 x)) (fun x => (g1 x + g2 x)) r.
  Proof.
    intros H1 H2 eps epsgt0.
    assert (eps / real_2_neq_0 > real_0) by (apply real_half_gt_zero;auto).
    destruct (H1 (eps / real_2_neq_0)) as [d1 [d1gt0 D1]];auto.
    destruct (H2 (eps / real_2_neq_0)) as [d2 [d2gt0 D2]];auto.
    exists (Minmax.real_min d1 d2);split;[destruct (Minmax.real_min_cand d1 d2) as [-> | ->];auto|].
    intros.
    replace (f1 y + f2 y - (f1 x + f2 x) - (g1 x + g2 x)*(y - x)) with ((f1 y - f1 x -(g1 x)*(y-x)) + (f2 y - f2 x - (g2 x)*(y-x))) by ring.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    replace (eps * abs (y-x)) with (eps /real_2_neq_0 * abs (y-x) + eps / real_2_neq_0 * abs (y-x)) by (rewrite <-(half_twice eps);ring_simplify;rewrite half_twice; ring).
    apply real_le_le_plus_le; [apply D1 | apply D2];auto; apply (real_le_le_le _ _ _ H4); [apply Minmax.real_min_fst_le | apply Minmax.real_min_snd_le].
 Qed.
End ConstructiveDerivatives.
