Require Import Real.
Require Import ClassicalMonads ClassicalPartiality ClassicalPartialReals ClassicalContinuity ClassicalContinuousPartialRealFunctions.
Require Import RealAssumption.
Require Import Minmax.

Require Import Psatz.
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

  Lemma interval_div_by_d x y d : (d > real_0) ->  exists (n : nat) (d' : Real), (real_0 <= d') /\ d' <= d /\ dist x y = Nreal n*d+d'.
  Proof.
    destruct (real_total_order (dist x y) d) as [T1 | [T2 | T3]];intros.
    - exists 0; exists (dist x y).
      split; [apply dist_pos | split].
      apply real_lt_le;auto.
      simpl;ring.
    - exists 0; exists (dist x y).
      split;simpl;[apply dist_pos | split; [apply real_eq_le;auto | ring]].
    - assert (exists n, Nreal n * d <= dist x y /\ Nreal (S n) * d >= dist x y) as [n [N1 N2]].
      {
        admit.
      }
      exists n.
      exists (dist x y - Nreal n * d).
      split;[|split]; try ring.
      add_both_side_by  (Nreal n * d).
      apply N1.
      add_both_side_by  (Nreal n * d).
      replace (Nreal n * d + d) with (Nreal (S n) * d) by (simpl;ring).
      apply N2.
  Admitted.

  Lemma Nreal_nonneg n : real_0 <= Nreal n.
  Proof.
    destruct n;[apply real_eq_le;simpl;auto|].
    apply real_lt_le.
    apply Nreal_pos.
    lia.
  Qed.

  Lemma interval_subdivision_step_lt x y d d' n : x <= y -> (d > real_0) -> (real_0 <= d') -> (d' <= d) -> (dist x y = (Nreal (S n) * d) + d')-> exists x1, dist x x1 <= d /\ dist x1 y = Nreal n * d + d' /\ abs x1 <= abs y.
  Proof.
    intros.
    exists (x+d).
    split; [|split].
    - unfold dist.
      replace (x - (x+d)) with (-d) by ring.
      rewrite <-abs_symm,abs_pos_id; [apply real_le_triv|apply real_lt_le;auto].
    - rewrite dist_symm.
      rewrite (le_metric _ _ H) in H3.
      unfold dist.
      replace (y - (x+d)) with ((y - x) - d) by ring.
      rewrite H3.
      rewrite abs_pos_id; [simpl;ring|].
      simpl.
      apply (real_le_le_le _ (Nreal n * d)).
      apply real_le_pos_mult_pos_pos;[apply Nreal_nonneg|apply real_lt_le];auto.
      add_both_side_by (- Nreal n * d).
      apply H1.
  - 
  Qed.

  Lemma interval_subdivision_step x y d d' n : (d > real_0) -> (real_0 <= d') -> (d' <= d) -> (dist x y = (Nreal (S n) * d) + d')-> exists x1, dist x x1 <= d /\ dist x1 y = Nreal n * d + d'.
  Proof.
  Admitted.

  Lemma lbc_approx f f' r M :  constructive_derivative f f' r -> (forall x, abs x <= r -> abs (f' x) <= M) -> forall x y eps , (real_0 < eps) -> abs x <= r -> abs y <= r -> dist (f x) (f y) <= (eps+M) * dist x y.
  Proof.
    intros.
    destruct (X eps) as [d [D1 D2]];auto.
    destruct (interval_div_by_d x y d) as [n [d' [N1 [N2 N3]]]];auto.
    rewrite N3.
    revert dependent x.
    induction n.
    - intros.
      simpl;ring_simplify.
      simpl in N3.
      ring_simplify in N3.
      apply (real_le_le_le _ (eps * dist x y + M * dist x y)).
      rewrite dist_symm in N3.
      rewrite dist_symm, (dist_symm x).
      unfold dist.
      replace (f y - f x) with ((f y - f x - f' x * (y-x)) + f' x * (y-x)) by ring.
      apply (real_le_le_le _ _ _ (abs_tri _ _)).
      apply real_le_le_plus_le;auto.
      apply D2;try rewrite dist_symm;auto.
      apply (real_le_le_le _ d');auto.
      rewrite N3;apply real_le_triv.
      rewrite abs_mult.
      rewrite real_mult_comm, (real_mult_comm M).
      apply real_le_mult_pos_le; [apply abs_pos|auto].
      apply real_le_le_plus_le;apply real_le_mult_pos_le; [apply real_lt_le |apply real_eq_le | | apply real_eq_le];auto.
      apply (real_le_le_le _ _ _ (abs_pos (f' x)));auto.
    - intros.
      destruct (interval_subdivision_step _ _ _ _ _ D1 N1 N2 N3) as [x' [P1 P2]].
      apply (real_le_le_le _ _ _ (dist_tri _ (f x') _)).
      replace ((eps+M)*(Nreal (S n) * d + d')) with ((eps*d + M*d) + (eps+M)*(Nreal n *d + d')) by (simpl;ring).
      apply real_le_le_plus_le.
      rewrite dist_symm.
      unfold dist.
      replace (f x' - f x) with ((f x' - f x - f' x * (x'-x)) + f' x * (x'-x)) by ring.
      apply (real_le_le_le _ _ _ (abs_tri _ _)).
      apply real_le_le_plus_le;auto.
      apply (real_le_le_le _ (eps * abs (x'-x))); [| apply real_le_mult_pos_le; [apply real_lt_le |rewrite dist_symm in P1]];auto.
      apply D2;auto.
      admit.
      admit.
      apply IHn;auto.
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
