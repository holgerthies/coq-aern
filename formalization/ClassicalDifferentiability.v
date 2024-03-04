Require Import Real.
Require Import ClassicalMonads ClassicalPartiality ClassicalPartialReals ClassicalContinuity ClassicalContinuousPartialRealFunctions.
Require Import RealAssumption.
Require Import Minmax.

Require Import Psatz.
Open Scope Real_scope.

Section toMove.

  Lemma real_div_gt_0 x y (yd : y <> real_0) : x > real_0 -> y > real_0 -> (x / yd > real_0).
  Proof.
    intros.
    unfold real_div.
    rewrite real_mult_comm.
    apply (real_lt_mult_pos_cancel y);auto.
    rewrite real_mult_assoc, (real_mult_comm x), <-real_mult_assoc, real_mult_inv.
    ring_simplify;auto.
  Qed.
  Lemma dist_abs x y : dist x y = abs (y - x).
  Proof.
    rewrite dist_symm;auto.
  Qed.
  Lemma abs_plus_one_div_inv x y: (y > real_0) -> (y / (real_gt_neq _ _ (abs_plus_1_gt_0 x))) * abs x <= y. 
  Proof.
    intros H.
    apply (real_le_le_le _ ((y / (real_gt_neq _ _ (abs_plus_1_gt_0 x))) * (abs x + real_1))).  
    - apply real_le_mult_pos_le.
      apply real_lt_le.
      apply real_div_gt_0;try apply abs_plus_1_gt_0;auto.
      add_both_side_by (- (abs x)).
      apply real_lt_le.
      apply real_1_gt_0.
  - unfold real_div.
    rewrite real_mult_assoc, real_mult_inv.
    apply real_eq_le; ring.
  Qed.

  Lemma half_twice_mult x y : x * y = x / real_2_neq_0 * y + x / real_2_neq_0 * y.
  Proof.
    rewrite <-(half_twice x);ring_simplify;rewrite half_twice; ring.    
  Qed.

  Lemma Nreal_nonneg n : real_0 <= Nreal n.
  Proof.
    destruct n;[apply real_eq_le;simpl;auto|].
    apply real_lt_le.
    apply Nreal_pos.
    lia.
  Qed.
End toMove.

Section ClassicalDerivatives.
  Definition I r := {x : Real | abs x <= r}.
  Coercion I_to_real r := fun x : (I r) => proj1_sig x.


  Definition uniformly_continuous (f: Real -> pc Real) r := forall eps, eps > 0 -> exists d : Real, d > real_0 /\ forall (x y : (I r)), dist x y <= d -> (pc_dist (f x) (f y) <= pc_unit _ eps)%pcreal.

  Definition uniform_derivative (f: ^Real -> pc ^Real) (f': ^Real -> pc ^Real) r := (forall (x : (I r)), defined (f x) /\ defined (f' x)) /\  forall eps, eps > real_0 -> exists delta, delta > real_0 /\ forall (x y : (I r)), dist x y <= delta -> (pc_abs ((f y) - (f x) - (f' x) * (pc_unit _ (y-x)%Real))%pcreal <= (pc_unit _ (eps * abs(y-x))))%pcreal.

  Definition bounded_by (f : ^Real -> pc ^Real) M r := (forall (x : (I r)), (pc_abs (f x) <= (pc_unit _ M))%pcreal).


  Lemma pc_dist_bound {x x' y y' z} : defined_to x x' -> defined_to y y' ->  (pc_dist x y <= pc_unit _ z)%pcreal <-> dist x' y' <= z.
  Proof.
    intros.
    split.
   Admitted.
  Lemma lbc_helper (f f' : ^Real -> pc ^Real) r M : uniform_derivative f f' r -> bounded_by f' M r  ->forall eps, eps > real_0 -> exists d, d > real_0 /\ (forall (x y : (I r)), (dist x y <= d)%Real -> (pc_dist (f x) (f y) <= pc_unit _ (eps*d + M *d)))%pcreal.
  Proof.
    intros.
    destruct  H as [X1 X2].
    destruct (X2 eps) as [d [D1 D2]];auto.
    exists d;split;auto.
    intros.
    destruct (X1 x) as [[fx Fx] _].
    destruct (X1 y) as [[fy Fy] _].
    apply (pc_dist_bound Fx Fy).
    rewrite dist_symm.
    unfold dist.
    destruct (X1 x) as [_ [fx' P]].
    replace (fy - fx) with ((fy - fx - fx' * (y -x)) + fx' * (y - x)) by ring.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    apply real_le_le_plus_le.
    - apply (real_le_le_le _ (eps * abs (y-x)) _ ).
      specialize (D2 _ _ H).
      apply (pc_dist_bound in D2.
      apply 
      [apply D2;auto|].
      apply real_le_mult_pos_le;auto.
      apply real_lt_le; auto.
      rewrite dist_symm in H3;auto.
   - rewrite abs_mult.
     apply (real_le_le_le _ (abs (fx') * d)).
     apply real_le_mult_pos_le; [apply abs_pos |rewrite dist_symm in H3;auto].
     rewrite !(real_mult_comm _ d).
     apply real_le_mult_pos_le;[apply real_lt_le|];auto.
     apply (H0 x);auto.
  Qed.

  
  Lemma min_upperbound_exists x : (real_0 < x) -> exists (n: nat), (Nreal n <= x) /\ (x <= Nreal (S n)). 
  Proof.
  Admitted.
  
  Lemma interval_div_by_d x y d : (d > real_0) ->  exists (n : nat) (d' : Real), (real_0 <= d') /\ d' <= d /\ dist x y = Nreal n*d+d'.
  Proof.
    destruct (real_total_order (dist x y) d) as [T1 | [T2 | T3]];intros.
    - exists 0%nat; exists (dist x y).
      split; [apply dist_pos | split].
      apply real_lt_le;auto.
      simpl;ring.
    - exists 0%nat; exists (dist x y).
      split;simpl;[apply dist_pos | split; [apply real_eq_le;auto | ring]].
    -
      assert (dist x y / (dg0 H) > real_0) by (apply real_lt_mult_pos_move_rr;apply (real_lt_lt_lt _ d);ring_simplify;auto).
      assert (exists n, Nreal n * d <= dist x y /\ Nreal (S n) * d >= dist x y) as [n [N1 N2]].
      {
        destruct (min_upperbound_exists _ H0) as [n [N1 N2]].
        exists n.
        split.
        apply (real_le_mult_pos_cancel (/ dg0 H));[apply real_pos_inv_pos|];auto.
        rewrite real_mult_assoc, (real_mult_comm d),real_mult_inv.
        ring_simplify;auto.
        apply (real_le_mult_pos_cancel (/ dg0 H));[apply real_pos_inv_pos|];auto.
        rewrite real_mult_assoc, (real_mult_comm d),real_mult_inv.
        ring_simplify;auto.
      }
      exists n.
      exists (dist x y - Nreal n * d).
      split;[|split]; try ring.
      add_both_side_by  (Nreal n * d).
      apply N1.
      add_both_side_by  (Nreal n * d).
      replace (Nreal n * d + d) with (Nreal (S n) * d) by (simpl;ring).
      apply N2.
  Qed.


  Lemma interval_subdivision_step_lt x y d d' n : x <= y -> (d > real_0) -> (real_0 <= d') -> (d' <= d) -> (dist x y = (Nreal (S n) * d) + d')-> exists x1, dist x x1 <= d /\ dist x1 y = Nreal n * d + d' /\ x1 <= y.
  Proof.
    intros.
    rewrite (le_metric _ _ H) in H3.
    exists (x+d).
    split; [|split].
    - unfold dist.
      replace (x - (x+d)) with (-d) by ring.
      rewrite <-abs_symm,abs_pos_id; [apply real_le_triv|apply real_lt_le;auto].
    - rewrite dist_symm.
      unfold dist.
      replace (y - (x+d)) with ((y - x) - d) by ring.
      rewrite H3.
      rewrite abs_pos_id; [simpl;ring|].
      simpl.
      apply (real_le_le_le _ (Nreal n * d)).
      apply real_le_pos_mult_pos_pos;[apply Nreal_nonneg|apply real_lt_le];auto.
      add_both_side_by (- Nreal n * d).
      apply H1.
    - replace y with (x + (y - x)) by ring.
      rewrite H3.
      apply real_le_plus_le.
      apply (real_le_le_le _ (Nreal (S n) *d)).
      simpl;add_both_side_by (-d);apply real_le_pos_mult_pos_pos;[apply real_lt_le;auto|apply Nreal_nonneg].
      add_both_side_by (-Nreal (S n) * d);auto.
  Qed.

  Lemma real_le_or_ge : forall x y, (x <= y) \/ (y <= x).
  Proof.
    intros.
    destruct (real_total_order x y) as [T | [T | T]].
    left;apply real_lt_le;auto.
    left;apply real_eq_le;auto.
    right;apply real_lt_le;auto.
  Qed.

  Lemma interval_subdivision_step x y d d' n : (d > real_0) -> (real_0 <= d') -> (d' <= d) -> (dist x y = (Nreal (S n) * d) + d')-> exists x1, dist x x1 <= d /\ dist x1 y = Nreal n * d + d' /\ (abs x1 <= abs x \/ abs x1 <= abs y).
  Proof.
    destruct (real_le_or_ge x y) as [T | T].
    intros.
    destruct (interval_subdivision_step_lt x y d d' n T H H0 H1 H2) as [x1 [P1 [P2 P3]]].
    exists x1.
    split;[|split];auto.
    destruct (real_total_order (abs x) (abs y)).
    right.
  Admitted.  


  Lemma lbc_approx f f' r M :  uniform_derivative f f' r -> bounded_by f' M r -> forall (x y : (I r)) eps fx fy , defined_to (f x) fx -> defined_to (f y) fy -> (real_0 < eps) -> dist (fx) (fy) <= (M+eps) * dist x y.
  Proof.
    intros.
    rewrite real_plus_comm.
    destruct H as [X0 X].
    destruct (X eps) as [d [D1 D2]];auto.
    destruct (interval_div_by_d x y d) as [n [d' [N1 [N2 N3]]]];auto.
    rewrite N3.
    revert dependent fx; revert dependent x.
    induction n.
    - intros.
      simpl;ring_simplify.
      simpl in N3.
      ring_simplify in N3.
      destruct (X0 x) as [_ [f'x P]].
      apply (real_le_le_le _ (eps * dist x y + M * dist x y)).
      rewrite dist_symm in N3.
      rewrite dist_symm, (dist_symm x).
      unfold dist.
      replace (fy - fx) with ((fy - fx - f'x * (y-x)) + f'x * (y-x)) by ring.
      apply (real_le_le_le _ _ _ (abs_tri _ _)).
      apply real_le_le_plus_le;auto.
      rewrite abs_mult.
      rewrite real_mult_comm, (real_mult_comm M).
      apply real_le_mult_pos_le; [apply abs_pos|auto].
      apply (H0 x);auto.
      apply real_le_le_plus_le;apply real_le_mult_pos_le; [apply real_lt_le |apply real_eq_le | | apply real_eq_le];auto.
      apply (real_le_le_le _ _ _ (abs_pos (f'x)));auto.
      apply (H0 x);auto.
    - intros.
      destruct (X0 x) as [_ [f'x P]].
      destruct (interval_subdivision_step _ _ _ _ _ D1 N1 N2 N3) as [x' [P1 [P2 P3]]].
      assert (abs x' <= r).
      destruct P3; apply (real_le_le_le _ _ _ H);destruct x; destruct y; auto.
      assert { x'' :  (I r) | (proj1_sig x'') = x'} as [x'' Px] by (exists (exist _ x' H);auto).
      destruct (X0 x'') as [[fx' P'] _].
      apply (real_le_le_le _ _ _ (dist_tri _ (fx') _)).
      replace ((eps+M)*(Nreal (S n) * d + d')) with ((eps*d + M*d) + (eps+M)*(Nreal n *d + d')) by (simpl;ring).
      apply real_le_le_plus_le.
      rewrite dist_symm.
      unfold dist.
      replace (fx' - fx) with ((fx' - fx - f'x * (x''-x)) + f'x * (x''-x)) by ring.
      apply (real_le_le_le _ _ _ (abs_tri _ _)).
      apply real_le_le_plus_le;auto.
      apply (real_le_le_le _ (eps * abs (x''-x))); [| apply real_le_mult_pos_le; [apply real_lt_le |rewrite dist_symm in P1]];auto; destruct x'';simpl in *;rewrite Px;auto.
      destruct x'';simpl in *;rewrite Px;auto.
      rewrite abs_mult.
      apply (real_le_le_le _ (M * abs (x' -x))).
      rewrite real_mult_comm, (real_mult_comm M).
      apply real_le_mult_pos_le; [apply abs_pos | auto].
      rewrite dist_symm in P1.
      apply (H0 x);auto.
      apply real_le_mult_pos_le;auto.
      apply (real_le_le_le _ _ _ (abs_pos (f'x)));auto.
      apply (H0 x);auto.
      rewrite dist_symm in P1;auto.
      apply (IHn x'');destruct x'';simpl in *; rewrite Px in *;auto.
  Qed.

  Lemma lim_zero_eq_zero x : (forall eps, eps > real_0 -> abs x <= eps) -> x = real_0.
  Proof.
    intros.
    apply abs_zero.
    destruct (real_total_order (abs x) real_0) as [T | [T | T]];auto.
    apply real_gt_nle in T;contradict T;apply abs_pos.
    destruct (real_Archimedean _ T).
    apply real_gt_nle in H0.
    contradict H0.
    apply H.
    apply prec_pos.
  Qed.


  Lemma lim_le_le x y : (forall eps, eps > real_0 -> x <= y + eps) -> x <= y.
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
  Lemma lim_le_le_mult x y z : z >= real_0 -> (forall eps, eps > real_0 -> x <= (y + eps)*z) -> x <= y*z.
  Proof.
    intros.
    destruct H.
    apply lim_le_le.
    intros.
    assert (eps / dg0 H > real_0) by (apply real_lt_mult_pos_move_rl;ring_simplify;auto).
    apply (real_le_le_le _ _ _ (H0 _ H2)).
    unfold real_div;ring_simplify; rewrite real_mult_assoc, real_mult_inv.
    apply real_eq_le; ring.
    apply (real_le_le_le _ _ _ (H0 _ real_1_gt_0)).
    rewrite <-H.
    apply real_eq_le;ring.
  Qed.

  Lemma lbc f f' r M :  uniform_derivative f f' r -> bounded_by f' M r -> forall (x y : (I r)) fx fy, defined_to (f x) fx -> defined_to (f y) fy -> dist (fx) (fy) <= M * dist x y.
  Proof.
    intros.
    apply lim_le_le_mult; [apply dist_pos|].
    intros.
    apply (lbc_approx _ _ _ _ H H0 x y);auto.
  Qed.
  
    
End ClassicalDerivatives.
Section Operations.
  Lemma sum_defined x y : defined x -> defined y -> defined (x + y)%pcreal.
  Proof.
    intros.
    destruct H, H0.
    exists (x0+x1).
    apply pc_lift2_iff.
    exists x0; exists x1;auto.
  Qed.

  Lemma product_defined x y : defined x -> defined y -> defined (x * y)%pcreal.
  Proof.
    intros.
    destruct H, H0.
    exists (x0*x1).
    apply pc_lift2_iff.
    exists x0; exists x1;auto.
  Qed.

  Lemma unit_defined (x : ^Real) : defined (pc_unit _ x).
  Proof.
    exists x;unfold defined_to; auto.
  Qed.
  Definition derivative_sum f1 f2 g1 g2 r : uniform_derivative f1 g1 r -> uniform_derivative f2 g2 r -> uniform_derivative (fun x => (f1 x + f2 x)%pcreal) (fun x => (g1 x + g2 x)%pcreal) r.
  Proof.
    intros [H1 H1'] [H2 H2'].
    split; [intros; split;destruct (H1 x);destruct (H2 x); apply sum_defined;auto|].
    intros eps epsgt0.
    assert (eps / real_2_neq_0 > real_0) by (apply real_half_gt_zero;auto).
    destruct (H1' (eps / real_2_neq_0)) as [d1 [d1gt0 D1]];auto.
    destruct (H2' (eps / real_2_neq_0)) as [d2 [d2gt0 D2]];auto.
    exists (Minmax.real_min d1 d2);split;[destruct (Minmax.real_min_cand d1 d2) as [-> | ->];auto|].
    intros.
    apply pc_lift2_iff in H0,H3,H4.
    destruct H0 as [f1x [f2x [F0 [F0' ->]]]].
    destruct H3 as [f1y [f2y [F1 [F1' ->]]]].
    destruct H4 as [g1x [g2x [F2 [F2' ->]]]].
    replace (f1y + f2y - (f1x + f2x) - (g1x + g2x)*(y - x)) with ((f1y - f1x -g1x*(y-x)) + (f2y - f2x - g2x*(y-x))) by ring.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    replace (eps * abs (y-x)) with (eps /real_2_neq_0 * abs (y-x) + eps / real_2_neq_0 * abs (y-x)) by (rewrite <-(half_twice eps);ring_simplify;rewrite half_twice; ring).
    apply real_le_le_plus_le;auto. 
 Qed.
  Lemma derivative_sproduct a f g r : uniform_derivative f g r -> uniform_derivative (fun x => (pc_unit _ a * f x)%pcreal) (fun x => (pc_unit _ a * g x)%pcreal) r.
  Proof.
    intros [H1 H1'].
    split; [intros; split;destruct (H1 x);apply product_defined;auto;apply unit_defined|].
    intros eps epsgt0.
    destruct (H1' (eps / (real_gt_neq _  _ (abs_plus_1_gt_0 a)))) as [d [dgt0 D]];[apply real_div_gt_0;try apply abs_plus_1_gt_0;auto |].
    exists d;split;auto.
    intros x y afx afy af'x H2 H3 H4.
    apply pc_lift2_iff in H2,H3,H4.
    destruct H2 as [a1 [fx [F0 [F0' ->]]]]; apply pc_unit_mono in F0; rewrite <-F0.
    destruct H3 as [a2 [fy [F1 [F1' ->]]]]; apply pc_unit_mono in F1; rewrite <-F1.
    destruct H4 as [a3 [f'x [F2 [F2' ->]]]]; apply pc_unit_mono in F2; rewrite <-F2.
    replace (a*fy - a * fx - a * f'x * (y-x)) with (a * (fy - fx - f'x * (y- x))) by ring.
    rewrite abs_mult.
    apply (real_le_le_le _ (abs a * ((eps / (real_gt_neq _  _ (abs_plus_1_gt_0 a))) * abs (y - x)))).
    apply real_le_mult_pos_le; [apply abs_pos | apply D];auto.
    rewrite <-real_mult_assoc.
    rewrite !(real_mult_comm _( abs (y - x))).
    apply real_le_mult_pos_le; try apply abs_pos.
    rewrite (real_mult_comm (abs a)). 
    apply abs_plus_one_div_inv;auto.
  Defined.

  Lemma derivative_bounded f g r: uniform_derivative f g r -> exists M, bounded_by g M r.
  Admitted.

  Lemma uniform_derivative_uniform_continuous f g r : uniform_derivative f g r -> uniformly_continuous f r.
  Admitted.

  Lemma derivative_product f1 f2 g1 g2 r : uniform_derivative f1 g1 r -> uniform_derivative f2 g2 r -> uniform_derivative (fun x => (f1 x * f2 x)%pcreal) (fun x => ((f1 x * g2 x) + (g1 x * f2 x))%pcreal) r.
  Proof.
    intros H1 H2.
    destruct (derivative_bounded _ _ _ H2) as [Mg g2M].
    assert (exists Mf1, bounded_by f1 Mf1 r) as [Mf1 f1M].
    admit.
    assert (exists Mf2, bounded_by f2 Mf2 r) as [Mf2 f2M].
    admit.
    split; [intros; split;destruct (proj1 H1 x);destruct (proj1 H2 x); try apply sum_defined;try apply product_defined;auto|].
    intros eps epsgt0.
    remember (eps / real_2_neq_0  / (real_gt_neq _  _ (abs_plus_1_gt_0 Mg))) as eps0'.
    remember (Minmax.real_min real_1 eps0') as eps0.
    assert (eps0 > real_0) as eps0gt0.
    {
      rewrite Heqeps0, Heqeps0'.
      destruct (Minmax.real_min_cand real_1 (eps / real_2_neq_0  / (real_gt_neq _  _ (abs_plus_1_gt_0 Mg)))) as [-> | ->];try apply real_1_gt_0.
     apply real_div_gt_0; [apply real_half_gt_zero|apply abs_plus_1_gt_0].
     exact epsgt0.
    }
    destruct (uniform_derivative_uniform_continuous _ _ _ H1 eps0) as [d0 [d0gt0 D0]];auto.
    remember ((eps / real_2_neq_0 / real_2_neq_0) / (real_gt_neq _ _ (abs_plus_1_gt_0 Mf2))) as eps1.
    assert (eps1 > real_0) as eps1gt0.
    {
      rewrite Heqeps1.
      apply real_div_gt_0; [|apply abs_plus_1_gt_0];auto.     
      apply real_half_gt_zero.
      apply real_half_gt_zero;auto.
    }
    destruct (proj2 H1 eps1) as [d1 [d1gt0 D1]]; auto.
    remember ((eps / real_2_neq_0 / real_2_neq_0) / (real_gt_neq _ _ (abs_plus_1_gt_0 Mf1))) as eps2.
    assert (eps2 > real_0) as eps2gt0.
    {
      rewrite Heqeps2.
      apply real_div_gt_0; try apply abs_plus_1_gt_0.
      apply real_half_gt_zero.
      apply real_half_gt_zero;auto.
    }
    destruct (proj2 H2 eps2) as [d2 [d2gt0 D2]]; [rewrite Heqeps2;apply real_div_gt_0; [apply real_half_gt_zero|apply abs_plus_1_gt_0];apply real_half_gt_zero;auto|].
    assert {d | d > real_0 /\ d <= d0 /\ d <= d1 /\ d <= d2} as [d [dgt0 [dd0 [dd1 dd2]]]].
    {
      exists (Minmax.real_min d0 (Minmax.real_min d1 d2)).
      split; [destruct (Minmax.real_min_cand d0 (Minmax.real_min d1 d2)) as [-> | ->];[|destruct (Minmax.real_min_cand d1 d2) as [-> | ->]]|];auto.
      split; [apply Minmax.real_min_fst_le|split]; apply (real_le_le_le _ _ _ (Minmax.real_min_snd_le _ _)).
      apply Minmax.real_min_fst_le.
      apply Minmax.real_min_snd_le.
    }
    exists d.
    split;auto.
    intros.
    apply pc_lift2_iff in H,H0,H3.
    destruct H as [f1x [f2x [F0 [F0' ->]]]].
    destruct H0 as [f1y [f2y [F1 [F1' ->]]]].
    destruct H3 as [fg1x [gf2x [F2 [F2' ->]]]].
    apply pc_lift2_iff in F2, F2'.
    destruct F2 as [f1x' [g2x [G1 [G1' ->]]]].
    destruct F2' as [g1x [f2x' [G2 [G2' ->]]]].
    replace f1x' with f1x by (apply pc_unit_mono;rewrite <-G1, <-F0;auto).
    replace f2x' with f2x by (apply pc_unit_mono;rewrite <-G2', <-F0';auto).
    replace (f1y * f2y - f1x * f2x - (f1x * g2x + g1x * f2x) * (y - x)) with ((f1y - f1x)*(g2x)*(y-x) + (f1y * (f2y - f2x - g2x * (y-x)) + f2x * (f1y - f1x - g1x * (y-x)))) by ring.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    rewrite (half_twice_mult eps _).
    apply real_le_le_plus_le; [|rewrite (half_twice_mult (eps / real_2_neq_0));apply (real_le_le_le _ _ _ (abs_tri _ _));apply real_le_le_plus_le];rewrite !abs_mult.
    - rewrite !(real_mult_comm _ (abs (y-x))).
      apply real_le_mult_pos_le; [apply abs_pos |].
      apply (real_le_le_le _ (eps0 * abs (g2x))).
      rewrite !(real_mult_comm _ (abs (g2x))); apply real_le_mult_pos_le;[apply abs_pos |].
      rewrite <-dist_abs.
      specialize (D0 x y).
      apply D0.
      apply (real_le_le_le _ _ _ H dd0).
      rewrite Heqeps0.
      apply (real_le_le_le _ (eps0' * abs (g2 x))); [rewrite !(real_mult_comm _ (abs _));apply real_le_mult_pos_le;try apply abs_pos;apply Minmax.real_min_snd_le | ].
      rewrite Heqeps0'.
      apply abs_plus_one_div_inv; apply real_half_gt_zero;auto.
   -  apply (real_le_le_le _ (abs (f1 y) * (eps2 * abs (y - x)))).
      apply real_le_mult_pos_le; [apply abs_pos | apply D2;apply (real_le_le_le _ _ _ H dd2)].
      rewrite !(real_mult_comm _ (abs (y-x))), <-real_mult_assoc,(real_mult_comm _ (abs (y-x))), real_mult_assoc.
      apply real_le_mult_pos_le;try apply abs_pos.
      rewrite real_mult_comm.
      apply (real_le_le_le _ (eps2 *(abs (f1 x)+real_1))).
      apply real_le_mult_pos_le;[apply real_lt_le|];auto.
      apply dist_bound.
      apply (real_le_le_le _ eps0); [apply D0;apply (real_le_le_le _ _ _ H dd0)|].
      rewrite Heqeps0.
      apply Minmax.real_min_fst_le.
      rewrite Heqeps2.
      unfold real_div.
      rewrite !real_mult_assoc,real_mult_inv.
      apply real_eq_le;ring.
   -  apply (real_le_le_le _ (abs (f2 x) * (eps1 * abs (y - x)))). 
      apply real_le_mult_pos_le; try apply abs_pos.
      apply D1.
      apply (real_le_le_le _ _ _ H dd1).
      rewrite <-real_mult_assoc, !(real_mult_comm _ (abs (y- x))).
      apply real_le_mult_pos_le;try apply abs_pos.
      rewrite Heqeps1.
      rewrite real_mult_comm.
      apply abs_plus_one_div_inv.
      apply real_half_gt_zero.
      apply real_half_gt_zero;auto.
  Defined.
End Section.

(* Section ConstructiveDerivatives. *)
(*   Definition constructive_derivative (f: Real -> Real) (g : Real -> Real) r := forall eps, eps > real_0 -> {d : Real | d > real_0 /\ forall x y, abs x <= r -> abs y <= r -> dist x y <= d -> abs (f y - f x - g x * (y -x)) <= eps * abs(y-x) }. *)

(*   Lemma lbc_helper f f' r M : constructive_derivative f f' r -> (forall x, abs x <= r -> abs (f' x) <= M) ->forall eps, eps > real_0 -> {d | d > real_0 /\ forall x y, abs x <= r -> abs y <= r ->dist x y <= d -> dist (f x) (f y) <= eps*d + M *d}. *)
(*   Proof. *)
(*     intros. *)
(*     destruct (X eps) as [d [D1 D2]];auto. *)
(*     exists d;split;auto. *)
(*     intros. *)
(*     rewrite dist_symm. *)
(*     unfold dist. *)
(*     replace (f y - f x) with ((f y - f x - f' x * (y -x)) + f' x * (y - x)) by ring. *)
(*     apply (real_le_le_le _ _ _ (abs_tri _ _)). *)
(*     apply real_le_le_plus_le. *)
(*     - apply (real_le_le_le _ (eps * abs (y-x)) _ ); [apply D2;auto|]. *)
(*       apply real_le_mult_pos_le;auto. *)
(*       apply real_lt_le; auto. *)
(*       rewrite dist_symm in H3;auto. *)
(*    - rewrite abs_mult. *)
(*      apply (real_le_le_le _ (abs (f' x) * d)). *)
(*      apply real_le_mult_pos_le; [apply abs_pos |rewrite dist_symm in H3;auto]. *)
(*      rewrite !(real_mult_comm _ d). *)
(*      apply real_le_mult_pos_le;[apply real_lt_le|];auto. *)
(*   Qed. *)

(*   Lemma min_upperbound_exists x : (real_0 < x) -> exists (n: nat), (Nreal n <= x) /\ (x <= Nreal (S n)).  *)
(*   Proof. *)
(*   Admitted. *)
    
(*   Lemma interval_div_by_d x y d : (d > real_0) ->  exists (n : nat) (d' : Real), (real_0 <= d') /\ d' <= d /\ dist x y = Nreal n*d+d'. *)
(*   Proof. *)
(*     destruct (real_total_order (dist x y) d) as [T1 | [T2 | T3]];intros. *)
(*     - exists 0; exists (dist x y). *)
(*       split; [apply dist_pos | split]. *)
(*       apply real_lt_le;auto. *)
(*       simpl;ring. *)
(*     - exists 0; exists (dist x y). *)
(*       split;simpl;[apply dist_pos | split; [apply real_eq_le;auto | ring]]. *)
(*     - *)
(*       assert (dist x y / (dg0 H) > real_0) by (apply real_lt_mult_pos_move_rr;apply (real_lt_lt_lt _ d);ring_simplify;auto). *)
(*       assert (exists n, Nreal n * d <= dist x y /\ Nreal (S n) * d >= dist x y) as [n [N1 N2]]. *)
(*       { *)
(*         destruct (min_upperbound_exists _ H0) as [n [N1 N2]]. *)
(*         exists n. *)
(*         split. *)
(*         apply (real_le_mult_pos_cancel (/ dg0 H));[apply real_pos_inv_pos|];auto. *)
(*         rewrite real_mult_assoc, (real_mult_comm d),real_mult_inv. *)
(*         ring_simplify;auto. *)
(*         apply (real_le_mult_pos_cancel (/ dg0 H));[apply real_pos_inv_pos|];auto. *)
(*         rewrite real_mult_assoc, (real_mult_comm d),real_mult_inv. *)
(*         ring_simplify;auto. *)
(*       } *)
(*       exists n. *)
(*       exists (dist x y - Nreal n * d). *)
(*       split;[|split]; try ring. *)
(*       add_both_side_by  (Nreal n * d). *)
(*       apply N1. *)
(*       add_both_side_by  (Nreal n * d). *)
(*       replace (Nreal n * d + d) with (Nreal (S n) * d) by (simpl;ring). *)
(*       apply N2. *)
(*   Qed. *)


(*   Lemma interval_subdivision_step_lt x y d d' n : x <= y -> (d > real_0) -> (real_0 <= d') -> (d' <= d) -> (dist x y = (Nreal (S n) * d) + d')-> exists x1, dist x x1 <= d /\ dist x1 y = Nreal n * d + d' /\ x1 <= y. *)
(*   Proof. *)
(*     intros. *)
(*     rewrite (le_metric _ _ H) in H3. *)
(*     exists (x+d). *)
(*     split; [|split]. *)
(*     - unfold dist. *)
(*       replace (x - (x+d)) with (-d) by ring. *)
(*       rewrite <-abs_symm,abs_pos_id; [apply real_le_triv|apply real_lt_le;auto]. *)
(*     - rewrite dist_symm. *)
(*       unfold dist. *)
(*       replace (y - (x+d)) with ((y - x) - d) by ring. *)
(*       rewrite H3. *)
(*       rewrite abs_pos_id; [simpl;ring|]. *)
(*       simpl. *)
(*       apply (real_le_le_le _ (Nreal n * d)). *)
(*       apply real_le_pos_mult_pos_pos;[apply Nreal_nonneg|apply real_lt_le];auto. *)
(*       add_both_side_by (- Nreal n * d). *)
(*       apply H1. *)
(*     - replace y with (x + (y - x)) by ring. *)
(*       rewrite H3. *)
(*       apply real_le_plus_le. *)
(*       apply (real_le_le_le _ (Nreal (S n) *d)). *)
(*       simpl;add_both_side_by (-d);apply real_le_pos_mult_pos_pos;[apply real_lt_le;auto|apply Nreal_nonneg]. *)
(*       add_both_side_by (-Nreal (S n) * d);auto. *)
(*   Qed. *)

(*   Lemma real_le_or_ge : forall x y, (x <= y) \/ (y <= x). *)
(*   Proof. *)
(*     intros. *)
(*     destruct (real_total_order x y) as [T | [T | T]]. *)
(*     left;apply real_lt_le;auto. *)
(*     left;apply real_eq_le;auto. *)
(*     right;apply real_lt_le;auto. *)
(*   Qed. *)

(*   Lemma interval_subdivision_step x y d d' n : (d > real_0) -> (real_0 <= d') -> (d' <= d) -> (dist x y = (Nreal (S n) * d) + d')-> exists x1, dist x x1 <= d /\ dist x1 y = Nreal n * d + d' /\ (abs x1 <= abs x \/ abs x1 <= abs y). *)
(*   Proof. *)
(*     destruct (real_le_or_ge x y) as [T | T]. *)
(*     intros. *)
(*     destruct (interval_subdivision_step_lt x y d d' n T H H0 H1 H2) as [x1 [P1 [P2 P3]]]. *)
(*     exists x1. *)
(*     split;[|split];auto. *)
(*     destruct (real_total_order (abs x) (abs y)). *)
(*     right. *)
(*   Admitted.   *)

(*   Lemma lbc_approx f f' r M :  constructive_derivative f f' r -> (forall x, abs x <= r -> abs (f' x) <= M) -> forall x y eps , (real_0 < eps) -> abs x <= r -> abs y <= r -> dist (f x) (f y) <= (M+eps) * dist x y. *)
(*   Proof. *)
(*     intros. *)
(*     rewrite real_plus_comm. *)
(*     destruct (X eps) as [d [D1 D2]];auto. *)
(*     destruct (interval_div_by_d x y d) as [n [d' [N1 [N2 N3]]]];auto. *)
(*     rewrite N3. *)
(*     revert dependent x. *)
(*     induction n. *)
(*     - intros. *)
(*       simpl;ring_simplify. *)
(*       simpl in N3. *)
(*       ring_simplify in N3. *)
(*       apply (real_le_le_le _ (eps * dist x y + M * dist x y)). *)
(*       rewrite dist_symm in N3. *)
(*       rewrite dist_symm, (dist_symm x). *)
(*       unfold dist. *)
(*       replace (f y - f x) with ((f y - f x - f' x * (y-x)) + f' x * (y-x)) by ring. *)
(*       apply (real_le_le_le _ _ _ (abs_tri _ _)). *)
(*       apply real_le_le_plus_le;auto. *)
(*       apply D2;try rewrite dist_symm;auto. *)
(*       apply (real_le_le_le _ d');auto. *)
(*       rewrite N3;apply real_le_triv. *)
(*       rewrite abs_mult. *)
(*       rewrite real_mult_comm, (real_mult_comm M). *)
(*       apply real_le_mult_pos_le; [apply abs_pos|auto]. *)
(*       apply real_le_le_plus_le;apply real_le_mult_pos_le; [apply real_lt_le |apply real_eq_le | | apply real_eq_le];auto. *)
(*       apply (real_le_le_le _ _ _ (abs_pos (f' x)));auto. *)
(*     - intros. *)
(*       destruct (interval_subdivision_step _ _ _ _ _ D1 N1 N2 N3) as [x' [P1 [P2 P3]]]. *)
(*       assert (abs x' <= r). *)
(*       destruct P3;apply (real_le_le_le _ _ _ H3);auto. *)
(*       apply (real_le_le_le _ _ _ (dist_tri _ (f x') _)). *)
(*       replace ((eps+M)*(Nreal (S n) * d + d')) with ((eps*d + M*d) + (eps+M)*(Nreal n *d + d')) by (simpl;ring). *)
(*       apply real_le_le_plus_le; [|apply IHn;auto]. *)
(*       rewrite dist_symm. *)
(*       unfold dist. *)
(*       replace (f x' - f x) with ((f x' - f x - f' x * (x'-x)) + f' x * (x'-x)) by ring. *)
(*       apply (real_le_le_le _ _ _ (abs_tri _ _)). *)
(*       apply real_le_le_plus_le;auto. *)
(*       apply (real_le_le_le _ (eps * abs (x'-x))); [| apply real_le_mult_pos_le; [apply real_lt_le |rewrite dist_symm in P1]];auto. *)
(*       rewrite abs_mult. *)
(*       apply (real_le_le_le _ (M * abs (x' -x))). *)
(*       rewrite real_mult_comm, (real_mult_comm M). *)
(*       apply real_le_mult_pos_le; [apply abs_pos | auto]. *)
(*       rewrite dist_symm in P1. *)
(*       apply real_le_mult_pos_le;auto. *)
(*       apply (real_le_le_le _ _ _ (abs_pos (f' x)));auto. *)
(*   Qed. *)

(*   Lemma lim_zero_eq_zero x : (forall eps, eps > real_0 -> abs x <= eps) -> x = real_0. *)
(*   Proof. *)
(*     intros. *)
(*     apply abs_zero. *)
(*     destruct (real_total_order (abs x) real_0) as [T | [T | T]];auto. *)
(*     apply real_gt_nle in T;contradict T;apply abs_pos. *)
(*     destruct (real_Archimedean _ T). *)
(*     apply real_gt_nle in H0. *)
(*     contradict H0. *)
(*     apply H. *)
(*     apply prec_pos. *)
(*   Qed. *)


(*   Lemma lim_le_le x y : (forall eps, eps > real_0 -> x <= y + eps) -> x <= y. *)
(*   Proof. *)
(*     intros. *)
(*     destruct (real_total_order x y) as [T | [T |T]]; [apply real_lt_le| apply real_eq_le | ];auto. *)
(*     add_both_side_by (-y). *)
(*     apply real_eq_le. *)
(*     apply lim_zero_eq_zero. *)
(*     intros. *)
(*     rewrite abs_pos_id; add_both_side_by y; [|apply real_lt_le;auto]. *)
(*     apply H;auto. *)
(*   Qed. *)
(*   Lemma lim_le_le_mult x y z : z >= real_0 -> (forall eps, eps > real_0 -> x <= (y + eps)*z) -> x <= y*z. *)
(*   Proof. *)
(*     intros. *)
(*     destruct H. *)
(*     apply lim_le_le. *)
(*     intros. *)
(*     assert (eps / dg0 H > real_0) by (apply real_lt_mult_pos_move_rl;ring_simplify;auto). *)
(*     apply (real_le_le_le _ _ _ (H0 _ H2)). *)
(*     unfold real_div;ring_simplify; rewrite real_mult_assoc, real_mult_inv. *)
(*     apply real_eq_le; ring. *)
(*     apply (real_le_le_le _ _ _ (H0 _ real_1_gt_0)). *)
(*     rewrite <-H. *)
(*     apply real_eq_le;ring. *)
(*   Qed. *)

(*   Lemma lbc f f' r M :  constructive_derivative f f' r -> (forall x, abs x <= r -> abs (f' x) <= M) -> forall x y, abs x <= r -> abs y <= r -> dist (f x) (f y) <= M * dist x y. *)
(*   Proof. *)
(*     intros. *)
(*     apply lim_le_le_mult; [apply dist_pos|]. *)
(*     intros. *)
(*     apply (lbc_approx _ _ _ _ X H x y);auto. *)
(*   Qed. *)
  

(* End ConstructiveDerivatives. *)
