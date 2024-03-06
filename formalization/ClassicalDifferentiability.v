Require Import Real.
Require Import ClassicalMonads ClassicalPartiality ClassicalPartialReals ClassicalContinuity ClassicalContinuousPartialRealFunctions ClassicalTopology.
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
  Coercion I_to_real {r} := fun x : (I r) => proj1_sig x.

  Lemma real_to_I {x r} (H: abs x <= r) : (I r).
  Proof.
   exists x.
   exact H.
  Defined.

   Definition uniformly_continuous (f: Real -> pc Real) r := forall eps, eps > 0 -> exists d : Real, d > 0 /\ forall (x y : (I r)), dist x y <= d -> (pc_dist (f x) (f y) <= pc_unit _ eps)%pcreal.

  Lemma uniformly_continuous_unfold f r : uniformly_continuous f r <-> (forall x,abs x <= r -> defined (f x)) /\ forall eps, eps > 0 -> exists d : Real, d > 0 /\ (forall x y fx fy , abs x <= r -> abs y <= r -> dist x y <= d -> defined_to (f x) fx -> defined_to (f y) fy -> dist fx fy <= eps).
  Proof.
    split;intros.
    - split.
      + intros.
        destruct (H (abs x + real_1)) as [d [D H']]; [apply (abs_plus_1_gt_0 x)|].
        specialize (H' (real_to_I H0) (real_to_I H0)).
        destruct H' as [y [y' [Y _]]].
        simpl.
        rewrite dist_axiom_identity.
        apply real_lt_le; auto.
        simpl in Y.
        apply pc_lift2_iff in Y.
        destruct Y as [fx [_ [Fx _]]].
        exists fx;auto.
      + intros.
        destruct (H _ (H0)) as [d [D1 D2]].
        exists d;split;auto.
        intros.
        specialize (D2 (real_to_I H1) (real_to_I H2) H3).
        simpl in D2.
        destruct D2 as [eps' [d' [D21 [D22 D23]]]].
        apply pc_lift2_iff in D21.
        apply pc_unit_mono in D22.
        rewrite D22.
        destruct D21 as [fx' [fy' [P1 [P2 P3]]]].
        replace fx with fx' by (apply pc_unit_mono;rewrite <-H4, <-P1;auto).
        replace fy with fy' by (apply pc_unit_mono;rewrite <-H5, <-P2;auto).
        rewrite <-P3;auto.
  - intros eps epsgt0.
    destruct H.
    destruct (H0 _ epsgt0) as [d [D1 D2]].
    exists d;split;auto.
    intros.
    destruct x,y.
    simpl in H1.
    destruct (H x) as [fx FX];auto.
    destruct (H x0) as [fy FY];auto.
    exists (dist fx fy).
    exists eps.
    simpl.
    split;[|split;[apply pc_unit_mono;simpl;auto |apply (D2 x x0 fx fy);auto]].
    apply pc_lift2_iff.
    exists fx; exists fy;auto.
  Qed.

  Definition uniform_derivative (f: ^Real -> pc ^Real) (f': ^Real -> pc ^Real) r :=  forall eps, eps > real_0 -> exists delta, delta > real_0 /\ forall (x y : (I r)), dist x y <= delta -> (pc_abs ((f y) - (f x) - (f' x) * (pc_unit _ (y-x)%Real))%pcreal <= (pc_unit _ (eps * abs(y-x))))%pcreal.

  Lemma pc_abs_le x y : (pc_abs x <= y)%pcreal <-> (exists x' y', defined_to x x' /\ defined_to y y' /\ (abs x' <= y')).
  Proof.
    split.
    - intros.
      destruct H as [a' [y' [Da [Dy' H]]]].
      unfold pc_abs in Da.
      destruct (pc_case x).
      rewrite H0 in Da.
      rewrite pc_lift_bot in Da.
      apply pc_bot_defined_to_absurd in Da;contradict Da;auto.
      destruct H0 as [x' Dx'].
      exists x'; exists y'.
      split;[|split];auto.
      rewrite Dx' in Da.
      rewrite pc_unit_ntrans in Da.
      apply pc_unit_mono in Da.
      rewrite Da;auto.
   - intros.
     destruct H as [x' [y' [D1 [D2 H]]]].
     exists (abs x').
     exists y'.
     split; [|split];auto.
     unfold pc_abs.
     apply pc_unit_mono.
     rewrite <-(pc_unit_ntrans _ _ abs); simpl.
     rewrite D1;auto.
  Qed.

  Definition uniform_derivative_unfolded (f: ^Real -> pc ^Real) (f': ^Real -> pc ^Real) r := (forall (x : Real), abs x <= r -> defined (f x) /\ defined (f' x)) /\  forall eps, eps > real_0 -> exists delta, delta > real_0 /\ forall x y fx fy f'x, abs x <= r -> abs y <= r -> defined_to (f x) fx -> defined_to (f y) fy -> defined_to (f' x) f'x -> dist x y <= delta -> (abs (fy - fx - f'x * (y-x)) <= (eps * abs(y-x))).

  Lemma opp_involutive x : x = (- - x)%pcreal.
  Proof.
    destruct (pc_case x).
    rewrite H.
    rewrite !pc_lift_bot;auto.
    destruct H as [x' ->].
    rewrite !pc_unit_ntrans.
    replace (- - x') with x' by ring;auto.
  Qed.

  Lemma defined_to_opp x y : defined_to (-x)%pcreal y <-> defined_to x (-y).
  Proof.
    rewrite (opp_involutive x) at 2.
    split.
    intros.
    destruct (pc_case x).
    rewrite H0 in H.
    unfold defined_to in H.
    rewrite pc_lift_bot in H.
    contradict (pc_bot_defined_to_absurd H).
    destruct H0 as [x' ->].
    rewrite pc_unit_ntrans in H.
    rewrite pc_unit_ntrans.
    rewrite H.
    rewrite pc_unit_ntrans.
    unfold defined_to;auto.

    intros.
    replace y with (- (-y )) by ring.
    unfold defined_to.
    rewrite <-pc_unit_ntrans.
    rewrite <-H.
    apply opp_involutive.
  Qed.

  Lemma uniform_derivative_unfold  f f' r : uniform_derivative f f' r <-> uniform_derivative_unfolded f f' r.
  Proof.
  split.
  - intros.  
    split.
    + intros.
      destruct (H (abs x + real_1)) as [d [D H']]; [apply (abs_plus_1_gt_0 x)|].
      specialize (H' (real_to_I H0) (real_to_I H0)).
      rewrite pc_abs_le in H'.
      simpl in H'.
      destruct H' as [x' [_ [Dx' _]]]; [rewrite dist_axiom_identity;apply real_lt_le;auto|].
      apply pc_lift2_iff in Dx'.
      destruct Dx' as [x0 [y0 [Dx' [Dy _]]]].
      apply pc_lift2_iff in Dx'.
      destruct Dx' as [fx [_ [Fx _]]].
      rewrite <-pc_unit_ntrans2 in Dy.
      apply defined_to_opp in Dy.
      apply pc_lift2_iff in Dy.
       destruct Dy as [fy [_ [Fy _]]]. 
      split;[exists fx | exists fy];auto.
   + intros.
      destruct (H _ (H0)) as [d [D1 D2]].
      exists d;split;auto.
      intros.
      specialize (D2 (real_to_I H1) (real_to_I H2) H6).
      rewrite pc_abs_le in D2.
      simpl in D2.
      destruct D2 as [l [rt [L [R A]]]].
      rewrite H3, H4, H5 in L.
      rewrite !pc_unit_ntrans2 in L.
      rewrite !pc_unit_ntrans in L.
      rewrite !pc_unit_ntrans2 in L.
      assert  (l = fy - fx -f'x*(y-x)) as <-.
      {
        apply pc_unit_mono; rewrite <-L.
        auto.
      }
      replace (eps * abs(y-x)) with rt by (apply pc_unit_mono; rewrite <-R;auto).
      apply A.
  - intros [D H] eps epsgt0.
    destruct (H _ epsgt0) as [d [dP P]].
    exists d; split;auto.
    intros.
    destruct x as [x xP]; destruct y as [y yP].
    apply pc_abs_le.
    simpl.
    destruct (D x) as [[fx Fx] [f'x F'x]];auto.
    destruct (D y) as [[fy Fy] _];auto.
    exists (fy - fx -f'x*(y-x)); exists (eps * abs (y-x)).
    split; [|split;[apply pc_unit_mono|]];auto.
    apply pc_unit_mono.
    rewrite <-pc_unit_ntrans2.
    rewrite Fx, Fy, F'x.
    rewrite !pc_unit_ntrans2.
    rewrite !pc_unit_ntrans.
    rewrite !pc_unit_ntrans2;auto.
Qed.

    Definition bounded_by (f : ^Real -> pc ^Real) M r := (forall (x : (I r)), (pc_abs (f x) <= (pc_unit _ M))%pcreal).

  Lemma bounded_by_unfold f M r : bounded_by f M r <-> (forall x, abs x <= r -> defined (f x)) /\ (forall x fx, abs x <= r -> defined_to (f x) fx -> abs fx <= M).
  split.
  - intros.
    unfold bounded_by in H.
    split;intros;specialize (H (real_to_I H0));apply pc_abs_le in H;destruct H as [x' [y' [X [Y H]]]];simpl in X.
    exists x';auto.
    replace M with y' by (apply pc_unit_mono;auto).
    replace fx with x' by (apply pc_unit_mono;rewrite <-H1;auto).
    apply H.
  - intros [H1 H2] x.
    apply pc_abs_le.
    destruct x as [x P].
    destruct (H1 _ P) as [x' X].
    exists x';exists M.
    split;[|split;[apply pc_unit_mono|]];auto.
    apply (H2 x);auto.
  Qed.

  Lemma lbc_helper (f f' : ^Real -> pc ^Real) r M : uniform_derivative f f' r -> bounded_by f' M r  ->forall eps, eps > real_0 -> exists d, d > real_0 /\ (forall (x y : (I r)), (dist x y <= d)%Real -> (pc_dist (f x) (f y) <= pc_unit _ (eps*d + M *d)))%pcreal.
  Proof.
    intros.
    apply uniform_derivative_unfold in H.
    destruct H as [X1 X2].
    destruct (X2 eps) as [d [D1 D2]];auto.
    exists d;split;auto.
    intros.
    destruct x as [x X].
    destruct y as [y Y].
    destruct (X1 x) as [[fx Fx] _];auto.
    destruct (X1 y) as [[fy Fy] _];auto.
    simpl.
    exists (dist fx fy); exists (eps*d + M*d);split;[|split;[apply pc_unit_mono|];auto].
    apply pc_lift2_iff; exists fx; exists fy;split;[|split];auto.
    rewrite dist_symm.
    unfold dist.
    destruct (X1 x) as [_ [fx' P]];auto.
    replace (fy - fx) with ((fy - fx - fx' * (y -x)) + fx' * (y - x)) by ring.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    apply real_le_le_plus_le.
    - apply (real_le_le_le _ (eps * abs (y-x)) _ ).
      apply D2;auto.
      apply real_le_mult_pos_le;auto.
      apply real_lt_le; auto.
      simpl in H.
      rewrite dist_symm in H;auto.
   - rewrite abs_mult.
     apply (real_le_le_le _ (abs (fx') * d)).
     apply real_le_mult_pos_le; [apply abs_pos |rewrite dist_symm in H;auto].
     rewrite !(real_mult_comm _ d).
     apply real_le_mult_pos_le;[apply real_lt_le|];auto.
     rewrite (bounded_by_unfold f' M r) in H0.
     destruct H0 as [_ H0].
     apply (H0 x fx' );auto.
  Qed.

  
Lemma min_upperbound_exists x : (real_0 < x) -> exists (n: nat), (Nreal n <= x) /\ (x <= Nreal (S n)).
  Proof.
    intros o.
    assert (exists n, x <= Nreal (S n)).
    pose proof (nat_bound_above _ o) as [n p].
    exists n.
    assert (Nreal n < Nreal (S n)).
    apply Nreal_strict_monotone.
    auto.
    left.
    apply (real_lt_lt_lt _ _ _ p H).
    pose proof (dec_inh_nat_subset_has_unique_least_element (fun n => x <= Nreal (S n)) (fun _ => lem _) H).
    destruct H0 as [n [[p q] r]].
    exists n.
    split; auto.
    destruct (lem (Nreal n <= x)); auto.
    apply real_nle_ge in H0.

    destruct n.
    simpl in H0.
    pose proof (real_lt_lt_lt _ _ _ o H0).
    contradict (real_nlt_triv _ H1).
    assert (x <= Nreal (S n)).
    left; auto.
    pose proof (q n H1).
    contradict H2.
    apply Nat.nle_succ_diag_l.
  Qed.  

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

  Lemma lbc_approx f f' r M :  uniform_derivative f f' r -> bounded_by f' M r -> forall (x y : (I r)) eps, (real_0 < eps) -> (pc_dist (f x) (f y) <= pc_unit _ ((M+eps) * dist x y))%pcreal.
  Proof.
    intros.
    rewrite real_plus_comm.
    apply uniform_derivative_unfold in H.
    destruct H as [X0 X].
    destruct (X eps) as [d [D1 D2]];auto.
    destruct (interval_div_by_d x y d) as [n [d' [N1 [N2 N3]]]];auto.
    rewrite N3.
    destruct x as [x Px]; destruct y as [y Py].
    destruct (X0 x) as [[fx FX] _];auto.
    destruct (X0 y) as [[fy FY] _];auto.
    simpl.
    exists (dist fx fy); exists ((eps+M)*(Nreal n * d + d'));split;[apply pc_lift2_iff;exists fx; exists fy|split;[apply pc_unit_mono|]];auto.
    revert dependent fx; revert dependent x.
    rewrite bounded_by_unfold in H0.
    destruct H0 as [_ H0].
    induction n.
    - intros.
      simpl;ring_simplify.
      simpl in N3.
      ring_simplify in N3.
      destruct (X0 x) as [_ [f'x P]];auto.
      apply (real_le_le_le _ (eps * dist x y + M * dist x y)).
      rewrite dist_symm in N3.
      rewrite dist_symm, (dist_symm x).
      unfold dist.
      replace (fy - fx) with ((fy - fx - f'x * (y-x)) + f'x * (y-x)) by ring.
      apply (real_le_le_le _ _ _ (abs_tri _ _)).
      apply real_le_le_plus_le;auto.
      apply D2;auto.
      rewrite dist_symm, N3; auto.
      rewrite abs_mult.
      rewrite real_mult_comm, (real_mult_comm M).
      apply real_le_mult_pos_le; [apply abs_pos|auto].
      apply (H0 x);auto.
      apply real_le_le_plus_le;apply real_le_mult_pos_le; [apply real_lt_le |apply real_eq_le | | apply real_eq_le];auto.
      apply (real_le_le_le _ _ _ (abs_pos (f'x)));auto.
      apply (H0 x);auto.
    - intros.
      destruct (X0 x) as [_ [f'x P]];auto.
      destruct (interval_subdivision_step _ _ _ _ _ D1 N1 N2 N3) as [x' [P1 [P2 P3]]].
      simpl in P3.
      assert (abs x' <= r) by (destruct P3; apply (real_le_le_le _ _ _ H);auto).
      destruct (X0 x') as [[fx' P'] _];auto.
      apply (real_le_le_le _ _ _ (dist_tri _ (fx') _)).
      replace ((eps+M)*(Nreal (S n) * d + d')) with ((eps*d + M*d) + (eps+M)*(Nreal n *d + d')) by (simpl;ring).
      apply real_le_le_plus_le.
      rewrite dist_symm.
      unfold dist.
      replace (fx' - fx) with ((fx' - fx - f'x * (x'-x)) + f'x * (x'-x)) by ring.
      apply (real_le_le_le _ _ _ (abs_tri _ _)).
      apply real_le_le_plus_le;auto.
      apply (real_le_le_le _ (eps * abs (x'-x))); [| apply real_le_mult_pos_le; [apply real_lt_le |rewrite dist_symm in P1]];auto; destruct x'';simpl in *;rewrite Px;auto.
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
      apply (IHn x' H);auto.
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
    pose proof (lbc_approx _ _ _ _ H H0 x y _ H3).
    destruct H4 as [d [l [D [L H4]]]].
    simpl in D.
    replace ((M+eps)*dist x y) with l by (apply pc_unit_mono;rewrite L;auto).
    replace (dist fx fy) with d by (apply pc_unit_mono; rewrite <-pc_unit_ntrans2, <-H1, <-H2;auto).
    apply H4.
  Qed.

  Definition restrict_to_interval (f : ^Real -> pc ^Real) (r : ^Real) : (^Real -> pc ^Real). 
  Proof.
     intros x.
     apply (pc_Prop_lem (abs x <= r)).
     intros.
     destruct H.
     apply (f x).
     apply pc_bot.
 Defined.

 Lemma restrict_to_interval_spec1 f r : forall x fx, abs x <= r -> (defined_to (f x) fx <-> defined_to (restrict_to_interval f r x) fx).
 Proof.
 Admitted.
Lemma restrict_to_interval_spec2 f r : forall x, defined (restrict_to_interval f r x) -> abs x <= r.
Proof.
Admitted.

 Lemma uniformly_continuous_continuous f r : uniformly_continuous f r -> 
    (forall x, abs x <= r -> cont_at (restrict_to_interval f r) x).
  Proof.
    rewrite uniformly_continuous_unfold.
    intros [H1 H2].
    split; [destruct (H1 _ H);exists x0; apply restrict_to_interval_spec1;auto|].
    intros.
    destruct (H2 eps) as [d [dg0 D]];auto.
    exists d;split;auto.
    simpl;intros.
    apply (D x y);auto.
    apply (restrict_to_interval_spec2 f r y);exists fy;auto.
    apply (restrict_to_interval_spec1 f r x fx);auto.
    apply (restrict_to_interval_spec1 f r y fy);auto.
    apply (restrict_to_interval_spec2 f r y);exists fy;auto.
  Qed.

  Lemma real_lt_or_ge x y : (x < y) \/ (x >= y).
  Admitted.

  Lemma abs_le_iff x y: abs x <= y <-> -y <= x <= y.
  Admitted.

  Lemma uniformly_continuous_bound_above f r : uniformly_continuous f r -> exists M, forall x, abs x <= r -> ((f x) <= pc_unit _ M)%pcreal.
  Proof.
    destruct (real_lt_or_ge r real_0).
    - intros.
      exists 0.
      intros.
      contradict H1.
      apply real_gt_nle.
      apply (real_lt_le_lt _ 0);try apply abs_pos;auto.
   - intros.
     assert (-r <= r).
     {
       add_both_side_by r.
       apply real_le_pos_mult_pos_pos;auto.
       apply real_lt_le.
       apply real_lt_0_2.
     }
     pose proof (pc_cont_fun_on_closed_interval_is_bounded_above (restrict_to_interval f r) _ _ H1).
     destruct H2 as [M U].
     intros.
     apply uniformly_continuous_continuous;auto.
     apply abs_le_iff;auto.
     exists M.
     intros.
     rewrite uniformly_continuous_unfold in H0.
     destruct (proj1 H0 x) as [fx Fx];auto.
     exists fx; exists M; split;[|split;[apply pc_unit_mono|]];auto.
     apply U.
     exists x;split;auto.
     apply abs_le_iff;auto.
     apply restrict_to_interval_spec1;auto.
  Qed.
  Lemma uniformly_continuous_inv f r : uniformly_continuous f r -> uniformly_continuous (fun x => - f x)%pcreal r.
  Proof.
  Admitted.
  
  Lemma uniformly_continuous_bound_below f r : uniformly_continuous f r -> exists M, forall x, abs x <= r -> ((f x) >= pc_unit _ M)%pcreal.
  Proof.
    intros.
    pose proof (uniformly_continuous_inv _ _ H).
    destruct (uniformly_continuous_bound_above _ _ H0) as [M P].
    exists (-M).
    intros.
    rewrite uniformly_continuous_unfold in H.
    destruct (proj1 H x) as [fx Fx];auto.
     exists (-M); exists fx; split;[apply pc_unit_mono | split];auto.
     add_both_side_by (M-fx).
     destruct (P _ H1) as [fx' [M' [F1 [F2 H2]]]].
     apply pc_unit_mono in F2.
     rewrite F2.
     replace (-fx) with fx';auto.
     apply pc_unit_mono.
     replace fx with (- - fx) in Fx by ring.
     apply defined_to_opp in Fx.
     rewrite <-Fx.
     rewrite F1;auto.
  Qed.

  Lemma pc_le_unit_l x x' y : (defined_to x x') -> ((x <= pc_unit _ y)%pcreal <-> x' <= y).
  Admitted.

  Lemma pc_le_unit_r x y y' : (defined_to y y') -> ((pc_unit _ x <= y)%pcreal <-> x <= y').
  Admitted.

  Lemma uniformly_continuous_bounded f r : uniformly_continuous f r -> exists M, forall x, abs x <= r -> (pc_abs (f x) <= pc_unit _ M)%pcreal.
  Proof.
    intros.
    destruct (uniformly_continuous_bound_above _ _ H) as [M1 P1].
    destruct (uniformly_continuous_bound_below _ _ H) as [M2 P2].
    exists (real_max M1 (-M2)).
    intros.
    apply pc_abs_le.
    rewrite uniformly_continuous_unfold in H.
    destruct (proj1 H x) as [fx Fx];auto.
     exists fx; exists (real_max M1 (-M2)); split;[|split;[apply pc_unit_mono|]];auto.
     assert (fx <= (real_max M1 (-M2))).
     {
       apply (real_le_le_le _ M1);try (apply real_max_fst_le_le; apply real_le_triv).
       apply (pc_le_unit_l _ _ _ Fx).
       apply P1;auto.
     }
     assert (-(real_max M1 (-M2)) <= fx).
     {
       add_both_side_by (-fx + real_max M1 (-M2)).
       apply (real_le_le_le _ (-M2));try (apply real_max_snd_le_le; apply real_le_triv).
       add_both_side_by (fx + M2).
       apply (pc_le_unit_r _ _ _ Fx).
       apply P2;auto.
     }
     apply abs_le_iff;auto.
  Qed.
  Lemma derivative_is_uniformly_continuous f g r : uniform_derivative f g r -> uniformly_continuous g r.
    rewrite uniform_derivative_unfold, uniformly_continuous_unfold.
    intros [H1 H2].
    split; [intros; apply (proj2 (H1 _ H))|].
    intros eps epsgt0.
    assert (eps / real_2_neq_0 > real_0) by (apply real_half_gt_zero;auto).
    destruct (H2 _ H) as [d [dgt0 D]].
    exists d; split;auto.
    intros x y gx gy xb yb db X Y.
    destruct (dist_pos_t x y).
    - rewrite dist_symm;rewrite dist_symm in H0;unfold dist.
      apply (real_le_mult_pos_cancel (abs (y-x)));auto.
      rewrite <-abs_mult.
      destruct (proj1 (H1 _ xb)) as [fx Fx].
      destruct (proj1 (H1 _ yb)) as [fy Fy].
      replace ((gy - gx)*(y-x)) with ((fy - fx - gx*(y-x)) + (fx - fy - gy * (x-y))) by ring.
      rewrite <-(half_twice eps), (real_mult_comm _ (abs _)), real_mult_plus_distr, !(real_mult_comm (abs _)).
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    apply real_le_le_plus_le;[apply D;auto|].
    rewrite <-(dist_abs x), dist_symm, dist_abs.
    apply D;try rewrite dist_symm;auto.
  - replace gy with gx.
    rewrite dist_axiom_identity; apply real_lt_le;auto.
    apply pc_unit_mono.
    rewrite <-X.
    replace x with y;auto.
    apply dist_zero;rewrite dist_symm;auto.
  Qed.
  Lemma derivative_bounded f g r: uniform_derivative f g r -> exists M, bounded_by g M r.
  intros.
  apply derivative_is_uniformly_continuous in H.
  destruct (uniformly_continuous_bounded _ _ H) as [M Mprp].
  exists M.
  intros x.
  destruct x as [x P].
  apply Mprp;apply P.
 Qed.
  Lemma abs_plus_one_div_le x y : x >= 0 ->  x / (real_gt_neq _  _ (abs_plus_1_gt_0 y)) <= x.
  Proof.
    intros.
    unfold real_div.
    apply (real_le_mult_pos_cancel (abs y + real_1)); [apply abs_plus_1_gt_0|].
    rewrite real_mult_assoc, real_mult_inv.
    ring_simplify.
    add_both_side_by (-x).
    apply real_le_pos_mult_pos_pos;auto.
    apply abs_pos.
  Qed.
  Lemma uniform_derivative_uniform_continuous f g r : uniform_derivative f g r -> uniformly_continuous f r.
    intros H eps epsgt0.
    destruct (derivative_bounded _ _ _ H) as [M P].
    apply uniform_derivative_unfold in H.
    destruct H.
    destruct (H0 _ (real_half_gt_zero _ epsgt0)) as [d [dgt0 D]].
    assert (exists d',  d' > real_0 /\ (forall x y, dist x y <= d' -> dist x y <= d /\ dist x y <= real_1 /\ dist x y <= ((eps / d2) / (real_gt_neq _  _ (abs_plus_1_gt_0 M))))) as [d' [d'gt0 P']].
    {
      exists (real_min d (real_min real_1 ((eps / d2) / (real_gt_neq _  _ (abs_plus_1_gt_0 M))))).
      split.
      - destruct (real_min_cand d (real_min real_1 ((eps / d2) / (real_gt_neq _  _ (abs_plus_1_gt_0 M))))) as [-> | ->]; auto;destruct (real_min_cand real_1 ((eps / d2) / (real_gt_neq _  _ (abs_plus_1_gt_0 M)))) as [-> | ->];auto.
       apply real_1_gt_0.
       apply real_div_gt_0; [apply real_half_gt_zero;auto|apply abs_plus_1_gt_0].
     - intros.
       split; [|split]; apply (real_le_le_le _ _ _ H1); [apply real_min_fst_le | |];apply (real_le_le_le _ _ _ (real_min_snd_le _ _)).
       apply real_min_fst_le.
       apply real_min_snd_le.
    } 
    exists d';split;auto.
    intros.
    destruct x as [x xr]; destruct y as [y yr]; simpl in *.
    destruct (P' _ _ H1) as [L1 [L2 L3]].
    destruct (H x) as [[fx Fx] [gx Gx]];auto.
    destruct (H y) as [[fy Fy] _];auto.
    assert (defined_to (pc_dist (f x) (f y)) (dist fx fy)).
    {
      unfold defined_to.
      rewrite <-pc_unit_ntrans2.
      rewrite Fx, Fy;auto.
    }
    apply (pc_le_unit_l _ _ _ H2).
    rewrite dist_symm.
    unfold dist.
    replace (fy - fx) with ((fy - fx - gx * (y-x)) + gx * (y-x)) by ring.
    rewrite <-(half_twice eps).
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    apply real_le_le_plus_le.
    - apply (real_le_le_le _ ((eps / d2) * abs (y - x))).
      apply D;auto.
      apply (real_le_le_le _ ((eps / d2) * real_1)); [|apply real_eq_le; ring_simplify;auto].
      apply real_le_mult_pos_le; [apply real_lt_le;apply real_half_gt_zero| rewrite <-dist_abs];auto.
    - rewrite abs_mult.
      apply (real_le_le_le _ (abs gx * ( (eps / d2) / (real_gt_neq _ _ (abs_plus_1_gt_0 M))))); [apply real_le_mult_pos_le; [apply abs_pos|rewrite <-dist_abs];auto|].
      apply (real_le_le_le _ (M * ((eps / d2)/ real_gt_neq _ _ (abs_plus_1_gt_0 M)))).
      rewrite !(real_mult_comm _ ((eps / _) / _)).
      apply real_le_mult_pos_le.
      apply (real_le_le_le _ _ _ (dist_pos x y));auto.
      apply bounded_by_unfold in P.
      apply (proj2 P x);auto.
      replace M with (abs M) at 1.
      rewrite real_mult_comm.
      apply abs_plus_one_div_inv; apply real_half_gt_zero;auto.
      apply abs_pos_id.
      apply bounded_by_unfold in P.
      apply (real_le_le_le _ _ _ (abs_pos gx)).
      apply (proj2 P x);auto.
  Qed.

  Lemma differentiable_bounded f g r: uniform_derivative f g r -> exists M, bounded_by f M r.
  Proof.
    intros.
    apply uniform_derivative_uniform_continuous in H.
    destruct (uniformly_continuous_bounded _ _ H) as [M Mprp].
    exists M.
    intros x.
    destruct x as [x P].
    apply Mprp;apply P.
 Qed.

 Lemma derive_ext f1 f2 g x : (forall x, f1 x = f2 x) ->  uniform_derivative f2 g x -> uniform_derivative f1 g x.
 Proof.
   intros H D eps epsgt0.
   destruct (D eps epsgt0) as [d [dgt dP]].
   exists d;split;auto.
   intros.
   rewrite !H.
   apply dP;auto.
 Qed.

 Lemma derive_ext2 f g1 g2 x : (forall x, g2 x = g1 x) ->  uniform_derivative f g1 x -> uniform_derivative f g2 x.
 Proof.
   intros H D eps epsgt0.
   destruct (D eps epsgt0) as [d [dgt dP]].
   exists d;split;auto.
   intros.
   rewrite H.
   apply dP;auto.
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
    rewrite !uniform_derivative_unfold; unfold uniform_derivative_unfolded.
    intros [H1 H1'] [H2 H2'].
    split; [intros; split;destruct (H1 x);destruct (H2 x);auto; apply sum_defined;auto|].
    intros eps epsgt0.
    assert (eps / real_2_neq_0 > real_0) by (apply real_half_gt_zero;auto).
    destruct (H1' (eps / real_2_neq_0)) as [d1 [d1gt0 D1]];auto.
    destruct (H2' (eps / real_2_neq_0)) as [d2 [d2gt0 D2]];auto.
    exists (Minmax.real_min d1 d2);split;[destruct (Minmax.real_min_cand d1 d2) as [-> | ->];auto|].
    intros.
    apply pc_lift2_iff in H4,H5,H6.
    destruct H4 as [f1x [f2x [F0 [F0' ->]]]].
    destruct H5 as [f1y [f2y [F1 [F1' ->]]]].
    destruct H6 as [g1x [g2x [F2 [F2' ->]]]].
    replace (f1y + f2y - (f1x + f2x) - (g1x + g2x)*(y - x)) with ((f1y - f1x -g1x*(y-x)) + (f2y - f2x - g2x*(y-x))) by ring.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    replace (eps * abs (y-x)) with (eps /real_2_neq_0 * abs (y-x) + eps / real_2_neq_0 * abs (y-x)) by (rewrite <-(half_twice eps);ring_simplify;rewrite half_twice; ring).
    apply real_le_le_plus_le;auto. 
    apply D1;auto.
    apply (real_le_le_le _ _ _ H7).
    apply real_min_fst_le.
    apply D2;auto.
    apply (real_le_le_le _ _ _ H7).
    apply real_min_snd_le.
 Qed.

  Lemma derivative_sproduct a f g r : uniform_derivative f g r -> uniform_derivative (fun x => (pc_unit _ a * f x)%pcreal) (fun x => (pc_unit _ a * g x)%pcreal) r.
  Proof.
    rewrite !uniform_derivative_unfold; unfold uniform_derivative_unfolded.
    intros [H0 H1].
     split; [intros; split;destruct (H0 x);auto;apply product_defined;auto;apply unit_defined|]. 
    intros eps epsgt0.
    destruct (H1 (eps / (real_gt_neq _  _ (abs_plus_1_gt_0 a)))) as [d [dgt0 D]];[apply real_div_gt_0;try apply abs_plus_1_gt_0;auto |].
    exists d;split;auto.
    intros x y afx afy af'x xr yr H2 H3 H4 H5.
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


  Lemma derivative_product f1 f2 g1 g2 r : uniform_derivative f1 g1 r -> uniform_derivative f2 g2 r -> uniform_derivative (fun x => (f1 x * f2 x)%pcreal) (fun x => ((f1 x * g2 x) + (g1 x * f2 x))%pcreal) r.
  Proof.
    intros H1 H2.
    destruct (derivative_bounded _ _ _ H2) as [Mg g2M].
    destruct (differentiable_bounded _ _ _ H1) as [Mf1 f1M].
    destruct (differentiable_bounded _ _ _ H2) as [Mf2 f2M].
    apply bounded_by_unfold in g2M, f1M, f2M.
    (* split; [intros; split;destruct (proj1 H1 x);destruct (proj1 H2 x); try apply sum_defined;try apply product_defined;auto|]. *)
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
    apply uniform_derivative_unfold in H1,H2.
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
    specialize (D0 x y).
    destruct x as [x px]; destruct y as [y py];simpl.
    apply pc_abs_le.
    destruct (proj1 H1 x) as [[f1x F1x] [g1x G1x]];auto.
    destruct (proj1 H1 y) as [[f1y F1y] _];auto.
    destruct (proj1 H2 x) as [[f2x F2x] [g2x G2x]];auto.
    destruct (proj1 H2 y) as [[f2y F2y] _];auto.
    exists (f1y * f2y - f1x * f2x - (f1x * g2x + g1x * f2x) * (y - x)); exists (eps * abs(y-x)).
    split; [rewrite F1x, F1y, F2x, F2y, G1x, G2x, !pc_unit_ntrans2,!pc_unit_ntrans, !pc_unit_ntrans2;apply pc_unit_mono;auto|split;[apply pc_unit_mono;auto|]].
    replace (f1y * f2y - f1x * f2x - (f1x * g2x + g1x * f2x) * (y - x)) with ((f1y - f1x)*(g2x)*(y-x) + (f1y * (f2y - f2x - g2x * (y-x)) + f2x * (f1y - f1x - g1x * (y-x)))) by ring.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    rewrite (half_twice_mult eps _).
    apply real_le_le_plus_le; [|rewrite (half_twice_mult (eps / real_2_neq_0));apply (real_le_le_le _ _ _ (abs_tri _ _));apply real_le_le_plus_le];rewrite !abs_mult.
    - rewrite !(real_mult_comm _ (abs (y-x))).
      apply real_le_mult_pos_le; [apply abs_pos |].
      apply (real_le_le_le _ (eps0 * Mg)).
      apply (real_le_le_le _ (abs (f1y - f1x)*Mg)).
      apply real_le_mult_pos_le;[apply abs_pos |];auto.
      apply (proj2 g2M x);auto.
      rewrite !(real_mult_comm _ Mg).
      apply real_le_mult_pos_le; [apply (real_le_le_le _ (abs g2x));[apply abs_pos| apply (proj2 g2M x);auto]|].
      rewrite <-dist_abs.
      simpl in D0.
      destruct D0 as [l [rt [L [Rt P]]]]; [apply (real_le_le_le _ _ _ H dd0)|].
      replace (eps0) with rt by (apply pc_unit_mono;auto).
      replace (dist f1x f1y) with l by (apply pc_unit_mono;rewrite <-pc_unit_ntrans2, <-F1x, <-F1y;auto).
      apply P.
      rewrite Heqeps0.
      assert (0 <= Mg) by (apply (real_le_le_le _ (abs g2x));[apply abs_pos | apply (proj2 g2M x);auto]).
      apply (real_le_le_le _ (eps0' * Mg)); [rewrite !(real_mult_comm _ Mg);apply real_le_mult_pos_le;auto;try apply Minmax.real_min_snd_le | ].
      rewrite Heqeps0'.
      replace Mg with (abs Mg) at 4 by (apply abs_pos_id;auto).
      apply abs_plus_one_div_inv; apply real_half_gt_zero;auto.
   -  apply (real_le_le_le _ (abs (f1y) * (eps2 * abs (y - x)))).
      apply real_le_mult_pos_le; [apply abs_pos | apply D2;auto;apply (real_le_le_le _ _ _ H dd2)].
      rewrite !(real_mult_comm _ (abs (y-x))), <-real_mult_assoc,(real_mult_comm _ (abs (y-x))), real_mult_assoc.
      apply real_le_mult_pos_le;try apply abs_pos.
      rewrite real_mult_comm.
      apply (real_le_le_le _ (eps2 *(Mf1+real_1))).
      apply real_le_mult_pos_le;[apply real_lt_le|];auto.
      apply (real_le_le_le _ Mf1); [apply (proj2 f1M y);auto|add_both_side_by (-Mf1);apply real_lt_le;apply real_1_gt_0].
      assert (0 <= Mf1) by (apply (real_le_le_le _ (abs f1x));[apply abs_pos | apply (proj2 f1M x);auto]).
      replace Mf1 with (abs Mf1)  by (apply abs_pos_id;auto).
      rewrite Heqeps2.
      unfold real_div.
      rewrite !real_mult_assoc,real_mult_inv.
      apply real_eq_le;ring.
   -  assert (0 <= Mf2) by (apply (real_le_le_le _ (abs f2x));[apply abs_pos | apply (proj2 f2M x);auto]).
      apply (real_le_le_le _ (Mf2 * (eps1 * abs (y - x)))).
      apply (real_le_le_le _ (Mf2 * (abs (f1y - f1x -g1x * (y-x))))).
      rewrite real_mult_comm, (real_mult_comm Mf2);apply real_le_mult_pos_le;[apply abs_pos|].
      apply (proj2 f2M x);auto.
      apply real_le_mult_pos_le; auto.
      apply D1;auto.
      apply (real_le_le_le _ _ _ H dd1).
      rewrite <-real_mult_assoc, !(real_mult_comm _ (abs (y- x))).
      apply real_le_mult_pos_le;try apply abs_pos.
      rewrite Heqeps1.
      rewrite real_mult_comm.
      replace Mf2 with (abs Mf2) at 4 by (apply abs_pos_id;auto).
      apply abs_plus_one_div_inv.
      apply real_half_gt_zero.
      apply real_half_gt_zero;auto.
  Defined.
End Operations.

Section Examples.
  Lemma derivative_const c r f:  (forall (x : (I r)), defined_to (f x) c) -> uniform_derivative (fun x => (pc_unit _ c)) (fun x => pc_unit _ real_0 ) r.
  Proof.
   intros H eps epsgt0.
   exists real_1.
   split; [apply real_1_gt_0|].
   intros.
   rewrite !pc_unit_ntrans2, !pc_unit_ntrans, !pc_unit_ntrans2.
   replace (c+-c+-(real_0 * (y-x))) with real_0 by ring.
   unfold pc_abs.
   rewrite pc_unit_ntrans.
   rewrite (proj2 (abs_zero real_0)); try apply real_le_triv;auto.
   exists (real_0); exists (eps * abs (y-x)); split;[|split]; unfold defined_to;auto.
   apply real_le_pos_mult_pos_pos.
   apply real_lt_le;auto.
   apply abs_pos.
 Qed.
  
  Lemma derivative_id r f : (forall (x : (I r)), defined_to (f x) x) -> uniform_derivative (fun x => pc_unit _ x) (fun x => pc_unit _ real_1) r.
  Proof.
   intros H eps epsgt0.
   exists real_1.
   split; [apply real_1_gt_0|].
   intros.
   rewrite !pc_unit_ntrans2, !pc_unit_ntrans, !pc_unit_ntrans2.
   replace (y+-x+-(real_1 * (y-x))) with real_0 by ring.
   unfold pc_abs.
   rewrite pc_unit_ntrans.
   rewrite (proj2 (abs_zero real_0)); try apply real_le_triv;auto.
   exists (real_0); exists (eps * abs (y-x)); split;[|split]; unfold defined_to;auto.
   apply real_le_pos_mult_pos_pos.
   apply real_lt_le;auto.
   apply abs_pos.
 Qed.
End Examples.
Section FunctionDerivatives.

  Definition uniform_derivative_fun (f : ^Real -> ^Real) (g : ^Real -> ^Real) r := forall eps, (eps > 0) -> exists delta, delta > 0 /\ forall (x y : (I r)), dist x y <= delta -> abs (f y - f x - g x * (y - x)) <= eps*abs (y-x).

  Definition derivative_function_iff (f : ^Real -> ^Real) (g : ^Real -> ^Real) r : uniform_derivative (fun x => pc_unit _ (f x)) (fun x => pc_unit _ (g x)) r <-> uniform_derivative_fun f g r.
  Proof.
  rewrite uniform_derivative_unfold.
  split;intros.
  - intros eps epsgt0. 
    destruct (proj2 H _ epsgt0) as [d [dgt0 D]].
    exists d; split;auto.
    intros.
    destruct x as [x px]; destruct y as [y py].
    simpl.
    apply D;auto;apply pc_unit_mono;auto.
  - split; [intros; split; [exists (f x) | exists (g x)];apply pc_unit_mono;auto |].
    intros eps epsgt0.
    destruct (H _ epsgt0) as [d [dgt0 D]].
    exists d;split;auto.
    intros.
    apply pc_unit_mono in H2,H3, H4.
    rewrite <-H2, <-H3, <-H4;auto.
    apply (D (real_to_I H0) (real_to_I H1));auto.
  Qed.

  Lemma sum_rule f1 f2 g1 g2 r : uniform_derivative_fun f1 g1 r -> uniform_derivative_fun f2 g2 r -> uniform_derivative_fun (fun x => (f1 x + f2 x)) (fun x => (g1 x + g2 x)) r.
  Proof.
    rewrite <-!derivative_function_iff.
    intros.
    pose proof (derivative_sum _ _ _ _ _ H H0).
    simpl in H1.
    intros eps epsgt0.
    destruct (H1 _ epsgt0) as [d [dgt0 D]].
    exists d;split;auto;intros.
    specialize (D _ _ H2).
    rewrite <-!pc_unit_ntrans2 in *.
    rewrite <-!pc_unit_ntrans in *.
    apply D.
 Qed.
  Lemma derivative_fun_sproduct a f g r : uniform_derivative_fun f g r -> uniform_derivative_fun (fun x => a * f x) (fun x => a * g x) r.
  Proof.
    rewrite <-!derivative_function_iff.
    intros.
    pose proof (derivative_sproduct a _ _ _ H).
    simpl in H0.
    intros eps epsgt0.
    destruct (H0 _ epsgt0) as [d [dgt0 D]].
    exists d;split;auto;intros.
    specialize (D _ _ H1).
    rewrite <-!pc_unit_ntrans2 in *.
    rewrite <-!pc_unit_ntrans in *.
    apply D.
 Qed.
Lemma product_rule f1 f2 g1 g2 r : uniform_derivative_fun f1 g1 r -> uniform_derivative_fun f2 g2 r -> uniform_derivative_fun (fun x => (f1 x * f2 x)) (fun x => (f1 x * g2 x + g1 x * f2 x )) r.
  Proof.
    rewrite <-!derivative_function_iff.
    intros.
    pose proof (derivative_product _ _ _ _ _ H H0).
    simpl in *.
    intros eps epsgt0.
    destruct (H1 _ epsgt0) as [d [dgt0 D]].
    exists d;split;auto;intros.
    specialize (D _ _ H2).
    rewrite <-!pc_unit_ntrans2 in *.
    rewrite <-!pc_unit_ntrans in *.
    apply D.
  Qed.

  Lemma derivative_const_fun c r: uniform_derivative_fun (fun x => c) (fun x => real_0) r. 
  Proof.
    rewrite <-!derivative_function_iff.
    intros.
    pose proof (derivative_const c r (fun x => pc_unit _ c)).
    apply H.
    intros.
    apply pc_unit_mono;auto.
 Qed.

  Lemma derivative_id_fun r : uniform_derivative_fun (fun x => x) (fun x => real_1) r.
  Proof.
    rewrite <-!derivative_function_iff.
    intros.
    pose proof (derivative_id r (fun x => pc_unit _ x)).
    apply H.
    intros.
    apply pc_unit_mono;auto.
  Qed.

 Lemma derive_ext_fun f1 f2 g x : (forall x, f1 x = f2 x) ->  uniform_derivative_fun f2 g x -> uniform_derivative_fun f1 g x.
 Proof.
   intros H D eps epsgt0.
   destruct (D eps epsgt0) as [d [dgt dP]].
   exists d;split;auto.
   intros.
   rewrite !H.
   apply dP;auto.
 Qed.

 Lemma derive_ext_fun2 f g1 g2 x : (forall x, g2 x = g1 x) ->  uniform_derivative_fun f g1 x -> uniform_derivative_fun f g2 x.
 Proof.
   intros H D eps epsgt0.
   destruct (D eps epsgt0) as [d [dgt dP]].
   exists d;split;auto.
   intros.
   rewrite H.
   apply dP;auto.
 Qed.
End FunctionDerivatives.
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
