Require Import Real.
Require Import ClassicalMonads ClassicalPartiality ClassicalPartialReals ClassicalContinuity.
Require Import RealAssumption.
Require Import Minmax.

Lemma dist_axiom_identity : forall x, dist x x = real_0.
Proof.
  intro x.
  destruct (dist_prop x x).
  destruct H0.
  apply H0; auto.
Defined.

Lemma real_le_eq_or_lt : forall x y, x <= y -> x = y \/ x < y.
Proof.
Admitted.

Lemma dist_axiom_positivity : forall x y, x <> y -> dist x y > real_0.
Proof.
  intros x y o.
  pose proof (dist_pos_t x y).
  pose proof (dist_zero x y).
  destruct (real_le_eq_or_lt _ _ H).
  apply eq_sym in H1.
  destruct H0.
  apply H0 in H1.
  contradict (o H1).
  exact H1.
Defined.

Lemma dist_axiom_symmetry : forall x y, dist x y = dist y x.
Proof.
  apply dist_symm.
Defined.

Lemma dist_axiom_triangle : forall x y z, dist x z <= dist x y + dist y z.
Proof.
  intros.
  apply dist_tri.
Defined.

Global Instance real_metric_space : MetricSpace ^Real :=
  {
    metric := dist ;
    metric_axiom_identity := dist_axiom_identity ;
    metric_axiom_positivity := dist_axiom_positivity ;
    metric_axiom_symmetry := dist_axiom_symmetry ;
    metric_axiom_triangle := dist_axiom_triangle
  }.

Section ClassicalContinuityRealOps.

  Lemma dist_plus_le a b c d : dist (a+b) (c+d) <= dist a c + dist b d.
  Proof.
    unfold dist.
    assert (a+b - (c+d) = (a-c) + (b-d)) as -> by ring.
    apply abs_tri.
  Qed.

  Lemma dist_bound x y eps : dist x y <= eps -> abs y <= abs x + eps.
  Proof.
    intros.
    replace y with (x + (y-x)) by ring.
    rewrite dist_symm in H.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    apply real_le_le_plus_le; [apply real_le_triv | apply H].
  Qed.

  Lemma half_twice x : (x / real_2_neq_0) + (x / real_2_neq_0) = x.
  Proof.
    rewrite real_div_distr.

    replace (x + x) with (x * real_2) by (unfold real_2; simpl;ring).
    unfold real_div; rewrite real_mult_assoc, (real_mult_comm real_2), real_mult_inv.
    ring.
  Qed.

  Lemma half_le_le x y : (x <= y) -> (x / real_2_neq_0) <= (y / real_2_neq_0).
  Proof.
    intros.
    unfold real_div.
    apply (real_le_mult_pos_cancel real_2); [apply real_2_pos|].
    rewrite !real_mult_assoc.
    rewrite real_mult_inv.
    ring_simplify;auto.
  Qed.

  Lemma abs_plus_1_gt_0 : forall x, (abs x)+real_1 > real_0.
  Proof.
    intros.
    apply (real_lt_le_lt _ (real_0 + real_1)); [rewrite real_plus_unit; apply real_1_gt_0 |].
    apply real_le_le_plus_le; [apply abs_pos|apply real_le_triv].
  Qed.

  Lemma real_plus_cont : forall x,
      @cont_at (^Real * ^Real) prod_max_metric_space _ _ (fun x => Nabla_unit _ (Some ((fst x) + (snd x)))) x.
  Proof.
    intros [x y].
    split.
    exists (x + y).
    simpl.
    unfold defined_to; auto.

    intros eps eps_pos.
    exists (eps / real_2_neq_0).
    split.
    apply real_half_gt_zero; auto.
    intros [x' y'] x'' y''.
    simpl.
    intro ord.
    intros p q.
    apply Nabla_unit_mono in p.
    apply Nabla_unit_mono in q.
    injection p; intro h1.
    injection q; intro h2.
    rewrite <- h1, <- h2.
    clear p q h1 h2.
    apply (real_le_le_le _ _ _ (dist_plus_le _ _ _ _)).
    rewrite <-half_twice.
    apply real_le_le_plus_le.
    apply real_max_le_fst_le in ord.
    exact ord.
    apply real_max_le_snd_le in ord.
    exact ord.
  Defined.

  Lemma real_mult_cont : forall x, 
      @cont_at (^Real * ^Real) prod_max_metric_space _ _ (fun x => Nabla_unit _ (Some ((fst x) * (snd x)))) x.
  Proof.
    intros [x y].
    split.
    exists (x * y).
    simpl.
    unfold defined_to; auto.

    intros.
    
    pose proof (abs_plus_1_gt_0 x).
    remember (Minmax.real_min real_1 (eps / (real_gt_neq _ _ H0) / real_2_neq_0)) as eps0.
    assert (eps0 > real_0) as eps0gt0.
    {
      rewrite Heqeps0.
      destruct (Minmax.real_min_cand real_1 (eps / (real_gt_neq _ _ H0) / real_2_neq_0)) as [-> | ->].
      apply real_1_gt_0.
      apply real_half_gt_zero.
      unfold real_div.
      apply real_lt_pos_mult_pos_pos;auto.
      apply real_pos_inv_pos;auto.
    }
    assert (abs (y) + eps0  > real_0) as f2xepsgt0.
    {
      
      apply (real_lt_le_lt _ (real_0 + eps0)); [rewrite real_plus_unit; auto |].
      apply real_le_le_plus_le; [apply abs_pos|apply real_le_triv].
    }
    pose proof (abs_plus_1_gt_0 y).
    remember (eps / (real_gt_neq _ _ H1) / real_2_neq_0) as eps1.
    assert (eps1 > real_0) as eps1gt0.
    {
      rewrite Heqeps1.
      apply real_half_gt_zero.
      unfold real_div.
      apply real_lt_pos_mult_pos_pos;auto.
      apply real_pos_inv_pos;auto.
    }
    assert (forall a b c (cn0 : c <> real_0), a * (b / cn0) = (a*b)/ cn0) as diff by (intros;unfold real_div;ring_simplify;auto).
    exists (real_min eps0 eps1).
    simpl.
    split; [destruct (Minmax.real_min_cand eps0 eps1) as [-> | ->];auto|].
    intros.
    rename x into f1x.
    rename y into f2x.
    replace fx with (f1x *f2x).
    destruct y0 as [f1y f2y].
    replace fy with (f1y *f2y).
    unfold dist.
    replace (f1x * f2x - f1y * f2y) with ((f1x * (f2x -  f2y)) + (f2y * ( f1x - f1y))) by ring.
    replace eps with (eps / real_2_neq_0 + eps / real_2_neq_0) by apply half_twice.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    apply real_le_le_plus_le;rewrite abs_mult.
    - apply (real_le_le_le _ (abs (f1x) * eps0)).
      + apply real_le_mult_pos_le; [apply abs_pos |].
        pose proof (real_le_le_le _ _ _ H2 (real_min_fst_le eps0 eps1)).
        pose proof (real_le_le_le _ _ _ (real_max_snd_ge  (dist f1x f1y) (dist f2x f2y)) H5).
        exact H6.
      + apply (real_le_le_le _ (abs f1x * (eps / real_gt_neq (abs f1x + real_1) real_0 H0 / real_2_neq_0))).
        rewrite Heqeps0.
        apply real_le_mult_pos_le;[apply abs_pos|].
        apply Minmax.real_min_snd_le.
        rewrite diff.
        apply half_le_le.
        unfold real_div.
        rewrite <-real_mult_assoc, real_mult_comm, <-real_mult_assoc, real_mult_comm.
        replace eps with ( eps * real_1) at 2 by ring.
        apply real_le_mult_pos_le;[apply real_lt_le;auto|].
        apply (real_le_mult_pos_cancel (abs (f1x) + real_1));auto.
        rewrite real_mult_assoc, (real_mult_comm (abs (f1x))), <-real_mult_assoc, real_mult_inv, !real_mult_unit.
        add_both_side_by (-abs (f1x)).
        apply real_lt_le;apply real_1_gt_0.
    - apply (real_le_le_le _ (abs (f2y) * eps1)).
      + apply real_le_mult_pos_le; [apply abs_pos |].
        pose proof (real_le_le_le _ _ _ H2 (real_min_snd_le eps0 eps1)).
        pose proof (real_le_le_le _ _ _ (real_max_fst_ge  (dist f1x f1y) (dist f2x f2y)) H5).
        exact H6.
      + rewrite Heqeps1.
        rewrite diff.
        apply half_le_le.
        unfold real_div.
        rewrite <-real_mult_assoc, real_mult_comm, <-real_mult_assoc, real_mult_comm.
        replace eps with ( eps * real_1) at 2 by ring.
        apply real_le_mult_pos_le;[apply real_lt_le;auto|].
        apply (real_le_mult_pos_cancel (abs (f2x) + real_1));auto.
        rewrite real_mult_assoc, (real_mult_comm (abs (f2y))), <-real_mult_assoc, real_mult_inv, !real_mult_unit.
        apply (real_le_le_le _ (abs f2x + eps0)).
        apply dist_bound.
        pose proof (real_le_le_le _ _ _ H2 (real_min_fst_le eps0 eps1)).
        pose proof (real_le_le_le _ _ _ (real_max_snd_ge  (dist f1x f1y) (dist f2x f2y)) H5).
        exact H6.
        apply real_le_plus_le.
        rewrite Heqeps0.
        apply Minmax.real_min_fst_le.
    -
      apply Nabla_unit_mono in H4.
      injection H4; intros; auto.
    -
      apply Nabla_unit_mono in H3.
      injection H3; intros; auto.
  Defined.
  
End ClassicalContinuityRealOps.


Section ClassicalDerivatives.
  Definition derivative_pt (f: Real -> pc Real) (gx : Real) x :=
    defined (f x) /\
      forall eps, eps > real_0 ->
                  exists delta, delta > real_0 /\
                                  forall y fx fy,
                                    dist x y <= delta ->
                                    defined_to (f x) fx -> defined_to (f y) fy ->
                                    abs (fy - fx - gx * (y -x)) <= eps * abs(y-x) .

  Definition cderivative (f g : Real -> pc Real) x0 r :=
    forall x, exists gx, defined_to (g x) gx /\  dist x x0 <= r -> derivative_pt f gx x.

  Fixpoint nth_derivative (f g : Real -> pc Real) x0 r n :=
    match n with
    | 0 => forall x, dist x x0 < r /\ defined (f x) -> forall y, defined_to (f x) y -> defined_to (g x) y
    | S n' => exists f', cderivative f f' x0 r /\ nth_derivative f' g x0 r n'
    end.

End ClassicalDerivatives.

Section ConstructiveVersions.
  Definition continuous (f: Real -> Real) x := forall eps, eps > real_0 -> {d : Real | d > real_0 /\ forall y, dist x y <= d -> dist (f x) (f y) <= eps}.

  Lemma continuous_ccontinuous f x : continuous f x -> @cont_at _ real_metric_space _ real_metric_space (fun x => Nabla_unit _ (Some (f x))) x.
  Proof.
    intros H.
    split.
    exists (f x).
    apply eq_refl. 

    intros.
    destruct (H eps) as [delta [H1 H2]];auto.
    exists delta;split;auto.
    intros.
    apply Nabla_unit_mono in H4, H5.
    injection H4; intros; injection H5; intros.
    rewrite <-H6, <-H7.
    apply H2.
    auto.
  Qed.
End ConstructiveVersions.

Section Examples.
  (* Definition sqrt: cfun. *)
  (* Proof. *)
  (*   exists (fun xy => (snd xy >= real_0) /\ (snd xy * snd xy) = fst xy ). *)
  (*   simpl. *)
  (*   intros x y1 y2 [[H1 H2] [H1' H2']]. *)
  (*   assert (forall z, z*z = real_0 -> z = real_0). *)
  (*   { *)
  (*     intros. *)
  (*     destruct (real_total_order z real_0) as [Z| [-> | Z]];auto; apply (real_eq_mult_cancel z); try rewrite H;try ring. *)
  (*     apply real_lt_neq;auto. *)
  (*     apply real_gt_neq;auto. *)
  (*   } *)
  (*   destruct H1;destruct H1'. *)
  (*   - apply real_pos_square_eq_eq; [| | rewrite H2, H2'];auto. *)
  (*   -  rewrite <-H1. *)
  (*      apply H. *)
  (*      rewrite H2. *)
  (*      rewrite <-H2'. *)
  (*      rewrite <-H1. *)
  (*      ring. *)
  (*   -  rewrite <-H0. *)
  (*      rewrite H;auto. *)
  (*      rewrite H2'. *)
  (*      rewrite <-H2. *)
  (*      rewrite <-H0;ring. *)
  (*   - rewrite <-H0, <-H1;auto. *)
  (* Qed. *)
End Examples.
