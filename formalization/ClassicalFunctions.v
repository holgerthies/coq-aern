Require Import Real.
Require Import Euclidean.
Require Import List.
Require Import Psatz.
Import ListNotations.
Require Import Poly.

#[local] Notation "^K" := (@K Poly.types) (at level 0).
#[local] Notation "^M" := (@M Poly.types) (at level 0).
#[local] Notation "^Real" := (@Real Poly.types) (at level 0).
 Declare Scope cfun_scope.
 Delimit Scope cfun_scope with cfun.
Section ClassicalFunctions.
  Definition cfun := {f : (^Real * ^Real) -> Prop | forall x y1 y2, f (x,y1) /\ f (x,y2) -> y1 = y2}.
  Definition img (f : cfun) x y := (pr1  _ _ f (x,y)).

  Definition sumcf (f g : cfun) : cfun.
  Proof.
    exists (fun xy => exists y z, img f (fst xy) y /\ img g (fst xy) z /\ ((snd xy) = y + z)).
    intros.
    destruct f,g.
    simpl in *.
    destruct H as [[y [z [H1 [H1' ->]]]] [y' [z' [H2 [H2' ->]]]]].
    rewrite (e x y y');auto.
    rewrite (e0 x z z');auto.
 Defined.

  Lemma sumcf_spec f g: forall x y, img (sumcf f g) x y <-> exists y1 y2, img f x y1 /\ img g x y2 /\ y = y1 + y2.
  Proof.
    intros.
    unfold sumcf.
    simpl.
    split; auto.
  Qed.
  Definition mulcf (f g : cfun) : cfun.
  Proof.
    exists (fun xy => exists y z, img f (fst xy) y /\ img g (fst xy) z /\ ((snd xy) = y * z)).
    intros.
    destruct f,g.
    simpl in *.
    destruct H as [[y [z [H1 [H1' ->]]]] [y' [z' [H2 [H2' ->]]]]].
    rewrite (e x y y');auto.
    rewrite (e0 x z z');auto.
 Defined.

  Lemma mulcf_spec f g: forall x y, img (mulcf f g) x y <-> exists y1 y2, img f x y1 /\ img g x y2 /\ y = y1 * y2.
  Proof.
    intros.
    unfold mulcf.
    simpl.
    split; auto.
  Qed.

  Definition dom f x := exists fx, img f x fx.

  Lemma dom_sum f1 f2 x : dom (sumcf f1 f2) x <-> dom f1 x /\ dom f2 x.
  Proof.
    split;[intros H | intros [[y1 H1] [y2 H2]]].
    destruct H as [y [y1 [y2 [H1 [H2 H3]]]]].
    split; [exists y1 | exists y2];auto.
    exists (y1 + y2).
    exists y1; exists y2; auto.
 Qed.
 Lemma dom_mul f1 f2 x : dom (mulcf f1 f2) x <-> dom f1 x /\ dom f2 x.
  Proof.
    split;[intros H | intros [[y1 H1] [y2 H2]]].
    destruct H as [y [y1 [y2 [H1 [H2 H3]]]]].
    split; [exists y1 | exists y2];auto.
    exists (y1 * y2).
    exists y1; exists y2; auto.
  Qed.

  Lemma cfun_spec (f : cfun) x y1 y2 : img f x y1 -> img f x y2 -> y1 = y2.
  Proof.
    intros H1 H2.
    destruct f;simpl in *.
    apply (e x).
    auto.
 Qed.

 Definition fun_to_cfun (f : ^Real -> ^Real) : cfun.
 Proof.
   exists (fun xy => (f (fst xy)) = (snd xy)).
   intros.
   simpl in H.
   destruct H as [<- <-].
   reflexivity.
 Defined.

 Lemma fun_to_cfun_spec f : forall x y, img (fun_to_cfun f) x y <-> f x = y.
 Proof.
   intros.
   split;auto.
 Qed.

 Lemma fun_to_cfun_dom f : forall x, dom (fun_to_cfun f) x.
 Proof.
  intros.
  exists (f x);simpl;auto.
 Qed.
End ClassicalFunctions.

Notation "f + g" := (sumcf f g) : cfun_scope.
Notation "f * g" := (mulcf f g) : cfun_scope.

Section ClassicalContinuity.
  Definition ccontinuous (f: cfun) x := dom f x /\ forall eps, eps > real_0 -> exists delta, delta > real_0 /\ forall y fx fy, img f x fx ->  img f y fy  -> dist x y <= delta -> dist (fx) (fy) <= eps.

  Lemma continuous_prod f1 f2 x: ccontinuous f1 x -> ccontinuous f2 x -> ccontinuous (mulcf f1 f2) x.
  Proof.
    intros [D1 H1] [D2 H2].
    split; [apply dom_mul;split;auto |].
    intros eps H.
    destruct D1 as [f1x dom1].
    destruct D2 as [f2x dom2].
    pose proof (abs_plus_1_gt_0 f1x).
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
    assert (abs (f2x) + eps0  > real_0) as f2xepsgt0.
    {
      
      apply (real_lt_le_lt _ (real_0 + eps0)); [rewrite real_plus_unit; auto |].
      apply real_le_le_plus_le; [apply abs_pos|apply real_le_triv].
    }
    destruct (H2 _ eps0gt0) as [d0 [d0gt0 D0]].
    pose proof (abs_plus_1_gt_0 f2x).
    remember (eps / (real_gt_neq _ _ H3) / real_2_neq_0) as eps1.
    assert (eps1 > real_0) as eps1gt0.
    {
    rewrite Heqeps1.
    apply real_half_gt_zero.
    unfold real_div.
    apply real_lt_pos_mult_pos_pos;auto.
    apply real_pos_inv_pos;auto.
    }
    assert (forall a b c (cn0 : c <> real_0), a * (b / cn0) = (a*b)/ cn0) as diff by (intros;unfold real_div;ring_simplify;auto).
    destruct (H1 _ eps1gt0) as [d1 [d1gt0 D1]].
    exists (Minmax.real_min d0 d1).
    split; [destruct (Minmax.real_min_cand d0 d1) as [-> | ->];auto|].
    intros.
    replace fx with (f1x *f2x).
    destruct (proj1 (dom_mul f1 f2 y)) as [[f1y F1Y] [f2y F2Y]]; [exists fy;auto|].
    replace fy with (f1y *f2y).
    unfold dist.
    replace (f1x * f2x - f1y * f2y) with ((f1x * (f2x -  f2y)) + (f2y * ( f1x - f1y))) by ring.
    replace eps with (eps / real_2_neq_0 + eps / real_2_neq_0) by apply half_twice.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    apply real_le_le_plus_le;rewrite abs_mult.
    - apply (real_le_le_le _ (abs (f1x) * eps0)).
      + apply real_le_mult_pos_le; [apply abs_pos |].
        apply (D0 _ _ _ dom2 F2Y).
        apply (real_le_le_le _ _ _ H6).
        apply Minmax.real_min_fst_le.
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
        apply (D1 _ _ _ dom1 F1Y).
        apply (real_le_le_le _ _ _ H6).
        apply Minmax.real_min_snd_le.
      + rewrite Heqeps1.
        rewrite diff.
        apply half_le_le.
        unfold real_div.
        rewrite <-real_mult_assoc, real_mult_comm, <-real_mult_assoc, real_mult_comm.
        replace eps with ( eps * real_1) at 2 by ring.
        apply real_le_mult_pos_le;[apply real_lt_le;auto|].
        apply (real_le_mult_pos_cancel (abs (f2x) + real_1));auto.
        rewrite real_mult_assoc, (real_mult_comm (abs (f2y))), <-real_mult_assoc, real_mult_inv, !real_mult_unit.
        specialize (D0 _ _ _ dom2 F2Y).
        apply (real_le_le_le _ (abs f2x + eps0)).
        apply dist_bound.
        apply D0.
        apply (real_le_le_le _ _ _ H6).
        apply Minmax.real_min_fst_le.
        apply real_le_plus_le.
        rewrite Heqeps0.
        apply Minmax.real_min_fst_le.
   - apply mulcf_spec in H5.
     simpl in *.
     destruct H5 as [f1y' [f2y' [I1' [I2' I3']]]].
     rewrite I3'.
     rewrite (cfun_spec _ _ _ _ I1' F1Y).
     rewrite (cfun_spec _ _ _ _ I2' F2Y).
     reflexivity.
   - apply mulcf_spec in H4.
     simpl in *.
     destruct H4 as [f1x' [f2x' [I1' [I2' I3']]]].
     rewrite I3'.
     rewrite (cfun_spec _ _ _ _ I1' dom1).
     rewrite (cfun_spec _ _ _ _ I2' dom2).
     reflexivity.
  Defined.

  Lemma continuous_sum f1 f2 x : ccontinuous f1 x -> ccontinuous f2 x -> ccontinuous (sumcf f1 f2) x.
  Proof.
    intros [dom1 H1] [dom2 H2].
    split; [apply dom_sum;split;auto |].
    intros eps H.
    assert (eps / real_2_neq_0 > real_0) by (apply real_half_gt_zero;auto).
    destruct (H1 _ H0) as [d [D0 D1]].
    destruct (H2 _ H0) as [d' [D0' D1']].
    exists (Minmax.real_min d d').
    split; [destruct (Minmax.real_min_cand d d') as [-> | ->];auto|].
    intros.
    destruct dom1 as [f1x dom1].
    destruct dom2 as [f2x dom2].
    replace fx with (f1x + f2x).
    apply sumcf_spec in H4.
    destruct H4 as [f1y [f2y [I1 [I2 I3]]]].
    simpl in *.
    rewrite I3.
    apply (real_le_le_le _ _ _ (dist_plus_le _ _ _ _)).
    rewrite <-half_twice.
    specialize (D1 _ _ _ dom1 I1).
    specialize (D1' _ _ _ dom2 I2).
    apply real_le_le_plus_le; [apply D1 | apply D1'];apply (real_le_le_le _ _ _ H5).
    apply Minmax.real_min_fst_le.
    apply Minmax.real_min_snd_le.
    apply sumcf_spec in H3.
    simpl in *.
    destruct H3 as [f1x' [f2x' [I1 [I2 ->]]]].
     rewrite (cfun_spec _ _ _ _ I1 dom1).
     rewrite (cfun_spec _ _ _ _ I2 dom2).
     reflexivity.
  Defined.

End ClassicalContinuity.

Section ClassicalDerivatives.
  Definition derivative_pt (f: cfun) (gx : Real) x := dom f x /\ forall eps, eps > real_0 -> exists delta,  delta > real_0 /\ forall y fx fy, dist x y <= delta -> img f x fx -> img f y fy  -> abs (fy - fx - gx * (y -x)) <= eps * abs(y-x) .

  Definition cderivative (f: cfun) (g : cfun) x0 r := forall x, exists gx, img g x gx /\  dist x x0 <= r -> derivative_pt f gx x.

  Fixpoint nth_derivative (f: cfun) (g : cfun) x0 r n :=
    match n with
    | 0 => forall x, dist x x0 < r /\ dom f x -> forall y, img f x y -> img g x y
    | S n' => exists f', cderivative f f' x0 r /\ nth_derivative f' g x0 r n'
    end.

  (* Lemma approx_rolle (f : cfun) f' x0 r x y fx : x <= y -> cderivative f f' x0 r -> dist x x0 <= r -> dist y x0 <= r -> img f x fx -> img f y fx ->  forall n, exists z fz', img f' z fz' /\ abs fz' <= prec n. *)
  (* Admitted. *)
  (* Lemma rolle (f: cfun) f' x0 r x y fx : x <= y -> cderivative f f' x0 r -> dist x x0 <= r -> dist y x0 <= r -> img f x fx -> img f y fx -> exists z, img f' z real_0. *)
  (* Proof. *)
  (*   intros. *)
  (* Admitted. *)


End ClassicalDerivatives.

Section ConstructiveVersions.
  Definition continuous (f: Real -> Real) x := forall eps, eps > real_0 -> {d : Real | d > real_0 /\ forall y, dist x y <= d -> dist (f x) (f y) <= eps}.

  Lemma continuous_ccontinuous f x : continuous f x -> ccontinuous (fun_to_cfun f) x.
  Proof.
    intros H.
    split; [apply fun_to_cfun_dom |].
    intros.
    destruct (H eps) as [delta [H1 H2]];auto.
    exists delta;split;auto.
    intros.
    rewrite <-(proj1 (fun_to_cfun_spec f _ _) H3).
    rewrite <-(proj1 (fun_to_cfun_spec f _ _) H4).
    apply H2;auto.
 Qed.
End ConstructiveVersions.

Section Examples.
Definition sqrt: cfun.
Proof.
  exists (fun xy => (snd xy >= real_0) /\ (snd xy * snd xy) = fst xy ).
  simpl.
  intros x y1 y2 [[H1 H2] [H1' H2']].
  assert (forall z, z*z = real_0 -> z = real_0).
  {
    intros.
    destruct (real_total_order z real_0) as [Z| [-> | Z]];auto; apply (real_eq_mult_cancel z); try rewrite H;try ring.
    apply real_lt_neq;auto.
    apply real_gt_neq;auto.
  }
  destruct H1;destruct H1'.
  - apply real_pos_square_eq_eq; [| | rewrite H2, H2'];auto.
  -  rewrite <-H1.
     apply H.
     rewrite H2.
     rewrite <-H2'.
     rewrite <-H1.
     ring.
  -  rewrite <-H0.
     rewrite H;auto.
     rewrite H2'.
     rewrite <-H2.
     rewrite <-H0;ring.
  - rewrite <-H0, <-H1;auto.
Qed.
End Examples.
