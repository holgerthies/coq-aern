Require Import Real.
Require Import RealAssumption.
Require Import MultiLimit.
Require Import Euclidean.
Require Import Nnat.
Require Import ArithRing.
Require Export Ring Field.
Require Import Psatz.
Require Import List.
Import ListNotations.
Require Import ClassicalAnalysis.
Require Import ClassicalPartialReals.
Require Import Poly.
Require Import Taylormodel.


Section ToMove.

 Lemma min_le_both r1 r2 : Minmax.real_min r1 r2 <= r1 /\ Minmax.real_min r1 r2 <= r2.
 Proof.
   split.
   apply Minmax.real_min_fst_le.
   apply Minmax.real_min_snd_le.
 Qed.
  Lemma Npow2_pow n : Npow2 n = (2 ^ n).
  Proof.
    induction n.
    simpl;lia.
    simpl.
    rewrite IHn.
    lia.
  Qed.

 Lemma npow_monotone x n1 n2 : real_1 <= x -> (n1 <= n2)%nat -> npow x n1 <= npow x n2.
 Proof.
   revert n2.
   induction n1.
   - intros.
     pose proof (npow_nonneg_le real_1 x n2 (real_lt_le _ _ real_1_gt_0) H).
     rewrite npow_1 in H1.
     exact H1.
   - intros.
     destruct n2.
     rewrite Nat.le_0_r in H0.
     rewrite H0.
     apply real_le_triv.
     apply Nat.le_succ_le_pred in H0.
     simpl in H0.
     simpl.
     apply real_le_mult_pos_le.
     apply (real_le_le_le _ _ _ (real_lt_le _ _ real_1_gt_0));auto.
     apply IHn1;auto.
 Qed.

 Lemma pow2_max M1 M2: npow real_2 M1 <= npow real_2 (max M1 M2) /\ npow real_2 M2 <= npow real_2 (max M1 M2).
 Proof.
   split;(apply npow_monotone; [apply real_lt_le; apply real_2_gt_1 | ]).
   apply Nat.le_max_l.
   apply Nat.le_max_r.
Qed.
 
 Lemma inv_lt_gt x y (p1 : x<>real_0) (p2 : y <> real_0)  : real_0 < x -> x < y -> (/ p2) < (/ p1) .
 Proof.
     intros.
     apply (real_lt_mult_pos_cancel x);auto.
     rewrite real_mult_inv.
     apply (real_lt_mult_pos_cancel y);[ apply (real_lt_lt_lt _ x);auto|].
     rewrite real_mult_comm, <-real_mult_assoc, (real_mult_comm y), real_mult_inv.
     ring_simplify;auto.
 Qed.

 Lemma inv_le_ge x y (p1 : x<>real_0) (p2 : y <> real_0)  : real_0 < x -> x <= y -> (/ p2) <= (/ p1) .
 Proof.
   intros.
   destruct H0.
   apply real_lt_le.
   apply inv_lt_gt;auto.
   revert p1.
   rewrite H0.
   intros.
   assert (p1 = p2) as -> by apply irrl.
   apply real_le_triv.
 Qed.
End ToMove.

Section Series.

  Fixpoint partial_sum (a : nat -> Real) n :=
    match n with
    | 0 => (a 0)
    | (S n') => (a n)+partial_sum a n'
    end.

  Definition is_sum (a : nat -> Real) x := forall eps, eps > real_0 -> exists N, forall n, (n >= N)%nat -> dist (partial_sum a n) x <= eps.

  Lemma sum_is_unique a x y : is_sum a x -> is_sum a y -> x = y.
  Proof.
   intros. 
   apply dist_zero.
   destruct (real_total_order (dist x y) real_0) as [c1 | [c2 | c3]];auto.
   apply real_gt_nle in c1;contradict c1;apply dist_pos.
   destruct (real_Archimedean _ c3) as [m M].
   apply real_gt_nle in M.
   contradict M.
   destruct (H (prec (m+1))) as [n1 N1]; [apply prec_pos|].
   destruct (H0 (prec (m+1))) as [n2 N2]; [apply prec_pos|].
   apply (real_le_le_le _ _ _ (dist_tri _ (partial_sum a (n1+n2)%nat) _)).
   rewrite dist_symm, <-prec_twice.
   apply real_le_le_plus_le;[apply N1|apply N2];lia.
  Qed.  

  Lemma tpmn_sum a : (forall n, abs (a n) <= prec n) -> forall n, abs (partial_sum  a n) <= real_2 - prec n.
  Proof.
    intros H n.
    induction n.
    - unfold real_2.
      simpl.
      apply (real_le_le_le _ _ _ (H 0)).
      simpl.
      ring_simplify.
      apply real_eq_le;auto.
   - simpl.
     apply (real_le_le_le _ _ _ (abs_tri _ _)).
     apply (real_le_le_le _ _ _ (real_le_le_plus_le _ _ _ _ (H (S n)) IHn) ).
     rewrite <-(prec_twice n) at 1.
     rewrite Nat.add_1_r.
     ring_simplify.
     add_both_side_by (prec (S n)).
     simpl.
     ring_simplify.
     apply real_le_triv.
  Qed.

  Lemma tmpn_cauchy a m : (forall n,  abs (a (n+m)%nat) <= prec n) -> is_fast_cauchy (fun n => partial_sum a (n+m)%nat).
  Proof.
    intros H.
    apply consecutive_converging_fast_cauchy.
    intros n.
    unfold dist.
    simpl.
    assert (forall x y, (x - (y  + x)) = -y) as -> by (intros; ring).
    rewrite <-abs_symm.
    assert (S (n+m) = (S n)+m)%nat as -> by lia.
    apply H.
 Qed.

End Series.


Section Powerseries.

  Definition ps a x n := (a n) * npow x n. 

  Definition to_poly (a : nat -> ^Real) n := map a (seq 0 (S n)).


 Lemma eval_series_to_poly a x n i:  (i <= n)%nat -> eval_poly (to_poly a n) x = eval_poly (to_poly a i) x + (npow x (S i))*(eval_poly (map a (seq (S i) (n-i)%nat)) x).
  Proof.
    revert n.
    induction i; [intros;simpl;rewrite Nat.sub_0_r;ring | ].
    intros.
    rewrite (IHi (S i));try lia.
    rewrite IHi; try lia.
    replace (S i - i)%nat with 1 by lia.
    replace (n-i)%nat with (S (n - S i))%nat  by lia.
    simpl.
    ring.
Qed.

  Lemma eval_series_partial_sum a x n : eval_poly (to_poly a n) x = partial_sum (ps a x) n.
  Proof.
    unfold ps.
    induction n; [simpl;ring|].
    rewrite (eval_series_to_poly a x (S n) n); try lia.
    replace (S n - n)%nat with 1 by lia.
    simpl.
    rewrite <-IHn.
    destruct n;simpl;ring.
  Qed.

  Definition powerseries_pc (a : nat -> ^Real) : ^Real -> pc ^Real.
  Proof.
    apply pc_ana_fun_to_pc_fun.
    exists (fun xy => is_sum (ps a (fst xy)) (snd xy)).
    intros x y1 y2.      
    apply sum_is_unique.
  Defined.

  Lemma powerseries_pc_spec a x y: defined_to ((powerseries_pc a) x) y <-> is_sum (ps a x) y.
  Proof.
  Admitted.

  Definition bounded_seq (a : nat -> Real) M {r : Real} (H : real_0 < r)  :=  forall n, abs (a n) <= Nreal M * (npow (real_inv (real_gt_neq _ _ H))  n).
                                                                                   
 Lemma seq_bound_larger_M a M1 M2 r p: (M1 <= M2)%nat -> (@bounded_seq a M1 r p) -> (@bounded_seq a M2 r p).
 Proof.
   intros P1 P2 n.
   apply (real_le_le_le _ (Nreal M1 * npow (/ real_gt_neq r real_0 p) n));auto.
   rewrite !(real_mult_comm (Nreal _)).
   apply real_le_mult_pos_le.
   - apply npow_nonneg.
     apply real_lt_le.
     apply real_pos_inv_pos;auto.
  - apply Nreal_monotone;auto.
 Qed.

 Lemma seq_bound_smaller_r a M r1 p1 r2 p2: (r2 <= r1) -> (@bounded_seq a M r1 p1) -> (@bounded_seq a M r2 p2).
 Proof.
   intros P1 P2 n.
   apply (real_le_le_le _ ((Nreal M) * npow (/ real_gt_neq r1 real_0 p1) n));auto.
   apply real_le_mult_pos_le.
   - replace real_0 with (Nreal 0) by auto.
     apply Nreal_monotone;lia.
   - apply npow_nonneg_le; [apply real_lt_le;apply real_pos_inv_pos|];auto.
     apply inv_le_ge;auto.
 Qed.    
 Record bounded_ps : Type := mk_bounded_ps
                               {
                                 series : nat -> Real;
                                 bounded_ps_M : nat;
                                 bounded_ps_r :Real;
                                 bounded_ps_rgt0 : bounded_ps_r > real_0;
                                 bounded_ps_bounded: bounded_seq series bounded_ps_M bounded_ps_rgt0 
                               }.

  Lemma bounded_ps_change_Mr (a : bounded_ps) M r : (bounded_ps_M a <= M)%nat -> (real_0 < r <= bounded_ps_r a) -> {b : bounded_ps | series a = series b /\ bounded_ps_M b = M /\ bounded_ps_r b = r}.
  Proof.
  intros.
  destruct H0.
  destruct a.
  simpl in *.
  pose proof (seq_bound_larger_M _ _ _ _ _ H bounded_ps_bounded0).
  pose proof (seq_bound_smaller_r _ _ _ _ _ H0 H1 H2).
  exists (mk_bounded_ps _ _ _ _ H3);auto.
  Qed.

  Lemma increment_num M n : (Nreal M * prec (n+(S (Nat.log2 M)))) < prec n. 
  Proof.
    rewrite prec_hom, real_mult_comm, real_mult_assoc.
    replace (prec n) with ( prec n * real_1) at 2 by ring.
    apply real_lt_mult_pos_lt; try apply prec_pos.
    rewrite <-(prec_Npow2_unit (S (Nat.log2 M))).
    apply real_lt_mult_pos_lt; try apply prec_pos.
    apply Nreal_strict_monotone.
    rewrite Npow2_pow.
    destruct M;[simpl;lia | ].
    apply Nat.log2_spec;lia.
 Qed.
  
 Definition eval_radius (a : bounded_ps) := ((bounded_ps_r a) / real_2_neq_0).

 Definition eval_seq (a : bounded_ps) x:= (fun n => eval_poly (to_poly (series a) (n+(S (Nat.log2 (bounded_ps_M a))))%nat) x).


  Lemma is_fast_cauchy_eval (a : bounded_ps) x : abs x <= eval_radius a -> is_fast_cauchy (eval_seq a x).
  Proof.
    unfold eval_radius.
    destruct a as [a M r rgt0 B].
    simpl bounded_ps_r.
    intros H n m.
    unfold eval_seq.
    rewrite !eval_series_partial_sum.
    apply tmpn_cauchy.
    intros.
    unfold ps.
    unfold bounded_seq in B.
    rewrite abs_mult.
    apply real_lt_le.
    apply (real_le_lt_lt _ (Nreal M * prec (n0+(S (Nat.log2 M))))); [|apply increment_num].
   apply (real_le_le_le _ (((Nreal M) * (npow (/ (real_gt_neq _ _ rgt0)) (n0 + (S (Nat.log2 M)))%nat) * (npow (r / real_2_neq_0) (n0+S (Nat.log2 M))%nat)))).
   - apply real_le_mult_pos_le_le; try apply abs_pos; try apply B.
     rewrite abs_npow_distr.
     apply npow_nonneg_le;auto.
     apply abs_pos.
   - rewrite real_mult_assoc.
     apply real_le_mult_pos_le; [destruct M;[apply real_le_triv|apply real_lt_le;apply Nreal_pos;lia]|].
    rewrite npow_mult.
    unfold real_div.
    rewrite <-real_mult_assoc.
    assert (/ real_gt_neq r real_0 rgt0 * r = real_1) as -> by apply real_mult_inv.  
    rewrite real_mult_unit.
    rewrite npow_prec.
    apply real_le_triv.
 Qed.


 Lemma fast_limit_limit a x y : is_fast_limit y (eval_seq a x) -> is_sum (ps (series a) x) y.
 Proof.
   intros H eps epsgt0.
   destruct (real_Archimedean _ epsgt0) as [n N].
   exists (S n+(S (Nat.log2 (bounded_ps_M a))))%nat.
   intros m M.
   rewrite <-eval_series_partial_sum.
   rewrite dist_symm.
   apply real_lt_le.
   apply (real_le_lt_lt _ (prec n) _ );auto.
   assert (m = S n + (m-S n-S (Nat.log2 (bounded_ps_M a))) + S (Nat.log2 (bounded_ps_M a)))%nat as -> by lia.
   apply (real_le_le_le _ _ _ (H _)).
   apply real_lt_le.
   apply prec_monotone.
   lia.
 Qed.

 Lemma eval_val (a : bounded_ps) x : abs x <= eval_radius a -> {y | is_fast_limit y (eval_seq a x)}.
 Proof.
   intros.
   destruct (real_limit (eval_seq a x)).
   apply is_fast_cauchy_eval;auto.
   exists x0.
   apply i.
 Qed.

 Definition to_taylor_model (a : bounded_ps) (n : nat) : taylor_model (powerseries_pc (series a)).
 Proof.
   apply (mk_tm _ (to_poly (series a) (n+(S (Nat.log2 (bounded_ps_M a))))%nat) (eval_radius a) (prec n)).
   intros.
   apply powerseries_pc_spec in H0.
   destruct (eval_val _ _ H) as [y L].
   rewrite (sum_is_unique _ _ y H0); [|apply fast_limit_limit];auto.
   apply L.
 Defined.
 
 Lemma to_taylor_model_series a n x : (eval_tm (to_taylor_model a n) x) = eval_seq a x n.
 Proof. auto. Qed.

 Definition is_ps_for f a := forall x, abs x <= (eval_radius a) -> defined (f x) -> powerseries_pc (series a) x = f x.

 Definition is_ps_for_M_indep f a b : series a = series b -> bounded_ps_r b <= bounded_ps_r a -> is_ps_for f a ->  is_ps_for f b.
 Proof.
   unfold is_ps_for.
   intros.
   rewrite <- H1,H;auto.
   apply (real_le_le_le _ (eval_radius b));auto.
   apply half_le_le;auto.
 Qed.
 Lemma to_tm_approx (a : bounded_ps) : polynomial_approx (powerseries_pc (series a)) (to_taylor_model a) (eval_radius a).
 Proof.
   split;apply real_le_triv.
 Qed.

 Lemma approx_is_ps f a : (forall n x fx, abs x <= eval_radius a -> defined_to (f x) fx -> dist (eval_tm (to_taylor_model a n) x) fx <= prec n) -> is_ps_for f a.
 Proof.
   intros H x X D.
   destruct D as [y Y].
   assert (defined_to (powerseries_pc (series a) x) y).
   {
     apply powerseries_pc_spec.
     apply fast_limit_limit.
     intros n.
     rewrite dist_symm.
     rewrite <-to_taylor_model_series.
     apply H;auto.
     
   }
   rewrite Y,H0;auto.
 Qed.

 Lemma eval_seq_converges a n x y : abs x <= eval_radius a -> defined_to (powerseries_pc (series a) x) y -> dist (eval_seq a x n) y <= prec n.
 Proof.
   intros.
   apply powerseries_pc_spec in H0.
   destruct (eval_val _ _ H) as [z Z].
   rewrite (sum_is_unique  _ _ z H0);try rewrite dist_symm;auto.
   intros eps epsgt0.
   destruct (real_Archimedean _ epsgt0) as [m M].
   unfold is_fast_limit in Z.
   unfold eval_seq in Z.
   exists ((S m) + S (Nat.log2 (bounded_ps_M a)))%nat.
   intros k K.
   apply real_lt_le.
   rewrite <-eval_series_partial_sum.
   apply (real_lt_lt_lt _ (prec m));auto.
   replace k with ((S m + (k - (S m) - S (Nat.log2 (bounded_ps_M a))))+S (Nat.log2 (bounded_ps_M a)))%nat by lia.
   apply (real_le_lt_lt _ (prec (S m + (k - (S m) - S (Nat.log2 (bounded_ps_M a)))))); try (apply prec_monotone;lia).
   rewrite dist_symm.
   apply Z.
 Qed.
End Powerseries.
Section Addition.

 Definition sum (a : nat -> Real) (b: nat -> Real) := fun n => (a n) + (b n).

 Lemma to_poly_S a n : to_poly a (S n) = to_poly a n ++ [a (S n)].
 Proof.
    unfold to_poly.
    rewrite seq_S, map_app;auto.
 Qed.

 Lemma length_to_poly a n : length (to_poly a n) = (S n).
 Proof.
   induction n;auto.
   rewrite to_poly_S.
   rewrite app_length.
   rewrite IHn;simpl;lia.
 Qed.
 Lemma sum_to_poly_sum_poly a b : forall n, to_poly (sum a b) n = sum_polyf (to_poly a n) (to_poly b n).
 Proof.
   intros.
   induction n;auto.
   rewrite !to_poly_S.
   rewrite IHn.
   apply (nth_ext _ _ real_0 real_0).
   simpl;rewrite !app_length, !length_sum_coefficients, !app_length, !map_length.
   simpl;lia.
   intros m M.
   rewrite app_length, length_sum_coefficients,!length_to_poly, Nat.max_id in M.
   simpl in M.
   rewrite sum_coefficient_nth.
   apply Nat.lt_le_pred in M.
   apply Nat.le_lteq in M.
   simpl in M.
   destruct M.
   rewrite !app_nth1; [apply sum_coefficient_nth| | |rewrite length_sum_coefficients ]; try (rewrite length_to_poly;lia).
   rewrite H.
   rewrite !app_nth2; try rewrite length_sum_coefficients; rewrite !length_to_poly;try lia.
   rewrite Nat.max_id.
   replace (n+1 - S n)%nat with 0 by lia.
   simpl;auto.
Qed.

 Definition sum_pc (a b : bounded_ps) := fun x => (powerseries_pc (series a) x + powerseries_pc (series b) x)%pcreal.



 
 Definition sum_ps (a b : bounded_ps) : {c : bounded_ps | is_ps_for (sum_pc a b) c }.
 Proof.
   destruct a as [a' M1 r1 r1gt0 Ba] eqn:A.
   destruct b as [b' M2 r2 r2gt0 Bb] eqn:B.
   pose proof (min_le_both r1 r2) as [R1 R2]. 
   remember (Minmax.real_min r1 r2) as r.
   assert (real_0 < r) by (rewrite Heqr;destruct (Minmax.real_min_cand r1 r2) as [-> | ->];auto).
   destruct (bounded_ps_change_Mr a (S (M1+M2))%nat r) as [a0 [A1 [A2 A3]]];try rewrite A;simpl;[lia|split|];auto.
   destruct (bounded_ps_change_Mr b (S (M1+M2))%nat r) as [b0 [B1 [B2 B3]]];try rewrite B;simpl;[lia|split|];auto.
   assert (bounded_seq (sum a' b') (M1+M2)%nat H).
   { intros n.
     apply (real_le_le_le _ _ _ (abs_tri (a' n) (b' n))).
     rewrite Nreal_hom.
     rewrite real_mult_comm, real_mult_plus_distr.
     apply real_le_le_plus_le;rewrite real_mult_comm;auto.
     apply (seq_bound_smaller_r _ _ r1 r1gt0);auto.
     apply (seq_bound_smaller_r _ _ r2 r2gt0);auto.
  }
  remember (mk_bounded_ps _ _ _ _ H0) as c.
   exists c.
   destruct (bounded_ps_change_Mr c (2 * (S (bounded_ps_M c)))%nat (bounded_ps_r c)) as [c' [H1 [H2 H3]]];[lia| destruct c;simpl;split; [auto|apply real_le_triv]|].
   apply (is_ps_for_M_indep _ c');try apply real_eq_le;auto.
   apply approx_is_ps.
   intros.
   unfold to_taylor_model, eval_tm; simpl tm_poly.
   rewrite <-H1.
   rewrite H2.
   rewrite Heqc.
   simpl series; simpl bounded_ps_M.
   rewrite Nat.log2_double;try lia.
   rewrite <-Nat.add_succ_comm.
   rewrite sum_to_poly_sum_poly.
   rewrite sum_polyf_spec.
   apply pc_lift2_iff in H5.
   simpl in H5.
   destruct H5 as [y1 [y2 [D1 [D2 ->]]]].
   apply (real_le_le_le  _ _ _ (dist_plus_le _ _ _ _)).
   rewrite <-prec_twice.
   apply real_le_le_plus_le.
   - replace (eval_poly (to_poly a' (S n + S (Nat.log2 (S (M1+M2))%nat))) x) with (eval_tm (to_taylor_model a0 (S n)) x).
     rewrite to_taylor_model_series.
     rewrite Nat.add_1_r.
     apply eval_seq_converges.
     apply (real_le_le_le _ _ _ H4).
     unfold eval_radius.
     rewrite H3,A3, Heqc;simpl.
     apply real_le_triv.
     rewrite <-A1, A;simpl;auto.
     unfold to_taylor_model,eval_tm.
     simpl tm_poly.
     rewrite A2, <-A1, A; simpl;auto.
   - replace (eval_poly (to_poly b' (S n + S (Nat.log2 (S (M1+M2))%nat))) x) with (eval_tm (to_taylor_model b0 (S n)) x).
     rewrite to_taylor_model_series.
     rewrite Nat.add_1_r.
     apply eval_seq_converges.
     apply (real_le_le_le _ _ _ H4).
     unfold eval_radius.
     rewrite H3,B3, Heqc;simpl.
     apply real_le_triv.
     rewrite <-B1, B;simpl;auto.
     unfold to_taylor_model,eval_tm.
     simpl tm_poly.
     rewrite B2, <-B1, B; simpl;auto.
 Defined.

End Addition.
Section Derivative.
  Definition derivative_sequence (a : nat -> Real) n := Nreal (n+1) * (a (n+1)%nat).

  Lemma derivative_sequence_spec a : forall n x, derivative (eval_poly (to_poly a (S n))) (eval_poly (to_poly (derivative_sequence a) n)) x.
  Proof.
    intros.
    assert (to_poly (derivative_sequence a) n = derive_poly (to_poly a (S n))) as ->.
    {
      unfold derive_poly.
      destruct (poly_deriv_exists (to_poly a (S n))) as [p' [H1 H2]].
      simpl.
      apply (nth_ext _ _ real_0 real_0).
      - rewrite H1.
        simpl.
        rewrite !map_length.
        rewrite !seq_length;auto.
     - intros m M.
       rewrite H2.
       unfold derivative_sequence, to_poly.
       remember (fun n0 => (Nreal (n0+1)) * (a (n0+1)%nat)) as f.
       rewrite (@nth_indep _ _ _ real_0 (f 0));[| rewrite Heqf;auto].
       unfold to_poly in M.
       rewrite map_length, seq_length in M.
       rewrite (@nth_indep _ _ _ real_0 (a 0));[|rewrite map_length, seq_length;lia].
       rewrite !map_nth.
       rewrite !seq_nth;auto;try lia.
       rewrite Heqf.
       simpl.
       replace (m+1)%nat with (S m) by lia.
       simpl;auto.
    }
    apply derive_poly_spec.
 Qed.


 Lemma derivative_pt_unique f gx gx' x : derivative_pt f gx x -> derivative_pt f gx' x -> gx' = gx.
 Proof.
 Admitted.
 Definition derivative_fun (f : ^Real -> pc ^Real) : (^Real -> pc ^Real).
 Proof.
   apply pc_ana_fun_to_pc_fun.
   exists (fun xy => derivative_pt f (snd xy) (fst xy)).
   simpl.
   intros.
   apply (derivative_pt_unique _ _ _ _ H0 H).
 Qed.
 Lemma derivative_fun_spec f : forall x y, defined_to ((derivative_fun f) x) y <-> derivative_pt f y x.
 Admitted.
  Lemma Nreal_nonneg n : real_0 <= Nreal n.
  Proof.
    destruct n;[apply real_eq_le;simpl;auto|].
    apply real_lt_le.
    apply Nreal_pos.
    lia.
  Qed.

  Lemma derivative_factor_bound : forall n, Nreal (n+1) <= npow real_2 n.
  Proof.
    induction n; [apply real_eq_le;simpl;ring|].
    simpl.
    apply (real_le_le_le _ (real_1 + npow real_2 n)).
    add_both_side_by (-real_1);apply IHn.
    replace (real_2 * npow real_2 n) with (npow real_2 n + npow real_2 n) by (unfold real_2;ring).
    add_both_side_by (- npow real_2 n).
    replace real_1 with (npow real_2 0) by auto.
    apply npow_monotone;try lia.
    apply real_lt_le.
    apply real_2_gt_1.
  Qed.

 Lemma deriv_bounded_ps_bounded_r a m: prec m <= (bounded_ps_r a) ->  {b : bounded_ps | series b = derivative_sequence (series a) /\ ((bounded_ps_M a) <= (bounded_ps_M b))%nat /\ (bounded_ps_r b) <= (bounded_ps_r a)}.
 Proof.
   intros.
   destruct a as [a M r rgt0 Ha].
   simpl in *.
   assert (r/d2 <> real_0) by (apply real_gt_neq;apply real_half_gt_zero;auto).
   assert (bounded_seq (derivative_sequence a) (M * Npow2 m) (real_half_gt_zero _ rgt0)).
   - intros n.
     assert (/ real_gt_neq (r / d2) real_0 (real_half_gt_zero r rgt0) = (real_2 * / (real_gt_neq _ _ rgt0))) as ->.
     {
       apply (real_eq_mult_cancel (r / d2));auto.
       rewrite real_mult_inv.
       apply (real_eq_mult_cancel r);[apply real_gt_neq;auto|].
       rewrite real_mult_assoc, (real_mult_comm (r / d2)), <-real_mult_assoc.
       rewrite (real_mult_assoc real_2), real_mult_inv.
       unfold real_div.
       ring_simplify.
       rewrite real_mult_assoc, (real_mult_comm real_2), real_mult_inv.
       ring.
     }
     rewrite <-npow_mult.
     unfold derivative_sequence.
     apply (real_le_le_le _ (  Nreal M * Nreal (n+1)  *((npow (/ real_gt_neq _ _ rgt0) (n+1)%nat)))).
     + rewrite abs_mult,abs_pos_id; [| apply Nreal_nonneg].
       rewrite (real_mult_comm (Nreal M)), real_mult_assoc.
       apply real_le_mult_pos_le;[apply Nreal_nonneg|].
       apply Ha.
    + rewrite Nreal_mult.
      rewrite !real_mult_assoc.
       apply real_le_mult_pos_le;[apply Nreal_nonneg|].
       rewrite <-real_mult_assoc, (real_mult_comm (Nreal (Npow2 m))), real_mult_assoc.
       apply real_le_mult_pos_le_le; [apply Nreal_nonneg| apply npow_nonneg;apply real_lt_le;apply real_pos_inv_pos;auto | apply derivative_factor_bound |].
       replace (n+1)%nat with (S n) by lia.
       simpl.
       rewrite !(real_mult_comm _ (npow _ _)).
       apply real_le_mult_pos_le.
       apply npow_nonneg;apply real_lt_le;apply real_pos_inv_pos;auto.
       rewrite <-(precinv _ (real_gt_neq _ _ (prec_pos m))).
       apply inv_le_ge; [apply prec_pos|auto].
   - exists (mk_bounded_ps _ _ _ _ H1 );simpl;split;[|split];auto.
     assert (1 <= Npow2 m)%nat.
     replace 1 with (2 ^ 0) by auto.
     rewrite Npow2_pow.
     apply Nat.pow_le_mono_r;lia.
     nia.
     apply (real_le_mult_pos_cancel real_2); [apply real_lt_0_2|].
     unfold real_div.
     rewrite real_mult_assoc, real_mult_inv.
     unfold real_2;simpl.
     apply real_lt_le.
     add_both_side_by (-r);auto.
 Qed.

  Lemma archimedean_search (x : Real) : (real_0 < x) -> ^M {n | prec n < x}.
  Proof.
    intros.
    apply (M_lift {n | projP1 _ _ (real_lt_semidec (prec n) x) = lazy_bool_true}).
    - intros.
      destruct H0 as [n H0].
      exists n.
      destruct (real_lt_semidec (prec n) x).
      apply i.
      apply H0.
    - apply multivalued_countable_choice.
      destruct (real_Archimedean x) as [n N];auto.
      exists n.
      destruct (real_lt_semidec (prec n) x).
      apply i.
      exact N.
  Defined.

 Lemma deriv_bounded_ps a : ^M {b : bounded_ps | series b = derivative_sequence (series a) /\ ((bounded_ps_M a) <= (bounded_ps_M b))%nat /\ (bounded_ps_r b) <= (bounded_ps_r a)}.
 Proof.
   pose proof (archimedean_search _ (bounded_ps_rgt0 a)).
   revert X.
   apply M_lift.
   intros [n N].
   apply (deriv_bounded_ps_bounded_r a n).
   apply real_lt_le;auto.
 Qed.
 
 Lemma eval_to_poly_zero a : (forall n, (a n) = real_0) ->forall x n, eval_poly (to_poly a n) x = real_0.
 Proof.
   intros.
   induction n.
   simpl.
   rewrite H;ring.
   unfold to_poly.
   rewrite seq_S, map_app.
   rewrite eval_eval2.
   simpl map at 2.
   rewrite eval_poly2_app1.
   rewrite <-eval_eval2.
   unfold to_poly in IHn.
   rewrite H, IHn.
   ring.
 Qed.

 Lemma M_zero_is_zero a : (bounded_ps_M a = 0) -> forall n, (series a n) = real_0. 
 Proof.
   destruct a;simpl.
   intros.
   apply Minmax.real_abs_le0_eq0.
   apply (real_le_le_le _ _ _ (bounded_ps_bounded0 n)).
   rewrite H.
   apply real_eq_le.
   simpl;ring.
 Qed.

 Lemma M_zero_tm a : (bounded_ps_M a = 0) -> forall n x, (eval_tm (to_taylor_model a n) x) = real_0.
 Proof.
   intros.
   unfold eval_tm, to_taylor_model; simpl tm_poly.
   apply eval_to_poly_zero.
   apply M_zero_is_zero.
   exact H.
 Qed.

 Lemma deriv_bounded_ps_tm a b : series b = derivative_sequence (series a) -> (bounded_ps_M a) = (2 * bounded_ps_M b)%nat -> forall x n, derivative (eval_tm (to_taylor_model a n)) (eval_tm (to_taylor_model b n)) x.
 Proof.
   intros.
   destruct (bounded_ps_M b) eqn: Mb.
   - apply (derive_ext _ (fun x => real_0)); [apply M_zero_tm;lia|].
     apply (derive_ext2 _ (fun x => real_0)); [apply M_zero_tm|];auto.
     apply derivative_const.
   - unfold eval_tm, to_taylor_model;simpl tm_poly.
     rewrite H0, Mb,H.
     rewrite Nat.log2_double;try lia.
     rewrite Nat.add_succ_r.
     apply derivative_sequence_spec.
 Qed.

 Lemma powerseries_pc_defined a : forall x, abs x <= eval_radius a -> defined (powerseries_pc (series a) x).
 intros.
 destruct (eval_val _ _ H).
 exists x0.
 apply powerseries_pc_spec.
 apply fast_limit_limit;auto.
 Qed.



 Lemma eval_radius_gt0 (a : bounded_ps) : eval_radius a > real_0.
 Proof.
   unfold eval_radius.
   destruct a.
   simpl.
   apply real_half_gt_zero;auto.
 Qed.

 

 Lemma deriv_ps (a : bounded_ps) : ^M {b : bounded_ps | is_ps_for (derivative_fun (powerseries_pc (series a))) b}.
 Proof.
   pose proof (deriv_bounded_ps a).
   revert X.
   apply M_lift.
   intros [a' [A1 [A2 A3]]].
   destruct (bounded_ps_change_Mr a (2 * bounded_ps_M a') (bounded_ps_r a')) as [a0 [H0 [H1 H2]]];[lia | split;[apply (bounded_ps_rgt0 a')|]  | ];auto.
   rewrite H0 in *.
   clear H0 a A2 A3.
   destruct (bounded_ps_change_Mr a' (bounded_ps_M a') (bounded_ps_r a' / d2)) as [a'' [H0' [H1' H2']]]; [lia| split;[apply real_half_gt_zero;apply bounded_ps_rgt0 | apply real_lt_le;apply real_gt_half;apply bounded_ps_rgt0] |].
   exists a''.
   apply approx_is_ps.
   intros.
   assert (forall y, is_sum (ps (series a'') x) y -> derivative_pt (powerseries_pc (series a0)) y x).
   {
     rewrite <- H0'.
     intros.
     apply (polynomial_approx_derivative (powerseries_pc (series a0)) (to_taylor_model a0) (powerseries_pc (series a')) (to_taylor_model a') (eval_radius a')); try apply to_tm_approx; try apply powerseries_pc_defined.
     apply eval_radius_gt0.
     replace (eval_radius a') with (eval_radius a0) by (unfold eval_radius;rewrite H2;auto).
     apply to_tm_approx.
     apply deriv_bounded_ps_tm;auto.
     apply (real_le_le_le _ _ _ H).
     unfold eval_radius; rewrite H2'; rewrite H2; apply real_lt_le;apply real_gt_half;apply real_half_gt_zero;apply bounded_ps_rgt0.
     apply (real_le_lt_lt _ _ _ H).
     unfold eval_radius; rewrite H2'; apply real_gt_half;apply real_half_gt_zero;apply bounded_ps_rgt0.
     apply powerseries_pc_spec;auto.

   }
   rewrite to_taylor_model_series.
   destruct (eval_val _ _ H) as [y Y].
   replace fx with y; try (rewrite dist_symm;auto).
   apply derivative_fun_spec in H0.
   apply (derivative_pt_unique _ _ _ _ H0).
   apply H3.
   apply fast_limit_limit;auto.
Qed.

 End Derivative.
