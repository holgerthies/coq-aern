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
Require Import Poly.


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

  Definition converges_to (a : nat -> Real) x := forall eps, eps > real_0 -> exists N, forall n, (n > N)%nat -> dist (partial_sum a n) x < eps.

  
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

  Definition bounded_seq (a : nat -> Real) M {r : Real} (H : real_0 < r)  :=  forall n, abs (a n) <= Nreal M * (npow (real_inv (real_gt_neq _ _ H))  n).
                                                                                   
 Record bounded_ps : Type := mk_bounded_ps
                               {
                                 series : nat -> Real;
                                 bounded_ps_M : nat;
                                 bounded_ps_r :Real;
                                 bounded_ps_rgt0 : bounded_ps_r > real_0;
                                 bounded_ps_bounded: bounded_seq series bounded_ps_M bounded_ps_rgt0 
                               }.




  Definition to_poly (a : nat -> ^Real) n := map a (seq 0 (S n)).

  Definition ps a x n := (a n) * npow x n. 

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

 Lemma eval_val (a : bounded_ps) x : abs x <= eval_radius a -> {y | is_fast_limit_p y (eval_seq a x)}.
 Proof.
   intros.
   destruct (real_limit_p (eval_seq a x)).
   apply is_fast_cauchy_iff_p.
   apply is_fast_cauchy_eval;auto.
   exists x0.
   apply i.
 Qed.

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
 Definition ps_to_cfun (a : bounded_ps) : cfun.
 Proof.
   exists (fun xy => abs (fst xy) <= (eval_radius a) /\ is_fast_limit_p (snd xy) (eval_seq a (fst xy))).
   simpl.
   intros x y1 y2 [[H1 H2] [H1' H2']].
   apply (limit_is_unique _ _ _ H2);auto.
 Defined.

 Lemma ps_to_cfun_dom a x : dom (ps_to_cfun a) x <-> abs x <= (eval_radius a).
 Proof.
   split;intros;auto.
   destruct H as [y [H1 _]].
   apply H1.
   unfold dom.
   destruct (real_limit_p (eval_seq a x)).
   apply is_fast_cauchy_iff_p.
   apply is_fast_cauchy_eval;auto.
   exists x0.
   split;auto.
 Qed.
 Definition sum (a : nat -> Real) (b: nat -> Real) := fun n => (a n) + (b n).


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
 
 Definition cfun_eq (f g : cfun) := forall x fx, img f x fx <-> img g x fx.

 Lemma dist_plus x y x' y' : dist (x+x') (y + y') <= dist x y + dist x' y'.
 Proof.
   unfold dist.
   assert (x + x' - (y + y') = (x-y + (x' - y'))) as -> by ring.
   apply abs_tri.
 Qed.
 Lemma sum_limit a b x y : is_fast_limit_p x a -> is_fast_limit_p y b -> is_fast_limit_p (x + y) (fun n => a (S n) + b (S n)).
 Proof.
   intros.
   intro n.
   apply dist_le_prop.
   apply (real_le_le_le _ _ _ (dist_plus x (a (S n)) y (b (S n)))).
   rewrite <-prec_twice.
   apply real_le_le_plus_le; rewrite Nat.add_1_r;apply dist_le_prop;auto.
Qed.
 Lemma sum_ps_partial_sum a b x n : eval_poly (to_poly (sum a b) n) x  = eval_poly (to_poly a n) x + eval_poly (to_poly b n) x.
 Proof.
    rewrite !eval_series_partial_sum.
   induction n.
   - unfold sum,ps.
     simpl;ring_simplify;auto.
   -  simpl.
     rewrite IHn.
     unfold sum,ps.
     ring_simplify;auto.
 Qed.

 Lemma is_fast_limit_speedup a x y M1 M2 : (M1 <= M2)%nat -> is_fast_limit_p y (fun n => (eval_poly (to_poly a (n+M1)%nat)) x) -> is_fast_limit_p y (fun n => (eval_poly (to_poly a (n+M2))) x).
  Proof.
    intros H1 H2 n.
    assert (n+M2 = (n+(M2-M1))+M1)%nat as -> by lia.
    apply dist_le_prop.
    apply (real_le_le_le _ (prec (n + (M2-M1))%nat)).
    apply dist_le_prop.
    apply H2.
   assert (forall n m, (n <= m)%nat -> (prec m <= prec n)).
   {
     intros.
     destruct H; [apply real_le_triv | ].
     apply real_lt_le.
     apply prec_monotone.
     lia.
   }
   apply H.
   lia.
 Qed.

 Definition sum_ps (a b : bounded_ps) : {c : bounded_ps |cfun_eq (ps_to_cfun c) (ps_to_cfun a + ps_to_cfun b)%cfun}.
 Proof.
   destruct a as [a' M1 r1 r1gt0 Ba] eqn:A.
   destruct b as [b' M2 r2 r2gt0 Bb] eqn:B.
   pose proof (min_le_both r1 r2) as [R1 R2]. 
   remember (Minmax.real_min r1 r2) as r.
   assert (r > real_0).
   {
     rewrite Heqr.
     destruct (Minmax.real_min_cand r1 r2) as [-> | ->];auto.
   }
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
  assert ((S (Nat.log2 (bounded_ps_M c))) <= (S (S (Nat.log2 (bounded_ps_M c)))))%nat as L0 by lia.
  assert ((S (Nat.log2 (bounded_ps_M a)) <= S (Nat.log2 (M1+M2)))%nat /\ (S (Nat.log2 (bounded_ps_M b)) <= S (Nat.log2 (M1+M2)))%nat) as [L1 L2].
    {
      rewrite A, B.
      simpl.
      split;apply le_n_S;apply Nat.log2_le_mono;lia.
    }
  exists c.
  split.
   - simpl.
    intros [H1 H2].
    assert (abs x <= eval_radius a /\ abs x <= eval_radius b) as [P1 P2].
    {
      rewrite Heqc in H1.
      unfold eval_radius in *.
      rewrite A,B.
      simpl in *.
      split;apply (real_le_le_le _ (r / real_2_neq_0));auto;apply half_le_le;auto.
    }
    destruct (eval_val a x);auto.
    destruct (eval_val b x);auto.
    exists x0; exists x1.
    rewrite <-A, <-B.
    split;split;auto.
    pose proof (sum_limit _ _ _ _ i i0).
    unfold eval_seq in H2.
    pose proof (is_fast_limit_speedup _ x fx _ _ L0 H2 ).
    pose proof (is_fast_limit_speedup _ x x0 _ _ L1 i).
    pose proof (is_fast_limit_speedup _ x x1 _ _ L2 i0).
    apply (limit_is_unique _ _ _ H4).
    intros n.
    apply dist_le_prop.
    unfold eval_seq.
    rewrite Heqc.
    simpl series; simpl bounded_ps_M.
    rewrite sum_ps_partial_sum.
    rewrite <-prec_twice, Nat.add_1_r.
    apply (real_le_le_le _ _ _ (dist_plus _ _ _ _)).
    rewrite <-Nat.add_succ_comm.
    rewrite A in H5.
    rewrite B in H6.
    apply real_le_le_plus_le;apply dist_le_prop;auto.
  - simpl.
    intros [x0 [x1 [[C1 C2] [[C1' C2'] ->]]]].
    assert (abs x <= eval_radius c)
    by (rewrite Heqc;unfold eval_radius;simpl;rewrite Heqr;destruct (Minmax.real_min_cand r1 r2) as [-> | ->];auto).
    split;auto.
    destruct (eval_val c x);auto.
    pose proof (is_fast_limit_speedup _ x x2 _ _ L0 i).
    rewrite Heqc, A, B in *.
    unfold eval_seq,eval_radius in *; simpl series in *;simpl bounded_ps_r in *; simpl bounded_ps_M in *.
    pose proof (is_fast_limit_speedup _ x x0 _ _ L1 C2).
    pose proof (is_fast_limit_speedup _ x _ _ _ L2 C2').
    replace (x0 + x1) with x2;auto.
    apply (limit_is_unique _ _ _ H2).
    intros n.
    rewrite <-Nat.add_succ_comm.
    rewrite sum_ps_partial_sum.
    pose proof (sum_limit _ _ _ _ H3 H4).
    apply H5.
 Defined.

 (*  Lemma eval_radius_sum_both {x a b} : abs x <= (eval_radius a) -> abs x <= (eval_radius b) -> abs x <= (eval_radius (sum_ps a b)). *)
 (*  Proof. *)
 (*   unfold eval_radius. *)
 (*   destruct a. *)
 (*   destruct b. *)
 (*   unfold bounded_ps_r. *)
 (*   simpl. *)
 (*   intros. *)
 (*   destruct (Minmax.real_min_cand bounded_ps_r0 bounded_ps_r1) as [-> | ->];auto. *)
 (* Qed. *)
  

 


 Fixpoint derivative_factor (n : nat) (k : nat) := 
   match k with
   | 0 => real_1
   | (S k') => (Nreal (n+k)) * derivative_factor n k'
end.
 Lemma derivative_factor_bound (n : nat) (k : nat) : derivative_factor n k <= pow (real_2 * Nreal k) (n+k) * pow real_2 (n+k).
 Proof.
   induction k.
   - simpl.
     rewrite <-(pow_1 n).
     rewrite Nat.add_0_r.
     apply pow_nonneg_le;apply real_lt_le.
     apply real_1_gt_0.
     apply real_2_gt_1.
  - rewrite Nat.add_succ_r.
    simpl.
    destruct n.
    simpl.
 Lemma bounded_deriv a M r (rgt0 : r > real_0) k : (bounded_seq a M rgt0) ->  bounded_seq (fun n=> (derivative_factor n k) * a (n+k)%nat) M (real_half_gt_zero _ rgt0).
 Proof.
   unfold bounded_seq.
   intros.
   induction k.
   - simpl.
     rewrite real_mult_unit.
     apply (real_le_le_le _ _ _ (H n)).
     apply real_le_mult_pos_le; [apply pow_nonneg; apply real_lt_le; apply real_lt_0_2 |].
     apply pow_nonneg_le; [apply real_lt_le; apply real_pos_inv_pos;auto |].
     apply inv_le_ge; [| apply real_lt_le; apply real_gt_half]; try apply real_half_gt_zero;auto.
  - simpl.
 Lemma derivative_ps (a : bounded_ps) (k : nat) : {b : bounded_ps | (forall n, series b n = (derivate_factor n k) * series a n) /\ (bounded_ps_r b) >= (bounded_ps_r a / d2) /\ bounded_ps_M b = bounded_ps_M a}.
Proof.
  induction k.
  - exists a.
  destruct a as [a M r H1 H2].
  split; [intros; simpl; ring | split;simpl];auto.
  apply real_lt_le;apply real_gt_half;auto.
  - destruct a as [a M r H1 H2];simpl in *.
    destruct IHk as [b [B1 [B2 B3]]].
    destruct b as [b M' r' H1' H2'];simpl in *.
    destruct (mk_bounded_ps (fun n => derivate_factor n k * a n) M (r /d2) (real_half_gt_zero _ H1)). 
    intros n.
    unfold bounded_seq in H2'.
    destruct IHk.
 End Powerseries.
