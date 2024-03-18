Require Import Real.
Require Import MultiLimit.
Require Import Euclidean.
Require Import Nnat.
Require Import ArithRing.
Require Export Ring Field.
Require Import Psatz.
Require Import List.
Import ListNotations.
Require Import Poly.

Require Import RealAssumption.
Require Import ClassicalAnalysis.
Require Import ClassicalPartialReals ClassicalDifferentiability.

Section TaylorModels.

 Record taylor_model (f : Real -> pc Real) : Type := mk_tm
                                     {
                                       tm_poly : poly;
                                       tm_radius: Real;
                                       tm_error : Real;
                                       tm_spec : forall x, abs x <= tm_radius
                                        -> forall fx, defined_to (f x) fx
                                        -> dist (fx) (eval_poly tm_poly x) <= tm_error             
                                     }.

 Definition eval_tm {f} t x := (eval_poly (tm_poly f t) x).
 Definition tm_deg {f} (t : taylor_model f) := length (tm_poly f t).

 Lemma min_le_both r1 r2 : Minmax.real_min r1 r2 <= r1 /\ Minmax.real_min r1 r2 <= r2.
 Proof.
   split.
   apply Minmax.real_min_fst_le.
   apply Minmax.real_min_snd_le.
 Qed.
 

 Definition sum_tm f1 f2 (t1 : taylor_model f1) (t2 : taylor_model f2) : taylor_model (fun x => f1 x + f2 x)%pcreal.
 Proof.
   destruct t1 as [p1 r1 e1 H1].  
   destruct t2 as [p2 r2 e2 H2].  
   destruct (sum_poly p1 p2) as [p3 H3].
   pose proof (min_le_both r1 r2) as [M1 M2].
   apply (mk_tm _ p3 (Minmax.real_min r1 r2) (e1+e2)).
   intros. 
   rewrite H3.
   destruct (proj1 (pc_lift2_iff _ _ _ _ ) H0) as [f1x [f2x [Hf1x [Hf2x ->]]]].
   apply (real_le_le_le _ _ _ (dist_plus_le _ _ _ _)).
   apply real_le_le_plus_le;[apply H1 | apply H2];try apply (real_le_le_le _ _ _ H);auto.
 Defined.

 Definition mult_tm f1 f2 (t1 : taylor_model f1) (t2 : taylor_model f2) : taylor_model (fun x => f1 x * f2 x)%pcreal.
 Proof.
   destruct t1 as [p1 r1 e1 H1].  
   destruct t2 as [p2 r2 e2 H2].  
   destruct (mult_poly p1 p2) as [p3 H3].
   pose proof (min_le_both r1 r2) as [M1 M2].
   remember (Minmax.real_min r1 r2) as r.
   destruct (bound_polynomial p1 r) as [b1 B1].
   destruct (bound_polynomial p2 r) as [b2 B2].
   apply (mk_tm _ p3 r ( b1 * e2 + b2 * e1 + e1*e2)).
   intros.
   destruct (proj1 (pc_lift2_iff _ _ _ _ ) H0) as [f1x [f2x [Hf1x [Hf2x ->]]]].
   rewrite H3.
   unfold dist.
  replace (f1x * f2x - eval_poly p1 x * eval_poly p2 x) with (eval_poly p1 x * (f2x -  eval_poly p2 x) + eval_poly p2 x * (f1x  - eval_poly p1 x) + (f1x - eval_poly p1 x )* ((f2x) - eval_poly p2 x))  by ring.
    apply (real_le_le_le _ _ _ (abs_tri _ _ )).
    rewrite Heqr in *.
    pose proof (real_le_le_le _ _ _ H (Minmax.real_min_fst_le r1 r2)).
    pose proof (real_le_le_le _ _ _ H (Minmax.real_min_snd_le r1 r2)).
    apply real_le_le_plus_le;[apply (real_le_le_le _ _ _ (abs_tri _ _ )); apply real_le_le_plus_le|]; rewrite abs_mult.
    - apply real_le_mult_pos_le_le; try apply abs_pos; [apply B1 |];auto.
      apply H2;auto.
    - apply real_le_mult_pos_le_le; try apply abs_pos; [apply B2 |];auto.
      apply H1;auto.
    - apply real_le_mult_pos_le_le; try apply abs_pos; auto.
      apply (real_le_le_le _ (dist (f1x) (eval_poly p1 x)));auto.
      apply real_le_triv.
      apply (real_le_le_le _ (dist (f2x) (eval_poly p2 x)));auto.
      apply real_le_triv.
  Defined.

  Definition swipe_tm f (t : taylor_model f) (m : nat) : {t' : taylor_model f | (tm_deg t' <= m)%nat}.
  Proof.
   destruct t as [p r e H].  
   destruct (split_poly p m) as [[p1 p2] [L1 [L2 P]]].
   destruct (bound_polynomial p2 r) as [b B].
   assert (forall x, abs x <= r -> forall fx,  defined_to (f x) fx -> dist fx (eval_poly p1 x) <= e + npow r m * b). 
   {  intros.
      apply (real_le_le_le _ _ _ (dist_tri  _ (eval_poly p x) _ )).
      rewrite real_plus_comm, (real_plus_comm e).
      apply real_le_le_plus_le;auto.
      rewrite P.
      simpl.
      unfold dist.
      rewrite real_plus_comm; unfold real_minus; rewrite real_plus_assoc, real_plus_inv, real_plus_comm, real_plus_unit.
      rewrite abs_mult.
      rewrite abs_npow_distr.
      apply real_le_mult_pos_le_le;[apply npow_nonneg| |apply npow_nonneg_le |apply B];try apply abs_pos;auto.
    }
    exists (mk_tm f p1 r (e + (npow r m) * b) H0) .
    unfold tm_deg; simpl.
    simpl in L1;rewrite L1.
    apply Nat.le_min_l.
  Defined.
  
  Definition represents (f : Real -> pc_Real) (t : nat -> (taylor_model f)) r := forall n, (tm_error f (t n)) <= prec n /\ (tm_radius f (t n)) >= r.
  
  Lemma represents_cont (f : Real -> pc_Real) t r : (forall x : (I r), defined (f x)) -> represents f t r -> uniformly_continuous f r.
  Proof.
    intros.
    apply uniformly_continuous_unfold.
    split;[intros; apply (H (real_to_I H1)) | ].
    intros eps epsgt0.
    destruct (real_Archimedean _ epsgt0) as [n N].
    destruct (continuous_poly (tm_poly f (t (n+1+1)%nat)) r (prec (n+1)%nat)) as [d [Dp D]]; try apply prec_pos.
    exists d ; split;auto.
    intros.
    unfold dist.
    replace (fx - fy) with ((fx - (eval_tm (t (n+1+1)%nat) x)) + ((eval_tm (t (n+1+1)%nat) y)- fy) + ((eval_tm (t (n+1+1)%nat) x) - (eval_tm (t (n+1+1)%nat) y))) by ring.
    apply (real_le_le_le _ (prec n) _); [| apply real_lt_le; auto].
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    rewrite <-prec_twice.
    apply real_le_le_plus_le; [|apply (D (real_to_I H1) (real_to_I H2));auto].
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    rewrite <-prec_twice.
    specialize (H0 (n+1+1)%nat) as [H0 H0'].
    destruct (t (n+1+1)%nat).
    unfold eval_tm.
    simpl in *.
    rewrite <-!dist_abs.
    apply real_le_le_plus_le; apply (real_le_le_le _ tm_error0);auto.
    rewrite dist_symm.
    apply tm_spec0;auto.
    apply (real_le_le_le _ r);auto.
    apply tm_spec0;auto.
    apply (real_le_le_le _ r _);auto.
  Qed.

  Lemma poly_approx_spec f t r n : forall (x : I r), (represents f t r) -> forall fx, defined_to (f x) fx -> dist (fx) (eval_tm (t n) x) <= prec n. 
  Proof.
    intros.
    specialize (H n) as [H1 H1'].
    unfold eval_tm.
    destruct (t n).
    simpl in *.
    apply (real_le_le_le _ tm_error0);auto.
    apply tm_spec0;auto.
    destruct x.
    apply (real_le_le_le _ r);auto.
 Qed.

  Lemma poly_approx_dist f t r : (represents f t r) -> forall eps, eps > real_0 -> exists N, forall m n, (n > N)%nat -> (m > N)%nat -> forall (x : I r), defined (f x)  -> dist (eval_tm (t n) x) (eval_tm (t m) x) <= eps. 
  Proof.
   intros.
   destruct (real_Archimedean _ H0) as [N Np].
   exists (N+1)%nat.
   intros.
   unfold dist.
   destruct H3 as [fx Fx].
   replace (eval_tm (t n) x - eval_tm (t m) x) with ((eval_tm (t n) x - fx) + (fx - eval_tm (t m) x)) by ring.
   apply real_lt_le.
   apply (real_le_lt_lt _ (prec N));auto.
   rewrite <- prec_twice.
   apply (real_le_le_le _ _ _ (abs_tri _ _ )).
   apply real_le_le_plus_le.
   - apply real_lt_le; apply (real_le_lt_lt _ (prec n)); try apply prec_monotone;auto.
     rewrite <-dist_abs.
     apply (poly_approx_spec _ _ _ n x H _ Fx);auto.
   - apply real_lt_le; apply (real_le_lt_lt _ (prec m)); try apply prec_monotone;auto.
     apply (poly_approx_spec _ _ _ m x H _ Fx);auto.
 Qed.


  Lemma polynomial_approx_derivative_bound {f} {t : nat -> (taylor_model f)} {f' t'  r} :  (represents f' t' r)  -> (forall (x : I r), defined (f' x)) ->  (forall n,  uniform_derivative_fun (eval_tm (t n)) (eval_tm (t' n)) r) -> forall eps, eps > real_0 -> exists N, forall m n, (n > N)%nat -> (m > N)%nat -> forall (x y : (I r)), dist (eval_tm (t m) x - eval_tm (t n) x) (eval_tm (t m) y - eval_tm (t n) y) <= eps * dist x y.
  Proof.
    intros.
    destruct (poly_approx_dist _ _ _ H _ H2) as [N NP].
    exists N.
    intros.
    assert (uniform_derivative_fun (fun x => (eval_tm (t m)) x - eval_tm (t n) x) (fun x => (eval_tm (t' m) x - eval_tm (t' n) x )) r).
    {
      intros.
      apply sum_rule;auto.
      apply derivative_opp_fun;auto.
    }
    specialize (NP _ _ H3 H4).

    apply (lbc_fun _ _ _ eps H5 );auto.
    intros x'.
    rewrite <-dist_abs.
    apply NP;auto.
  Qed.

  Lemma polynomial_approx_derivative_helper {f t f' t' r} :   (represents f t r)  ->  (represents f' t' r) -> (forall (x : I r), defined (f' x)) ->(forall n, uniform_derivative_fun (eval_tm (t n)) (eval_tm (t' n)) r) -> forall eps, eps > real_0 -> exists N, forall n (x y : (I r)) fx fy, (n >= N)%nat -> defined_to (f x) fx -> defined_to (f y) fy -> dist (fy - fx) (eval_tm (t n) y - eval_tm (t n) x) <= eps * dist x y.
  Proof.
    intros.
    destruct (real_Archimedean _ H3) as [m mlt].
    destruct (polynomial_approx_derivative_bound H0 H1  H2 _ (prec_pos (m+1)%nat)) as [N NP].
    exists (N+1)%nat.
    intros.
    destruct (dist_pos x y).
    (* apply real_lt_le. *)
    assert (prec (m+1)%nat * dist x y > real_0) by (apply real_lt_pos_mult_pos_pos;auto;apply prec_pos).
    apply (real_le_le_le _ (prec (m+1)%nat * dist x y + (prec (m+1)%nat)*dist x y)); [|apply (real_le_le_le _ (prec m * dist x y)); [rewrite <-(prec_twice m);ring_simplify;apply real_eq_le|rewrite !(real_mult_comm _ (dist _ _));apply real_le_mult_pos_le];try apply real_lt_le];auto.
    unfold dist.
    destruct (real_Archimedean _ H8) as [N' NP'].
    replace (fy - fx - (eval_tm (t n) y - eval_tm (t n) x)) with ((fy - (eval_tm (t (N+N'+1)%nat)) y) + (eval_tm (t (N+N'+1)%nat) x - fx) + ((eval_tm (t (N+N'+1)%nat) y - eval_tm (t n) y) - ((eval_tm (t (N+N'+1)%nat) x) - eval_tm (t n) x))) by ring.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    apply real_le_le_plus_le; [|rewrite <-!dist_abs, (dist_symm y);apply NP;auto;lia].

    apply (real_le_le_le _ (prec N'));auto.
    apply (real_le_le_le _ (prec (N + N'))); [|destruct N; [apply real_eq_le;auto|apply real_lt_le; apply prec_monotone;lia]].
    rewrite <-prec_twice.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    apply real_le_le_plus_le.
    apply (poly_approx_spec _ _ _ _ _ H);auto.
    rewrite <-dist_abs.
    apply (poly_approx_spec _ _ _ _ _ H);auto.
    apply real_lt_le;auto.
    rewrite <-H7.
    replace (eps*real_0) with real_0 by ring.
    apply real_eq_le.
    apply dist_zero.
    rewrite (proj1 (dist_zero x y));auto.
    replace fy with fx.
    ring_simplify;auto.
    rewrite (proj1 (dist_zero x y)) in H5; auto.
    rewrite H5 in H6.
    apply pc_unit_mono in H6.
    auto.
 Qed.

  Lemma real_ge_minus_ge_zero x y : x >= y -> x - y >= real_0.
  Proof.
    intros.
    destruct H.
    apply real_lt_le.
    apply real_gt_minus_gt_zero;auto.
    rewrite H.
    apply real_eq_le;ring.
  Qed.

  Lemma polynomial_approx_derivative f t f' t' r  : (represents f t r)  ->  (represents f' t' r) -> (forall (x : I r), defined (f x) /\ defined (f' x) ) -> (forall n, uniform_derivative_fun (eval_poly (tm_poly f (t n))) (eval_poly (tm_poly f' (t' n))) r) -> uniform_derivative f f' r. 
  Proof.
    intros.
    apply uniform_derivative_unfold.
    split;[intros;  apply (H1 (real_to_I H3)) |].
    intros.
    destruct (real_Archimedean _ H3) as [n np].
    assert (forall (x : I r), defined (f' x)) as H1' by (intros; apply H1).
    destruct (polynomial_approx_derivative_helper H H0 H1' H2 _ (prec_pos (n+1)%nat))as [N0 NP0].
    assert (exists N, (N >= N0)%nat /\ (N >= (n+3))%nat) as [N [NP NP']] by (exists (n+N0+3)%nat;lia).
    destruct (H2 N  _ (prec_pos (n+1+1)%nat)) as [d [dp0 D0]].
    exists d.
    split;auto.
    intros.
    replace (fy - fx - f'x*(y-x)) with (((fy - fx) - ( (eval_tm (t N) y) - (eval_tm (t N) x))) + (((eval_tm (t' N) x) - f'x)*(y-x)+((eval_tm (t N) y)-(eval_tm (t N) x)-(eval_tm (t' N) x)*(y-x)))) by ring.
    apply (real_le_le_le _ (prec n * abs (y -x))); [|rewrite !(real_mult_comm _ (abs _));apply real_le_mult_pos_le;[apply abs_pos|apply real_lt_le;auto]].
    rewrite <-prec_twice, (real_mult_comm (_ + _)), real_mult_plus_distr.
    apply (real_le_le_le _ _ _ (abs_tri  _ _)).
    apply real_le_le_plus_le.   
    - rewrite real_mult_comm.
      rewrite <-!dist_abs.
      rewrite dist_symm.
      apply (NP0 N (real_to_I H4) (real_to_I H5));auto.
    - apply (real_le_le_le _ _ _ (abs_tri  _ _)).
      rewrite <-prec_twice, real_mult_plus_distr.
      apply real_le_le_plus_le.
      + rewrite abs_mult, real_mult_comm.
        apply real_le_mult_pos_le; try apply abs_pos.
        apply (real_le_le_le _ (prec N)); [|apply real_lt_le;apply prec_monotone;lia].
        rewrite <-dist_abs.
        apply (poly_approx_spec  _ _ _ N (real_to_I H4) H0 );auto.
      + rewrite (real_mult_comm (abs _)).
        apply (D0 (real_to_I H4) (real_to_I H5));auto.
  Qed.
  
  Definition is_fast_cauchy_poly (p : nat -> poly) r := forall x n m, abs x < r -> dist (eval_poly (p n) x) (eval_poly (p m) x) <= prec n + prec m.

  Lemma poly_limit (p : nat -> poly) r : is_fast_cauchy_poly p r -> forall x, abs x < r -> {y | is_fast_limit_p y (fun n => eval_poly (p n) x)}.
  Proof.
    intros.
    apply real_limit_p.
    rewrite <-is_fast_cauchy_iff_p.
    intros n m.
    apply H;auto.
  Qed.
  
    
End TaylorModels.
