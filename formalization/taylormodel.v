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
Require Import ClassicalPartialReals.

Section TaylorModels.

 Record taylor_model (f : Real -> pc Real) : Type := mk_tm
                                     {
                                       tm_poly : poly;
                                       tm_radius: Real;
                                       tm_error : Real;
                                       tm_spec : forall x, abs x <= tm_radius -> forall fx, defined_to (f x) fx -> dist (fx) (eval_poly tm_poly x) <= tm_error             
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
  
  Definition polynomial_approx (f : Real -> pcReal) (t : nat -> (taylor_model f)) r := forall n, (tm_error f (t n)) <= prec n /\ (tm_radius f (t n)) >= r.
  
  Lemma polynomial_approx_cont f t r x : (r > real_0) -> defined (f x) -> polynomial_approx f t r -> abs x < r -> cont_at f x.
  Proof.
    intros.
    split;auto.
    intros.
    destruct (real_Archimedean _ H3) as [n N].
    destruct (continuous_poly (tm_poly f (t (n+1+1)%nat)) x (prec (n+1)%nat)) as [d [Dp D]]; try apply prec_pos.
    assert (exists c, c > real_0 /\ c <= d /\ forall y, dist x y <= c -> abs y < r) as [c [C0 [C1 C2]]].
    {
      assert (r - abs x > real_0) as R by (apply real_gt_minus_gt_zero;auto).
      destruct (real_Archimedean _ R) as [m M].
      exists (Minmax.real_min d (prec m)).
      split; [destruct (Minmax.real_min_cand d (prec m)) as [-> | ->]|split;try apply Minmax.real_min_fst_le];try apply prec_pos;auto.
      intros.
      replace y with ((y - x) + x) by ring.
      apply (real_le_lt_lt _ _ _ (abs_tri _ _)).
      apply (real_lt_le_lt _ ((r - abs x) + abs x) _); [|ring_simplify;apply real_le_triv].
      apply real_lt_plus_r_lt;auto.
      apply (real_le_lt_lt _ (prec m));auto.
      rewrite <-dist_abs.
      apply (real_le_le_le _ _ _ H4).
      apply Minmax.real_min_snd_le.
    }
    exists c ; split;auto.
    intros.
    simpl.
    unfold dist.
    replace (fx - fy) with ((fx - (eval_tm (t (n+1+1)%nat) x)) + ((eval_tm (t (n+1+1)%nat) y)- fy) + ((eval_tm (t (n+1+1)%nat) x) - (eval_tm (t (n+1+1)%nat) y))) by ring.
    apply (real_le_le_le _ (prec n) _); [| apply real_lt_le; auto].
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    rewrite <-prec_twice.
    apply real_le_le_plus_le; [|apply D;apply (real_le_le_le _ _ _ H4);auto].
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    rewrite <-prec_twice.
    specialize (H1 (n+1+1)%nat) as [H1 H1'].
    destruct (t (n+1+1)%nat).
    unfold eval_tm.
    simpl in *.
    rewrite <-!dist_abs.
    apply real_le_le_plus_le; apply (real_le_le_le _ tm_error0);auto.
    rewrite dist_symm.
    apply tm_spec0;auto.
    apply real_lt_le.
    apply (real_lt_le_lt _ r);auto.
    apply tm_spec0;auto.
    apply real_lt_le.
    apply (real_lt_le_lt _ r _);auto.
  Qed.

  Lemma poly_approx_spec f t r x n : r > real_0 -> abs x <= r -> (polynomial_approx f t r) -> forall fx, defined_to (f x) fx -> dist (fx) (eval_tm (t n) x) <= prec n. 
  Proof.
    intros.
    specialize (H1 n) as [H1 H1'].
    unfold eval_tm.
    destruct (t n).
    simpl in *.
    apply (real_le_le_le _ tm_error0);auto.
    apply tm_spec0;auto.
    apply (real_le_le_le _ r);auto.
 Qed.

  Lemma poly_approx_dist f t r : r > real_0 -> (polynomial_approx f t r) -> forall eps, eps > real_0 -> exists N, forall m n, (n > N)%nat -> (m > N)%nat -> forall x, defined (f x) -> abs x <= r -> dist (eval_tm (t n) x) (eval_tm (t m) x) < eps. 
  Proof.
    intros.
   destruct (real_Archimedean _ H1) as [N Np].
   exists (N+1)%nat.
   intros.
   unfold dist.
   destruct H4 as [fx Fx].
   replace (eval_tm (t n) x - eval_tm (t m) x) with ((eval_tm (t n) x - fx) + (fx - eval_tm (t m) x)) by ring.
   apply (real_lt_lt_lt _ (prec N));auto.
   rewrite <- prec_twice.
   apply (real_le_lt_lt _ _ _ (abs_tri _ _ )).
   apply real_lt_lt_plus_lt.
   - apply (real_le_lt_lt _ (prec n)); try apply prec_monotone;auto.
     rewrite <-dist_abs.
     apply (poly_approx_spec _ _ _ _ n H H5 H0);auto.
   - apply (real_le_lt_lt _ (prec m)); try apply prec_monotone;auto.
     apply (poly_approx_spec _ _ _ _ m H H5 H0);auto.
 Qed.

  Lemma lbc f f' r M : (forall x, abs x <= r -> derivative f f' x) -> (forall x, abs x <= r -> abs (f' x) < M) -> forall x y, abs x <= r -> abs y <= r -> dist (f x) (f y) < M * dist x y.
  Proof.
    intros.
  Admitted.

  Lemma derivative_inv f g x : derivative f g x -> derivative (fun x => - f x) (fun x => - g x) x.
  Proof.
    intros.
    intros eps epsgt0.
    destruct (X _ epsgt0) as [d [X1 X2]].
    exists d;split;auto.
    intros.
    rewrite abs_symm.
    replace (- (- f y - - f x - - g x *(y-x))) with (f y - f x - g x * (y-x)) by ring.
    apply X2;auto.
  Defined.

  Lemma polynomial_approx_derivative_bound f t f' t' r :  (r > real_0) -> (polynomial_approx f t r)  ->  (polynomial_approx f' t' r) -> (forall x, abs x <= r -> defined (f' x)) ->(forall x n, abs x <= r -> derivative (eval_tm (t n)) (eval_tm (t' n)) x) -> forall eps, eps > real_0 -> exists N, forall m n, (n > N)%nat -> (m > N)%nat -> forall x y, abs x <= r -> abs y <= r -> dist (eval_tm (t m) x - eval_tm (t n) x) (eval_tm (t m) y - eval_tm (t n) y) < eps * dist x y.
  Proof.
    intros.
    destruct (poly_approx_dist _ _ _ H H1 _ H3) as [N NP].
    exists N.
    intros.
    assert (forall x, abs x <= r -> derivative (fun x => (eval_tm (t m)) x - eval_tm (t n) x) (fun x => (eval_tm (t' m) x - eval_tm (t' n) x )) x).
    {
      intros.
      apply derivative_sum;auto.
      apply derivative_inv;auto.
    }
    specialize (NP _ _ H4 H5).
    apply (lbc _ _ _ eps X0 );auto.
    intros.
    rewrite <-dist_abs.
    apply NP;auto.
  Qed.

  Lemma polynomial_approx_derivative_helper f t f' t' r :  (r > real_0) -> (polynomial_approx f t r)  ->  (polynomial_approx f' t' r) -> (forall x, abs x <= r -> defined (f' x)) ->(forall x n, abs x <= r -> derivative (eval_tm (t n)) (eval_tm (t' n)) x) -> forall eps, eps > real_0 -> exists N, forall n x y fx fy, (n >= N)%nat -> abs x <= r ->  abs y <= r -> defined_to (f x) fx -> defined_to (f y) fy -> dist (fy - fx) (eval_tm (t n) y - eval_tm (t n) x) <= eps * dist x y.
  Proof.
    intros.
    destruct (real_Archimedean _ H3) as [m mlt].
    destruct (polynomial_approx_derivative_bound _ _ _ _ _ H H0 H1 H2 X _ (prec_pos (m+1)%nat)) as [N NP].
    exists (N+1)%nat.
    intros.
    destruct (dist_pos x y).
    (* apply real_lt_le. *)
    assert (prec (m+1)%nat * dist x y > real_0) by (apply real_lt_pos_mult_pos_pos;auto;apply prec_pos).
    apply (real_le_le_le _ (prec (m+1)%nat * dist x y + (prec (m+1)%nat)*dist x y)); [|apply (real_le_le_le _ (prec m * dist x y)); [rewrite <-(prec_twice m);ring_simplify;apply real_eq_le|rewrite !(real_mult_comm _ (dist _ _));apply real_le_mult_pos_le];try apply real_lt_le];auto.
    unfold dist.
    destruct (real_Archimedean _ H10) as [N' NP'].
    replace (fy - fx - (eval_tm (t n) y - eval_tm (t n) x)) with ((fy - (eval_tm (t (N+N'+1)%nat)) y) + (eval_tm (t (N+N'+1)%nat) x - fx) + ((eval_tm (t (N+N'+1)%nat) y - eval_tm (t n) y) - ((eval_tm (t (N+N'+1)%nat) x) - eval_tm (t n) x))) by ring.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    apply real_le_le_plus_le; [|rewrite <-!dist_abs, (dist_symm y);apply real_lt_le;apply NP;auto;lia].
    apply (real_le_le_le _ (prec N'));auto.
    apply (real_le_le_le _ (prec (N + N'))); [|destruct N; [apply real_eq_le;auto|apply real_lt_le; apply prec_monotone;lia]].
    rewrite <-prec_twice.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    apply real_le_le_plus_le.
    apply (poly_approx_spec _ _ _ _ _ H);auto.
    rewrite <-dist_abs.
    apply (poly_approx_spec _ _ _ _ _ H);auto.
    apply real_lt_le;auto.
    rewrite <-H9.
    replace (eps*real_0) with real_0 by ring.
    apply real_eq_le.
    apply dist_zero.
    rewrite (proj1 (dist_zero x y));auto.
    replace fy with fx.
    ring_simplify;auto.
    rewrite (proj1 (dist_zero x y)) in H7; auto.
    rewrite H7 in H8.
    apply pc_unit_mono in H8.
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

  Lemma polynomial_approx_derivative f t f' t' r  : r > real_0 ->  (polynomial_approx f t r)  ->  (polynomial_approx f' t' r) -> (forall x, abs x <= r -> defined (f' x)) -> (forall x n, abs x <= r -> derivative (eval_poly (tm_poly f (t n))) (eval_poly (tm_poly f' (t' n))) x) -> forall x fx', defined (f x) -> (abs x < r) -> defined_to (f' x) fx' -> derivative_pt f fx' x. 
  Proof.
    intros.
    split;auto.
    intros.
    destruct (real_Archimedean _ H6) as [n np].
    destruct (polynomial_approx_derivative_helper _ _ _ _ _ H H0 H1 H2 X _ (prec_pos (n+1)%nat))as [N0 NP0].
    assert (exists N, (N >= N0)%nat /\ (N >= (n+3))%nat) as [N [NP NP']] by (exists (n+N0+3)%nat;lia).
    destruct (X x  N (real_lt_le _ _ H4) _ (prec_pos (n+1+1)%nat)) as [d0 [dp0 D0]].
    assert (exists d, d > real_0 /\ d <= d0 /\ (forall y, dist x y <= d -> abs y < r)) as [d [Dp1 [Dp2 Dp3]]].
    {
      assert (r - abs x > real_0) as R by (apply real_gt_minus_gt_zero;auto).
      destruct (real_Archimedean _ R) as [m M].
      exists (Minmax.real_min d0 (prec m)).
      split; [destruct (Minmax.real_min_cand d0 (prec m)) as [-> | ->]|split;try apply Minmax.real_min_fst_le];try apply prec_pos;auto.
      intros.
      replace y with ((y - x) + x) by ring.
      apply (real_le_lt_lt _ _ _ (abs_tri _ _)).
      apply (real_lt_le_lt _ ((r - abs x) + abs x) _); [|ring_simplify;apply real_le_triv].
      apply real_lt_plus_r_lt;auto.
      apply (real_le_lt_lt _ (prec m));auto.
      rewrite <-dist_abs.
      apply (real_le_le_le _ _ _ H7).
      apply Minmax.real_min_snd_le.
    }
    exists d.
    split;auto.
    intros.
    replace (fy - fx - fx'*(y-x)) with (((fy - fx) - ( (eval_tm (t N) y) - (eval_tm (t N) x))) + (((eval_tm (t' N) x) - fx')*(y-x)+((eval_tm (t N) y)-(eval_tm (t N) x)-(eval_tm (t' N) x)*(y-x)))) by ring.
    apply (real_le_le_le _ (prec n * abs (y -x))); [|rewrite !(real_mult_comm _ (abs _));apply real_le_mult_pos_le;[apply abs_pos|apply real_lt_le;auto]].
    rewrite <-prec_twice, (real_mult_comm (_ + _)), real_mult_plus_distr.
    apply (real_le_le_le _ _ _ (abs_tri  _ _)).
    apply real_le_le_plus_le.   
    - rewrite real_mult_comm.
      rewrite <-!dist_abs.
      rewrite dist_symm.
      apply NP0;try apply real_lt_le;auto.
    - apply (real_le_le_le _ _ _ (abs_tri  _ _)).
      rewrite <-prec_twice, real_mult_plus_distr.
      apply real_le_le_plus_le.
      + rewrite abs_mult, real_mult_comm.
        apply real_le_mult_pos_le; try apply abs_pos.
        apply (real_le_le_le _ (prec N)); [|apply real_lt_le;apply prec_monotone;lia].
        rewrite <-dist_abs.
        apply (poly_approx_spec _ _ _ _ N H (real_lt_le _ _ H4) H1 _ H5).
      + rewrite (real_mult_comm (abs _)).
        apply D0;auto.
        apply (real_le_le_le _ d);auto.
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


  Definition not A := A -> False.

  Lemma dn_elimm : forall P : Prop, not (not P) -> P.
  Proof.
    intros.
    destruct (lem P); auto.
    contradict (H H0).
  Defined.
  
  Lemma hprop_Nabla_hprop : forall P, is_hprop P -> is_hprop (Nabla P).
  Proof.
    intros.
    intros [p1 h1] [p2 h2].
    assert (p1 = p2).
    apply fun_ext.
    intros.
    apply Prop_ext.
    intro.
    destruct h2.
    destruct H1.
    rewrite (H x x0).
    exact H1.
    intro.
    destruct h1.
    destruct H1.
    rewrite (H x x0).
    exact H1.
    destruct H0.
    assert (h1 = h2).
    apply irrl.
    destruct H0.
    auto.
  Defined.
  
  Lemma False_hprop : is_hprop False.
  Proof.
    intros x y.
    contradict x.
  Defined.

  Definition dn_lift {A B} (f : A -> B) : not (not A) -> not (not B).
  Proof.
    intros.
    
    intro.
    exact (H (fun a : A => H0 (f a))).
  Defined.
  
  Lemma dn_hprop : forall P, is_hprop (not (not P)).
  Proof.
    intros.
    intros x y.
    apply fun_ext.
    intros.
    apply False_hprop.
  Defined.
  
    
  Definition Nabla_dn_shift : forall P A, is_hprop P -> (not (not P) -> Nabla A) -> P -> Nabla A.
  Proof.
    intros.
    apply X.
    intro.
    exact (H0 X0).
  Defined.
  
  Definition Nabla_dn_extend : forall P A, is_hprop P -> (P -> Nabla A) -> (not (not P) -> Nabla A).
  Proof.
    intros.
    apply (Nabla_bind X).
    clear X A.
    exists (fun p : P => True).
    destruct (lem (exists p : P, True)).
    destruct H1.
    exists x.
    split.
    auto.
    intros.
    apply H.
    assert (forall p : P, False).
    intro.
    contradict H1.
    exists p; auto.
    contradict (H0 H2).
  Defined.
  
  Lemma Nabla_dn_sheaf_1 : forall P A h x, 
      Nabla_dn_shift P A h (Nabla_dn_extend P A h x) = x.
  Proof.
    intros.
    apply fun_ext.
    intro.
    unfold Nabla_dn_extend.
    unfold Nabla_bind.
    unfold Nabla_dn_shift.
    destruct (lem (exists _ : P, True)).
    destruct e.
    induction (h x0 x1).
    assert ((exist (fun P0 : P -> Prop => exists ! a : P, P0 a) (fun _ : P => True)
               (ex_intro (unique (fun _ : P => True)) x0 (conj t (fun (x' : P) (_ : True) => h x0 x')))) = Nabla_unit _ x0).
    apply hprop_Nabla_hprop.
    exact h.
    rewrite H.
    rewrite Nabla_unit_ntrans.
    rewrite Nabla_coh1.
    exact eq_refl.
    contradict n.
  Defined.
  
  Lemma Nabla_dn_sheaf_2 : forall P A h x, 
      Nabla_dn_extend P A h (Nabla_dn_shift P A h x) = x.
  Proof.
    intros.
    apply fun_ext.
    intros.
    unfold Nabla_dn_extend.
    unfold Nabla_bind.
    unfold Nabla_dn_shift.
    destruct (lem (exists _ : P, True)).
    destruct e.
    assert ((exist (fun P0 : P -> Prop => exists ! a : P, P0 a) (fun _ : P => True)
               (ex_intro (unique (fun _ : P => True)) x1 (conj t (fun (x' : P) (_ : True) => h x1 x')))) = Nabla_unit _ x1).
    apply hprop_Nabla_hprop.
    exact h.
    rewrite H.
    rewrite Nabla_unit_ntrans.
    rewrite Nabla_coh1.
    rewrite (dn_hprop P  (fun H0 : not P => H0 x1) x0).
    apply eq_refl.
    contradict n.
    destruct (lem (not P)).
    contradict (x0 H).
    apply dn_elimm.
    apply (dn_lift (fun p : P => ex_intro _ p I)). 
    exact x0.
  Defined.

  Lemma dn_lem : forall A, not (not (A + not A)).
  Proof.
    intros.
    intro p.
    assert (not A).
    intro.
    assert (A + not A).
    left; auto.
    exact (p X0).
    assert (A + not A).
    right; auto.
    exact (p X).
  Defined.     

  Definition Nabla_hprop_lem {A} : forall P, is_hprop P -> ((P + not P) -> Nabla A) -> Nabla A.
  Proof.
    intros P h f.
    apply (Nabla_dn_extend (P + not P) A).
    intros x y.
    destruct x, y.
    rewrite (h p p0); auto.
    contradict (n p).
    contradict (n p).
    assert (n = n0).
    apply fun_ext.
    intro.
    contradict (n x).
    rewrite H; auto.
    exact f.
    apply dn_lem.
  Defined.

  Definition Nabla_Prop_lem {A} : forall P : Prop, ((P + ~ P) -> Nabla A) -> Nabla A.
  Proof.
    intro P.
    assert (is_hprop P).
    intros x y.
    apply irrl.
    apply Nabla_hprop_lem.
    exact H.
  Defined.

  Definition pc_hprop_lem {A} : forall P, is_hprop P -> ((P + not P) -> pc A) -> pc A.
  Proof.
    intros.
    exact (Nabla_hprop_lem P H X).
  Defined.
  
    
  Definition pc_Prop_lem {A} : forall P : Prop, ((P + ~ P) -> pc A) -> pc A.
  Proof.
    intro P.
    assert (is_hprop P).
    intros x y.
    apply irrl.
    apply Nabla_hprop_lem.
    exact H.
  Defined.

  Definition pc_ana_fun A B := {S : A * B -> Prop | forall x y1 y2, S (x, y1) -> S (x, y2) -> y1 = y2}.

  Definition pc_ana_fun_to_pc_fun A B : pc_ana_fun A B -> A -> pc B.
  Proof.
    intros [S p] x. 
    apply (pc_hprop_lem ({y | S (x, y)})).
    intros [a h1] [b h2].
    pose proof (p x a b h1 h2).
    destruct H.
    rewrite (irrl _ h1 h2).
    apply eq_refl.
    intros [l|r].
    destruct l.
    exact (pc_unit _ x0).
    exact pc_bot.
  Defined.
    
  
  Definition limit_cfun' (p : nat -> poly) : pc_ana_fun ^Real ^Real. 
  Proof.
   exists (fun xy => is_fast_limit_p (snd xy)  (fun n => (eval_poly (p n) (fst xy)))).
   intros.
   simpl in H0.
   apply (limit_is_unique _ _ _ H H0).
  Qed.

  Definition limit_cfun (p : nat -> poly) : ^Real -> pc ^Real. 
  Proof.
    apply pc_ana_fun_to_pc_fun.
    exact (limit_cfun' p).
  Defined.
  
    
End TaylorModels.
