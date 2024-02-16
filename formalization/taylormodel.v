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
Require Import ClassicalFunctions.

Section TaylorModels.

 Record taylor_model (f : cfun) : Type := mk_tm
                                     {
                                       tm_poly : poly;
                                       tm_radius: Real;
                                       tm_error : Real;
                                       tm_spec : forall x, abs x < tm_radius -> forall fx, img f x fx -> dist (fx) (eval_poly tm_poly x) < tm_error             
                                     }.

 Definition tm_deg {f} (t : taylor_model f) := length (tm_poly f t).

 Lemma min_le_both r1 r2 : Minmax.real_min r1 r2 <= r1 /\ Minmax.real_min r1 r2 <= r2.
 Proof.
   split.
   apply Minmax.real_min_fst_le.
   apply Minmax.real_min_snd_le.
 Qed.

 Definition sum_tm f1 f2 (t1 : taylor_model f1) (t2 : taylor_model f2) : taylor_model (f1+f2)%cfun.
 Proof.
   destruct t1 as [p1 r1 e1 H1].  
   destruct t2 as [p2 r2 e2 H2].  
   destruct (sum_poly p1 p2) as [p3 H3].
   pose proof (min_le_both r1 r2) as [M1 M2].
   apply (mk_tm _ p3 (Minmax.real_min r1 r2) (e1+e2)).
   intros. 
   rewrite H3.
   pose proof (proj1 (sumcf_spec f1 f2 x fx) H0) as [f1x [f2x [Hf1x [Hf2x ->]]]].
   apply (real_le_lt_lt _ _ _ (dist_plus_le _ _ _ _)).
   apply real_lt_lt_plus_lt;[apply H1 | apply H2];try apply (real_lt_le_lt _ _ _ H);auto.
 Defined.

 Definition mult_tm f1 f2 (t1 : taylor_model f1) (t2 : taylor_model f2) : taylor_model (f1 * f2)%cfun.
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
   pose proof (proj1 (mulcf_spec f1 f2 x fx) H0) as [f1x [f2x [Hf1x [Hf2x ->]]]].
   rewrite H3.
   unfold dist.
   replace (f1x * f2x - eval_poly p1 x * eval_poly p2 x) with (eval_poly p1 x * (f2x -  eval_poly p2 x) + eval_poly p2 x * (f1x  - eval_poly p1 x) + (f1x - eval_poly p1 x )* ((f2x) - eval_poly p2 x))  by ring.
    apply (real_le_lt_lt _ _ _ (abs_tri _ _ )).
    rewrite Heqr in *.
    pose proof (real_lt_le_lt _ _ _ H (Minmax.real_min_fst_le r1 r2)).
    pose proof (real_lt_le_lt _ _ _ H (Minmax.real_min_snd_le r1 r2)).
    apply real_le_lt_plus_lt;[apply (real_le_le_le _ _ _ (abs_tri _ _ )); apply real_le_le_plus_le|]; rewrite abs_mult.
    - apply real_le_mult_pos_le_le; try apply abs_pos; [apply B1 |]; apply real_lt_le;auto.
      apply H2;auto.
    - apply real_le_mult_pos_le_le; try apply abs_pos; [apply B2 |];apply real_lt_le;auto.
      apply H1;auto.
    - apply real_lt_mult_pos_lt_lt; try apply abs_pos; auto.
      apply (real_le_lt_lt _ (dist (f1x) (eval_poly p1 x)));auto.
      apply dist_pos.
      apply (real_le_lt_lt _ (dist (f2x) (eval_poly p2 x)));auto.
      apply dist_pos.
      apply H1;auto.
      apply H2;auto.
  Defined.

  Definition swipe_tm f (t : taylor_model f) (m : nat) : {t' : taylor_model f | (tm_deg t' <= m)%nat}.
  Proof.
   destruct t as [p r e H].  
   destruct (split_poly p m) as [[p1 p2] [L1 [L2 P]]].
   destruct (bound_polynomial p2 r) as [b B].
   assert (forall x, abs x < r -> forall fx,  img f x fx -> dist fx (eval_poly p1 x) < e + npow r m * b). 
   {  intros.
      apply (real_le_lt_lt _ _ _ (dist_tri  _ (eval_poly p x) _ )).
      rewrite real_plus_comm, (real_plus_comm e).
      apply real_le_lt_plus_lt;auto.
      rewrite P.
      simpl.
      unfold dist.
      rewrite real_plus_comm; unfold real_minus; rewrite real_plus_assoc, real_plus_inv, real_plus_comm, real_plus_unit.
      rewrite abs_mult.
      rewrite abs_npow_distr.
      apply real_le_mult_pos_le_le;[apply npow_nonneg| |apply npow_nonneg_le |apply B];try apply abs_pos;apply real_lt_le;auto.
    }
    exists (mk_tm f p1 r (e + (npow r m) * b) H0) .
    unfold tm_deg; simpl.
    simpl in L1;rewrite L1.
    apply Nat.le_min_l.
  Defined.

End TaylorModels.
