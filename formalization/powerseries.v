Require Import Real.
Require Import MultiLimit.
Require Import Euclidean.
Require Import Nnat.
Require Import ArithRing.
Require Export Ring Field.
Require Import Psatz.
Require Import List.
Import ListNotations.
Require Import Polynomial.
Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).

  (* ring structure on Real *)
  Ltac IZReal_tac t :=
    match t with
    | real_0 => constr:(0%Z)
    | real_1 => constr:(1%Z)
    | IZreal ?u =>
      match isZcst u with
      | true => u
      | _ => constr:(InitialRing.NotConstant)
      end
    | _ => constr:(InitialRing.NotConstant)
    end.

  Add Ring realRing : (realTheory ) (constants [IZReal_tac]).

Section Power.



 (* Lemma pow_div r1 {r2} (r2' : real_0 < r2) n : (pow r1 n) / (pow_neq_0 _ n r2') = (pow (r1 / (real_gt_neq _ _ r2')) n). *)
 (* Proof. *)
 (*   induction n. *)
 (*   - simpl. *)
 (*     unfold real_div. *)
 (*     ring_simplify. *)
 (*     apply (real_eq_mult_cancel (pow r2 0)). *)
 (*     apply real_gt_neq;apply pow_pos;auto. *)
 (*     pose proof (real_mult_inv (pow r2 0) (pow_neq_0 _ 0 r2')). *)
 (*     simpl;simpl in H. *)
 (*     rewrite H. *)
 (*     ring. *)
 (*  -  *)

End Power.

Section PolynomialModels.

 Record polynomial_model : Type := mk_polynomial_model
                                     {
                                       pm_coeffs : list ^Real;
                                       pm_radius: ^Real;
                                       pm_error : ^Real
                                     }.


  Definition eval_pm p x := eval_series (pm_coeffs p) x.
 Definition is_polynomial_model (p : polynomial_model) (f : Real -> Real) := forall x, abs x < pm_radius p -> dist (f x) (eval_pm p x) < pm_error p.

 Fixpoint sum_coefficients (a b : list Real) :=
   match a with
     | nil => b
     | a0 :: atl =>
       match b with
       | nil => a
       | b0 :: btl => (a0 + b0) :: sum_coefficients atl btl
       end
     end.
                 

   Lemma sum_eval a b x : eval_series (sum_coefficients a b) x = eval_series a x + eval_series b x.
   Proof.
     revert b.
     induction a as [| a0 a];intros; [simpl;ring|].
     destruct b as [| b0 b];[simpl;ring|].
     simpl.
     assert (forall y z u, y = z + u -> a0 + b0 + y = a0+z+(b0+u)) by (intros;rewrite H;ring).
     apply H.
     rewrite <-real_mult_plus_distr.
     apply real_eq_mult_eq.
     apply IHa.
   Qed.
   
  Definition sum_pm (p1 p2 : polynomial_model) : polynomial_model.
  Proof.
    apply mk_polynomial_model.
    apply (sum_coefficients (pm_coeffs p1) (pm_coeffs p2)).
    apply (Minmax.real_min (pm_radius p1) (pm_radius p2)).
    apply (pm_error p1 + pm_error p2).
  Defined.

  Lemma sum_pm_spec p1 p2 f1 f2: is_polynomial_model p1 f1 -> is_polynomial_model p2 f2 -> is_polynomial_model (sum_pm p1 p2) (fun x => (f1 x) + (f2 x)). 
 Proof.
   destruct p1; destruct p2.
   unfold is_polynomial_model, eval_pm.
   simpl.
   intros.
   rewrite sum_eval.
   apply (real_le_lt_lt _ _ _ (dist_plus_le _ _ _ _)).
   apply real_lt_lt_plus_lt;[apply H | apply H0];apply (real_lt_le_lt _ _ _ H1).
   apply Minmax.real_min_fst_le.
   apply Minmax.real_min_snd_le.
  Defined.


  Definition swipe (p : polynomial_model) (n : nat) : polynomial_model.
  Proof.
    destruct p as [a r err].
    apply mk_polynomial_model.
    apply (firstn n a).
    apply r.
    apply (err + (pow r n) * (bound_polynomial (skipn n a) r)).
  Defined.

  Lemma pm_r_gt0 p f : (pm_radius p) < real_0 -> is_polynomial_model p f.
  Proof.
    unfold is_polynomial_model, eval_pm.
    intros.
    destruct p as [a r err]; simpl in *.
    contradict H0.
    apply real_lt_nlt.
    apply (real_lt_le_lt _ _ _ H).
    apply abs_pos.
  Qed.

  Lemma swipe_pm p f n : is_polynomial_model p f -> is_polynomial_model (swipe p n) f.
  Proof.
    unfold is_polynomial_model.
    destruct p as [a r err].
    unfold swipe; unfold eval_pm;simpl.
    intros.
    apply (real_le_lt_lt _ _ _ (dist_tri  _ (eval_series a x) _ )).
    rewrite real_plus_comm, (real_plus_comm err).
    apply real_le_lt_plus_lt;auto.
    assert (real_0 <= r) as rge0 by (apply real_lt_le; apply (real_le_lt_lt _ (abs x)); try apply abs_pos;auto).
    replace (dist (eval_series a x) (eval_series (firstn n a) x)) with (abs (pow x n) * abs (eval_series (skipn n a) x)).
    { 
      apply real_le_mult_pos_le_le; try apply abs_pos; try apply real_le_triv.
      rewrite pow_abs.
      apply pow_nonneg_le;try apply abs_pos; apply real_lt_le;auto.
      apply bound_polynomial_spec;apply real_lt_le;auto.
    }
    rewrite <- abs_mult.
    unfold dist.
    f_equal.
    clear H.
    revert a.
    induction n;intros; [simpl;ring |].
    simpl.
    destruct a;simpl;try ring.
    rewrite real_mult_assoc.
    rewrite IHn.
    ring.
  Qed.

  Definition mult_pm (p1 p2 : polynomial_model) : polynomial_model.
  Proof.
    destruct p1 as [a ra erra]; destruct p2 as [b rb errb].
    remember (Minmax.real_min ra rb) as r.
    apply mk_polynomial_model.
    apply (mult_coefficients a b).
    apply r.
    apply (erra*errb + bound_polynomial a r * errb + bound_polynomial b r * erra).
 Defined.
  Lemma mult_pm_spec p1 p2 f1 f2: is_polynomial_model p1 f1 -> is_polynomial_model p2 f2 -> is_polynomial_model (mult_pm p1 p2) (fun x => (f1 x) * (f2 x)). 
  Proof.
    destruct p1 as [a ra erra]; destruct p2 as [b rb errb].
    unfold is_polynomial_model, eval_pm; simpl.
    intros.
    rewrite mult_eval.
    unfold dist.
    replace (f1 x * f2 x - eval_series a x * eval_series b x) with (eval_series a x * (f2 x -  eval_series b x) + eval_series b x * (f1 x  - eval_series a x) + (f1 x - eval_series a x )* ((f2 x) - eval_series b x))  by ring.
    rewrite (real_plus_assoc (erra*errb)), (real_plus_comm (erra * errb)).
    apply (real_le_lt_lt _ _ _ (abs_tri _ _ )).
    apply real_le_lt_plus_lt;[apply (real_le_le_le _ _ _ (abs_tri _ _ )); apply real_le_le_plus_le|]; rewrite abs_mult.
    - apply real_le_mult_pos_le_le; try apply abs_pos; [apply bound_polynomial_spec |];apply real_lt_le;auto.
      apply H0.
      apply (real_lt_le_lt _ _ _ H1).
      apply Minmax.real_min_snd_le.
    - apply real_le_mult_pos_le_le; try apply abs_pos; [apply bound_polynomial_spec |];apply real_lt_le;auto.
      apply H.
      apply (real_lt_le_lt _ _ _ H1).
      apply Minmax.real_min_fst_le.
    - pose proof (real_lt_le_lt _ _ _ H1 (Minmax.real_min_fst_le ra rb)).
      pose proof (real_lt_le_lt _ _ _ H1 (Minmax.real_min_snd_le ra rb)).
      specialize (H _ H2).
      specialize (H0 _ H3).
      apply real_lt_mult_pos_lt_lt; try apply abs_pos; auto.
      apply (real_le_lt_lt _ (dist (f1 x) (eval_series a x)));auto.
      apply dist_pos.
      apply (real_le_lt_lt _ (dist (f2 x) (eval_series b x)));auto.
      apply dist_pos.
 Qed.
End PolynomialModels.

Section Powerseries.

  

  Definition bounded_seq (a : nat -> Real) M {r : Real} (H : real_0 < r)  :=  forall n, abs (a n) <= Nreal M * (pow (/ (real_gt_neq _ _ H)) n).
                                                                                   
 Record bounded_ps : Type := mk_bounded_ps
                               {
                                 series : nat -> Real;
                                 bounded_ps_M : nat;
                                 bounded_ps_r :Real;
                                 bounded_ps_rgt0 : bounded_ps_r > real_0;
                                 bounded_ps_bounded: bounded_seq series bounded_ps_M bounded_ps_rgt0 
                               }.


  Fixpoint partial_sum (a : nat -> Real) n :=
    match n with
    | 0 => (a 0)
    | (S n') => (a n)+partial_sum a n'
    end.
  Lemma tpmn_sum a : (forall n, abs (a n) <= prec n) -> forall n, abs (partial_sum  a n) <= real_2 - prec n.
  Proof.
    intros H n.
    induction n.
    - unfold real_2.
      simpl.
      ring_simplify;auto.
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

  Definition to_list (a : nat -> ^Real) n := map a (seq 0 (S n)).


 Definition partial_sum_inc a m n := partial_sum a (n+m)%nat.

 Definition ps a x n := (a n) * pow x n. 

 Lemma eval_series_to_list a x n i:  (i <= n)%nat -> eval_series (to_list a n) x = eval_series (to_list a i) x + (pow x (S i))*(eval_series (map a (seq (S i) (n-i)%nat)) x).
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

  Lemma eval_series_partial_sum a x n : eval_series (to_list a n) x = partial_sum (ps a x) n.
  Proof.
    unfold ps.
    induction n; [simpl;ring|].
    rewrite (eval_series_to_list a x (S n) n); try lia.
    replace (S n - n)%nat with 1 by lia.
    simpl.
    rewrite <-IHn.
    destruct n;simpl;ring.
  Qed.

  Lemma Npow2_pow n : Npow2 n = (2 ^ n).
  Proof.
    induction n.
    simpl;lia.
    simpl.
    rewrite IHn.
    lia.
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

  Definition to_polynomial_model (a : bounded_ps) (n : nat) : polynomial_model.
  Proof.
    destruct a as [a M r rgt0 B].
    apply mk_polynomial_model.
    apply (to_list a (n+(S (Nat.log2 M)))%nat).
    apply (r / real_2_neq_0).
    apply (prec n).
  Defined.

  Lemma is_fast_cauchy_eval (a : bounded_ps) x : abs x <= eval_radius a -> is_fast_cauchy (fun n => eval_pm (to_polynomial_model a n) x).
  Proof.
    unfold eval_radius, eval_pm.
    destruct a as [a M r rgt0 B].
    simpl bounded_ps_r.
    simpl pm_coeffs.
    intros H n m.
    rewrite !eval_series_partial_sum.
    apply tmpn_cauchy.
    intros.
    unfold ps.
    unfold bounded_seq in B.
    rewrite abs_mult.
    apply real_lt_le.
    apply (real_le_lt_lt _ (Nreal M * prec (n0+(S (Nat.log2 M))))); [|apply increment_num].
   apply (real_le_le_le _ (((Nreal M) * (pow (/ (real_gt_neq _ _ rgt0)) (n0 + (S (Nat.log2 M)))%nat) * (pow (r / real_2_neq_0) (n0+S (Nat.log2 M))%nat)))).
   - apply real_le_mult_pos_le_le; try apply abs_pos; try apply B.
     rewrite pow_abs.
     apply pow_nonneg_le;auto.
     apply abs_pos.
   - rewrite real_mult_assoc.
     apply real_le_mult_pos_le; [destruct M;[apply real_le_triv|apply real_lt_le;apply Nreal_pos;lia]|].
    rewrite pow_mult.
    unfold real_div.
    rewrite <-real_mult_assoc.
    assert (/ real_gt_neq r real_0 rgt0 * r = real_1) as -> by apply real_mult_inv.  
    rewrite real_mult_unit.
    rewrite pow_prec.
    apply real_le_triv.
 Qed.

 Definition eval (a : bounded_ps) (x : Real):  abs x <=  (eval_radius  a) -> ^Real.
 Proof.
   intros.
   destruct (real_limit (fun n => eval_pm (to_polynomial_model a n) x)).
   apply is_fast_cauchy_eval;auto.
   apply x0.
 Defined.

 (* Definition coeff_bound a := {M : nat & {r : Real & {H : (r > real_0) | bounded_seq a M H }}}. *)

 Definition sum (a : nat -> Real) (b: nat -> Real) := fun n => (a n) + (b n).

 Lemma pow_monotone x n1 n2 : real_1 <= x -> (n1 <= n2)%nat -> pow x n1 <= pow x n2.
 Proof.
   revert n2.
   induction n1.
   - intros.
     pose proof (pow_nonneg_le real_1 x n2 (real_lt_le _ _ real_1_gt_0) H).
     rewrite pow_1 in H1.
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

 Lemma pow2_max M1 M2: pow real_2 M1 <= pow real_2 (max M1 M2) /\ pow real_2 M2 <= pow real_2 (max M1 M2).
 Proof.
   split;(apply pow_monotone; [apply real_lt_le; apply real_2_gt_1 | ]).
   apply Nat.le_max_l.
   apply Nat.le_max_r.
Qed.

 Lemma seq_bound_larger_M a M1 M2 r p: (M1 <= M2)%nat -> (@bounded_seq a M1 r p) -> (@bounded_seq a M2 r p).
 Proof.
   intros P1 P2 n.
   apply (real_le_le_le _ ((pow real_2 M1) * pow (/ real_gt_neq r real_0 p) n));auto.
   rewrite !(real_mult_comm (pow real_2 _)).
   apply real_le_mult_pos_le.
   - apply pow_nonneg.
     apply real_lt_le.
     apply real_pos_inv_pos;auto.
  - apply pow_monotone;auto.
    apply real_lt_le.
    apply real_2_gt_1.
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
 Lemma seq_bound_smaller_r a M r1 p1 r2 p2: (r2 <= r1) -> (@bounded_seq a M r1 p1) -> (@bounded_seq a M r2 p2).
 Proof.
   intros P1 P2 n.
   apply (real_le_le_le _ ((pow real_2 M) * pow (/ real_gt_neq r1 real_0 p1) n));auto.
   apply real_le_mult_pos_le.
   - apply pow_nonneg.
     apply real_lt_le.
     apply real_lt_0_2.
   - apply pow_nonneg_le; [apply real_lt_le;apply real_pos_inv_pos|];auto.
     apply inv_le_ge;auto.
 Qed.    
 
 Definition sum_ps (a : bounded_ps) (b : bounded_ps) : bounded_ps.
 Proof.
   destruct a as [a M1 r1 r1gt0 Ba].
   destruct b as [b M2 r2 r2gt0 Bb].
   remember (Minmax.real_min r1 r2) as r.
   assert (r > real_0).
   {
     rewrite Heqr.
     destruct (Minmax.real_min_cand r1 r2) as [-> | ->];auto.
   }
   apply (mk_bounded_ps (sum a b) (S (max M1 M2)) r H).
   assert (forall  M' r' p, (@bounded_seq a M' r' p) -> (@bounded_seq b M' r' p) -> (@bounded_seq (sum a b) (S M') r' p)).
   {
     intros M' r' p B1 B2 n.
     apply (real_le_le_le _ _ _ (abs_tri (a n) (b n))).
     simpl; assert (forall x, real_2 *  x = x + x) as -> by (intros;ring_simplify; auto).
     rewrite real_mult_comm, real_mult_plus_distr.
     apply real_le_le_plus_le;rewrite real_mult_comm;auto.
   }
   apply H0.
   - apply (seq_bound_larger_M _ M1); [apply Nat.le_max_l |].
     apply (seq_bound_smaller_r _ _ r1 r1gt0);auto.
     rewrite Heqr.
     apply Minmax.real_min_fst_le.
   - apply (seq_bound_larger_M _ M2); [apply Nat.le_max_r |].
     apply (seq_bound_smaller_r _ _ r2 r2gt0);auto.
     rewrite Heqr.
     apply Minmax.real_min_snd_le.
 Defined.


  Lemma eval_radius_sum_both {x a b} : abs x <= (eval_radius a) -> abs x <= (eval_radius b) -> abs x <= (eval_radius (sum_ps a b)).
  Proof.
   unfold eval_radius.
   destruct a.
   destruct b.
   unfold bounded_ps_r.
   simpl.
   intros.
   destruct (Minmax.real_min_cand bounded_ps_r0 bounded_ps_r1) as [-> | ->];auto.
 Qed.
  
 Lemma eval_spec a x H : (is_fast_limit (eval a x H) (partial_sum_inc (ps (series a) x) (bounded_ps_M a))).
 Proof.
   unfold eval.
   destruct (evaluation a x H).
   simpl.
   exact i.
 Qed.

 Lemma dist_plus x y x' y' : dist (x+x') (y + y') <= dist x y + dist x' y'.
 Proof.
   unfold dist.
   assert (x + x' - (y + y') = (x-y + (x' - y'))) as -> by ring.
   apply abs_tri.
 Qed.

 Lemma sum_limit a b x y : is_fast_limit x a -> is_fast_limit y b -> is_fast_limit (x + y) (fun n => a (S n) + b (S n)).
 Proof.
   intros.
   intro n.
   apply (real_le_le_le _ _ _ (dist_plus x (a (S n)) y (b (S n)))).
   rewrite <-prec_twice.
   apply real_le_le_plus_le; rewrite Nat.add_1_r;auto.
Qed.

 
 Lemma real_limit_limit_p a x : is_fast_limit x a <-> is_fast_limit_p x a.
 Proof.
   split; intros H n;apply dist_le_prop;auto.
 Qed.

 Lemma real_limit_unique a x y : is_fast_limit x a -> is_fast_limit y a -> x=y.
 Proof.
  rewrite !real_limit_limit_p.
  apply limit_is_unique.
Qed.

 Lemma is_fast_limit_speedup a x M1 M2 : (M1 <= M2)%nat -> is_fast_limit x (partial_sum_inc a M1) -> is_fast_limit x (partial_sum_inc a M2).
 Proof.
   intros H1 H2 n.
   unfold partial_sum_inc.
   assert (n+M2 = n+(M2-M1)+M1)%nat as -> by lia.
   apply (real_le_le_le _ (prec (n + (M2-M1))%nat)); [apply H2 |].
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

 Lemma sum_ps_series a b n : series (sum_ps a b) n = series a n + series b n.
 Proof.
   destruct a; destruct b.
   simpl.
   auto.
 Qed.

 Lemma sum_ps_partial_sum a b x n : partial_sum (ps (series (sum_ps a b)) x) n = partial_sum (ps (series a) x) n + partial_sum (ps (series b) x) n.
 Proof.
   destruct a; destruct b;simpl.
   induction n.
   - unfold sum,ps.
     simpl;ring_simplify;auto.
   - simpl.
     rewrite IHn.
     unfold sum,ps.
     ring_simplify;auto.
 Qed.

 Lemma sum_ps_M_larger a b : ((bounded_ps_M a) <= (bounded_ps_M (sum_ps a b)) /\ (bounded_ps_M b) <= (bounded_ps_M (sum_ps a b)))%nat.
 Proof.
   destruct a,b;simpl.
   split; apply Nat.le_le_succ_r; [apply Nat.le_max_l | apply Nat.le_max_r ].
 Qed.

 Lemma sum_plus (a : bounded_ps) (b: bounded_ps) x H1 H2 : (eval a x H1) + (eval b x H2) = (eval (sum_ps a b) x (eval_radius_sum_both H1 H2)).

 Proof.
   pose proof (eval_spec a x H1) as E1.
   pose proof (eval_spec b x H2) as E2.
   pose proof (eval_spec (sum_ps a b) x (eval_radius_sum_both H1 H2)) as E3.
   pose proof (sum_ps_M_larger a b) as [L1 L2].
   remember (series a) as s1; remember (series b) as s2; remember (bounded_ps_M a) as M1; remember (bounded_ps_M b) as M2; remember (bounded_ps_M (sum_ps a b)) as M3.
   apply (is_fast_limit_speedup _  _ _ _ L1) in E1.
   apply (is_fast_limit_speedup _  _ _ _ L2) in E2.
   pose proof (sum_limit _ _ _ _ E1 E2).
   apply (real_limit_unique _ _ _ H).
   intros n.
   apply (real_le_le_le _ _ _ (dist_tri _ ((partial_sum_inc (ps (series (sum_ps a b )) x) M3) (S n)) _)).
   rewrite <-prec_twice, Nat.add_1_r.
   apply real_le_le_plus_le; auto.
   unfold partial_sum_inc.
   rewrite sum_ps_partial_sum.
   rewrite <-Heqs1, <-Heqs2.
   apply (real_le_le_le _ real_0); [apply real_eq_le; apply dist_zero;auto | apply real_lt_le; apply prec_pos ].
Qed.
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
