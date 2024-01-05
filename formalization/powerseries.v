Require Import Real.
Require Import MultiLimit.
Require Import Euclidean.
Require Import Nnat.
Require Import ArithRing.
Require Export Ring Field.
Require Import Psatz.
Require Import List.
Import ListNotations.
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
  Lemma pow_pos r : (real_0 < r) -> forall n, real_0 < pow r n.
  Proof.
    intros H n.
    induction n; [apply real_1_gt_0 | ].
    simpl.
    pose proof (real_lt_mult_pos_lt _ _ _ H IHn).
    ring_simplify in H0.
    apply H0.
  Qed.

  Lemma pow_mult r1 r2 n : (pow r1 n) * (pow r2 n) = (pow (r1 * r2) n).
  Proof.
    induction n;[simpl;ring|].
    simpl.
    rewrite <-IHn.
    ring.
  Qed.

  Lemma pow_nonneg r : (real_0 <= r) -> forall n, real_0 <= pow r n.
  Proof.
    intros H n.
    destruct H; [apply real_lt_le;apply pow_pos;auto |].
    rewrite <-H.
    induction n;[apply real_lt_le; apply real_1_gt_0 | ].
    apply real_eq_le.
    simpl.
    ring.
  Qed.

  Lemma pow_neq_0 r n : (real_0 < r) -> pow r n <> real_0.
  Proof.
    intros H.
    apply real_gt_neq.
    apply pow_pos.
    exact H.
  Qed.

  Lemma pow_abs r n : abs (pow r n) = pow (abs r) n.
  Proof.
    induction n.
    - simpl.
      apply abs_pos_id.
      apply real_lt_le.
      apply real_1_gt_0.
    - simpl.
      rewrite abs_mult.
      rewrite IHn.
      auto.
  Qed.
 Lemma pow_plus r n m : pow r (n+m) = pow r n * pow r m.
 Proof.
   induction m.
   rewrite <- plus_n_O;simpl;ring.
   rewrite Nat.add_succ_r.
   simpl.
   rewrite IHm.
   ring.
 Qed.

 Lemma pow_1 n : pow real_1 n = real_1.
 Proof.
   induction n;auto.
   simpl.
   rewrite IHn.
   ring.
 Qed.

 Lemma pow_prec n : pow (/ real_2_neq_0) n = prec n.
 Proof.
   induction n;auto.
   simpl.
   rewrite IHn.
   unfold real_div.
   ring.
 Qed.
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
 Lemma real_le_mult_pos_le_le r1 r2 r3 r4 : (real_0 <= r1) -> (real_0 <= r2) -> (r1 <= r3) -> (r2 <= r4) -> (r1 * r2 <= r3 * r4).
 Proof.
   intros.
   apply (real_le_le_le _ _ _ (real_le_mult_pos_le _ _ _ H H2)).
   rewrite !(real_mult_comm _ r4).
   apply real_le_mult_pos_le; auto.
   apply (real_le_le_le _ r2);auto.
 Qed.

  Lemma pow_nonneg_le r1 r2 n : (real_0 <= r1) -> (r1 <= r2) -> (pow r1 n) <= (pow r2 n).
  Proof.
    intros.
    induction n; [apply real_le_triv|].
    simpl.
    apply real_le_mult_pos_le_le;auto.
    apply pow_nonneg;auto.
  Qed.

End Power.

Section PolynomialModels.

 Record polynomial_model : Type := mk_polynomial_model
                                     {
                                       pm_coeffs : list ^Real;
                                       pm_radius: ^Real;
                                       pm_error : ^Real
                                     }.

  Fixpoint eval_series (a : list Real) (x : Real) :=
    match a with
    | nil => real_0
    | h :: t => h + x * (eval_series t x)  
    end.


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
  Lemma dist_plus_le a b c d : dist (a+b) (c+d) <= dist a c + dist b d.
  Proof.
    unfold dist.
    assert (a+b - (c+d) = (a-c) + (b-d)) as -> by ring.
    apply abs_tri.
  Qed.

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
 Fixpoint convolution_coeff_rec (a b : list Real) n i :=
   nth (n-i)%nat a real_0 * nth i b real_0 + match i with
     | 0 => real_0
     | S i' => convolution_coeff_rec a b n i'
    end.
 Definition convolution_coeff (a b : list Real) n := convolution_coeff_rec a b n n.

   Lemma convolution_coeff_rec_cons a b a0 n i  :(i <= n)%nat -> convolution_coeff_rec (a0 :: a) b (S n) i = convolution_coeff_rec a b n i.
  Proof.
   intros.
   induction i.
   - simpl.
     rewrite Nat.sub_0_r;unfold nth;simpl.
     ring.
   - simpl.
     assert (i < n)%nat by lia.
     destruct (n-i)%nat eqn: E; [lia|].
     rewrite IHi; try lia.
     assert ((n - S i)%nat = n0) as -> by lia.
     ring.
 Qed. 

 Lemma convolution_coeff_cons a b a0 n : convolution_coeff (a0 :: a) b (S n) = a0 * nth (S n) b real_0 + convolution_coeff a b n.
 Proof.
   unfold convolution_coeff.
   simpl.
   destruct (n-n)%nat eqn:E;rewrite convolution_coeff_rec_cons;try lia;auto.
 Qed.
   
 Fixpoint mult_coefficients_rec (a b : list Real) n :=
   match n with
    | 0 => []
    | S n' =>  convolution_coeff a b ((length a + length b - 1) - n)%nat :: mult_coefficients_rec a b n'
     end.

 Definition mult_coefficients_rec_spec a b n m : (n < m)%nat -> nth n (mult_coefficients_rec a b m) real_0 = convolution_coeff a b (length a + length b - 1  + n - m)%nat .
 Proof.
   revert n.
   induction m; intros; try lia.
   destruct n; simpl;try rewrite Nat.add_0_r;auto.
   rewrite IHm;try lia.
   assert (length a + length b - 1 + S n - S m = length a + length b - 1 + n - m)%nat as -> by lia.
   auto.
 Qed.

 Definition mult_coefficients a b := mult_coefficients_rec a b (length a + length b - 1).

 Definition mult_coefficients_spec a b n : (n < length a + length b - 1)%nat -> nth n (mult_coefficients a b) real_0 = convolution_coeff a b n.
 Proof.
   intros.
   unfold mult_coefficients.
   rewrite mult_coefficients_rec_spec; auto.
   assert (length a + length b - 1 + n - (length a + length b - 1) = n)%nat as -> by lia.
   reflexivity.
 Qed.

 Lemma length_mult_coefficients a b : length (mult_coefficients a b) = (length a + length b - 1)%nat.
 Proof.
   unfold mult_coefficients.
   induction (length a + length b - 1)%nat; simpl; try lia.
 Qed.
 Lemma convolution_coeff_rec_nil b i j : convolution_coeff_rec [] b j i = real_0.
 Proof.
   induction i;intros.
   simpl.
   destruct (j-0)%nat;ring.
   simpl.
   rewrite IHi.
   destruct (j - S i)%nat;ring.
 Qed.    
 Lemma mult_coefficients_single a0 b n : nth n (mult_coefficients [a0] b) real_0 = a0 * (nth n b real_0).
 Proof.
   destruct (Nat.le_gt_cases (n+1) ((length b))%nat).
   - rewrite mult_coefficients_spec; simpl;try rewrite Nat.sub_0_r;try lia.
     destruct n;unfold convolution_coeff;simpl.
     ring.
     rewrite Nat.sub_diag.
     rewrite convolution_coeff_rec_cons; try lia.
     rewrite convolution_coeff_rec_nil.
     ring.
   - assert (length (mult_coefficients [a0] b) <= n)%nat.
    {
     rewrite length_mult_coefficients.
     simpl.
     lia.
    }
    rewrite !nth_overflow;try ring;try lia;auto.
 Qed.

 Lemma mult_coefficients_single_list a0 b : mult_coefficients [a0] b = map (fun x => a0 * x) b.
 Proof.
   apply (nth_ext _ _ real_0 real_0).
   - rewrite length_mult_coefficients, map_length.
     simpl; lia.
  - intros.
    rewrite mult_coefficients_single.
    assert (real_0 = ((fun x => a0 * x) real_0)) as R by ring.
    rewrite R, map_nth.
    rewrite <-R.
    reflexivity.
 Qed.

 Lemma mult_coefficients_eval_single a0 b x : eval_series (mult_coefficients [a0] b) x = a0 * eval_series b x.
 Proof.
   rewrite mult_coefficients_single_list.
   induction b;simpl;try ring.
   rewrite IHb.
   ring.
 Qed.

 Lemma mult_coefficients_nil b n : nth n (mult_coefficients [] b) real_0 = real_0.
 Proof.
   destruct (Nat.le_gt_cases (n+1) ((length b-1))%nat).
   - rewrite mult_coefficients_spec; simpl; try lia.
     unfold convolution_coeff.
     apply convolution_coeff_rec_nil.
  - rewrite nth_overflow;auto.
    rewrite length_mult_coefficients.
    simpl;lia.
 Qed.
 Lemma mult_coefficients_nil_list b : mult_coefficients [] b = repeat real_0 (length b - 1)%nat.
 Proof.
    apply (nth_ext _ _ real_0 real_0).
    rewrite length_mult_coefficients, repeat_length.
    simpl;lia.
    intros.
    rewrite mult_coefficients_nil, nth_repeat;auto.
 Qed.
 Lemma mult_coefficients_eval_nil b x : eval_series (mult_coefficients [] b) x = real_0.
 Proof.
    rewrite mult_coefficients_nil_list.
    induction (length b - 1)%nat;simpl;auto.
    rewrite IHn.
    ring.
 Qed.

 Lemma convolution_coeff_zero a b n: (length a + length b - 1<= n)%nat  -> convolution_coeff a b n = real_0.
 Proof.
   revert n.
   induction a;intros.
   unfold convolution_coeff.
   rewrite convolution_coeff_rec_nil;auto.
   simpl in H.
   destruct n.
   - assert (b = []) as -> by (apply length_zero_iff_nil;lia).
     unfold convolution_coeff.
     simpl;ring.
   - rewrite convolution_coeff_cons.
     rewrite IHa; simpl in H;try lia.
      rewrite nth_overflow; [ring | lia].
 Qed.

 Lemma mult_coefficients_cons_nth a0 a b n : nth (S n) (mult_coefficients (a0 :: a) b) real_0 = a0 * nth (S n) b real_0 + convolution_coeff a b n.
 Proof.
   destruct (Nat.le_gt_cases (S n) ((length a+length b - 1))%nat).
   - rewrite mult_coefficients_spec; simpl; try lia.
     rewrite convolution_coeff_cons;auto.
  - rewrite !nth_overflow;try rewrite length_mult_coefficients;simpl; try lia.
    rewrite convolution_coeff_zero;  [ring | lia].
 Qed.

 Lemma length_sum_coefficients a b : length (sum_coefficients a b) = Nat.max (length a) (length b).
 Proof.
   revert b.
   induction a;simpl;auto.
   intros.
   destruct b;simpl; auto.
 Qed.

 Lemma sum_coefficient_nth a b n : nth n (sum_coefficients a b) real_0 = nth n a real_0 + nth n b real_0.
 Proof.
 revert n b.
 induction a;intros;simpl.
 destruct n;auto;ring.
 destruct b;destruct n;simpl; try ring;auto.
 Qed.
 Lemma convolution_coeff_sym a b n : convolution_coeff a b n = convolution_coeff b a n.
 Proof.
    revert n b.
    induction a;intros.
    unfold convolution_coeff.
    rewrite convolution_coeff_rec_nil.
    admit.
    destruct n.
    unfold convolution_coeff.
    simpl.
    ring.
    rewrite convolution_coeff_cons.
    simpl.
    unfold convolution_coeff; simpl.
 Lemma mult_coefficients_sym a b : mult_coefficients a b  = mult_coefficients b a.
 Proof.
   apply (nth_ext _ _ real_0 real_0).
   rewrite !length_mult_coefficients;lia.
   intros.
   rewrite length_mult_coefficients in H.
   rewrite !mult_coefficients_spec; try lia.
   induction n.
   unfold convolution_coeff.
   simpl.
   ring.

   unfold convolution_coeff.
   simpl.
   rewrite Nat.sub_diag.
   simpl.
 Lemma mult_coefficients_cons a b a0 b0 : mult_coefficients (a0 :: a) (b0 :: b) = sum_coefficients (mult_coefficients [a0] (b0 :: b)) (real_0 :: mult_coefficients a (b0 :: b)).
 Proof.
   apply (nth_ext _ _ real_0 real_0).
   - rewrite length_sum_coefficients.
     rewrite !length_mult_coefficients;simpl.
     rewrite length_mult_coefficients;simpl.
     rewrite max_r;try lia.
   - intros.
     rewrite length_mult_coefficients in H.
     simpl in H.
     rewrite mult_coefficients_spec; try (simpl;lia).
     rewrite sum_coefficient_nth.
     rewrite !mult_coefficients_single_list.
     destruct n;simpl; [unfold convolution_coeff;simpl;ring|].
     rewrite convolution_coeff_cons.
     rewrite mult_coefficients_spec; try (simpl;lia).
     assert (real_0 = a0 * real_0) as R by ring.
     rewrite R,map_nth.
     simpl.
     rewrite <-R;auto.
 Qed.

 Lemma mult_coefficients_eval_cons a b a0 x : eval_series (mult_coefficients (a0 :: a) b) x = a0 * eval_series b x + x*eval_series (mult_coefficients a b) x.
 Proof.
   rewrite <-mult_coefficients_eval_single.
   induction a.
   simpl.
   - rewrite mult_coefficients_eval_nil.
     ring.
  - simpl.
    rewrite Nat.sub_diag.
    unfold convolution_coeff.
    simpl.
 Lemma mult_eval a b x : eval_series (mult_coefficients a b) x = eval_series a x * eval_series b x.
 Proof.
   revert b.
   induction a.
   intros.
   admit.
   intros.
   simpl.
   simpl.
   unfold convolution_coeff, convolution_coeff_rec.
   rewrite Nat.sub_diag.
   simpl.
   unfold nth_default.
   simpl.
   ring_simplify.
End PolynomialModels.

Section Powerseries.


  Definition bounded_seq (a : nat -> Real) M {r : Real} (H : real_0 < r)  :=  forall n, abs (a n) <= pow (real_2) M * (pow (/ (real_gt_neq _ _ H)) n).
                                                                                                         

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

 Definition ps a x n := (a n) * pow x n. 

 Definition partial_sum_inc a m n := partial_sum a (n+m)%nat.

 Lemma ps_fast_cauchy a M {r} (rgt0 : real_0 < r)  : bounded_seq a M rgt0 -> forall x, abs x <=  (r / real_2_neq_0) -> is_fast_cauchy (partial_sum_inc (ps a x) M). 
 Proof.
   intros.
   apply tmpn_cauchy.
   intros.
   unfold ps.
   unfold bounded_seq in H.
   rewrite abs_mult.
   apply (real_le_le_le _ (((pow real_2 M) * (pow (/ (real_gt_neq _ _ rgt0)) (n + M)%nat) * (pow (r / real_2_neq_0) (n+M)%nat)))).
   - apply real_le_mult_pos_le_le; try apply abs_pos;[apply H|].
     rewrite pow_abs.
     apply pow_nonneg_le;auto.
     apply abs_pos.
  - rewrite real_mult_assoc.
    rewrite pow_mult.
    unfold real_div.
    rewrite <-real_mult_assoc.
    assert (/ real_gt_neq r real_0 rgt0 * r = real_1) as -> by apply real_mult_inv.
    rewrite real_mult_unit.
    rewrite pow_plus.
    rewrite real_mult_comm, real_mult_assoc.
    rewrite pow_mult.
    assert (/ real_2_neq_0 * real_2 = real_1) as -> by apply real_mult_inv.
    apply real_eq_le.
    rewrite pow_1.
    rewrite pow_prec.
    ring.
 Qed.

 Record bounded_ps : Type := mk_bounded_ps
                               {
                                 series : nat -> ^Real;
                                 bounded_ps_M : nat;
                                 bounded_ps_r :^Real;
                                 bounded_ps_rgt0 : bounded_ps_r > real_0;
                                 bounded_ps_bounded: bounded_seq series bounded_ps_M bounded_ps_rgt0 
                               }.
 Definition eval_radius (a : bounded_ps) := ((bounded_ps_r a) / real_2_neq_0).

 Definition evaluation (a : bounded_ps) (x : Real):  abs x <=  (eval_radius  a) -> {y : Real | is_fast_limit y (partial_sum_inc (ps (series a) x) (bounded_ps_M a))}.
 Proof.
   destruct a as [a M r rgt0 B].
   intros.
   destruct (real_limit (fun n => (partial_sum (ps a x) (n+M)%nat))).
   apply (ps_fast_cauchy a M rgt0);auto.
   exists x0.
   apply i.
 Defined.

 Definition eval a x H := projP1 _ _ (evaluation a x H).
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
