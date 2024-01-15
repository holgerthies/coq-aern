Require Import Real.
Require Import Euclidean.
Require Import List.
Require Import Psatz.
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

Section RealHelpers.
 Lemma real_le_mult_pos_le_le r1 r2 r3 r4 : (real_0 <= r1) -> (real_0 <= r2) -> (r1 <= r3) -> (r2 <= r4) -> (r1 * r2 <= r3 * r4).
 Proof.
   intros.
   apply (real_le_le_le _ _ _ (real_le_mult_pos_le _ _ _ H H2)).
   rewrite !(real_mult_comm _ r4).
   apply real_le_mult_pos_le; auto.
   apply (real_le_le_le _ r2);auto.
 Qed.

  Lemma real_lt_mult_pos_lt_lt r1 r2 r3 r4:  (real_0 <= r1) -> (real_0 < r3) -> (real_0 < r4) -> r1 < r3 -> r2 < r4 -> r1 * r2 < r3 * r4.
  Proof.
    intros.
    apply (real_le_lt_lt _ (r1 * r4)).
    apply real_le_mult_pos_le;auto.
    apply real_lt_le;auto.
    apply real_lt_mult_r_pos_lt;auto.
 Qed.

  Lemma dist_plus_le a b c d : dist (a+b) (c+d) <= dist a c + dist b d.
  Proof.
    unfold dist.
    assert (a+b - (c+d) = (a-c) + (b-d)) as -> by ring.
    apply abs_tri.
  Qed.
End RealHelpers.

Section Power.

  Fixpoint npow (x : Real) (n : nat) : Real :=
    match n with
    | O => real_1
    | S m => x * (npow x m)
    end.

 Lemma npow_pos r : (real_0 < r) -> forall n, real_0 < npow r n.
  Proof.
    intros H n.
    induction n; [apply real_1_gt_0 | ].
    simpl.
    pose proof (real_lt_mult_pos_lt _ _ _ H IHn).
    ring_simplify in H0.
    apply H0.
  Qed.
 
  Lemma npow_nonneg r : (real_0 <= r) -> forall n, real_0 <= npow r n.
  Proof.
    intros H n.
    destruct H; [apply real_lt_le;apply npow_pos;auto |].
    rewrite <-H.
    induction n;[apply real_lt_le; apply real_1_gt_0 | ].
    apply real_eq_le.
    simpl.
    ring.
  Qed.

  Lemma npow_nonneg_le r1 r2 n : (real_0 <= r1) -> (r1 <= r2) -> (npow r1 n) <= (npow r2 n).
  Proof.
    intros.
    induction n; [apply real_le_triv|].
    simpl.
    apply real_le_mult_pos_le_le;auto.
    apply npow_nonneg;auto.
  Qed.

  Lemma npow_neq_0 r n : (real_0 < r) -> npow r n <> real_0.
  Proof.
    intros H.
    apply real_gt_neq.
    apply npow_pos.
    exact H.
  Qed.

 Lemma npow_1 n : npow real_1 n = real_1.
 Proof.
   induction n;auto.
   simpl.
   rewrite IHn.
   ring.
 Qed.

  Lemma abs_npow_distr r n : abs (npow r n) = npow (abs r) n.
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


  Lemma npow_plus r n m : npow r (n+m) = npow r n * npow r m.
  Proof.
   induction m.
   rewrite <- plus_n_O;simpl;ring.
   rewrite Nat.add_succ_r.
   simpl.
   rewrite IHm.
   ring.
  Qed.

  Lemma npow_mult r1 r2 n : (npow r1 n) * (npow r2 n) = (npow (r1 * r2) n).
  Proof.
    induction n;[simpl;ring|].
    simpl.
    rewrite <-IHn.
    ring.
  Qed.

  Lemma npow_prec n : npow (/ real_2_neq_0) n = prec n.
  Proof.
   induction n;auto.
   simpl.
   rewrite IHn.
   unfold real_div.
   ring.
  Qed.

End Power.

Section Polynomials.
  
  Definition poly := list ^Real.

  Fixpoint eval_poly (a : poly) (x : Real) :=
    match a with
    | nil => real_0
    | h :: t => h + x * (eval_poly t x)  
    end.


  Lemma bound_polynomial p r : {B | forall x, abs x <= r -> abs (eval_poly p x) <= B}.
  Proof.
   induction p as [| a0 p' IH]; [exists real_0;intros; simpl;rewrite abs_pos_id; apply real_le_triv | ].
   destruct IH as [B' H].
   exists (abs a0 + r * B').
   intros.
   simpl.
   apply (real_le_le_le _ _ _ (abs_tri _ _)).
   apply real_le_plus_le.
   rewrite abs_mult.
   apply real_le_mult_pos_le_le;auto;apply abs_pos.
  Defined.

 Lemma smul_poly lambda p1: {p2 | forall x, eval_poly p2 x = lambda * eval_poly p1 x}.
 Proof.
   induction p1 as [| a0 p1' IH]; [exists []; intros;simpl;ring |].
   destruct IH as [p2' H].
   exists ((lambda * a0) :: p2' ).
   intros.
   simpl.
   replace (lambda * (a0 + x*eval_poly p1' x)) with (lambda*a0 + x * (lambda * eval_poly p1' x)) by ring.
   rewrite H;auto.
 Defined.
End Polynomials.

Section Addition.
  Definition sum_polyf  : poly -> poly -> poly.
  Proof.
    intros p1.
    induction p1 as [|a0 p1' S]; intros p2.
    apply p2.
    destruct p2 as [|b0 p2'].
    apply (a0 :: p1').
    apply ((a0 + b0) :: (S p2')).
  Defined.


  Lemma sum_polyf_spec p1 p2 x: eval_poly (sum_polyf p1 p2) x = eval_poly p1 x + eval_poly p2 x.
  Proof.
    revert p2.
    induction p1 as [| a0 p1'];intros; [simpl;ring|].
     destruct p2 as [| b0 p2'];[simpl;ring|].
     simpl.
     assert (forall y z u, y = z + u -> a0 + b0 + y = a0+z+(b0+u)) by (intros;rewrite H;ring).
     apply H.
     rewrite <-real_mult_plus_distr.
     apply real_eq_mult_eq.
     apply IHp1'.
  Qed.

 Lemma length_sum_coefficients a b : length (sum_polyf a b) = Nat.max (length a) (length b).
 Proof.
   revert b.
   induction a;simpl;auto.
   intros.
   destruct b;simpl; auto.
 Qed.

 Lemma sum_coefficient_nth a b n : nth n (sum_polyf a b) real_0 = nth n a real_0 + nth n b real_0.
 Proof.
 revert n b.
 induction a;intros;simpl.
 destruct n;auto;ring.
 destruct b;destruct n;simpl; try ring;auto.
 Qed.

 Lemma sum_poly p1 p2 : {p3 | forall x, eval_poly p3 x = eval_poly p1 x + eval_poly p2 x}.
 Proof.
   exists (sum_polyf p1 p2).
   apply sum_polyf_spec.
 Defined.

 Lemma sum_poly_ext p1 p2 l1 l2 : {p3 | forall x, eval_poly p3 x = l1 * eval_poly p1 x + l2 * eval_poly p2 x}.
 Proof.
   destruct (smul_poly l1 p1) as [lp1 H1].
   destruct (smul_poly l2 p2) as [lp2 H2].
   destruct (sum_poly lp1 lp2) as [p3 H3].
   exists p3.
   intros.
   rewrite H3, H2, H1;auto.
 Defined.

 Lemma sub_poly p1 p2 : {p3 | forall x, eval_poly p3 x = eval_poly p1 x - eval_poly p2 x}.
 Proof.
   destruct (sum_poly_ext p1 p2 real_1 (-real_1)) as [p3 H].
   exists p3.
   intros;rewrite H;ring.
 Defined.
End Addition.

Section Multiplication.

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
 Lemma convolution_coeff_rec_nil2 a i j : convolution_coeff_rec a [] j i = real_0.
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

 Lemma mult_coefficients_eval_single a0 b x : eval_poly (mult_coefficients [a0] b) x = a0 * eval_poly b x.
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
 Lemma mult_coefficients_eval_nil b x : eval_poly (mult_coefficients [] b) x = real_0.
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

 
 Lemma convolution_coeff_rec_inv_S a b n i : (i < n)%nat -> convolution_coeff_rec a b n (n-i) = convolution_coeff_rec a b n (n - S i) + nth i a real_0 * nth (n-i)%nat b real_0.
 Proof.
   simpl.
   destruct (n-i)%nat eqn:E.
   lia.
   intros.
   simpl.
   rewrite <-E.
   replace (n - (n-i))%nat with i by lia.
   destruct (n - S i)%nat eqn:E'.
   replace n0 with 0 by lia.
   simpl.
   ring.
   replace n0 with (S n1) by lia.
   ring.
 Qed.

 Lemma convolution_coeff_rec_opp_S a b n i: (S i < n)%nat -> convolution_coeff_rec a b n (S i) =  convolution_coeff_rec a b n i + convolution_coeff_rec b a n (n-(S i)) - convolution_coeff_rec b a n (n-(S (S i)))%nat.
 Proof.
   intros.
   rewrite convolution_coeff_rec_inv_S;auto.
   simpl.
   ring.
 Qed.

 Lemma convolution_coeff_rec_opp a b n i: (i < n)%nat -> convolution_coeff_rec a b n n = convolution_coeff_rec a b n (n-S i)%nat + convolution_coeff_rec b a n i.
 Proof.
   intros.
   induction i.
   - destruct n; try lia.
     simpl.
     rewrite Nat.sub_diag.
     rewrite Nat.sub_0_r.
     ring.
   - rewrite IHi; try lia.
     rewrite convolution_coeff_rec_opp_S; try lia.
     ring.
 Qed.
 Lemma convolution_coeff_sym a b n : convolution_coeff a b n = convolution_coeff b a n.
 Proof.
  unfold convolution_coeff.
  destruct n; [simpl; ring | ].
  rewrite (convolution_coeff_rec_opp _ _ _ (n-1)%nat);try lia.
  destruct n; [simpl;ring|].
  replace (S (S n) - S (S n - 1))%nat with 1 by lia.
  simpl.
  rewrite Nat.sub_0_r, Nat.sub_diag.
  ring_simplify.
  destruct n.
  ring.
  replace (S n - n)%nat with 1 by lia.
  ring.
 Qed.

 Lemma mult_coefficients_sym a b : mult_coefficients a b  = mult_coefficients b a.
 Proof.
   apply (nth_ext _ _ real_0 real_0).
   rewrite !length_mult_coefficients;lia.
   intros.
   rewrite length_mult_coefficients in H.
   rewrite !mult_coefficients_spec; try lia.
   apply convolution_coeff_sym.
  Qed.

 Lemma mult_coefficients_cons a b a0 b0 : mult_coefficients (a0 :: a) (b0 :: b) = sum_polyf (mult_coefficients [a0] (b0 :: b)) (real_0 :: mult_coefficients a (b0 :: b)).
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

 Lemma mult_coefficients_eval_cons a b a0 x : eval_poly (mult_coefficients (a0 :: a) b) x = a0 * eval_poly b x + x*eval_poly (mult_coefficients a b) x.
 Proof.
   rewrite <-mult_coefficients_eval_single.
   destruct b.
   - rewrite !(mult_coefficients_sym _ []).
     rewrite !mult_coefficients_eval_nil.
     ring.
   - rewrite mult_coefficients_cons.
     rewrite sum_polyf_spec;simpl.
     ring.
 Qed.

 Lemma mult_coeff_spec a b x : eval_poly (mult_coefficients a b) x = eval_poly a x * eval_poly b x.
 Proof.
   induction a; [rewrite mult_coefficients_eval_nil;simpl;ring |].
   simpl.
   rewrite mult_coefficients_eval_cons.
   rewrite IHa.
   ring.
 Qed.

 Lemma mult_poly p1 p2 : {p3 | forall x, eval_poly p3 x = eval_poly p1 x * eval_poly p2 x}.
 Proof.
   exists (mult_coefficients p1 p2).
   apply mult_coeff_spec.
 Defined.
End Multiplication.

Section Shift.
  Lemma shift_poly p1 c : {p2 | forall x, eval_poly p2 x = eval_poly p1 (x-c)}.
  Proof.
    induction p1 as [| a0 p1' IH]; [exists []; intros; simpl; ring | ].
    destruct IH as [p2 IH].
    destruct (mult_poly [-c; real_1] p2) as [q Q].
    destruct (sum_poly [a0] q) as [q' Q'].
    exists q'.
    intros.
    rewrite Q', Q, IH.
    simpl.
    ring.
 Qed.

  Lemma split_poly p d : {qu | (length (fst qu)) = (min d (length p)) /\ (length (snd qu)) = (length p - d)%nat /\ forall x, eval_poly p x = eval_poly (fst qu) x + npow x d * eval_poly (snd qu) x}.
  Proof.
    exists (firstn d p, skipn d p).
    split; [apply firstn_length|split;[apply skipn_length|]].
    intros.
    simpl.
    revert d.
    induction p; intros;[rewrite firstn_nil, skipn_nil;simpl;ring |].
    destruct d; [simpl;ring|].
    rewrite firstn_cons, skipn_cons.
    simpl.
    rewrite (IHp d).
    ring.
 Defined.
End Shift.

  
