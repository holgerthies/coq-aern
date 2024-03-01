Require Import Real.
Require Import RealAssumption.
Require Import Euclidean.
Require Import List.
Require Import Psatz.
Import ListNotations.


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

  Fixpoint eval_poly_rec (a : poly) (x : Real) (n : nat) :=
    match n with
    | 0 => real_0
    | (S n') => last a real_0  * (npow x n') + eval_poly_rec (removelast a) x n'
    end.

  Definition eval_poly2 a x := eval_poly_rec a x (length a).

  Lemma eval_poly2_app1 a an x : eval_poly2 (a ++ [an]) x = an * (npow x (length a)) + eval_poly2 a x.
  Proof.
    unfold eval_poly2 at 1.
    replace (length (a ++ [an])) with (S (length a)) by (rewrite app_length;simpl;lia).
    simpl.
    rewrite last_last.
    rewrite removelast_last.
    auto.
  Qed.

  Lemma eval_poly2_app a b x : eval_poly2 (a ++ b) x  = eval_poly2 a x  + npow x (length a) * eval_poly2 b x. 
  Proof.
  revert a.
  induction b as [| b0 b IH];intros.
  rewrite app_nil_r;unfold eval_poly2;simpl;ring.
  replace (a ++ b0 :: b) with ((a ++ [b0]) ++ b) by (rewrite <-app_assoc;auto).
  rewrite IH.
  rewrite eval_poly2_app1.
  rewrite app_length.
  simpl.
  rewrite real_plus_assoc, !(real_plus_comm (eval_poly2 a x)), <-real_plus_assoc.
  apply real_eq_plus_eq.
  replace (length a + 1)%nat with (S (length a)) by lia.
  simpl.
  replace (b0 * npow x (length a) + x *npow x (length a)*eval_poly2 b x) with (npow x (length a) * (b0 + x * eval_poly2 b x)) by ring.
  apply real_eq_mult_eq.
  replace (b0 :: b) with ([b0]++b) by auto.
  rewrite IH.
  unfold eval_poly2.
  simpl.
  ring.
  Qed.

  Lemma eval_eval2 a x : eval_poly a x = eval_poly2 a x.
  Proof.
    induction a as [| a0 a]; [unfold eval_poly2;simpl;ring|].
    replace (a0 :: a) with ([a0]++a) by auto.
    rewrite eval_poly2_app.
    simpl.
    rewrite IHa.
    unfold eval_poly2.
    simpl;ring.
  Qed.
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
   replace n0 with 0%nat by lia.
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
  replace (S (S n) - S (S n - 1))%nat with 1%nat by lia.
  simpl.
  rewrite Nat.sub_0_r, Nat.sub_diag.
  ring_simplify.
  destruct n.
  ring.
  replace (S n - n)%nat with 1%nat by lia.
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

Section Continuity.

  Definition continuous (f: Real -> Real) x := forall eps, eps > real_0 -> {d : Real | d > real_0 /\ forall y, dist x y <= d -> dist (f x) (f y) <= eps}.

  Lemma continuous_prod f1 f2 x: continuous f1 x -> continuous f2 x -> continuous (fun x => (f1 x) * (f2 x)) x.
  Proof.
    intros H1 H2.
    intros eps H.
    assert (abs (f1 x) + real_1 > real_0).
    {
      apply (real_lt_le_lt _ (real_0 + real_1)); [rewrite real_plus_unit; apply real_1_gt_0 |].
      apply real_le_le_plus_le; [apply abs_pos|apply real_le_triv].
    }
    remember (eps / (real_gt_neq _ _ H0) / real_2_neq_0) as eps0.
    assert (eps0 > real_0) as eps0gt0.
    {
    rewrite Heqeps0.
    apply real_half_gt_zero.
    unfold real_div.
    apply real_lt_pos_mult_pos_pos;auto.
    apply real_pos_inv_pos;auto.
    }
    destruct (H2 _ eps0gt0) as [d0 [d0gt0 D0]].
    assert (abs (f2 x) + eps0  > real_0).
    {
      
      apply (real_lt_le_lt _ (real_0 + eps0)); [rewrite real_plus_unit; auto |].
      apply real_le_le_plus_le; [apply abs_pos|apply real_le_triv].
    }
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
    unfold dist.
    replace (f1 x * f2 x - f1 y * f2 y) with ((f1 x * (f2 x -  f2 y)) + (f2 y * ( f1 x - f1 y))) by ring.
    replace eps with (eps / real_2_neq_0 + eps / real_2_neq_0) by apply half_twice.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    apply real_le_le_plus_le;rewrite abs_mult.
    - apply (real_le_le_le _ (abs (f1 x) * eps0)).
      + apply real_le_mult_pos_le; [apply abs_pos |].
        apply D0.
        apply (real_le_le_le _ _ _ H4).
        apply Minmax.real_min_fst_le.
      + rewrite Heqeps0.
        rewrite diff.
        apply half_le_le.
        unfold real_div.
        rewrite <-real_mult_assoc, real_mult_comm, <-real_mult_assoc, real_mult_comm.
        replace eps with ( eps * real_1) at 2 by ring.
        apply real_le_mult_pos_le;[apply real_lt_le;auto|].
        apply (real_le_mult_pos_cancel (abs (f1 x) + real_1));auto.
        rewrite real_mult_assoc, (real_mult_comm (abs (f1 x))), <-real_mult_assoc, real_mult_inv, !real_mult_unit.
        add_both_side_by (-abs (f1 x)).
        apply real_lt_le;apply real_1_gt_0.
     - apply (real_le_le_le _ (abs (f2 y) * eps1)).
      + apply real_le_mult_pos_le; [apply abs_pos |].
        apply D1.
        apply (real_le_le_le _ _ _ H4).
        apply Minmax.real_min_snd_le.
      + rewrite Heqeps1.
        rewrite diff.
        apply half_le_le.
        unfold real_div.
        rewrite <-real_mult_assoc, real_mult_comm, <-real_mult_assoc, real_mult_comm.
        replace eps with ( eps * real_1) at 2 by ring.
        apply real_le_mult_pos_le;[apply real_lt_le;auto|].
        apply (real_le_mult_pos_cancel (abs (f2 x) + eps0));auto.
        rewrite real_mult_assoc, (real_mult_comm (abs (f2 y))), <-real_mult_assoc, real_mult_inv, !real_mult_unit.
        apply dist_bound.
        apply D0.
        apply (real_le_le_le _ _ _ H4).
        apply Minmax.real_min_fst_le.
  Defined.

  Lemma continuous_sum f1 f2 x : continuous f1 x -> continuous f2 x -> continuous (fun x => (f1 x) + (f2 x)) x.
  Proof.
    intros H1 H2 eps H.
    assert (eps / real_2_neq_0 > real_0) by (apply real_half_gt_zero;auto).
    destruct (H1 _ H0) as [d [D0 D1]].
    destruct (H2 _ H0) as [d' [D0' D1']].
    exists (Minmax.real_min d d').
    split; [destruct (Minmax.real_min_cand d d') as [-> | ->];auto|].
    intros.
    apply (real_le_le_le _ _ _ (dist_plus_le _ _ _ _)).
    rewrite <-half_twice.
    apply real_le_le_plus_le; [apply D1 | apply D1'];apply (real_le_le_le _ _ _ H3).
    apply Minmax.real_min_fst_le.
    apply Minmax.real_min_snd_le.
  Defined.

  Lemma continuous_poly p : forall x, continuous (eval_poly p) x.
  Proof.
    intros x.
    induction p.
    exists real_1.
    split; [apply real_1_gt_0 | intros;simpl ];rewrite (proj2 (dist_zero real_0 real_0));try apply real_lt_le;auto.
    simpl.
    apply (continuous_sum (fun x => a) (fun x => x * eval_poly p x));auto.
    intros  eps' H'; exists real_1; split; [apply real_1_gt_0 |intros;simpl].
    rewrite (proj2 (dist_zero a a));try apply real_lt_le;auto.
    apply (continuous_prod (fun x => x) (eval_poly p));auto.
    intros eps H.
    exists eps;intros;auto.
 Defined.

End Continuity.

Section Derivative.
  Definition derivative (f: Real -> Real) (g : Real -> Real) x := forall eps, eps > real_0 -> {d : Real | d > real_0 /\ forall y, dist x y <= d -> abs (f y - f x - g x * (y -x)) <= eps * abs(y-x) }.

  
 Lemma derivable_continuous f g : forall x,  derivative f g x -> continuous f x.
 Proof.
   intros x D eps H.
   destruct (D _ (real_half_gt_zero _ H)) as [d [D1 D2]].
   pose proof (abs_plus_1_gt_0 (g x)).
    remember (eps / (real_gt_neq _ _ H0) / real_2_neq_0) as d'.
    assert (d' > real_0).
    {
      rewrite Heqd'.
      apply real_half_gt_zero.
      unfold real_div.
      apply real_lt_pos_mult_pos_pos;auto.
      apply real_pos_inv_pos;auto.
    }
    assert {d0 | d0 > real_0 /\ d0 <= d /\ d0 <= d' /\ d0 <= real_1} as [d0 [P1 [P2 [P3 P4]]]].
    {
     exists (Minmax.real_min real_1 (Minmax.real_min d d')).
     split; [destruct (Minmax.real_min_cand real_1 (Minmax.real_min d d')) as [-> | ->]|].
     apply real_1_gt_0.
     destruct (Minmax.real_min_cand d d') as [-> | ->];auto.
     split.
     apply (real_le_le_le _ _ _ (Minmax.real_min_snd_le _ _)).
     apply (Minmax.real_min_fst_le d d').
     split.
     apply (real_le_le_le _ _ _ (Minmax.real_min_snd_le _ _)).
     apply (Minmax.real_min_snd_le d d').
     apply (Minmax.real_min_fst_le ).
    }
    exists d0.
    split;auto.
    intros.
    rewrite dist_symm.
    unfold dist.
    replace (f y - f x) with ((f y - f x - g x * (y - x)) + g x * (y - x)) by ring.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    rewrite <-half_twice.
    apply real_le_le_plus_le.
   - apply (real_le_le_le _ ((eps / real_2_neq_0) * abs(y-x))); [apply D2; apply (real_le_le_le _ _ _ H2)|];auto.
     rewrite <-(real_mult_unit), (real_mult_comm real_1).
     apply real_le_mult_pos_le; [apply real_lt_le;apply real_half_gt_zero|];auto.
     rewrite dist_symm in H2.
     apply (real_le_le_le _ _ _ H2 P4).
   - rewrite abs_mult.
     rewrite real_mult_comm.
     apply (real_le_le_le _ (abs (y - x) * (abs (g x) + real_1)) _).
    apply real_le_mult_pos_le; try apply abs_pos; add_both_side_by (- abs (g x)); apply real_lt_le;apply real_1_gt_0.
    apply (real_le_mult_pos_cancel (/ real_gt_neq _ _ H0));[apply real_pos_inv_pos;auto |].
    rewrite real_mult_comm, (real_mult_comm (abs (y-x))), <-real_mult_assoc, real_mult_inv.
    ring_simplify.
    rewrite dist_symm in H2.
    apply (real_le_le_le _ _ _ H2).
    apply (real_le_le_le _ _ _ P3).
    rewrite Heqd'.
    unfold real_div; ring_simplify.
    apply real_le_triv.
  Defined.

  Definition derivative_sum f1 f2 g1 g2 x : derivative f1 g1 x -> derivative f2 g2 x -> derivative (fun x => (f1 x + f2 x)) (fun x => (g1 x + g2 x)) x.
  Proof.
    intros H1 H2 eps epsgt0.
    assert (eps / real_2_neq_0 > real_0) by (apply real_half_gt_zero;auto).
    destruct (H1 (eps / real_2_neq_0)) as [d1 [d1gt0 D1]];auto.
    destruct (H2 (eps / real_2_neq_0)) as [d2 [d2gt0 D2]];auto.
    exists (Minmax.real_min d1 d2);split;[destruct (Minmax.real_min_cand d1 d2) as [-> | ->];auto|].
    intros.
    replace (f1 y + f2 y - (f1 x + f2 x) - (g1 x + g2 x)*(y - x)) with ((f1 y - f1 x -(g1 x)*(y-x)) + (f2 y - f2 x - (g2 x)*(y-x))) by ring.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    replace (eps * abs (y-x)) with (eps /real_2_neq_0 * abs (y-x) + eps / real_2_neq_0 * abs (y-x)) by (rewrite <-(half_twice eps);ring_simplify;rewrite half_twice; ring).
    apply real_le_le_plus_le; [apply D1 | apply D2]; apply (real_le_le_le _ _ _ H0); [apply Minmax.real_min_fst_le | apply Minmax.real_min_snd_le].
 Qed.

  Lemma real_div_gt_0 x y (yd : y <> real_0) : x > real_0 -> y > real_0 -> (x / yd > real_0).
  Proof.
    intros.
    unfold real_div.
    rewrite real_mult_comm.
    apply (real_lt_mult_pos_cancel y);auto.
    rewrite real_mult_assoc, (real_mult_comm x), <-real_mult_assoc, real_mult_inv.
    ring_simplify;auto.
  Qed.
  Lemma dist_abs x y : dist x y = abs (y - x).
  Proof.
    rewrite dist_symm;auto.
  Qed.
  Lemma abs_plus_one_div_inv x y: (y > real_0) -> (y / (real_gt_neq _ _ (abs_plus_1_gt_0 x))) * abs x <= y. 
  Proof.
    intros H.
    apply (real_le_le_le _ ((y / (real_gt_neq _ _ (abs_plus_1_gt_0 x))) * (abs x + real_1))).  
    - apply real_le_mult_pos_le.
      apply real_lt_le.
      apply real_div_gt_0;try apply abs_plus_1_gt_0;auto.
      add_both_side_by (- (abs x)).
      apply real_lt_le.
      apply real_1_gt_0.
  - unfold real_div.
    rewrite real_mult_assoc, real_mult_inv.
    apply real_eq_le; ring.
  Qed.

  Lemma half_twice_mult x y : x * y = x / real_2_neq_0 * y + x / real_2_neq_0 * y.
  Proof.
    rewrite <-(half_twice x);ring_simplify;rewrite half_twice; ring.    
  Qed.

  Lemma derivative_sproduct a f g x : derivative f g x -> derivative (fun x => a * f x) (fun x => a * g x) x.
  Proof.
    intros H eps epsgt0.
    destruct (H (eps / (real_gt_neq _  _ (abs_plus_1_gt_0 a)))) as [d [dgt0 D]];[apply real_div_gt_0;try apply abs_plus_1_gt_0;auto |].
    exists d;split;auto.
    intros.
    replace (a*f y - a * f x - a * g x * (y-x)) with (a * (f y - f x - g x * (y- x))) by ring.
    rewrite abs_mult.
    apply (real_le_le_le _ (abs a * ((eps / (real_gt_neq _  _ (abs_plus_1_gt_0 a))) * abs (y - x)))).
    apply real_le_mult_pos_le; [apply abs_pos | apply D];auto.
    rewrite <-real_mult_assoc.
    rewrite !(real_mult_comm _( abs (y - x))).
    apply real_le_mult_pos_le; try apply abs_pos.
    rewrite (real_mult_comm (abs a)). 
    apply abs_plus_one_div_inv;auto.
  Defined.
  
  Lemma derivative_product f1 f2 g1 g2 x : derivative f1 g1 x -> derivative f2 g2 x -> derivative (fun x => (f1 x * f2 x)) (fun x => (f1 x * g2 x) + (g1 x * f2 x)) x.
  Proof.
    intros H1 H2 eps epsgt0.
    remember (eps / real_2_neq_0  / (real_gt_neq _  _ (abs_plus_1_gt_0 (g2 x)))) as eps0'.
    remember (Minmax.real_min real_1 eps0') as eps0.
    assert (eps0 > real_0) as eps0gt0.
    {
      rewrite Heqeps0, Heqeps0'.
      destruct (Minmax.real_min_cand real_1 (eps / real_2_neq_0  / (real_gt_neq _  _ (abs_plus_1_gt_0 (g2 x))))) as [-> | ->];try apply real_1_gt_0.
     apply real_div_gt_0; [apply real_half_gt_zero|apply abs_plus_1_gt_0].
     exact epsgt0.
    }
    destruct (derivable_continuous _ _ _ H1 eps0) as [d0 [d0gt0 D0]];auto.
    remember ((eps / real_2_neq_0 / real_2_neq_0) / (real_gt_neq _ _ (abs_plus_1_gt_0 (f2 x)))) as eps1.
    assert (eps1 > real_0) as eps1gt0.
    {
      rewrite Heqeps1.
      apply real_div_gt_0; [|apply abs_plus_1_gt_0];auto.     
      apply real_half_gt_zero.
      apply real_half_gt_zero;auto.
    }
    destruct (H1 eps1) as [d1 [d1gt0 D1]]; auto.
    remember ((eps / real_2_neq_0 / real_2_neq_0) / (real_gt_neq _ _ (abs_plus_1_gt_0 (f1 x)))) as eps2.
    assert (eps2 > real_0) as eps2gt0.
    {
      rewrite Heqeps2.
      apply real_div_gt_0; try apply abs_plus_1_gt_0.
      apply real_half_gt_zero.
      apply real_half_gt_zero;auto.
    }
    destruct (H2 eps2) as [d2 [d2gt0 D2]]; [rewrite Heqeps2;apply real_div_gt_0; [apply real_half_gt_zero|apply abs_plus_1_gt_0];apply real_half_gt_zero;auto|].
    assert {d | d > real_0 /\ d <= d0 /\ d <= d1 /\ d <= d2} as [d [dgt0 [dd0 [dd1 dd2]]]].
    {
      exists (Minmax.real_min d0 (Minmax.real_min d1 d2)).
      split; [destruct (Minmax.real_min_cand d0 (Minmax.real_min d1 d2)) as [-> | ->];[|destruct (Minmax.real_min_cand d1 d2) as [-> | ->]]|];auto.
      split; [apply Minmax.real_min_fst_le|split]; apply (real_le_le_le _ _ _ (Minmax.real_min_snd_le _ _)).
      apply Minmax.real_min_fst_le.
      apply Minmax.real_min_snd_le.
    }
    exists d.
    split;auto.
    intros.
    replace (f1 y * f2 y - f1 x * f2 x - (f1 x * g2 x + g1 x * f2 x) * (y - x)) with ((f1 y - f1 x)*(g2 x)*(y-x) + (f1 y * (f2 y - f2 x - g2 x * (y-x)) + f2 x * (f1 y - f1 x - g1 x * (y-x)))) by ring.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    rewrite (half_twice_mult eps _).
    apply real_le_le_plus_le; [|rewrite (half_twice_mult (eps / real_2_neq_0));apply (real_le_le_le _ _ _ (abs_tri _ _));apply real_le_le_plus_le];rewrite !abs_mult.
    - rewrite !(real_mult_comm _ (abs (y-x))).
      apply real_le_mult_pos_le; [apply abs_pos |].
      apply (real_le_le_le _ (eps0 * abs (g2 x))).
      rewrite !(real_mult_comm _ (abs (g2 x))); apply real_le_mult_pos_le;[apply abs_pos |].
      rewrite <-dist_abs.
      apply D0.
      apply (real_le_le_le _ _ _ H dd0).
      rewrite Heqeps0.
      apply (real_le_le_le _ (eps0' * abs (g2 x))); [rewrite !(real_mult_comm _ (abs _));apply real_le_mult_pos_le;try apply abs_pos;apply Minmax.real_min_snd_le | ].
      rewrite Heqeps0'.
      apply abs_plus_one_div_inv; apply real_half_gt_zero;auto.
   -  apply (real_le_le_le _ (abs (f1 y) * (eps2 * abs (y - x)))).
      apply real_le_mult_pos_le; [apply abs_pos | apply D2;apply (real_le_le_le _ _ _ H dd2)].
      rewrite !(real_mult_comm _ (abs (y-x))), <-real_mult_assoc,(real_mult_comm _ (abs (y-x))), real_mult_assoc.
      apply real_le_mult_pos_le;try apply abs_pos.
      rewrite real_mult_comm.
      apply (real_le_le_le _ (eps2 *(abs (f1 x)+real_1))).
      apply real_le_mult_pos_le;[apply real_lt_le|];auto.
      apply dist_bound.
      apply (real_le_le_le _ eps0); [apply D0;apply (real_le_le_le _ _ _ H dd0)|].
      rewrite Heqeps0.
      apply Minmax.real_min_fst_le.
      rewrite Heqeps2.
      unfold real_div.
      rewrite !real_mult_assoc,real_mult_inv.
      apply real_eq_le;ring.
   -  apply (real_le_le_le _ (abs (f2 x) * (eps1 * abs (y - x)))). 
      apply real_le_mult_pos_le; try apply abs_pos.
      apply D1.
      apply (real_le_le_le _ _ _ H dd1).
      rewrite <-real_mult_assoc, !(real_mult_comm _ (abs (y- x))).
      apply real_le_mult_pos_le;try apply abs_pos.
      rewrite Heqeps1.
      rewrite real_mult_comm.
      apply abs_plus_one_div_inv.
      apply real_half_gt_zero.
      apply real_half_gt_zero;auto.
  Defined.

  Lemma derivative_const c : forall x, derivative (fun x => c) (fun x => real_0) x.
 Proof. 
   intros x eps H.
   exists real_1.
   split; [apply real_1_gt_0|].
   intros.
   replace (c-c-real_0 * (y-x)) with real_0 by ring.
   rewrite (proj2 (abs_zero real_0)); try apply real_le_triv;auto.
   apply real_le_pos_mult_pos_pos.
   apply real_lt_le;auto.
   apply abs_pos.
 Qed.

  Lemma derivative_id : forall x, derivative (fun x => x) (fun x => real_1) x.
  Proof.
    intros x eps H.
    exists real_1.
   split; [apply real_1_gt_0|].
   intros.
   replace (y-x-real_1 * (y-x)) with real_0 by ring.
   rewrite (proj2 (abs_zero real_0)); try apply real_le_triv;auto.
   apply real_le_pos_mult_pos_pos.
   apply real_lt_le;auto.
   apply abs_pos.
 Qed.

 Lemma derivative_monomial n : forall x, derivative (fun x => (npow x (S n))) (fun x => (Nreal (S n) * npow x n)) x.
 Proof.
   intros.
   induction n.
   - simpl.
     replace ((real_1+real_0)*real_1) with real_1 by ring.
     replace (fun x => x*real_1) with (fun (x : ^Real) => x) by (apply fun_ext;intros;ring).
     apply derivative_id.
  - replace (fun x => Nreal (S (S n)) * npow x (S n)) with (fun (x : ^Real) => x*(Nreal (S n) * npow x n) + real_1 * npow x ((S n))) by (apply fun_ext;intros;simpl;ring).
    simpl.
    apply derivative_product.
    apply derivative_id.
    apply IHn.
 Qed.

 Lemma derive_ext f1 f2 g x : (forall x, f1 x = f2 x) ->  derivative f2 g x -> derivative f1 g x.
 Proof.
   intros H D eps epsgt0.
   destruct (D eps epsgt0) as [d [dgt dP]].
   exists d;split;auto.
   intros.
   rewrite !H.
   apply dP;auto.
 Qed.

 Lemma derive_ext2 f g1 g2 x : (forall x, g2 x = g1 x) ->  derivative f g1 x -> derivative f g2 x.
 Proof.
   intros H D eps epsgt0.
   destruct (D eps epsgt0) as [d [dgt dP]].
   exists d;split;auto.
   intros.
   rewrite H.
   apply dP;auto.
 Qed.
 Lemma monomial_poly a n : {p : poly | forall x, eval_poly p x = a * npow x n}.
 Proof.
   exists ((repeat real_0 n) ++ [a]).
   intros.
   induction n; [simpl; ring|].
   simpl.
   rewrite IHn.
   ring.
 Defined.

 Lemma derive_poly_helper p1 p2 p1' p2' : (forall x, derivative (eval_poly p1) (eval_poly p1') x) -> (forall x, derivative (fun x => (npow x (length p1)) * (eval_poly p2 x)) (eval_poly p2') x) -> forall x, derivative (eval_poly (p1++p2)) (fun x => (eval_poly p1' x + eval_poly p2' x)) x.
 Proof.
   intros H1 H2 x.
   apply (derive_ext _ (fun x => eval_poly p1 x + npow x (length p1) * eval_poly p2 x)); [intros;rewrite !eval_eval2;apply eval_poly2_app | ].
   apply derivative_sum;auto.
 Qed.

 Lemma derive_monomial a n : {p & forall x, derivative (fun x => a * npow x n) (eval_poly p) x}.
 Proof.
   destruct n; [exists []; simpl; apply derivative_const|].
   destruct (monomial_poly (a * (Nreal (S n))) n) as [p P].
   exists p.
   replace (eval_poly p) with (fun x => a * (Nreal (S n) * npow x n)) by (apply fun_ext;intros; rewrite P;ring).
   intros x.
   apply derivative_sproduct.
   apply derivative_monomial.
 Defined.

 Lemma derive_monomial_spec a n : (projT1  (derive_monomial a (S n))) = (pr1 _ _ (monomial_poly (a * Nreal (S n)) n)). 
 Proof.
   induction n;simpl;auto.
 Qed.

 Lemma poly_rev_ind : forall (P : poly -> Type),
  P [] -> (forall (x : Real) (l : poly), P l -> P (l ++ [x])) -> forall l : poly, P l.
 Proof.
   intros.
   replace l with (rev (rev l)) by (apply rev_involutive).
   induction (rev l).
   simpl.
   apply X.
   simpl.
   apply X0;auto.
 Qed.

 Lemma poly_deriv_exists (p : poly) : {p' : poly | length p' = (length p - 1)%nat /\ forall n,  nth n p' real_0 = Nreal (S n) * nth (S n) p real_0 }.
 Proof.
   induction p using poly_rev_ind;[exists [];split;auto; intros;rewrite nth_overflow;simpl;[ring | lia]|].
   destruct p.
   - exists [].
     split; auto.
     intros; rewrite nth_overflow; simpl; try lia.
     destruct n;simpl;ring.
   - destruct IHp as [p' [P1 P2]].
     simpl in P1.
     rewrite Nat.sub_0_r in P1.
     exists (p' ++ [(Nreal (S (length p)))*x]).
     split; [rewrite !app_length, P1;simpl;lia|].
     intros n.
     destruct (Nat.lt_ge_cases n (length p')).
     + rewrite app_nth1;auto.
       rewrite P2.
       simpl.
       rewrite app_nth1;try rewrite <-P1;auto.
    + destruct H; [simpl;rewrite nth_middle, P1, nth_middle;ring|].
      simpl.
      rewrite !nth_overflow; try ring; rewrite app_length;simpl; lia.
 Qed.

 Definition derive_poly p := (pr1 _ _ (poly_deriv_exists p)).
 Lemma derive_poly_app p a : forall x, eval_poly (derive_poly (p ++ [a])) x  = eval_poly (derive_poly p) x + eval_poly (projT1 (derive_monomial a (length p))) x.
 Proof.
   intros.
   unfold derive_poly.
   destruct (poly_deriv_exists p) as [p1 [H1 H2]].
   destruct (poly_deriv_exists (p ++ [a])) as [p2 [H1' H2']].
   assert (p1 = [] /\ p2 = [] \/ (length p > 0)%nat /\ p2 = p1 ++ [Nreal (S (length p1)) * a]).
   {
     destruct p; [left;rewrite length_zero_iff_nil in H1;rewrite length_zero_iff_nil in H1';auto|right].
     split;[simpl;lia|].
     apply (nth_ext _ _ real_0 real_0); [rewrite H1', !app_length, H1;simpl;lia|].
     intros.
     rewrite H2'.
     simpl.
     assert (length p1 = length p) by (simpl in H1;lia).
     rewrite app_length in H1'; simpl in H1'.
     destruct (Nat.lt_ge_cases n (length p)).
     rewrite !app_nth1;try lia;rewrite H2;auto.
     destruct H3.
     rewrite <-H0 at 3.
     rewrite !nth_middle.
     rewrite H0;auto.
     rewrite !nth_overflow; try lia.
   }
   destruct H as [[-> ->] | [H ->]]; [simpl; replace (length p) with 0%nat;simpl;[ring|simpl in H1';rewrite H1';rewrite app_length;simpl;lia]|].
   simpl.
   rewrite eval_eval2, eval_poly2_app, <-!eval_eval2.
   rewrite !(real_plus_comm (eval_poly p1 x)).
   apply real_eq_plus_eq.
   destruct (length p);try lia.
   rewrite derive_monomial_spec.
   destruct (monomial_poly (a * Nreal (S n)) n) as [m M].
   simpl;rewrite M.
   rewrite H1.
   simpl.
   replace (n-0)%nat with n by lia.
   ring.
 Qed.

 Lemma derive_poly_spec p : forall x, derivative (eval_poly p) (eval_poly (derive_poly p)) x.
 Proof.
   unfold derive_poly.
   induction p as [| a p IH] using poly_rev_ind.
   - intros.
     destruct (poly_deriv_exists []) as [p' [H1 H2]].
     simpl;replace p' with (@nil ^Real) by (rewrite length_zero_iff_nil in H1;auto).
     simpl;apply derivative_const.
   - intros x.
     pose proof (derive_poly_app p a).
     apply (derive_ext2 _ _ _ x H).
     apply derive_poly_helper;auto.
     intros.
     destruct (derive_monomial a (length p)) as [m M].
     simpl.
     apply (derive_ext _ (fun x => a * npow x (length p))); [intros;ring|].
     apply M.
 Qed.
 (* Lemma derive_poly (p : poly) : {p' & forall x, derivative (eval_poly p) (eval_poly p') x }. *)
 (* Proof. *)
 (*   replace p with (rev (rev p)) by (apply rev_involutive). *)
 (*   induction (rev p);[exists [];unfold eval_poly2;simpl; apply derivative_const|]. *)
 (*   simpl. *)
 (*   destruct IHl as [p' IH]. *)
 (*   destruct (derive_monomial a (length (rev l))) as [m M]. *)
 (*   destruct (sum_poly p' m) as [p0 P0]. *)
 (*   exists p0. *)
 (*   intros x eps epsgt0. *)
 (*   rewrite P0. *)
 (*   apply derive_poly_helper;auto. *)
 (*   clear x eps epsgt0. *)
 (*   simpl. *)
 (*   intros x. *)
 (*   apply (derive_ext _ (fun x => a * npow x (length (rev l)))); [intros;ring|]. *)
 (*   apply M. *)
 (*  Defined. *)

 

 (* Lemma derive_poly (p : poly) : {p' & forall x, derivative (eval_poly p) (eval_poly p') x }. *)
 (* Proof. *)
 (*   induction p; [exists [];apply derivative_const|]. *)
 (*   destruct IHp as [p' P'].() *)
 (*   destruct (mult_poly [real_0;real_1] p') as [xp' X]. *)
 (*   destruct (sum_poly p xp') as [p0' P]. *)
 (*   exists p0'. *)
 (*   simpl. *)
 (*   intros x. *)
 (*   replace (eval_poly p0') with (fun x => real_0 + eval_poly p0' x) by (apply fun_ext;intros;ring). *)
 (*   apply derivative_sum; [apply derivative_const |]. *)
 (*   replace (eval_poly p0') with (fun x =>  x * eval_poly p' x + real_1 * eval_poly p x ). *)
 (*   - apply derivative_product; [apply derivative_id |]. *)
 (*     apply P'. *)
 (*   - apply fun_ext. *)
 (*     intros. *)
 (*     rewrite P. *)
 (*     rewrite X. *)
 (*     simpl;ring. *)
 (* Defined. *)

 (* Lemma derive_poly_spec p : forall n, nth n (projT1 (derive_poly p)) real_0 = (Nreal (S n)) * (nth (S n) p real_0). *)
 (* Proof. *)
 (*   induction p. *)
 (*   intros n. *)
 (*   simpl. *)
 (*   unfold derive_poly. *)
 (*   simpl. *)
 (*   unfold eq_rect. *)
 (*   simpl. *)
 (*   admit. *)
 (*   intros. *)
 (*   simpl. *)
 (*   destruct n;simpl;ring. *)
 (*   intros n. *)
 (*   induction n. *)
End Derivative.
