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
Require Import ClassicalDifferentiability.
Require Import Poly.
Require Import Taylormodel.
Require Import Powerseries.

Section HigherDerivatives.
  (* Lemma derivative_unique f g1 g2 r : uniform_derivative_fun f g1 r -> uniform_derivative_fun f g2 r -> forall (x : I r), g1 x = g2 x. *)
  (* Admitted. *)

  Fixpoint nth_derivative (f : Real -> Real) (g : Real -> Real) r n :=
    match n with
    | 0 => forall (x : I r), f x = g x
    | S n' => exists f', uniform_derivative_fun f f' r /\ nth_derivative f' g r n'
    end.                                                               

  (* Lemma nth_derivative_unique f g1 g2 r n : nth_derivative f g1 r n -> nth_derivative f g2 r n -> forall x : (I r), g1 x = g2 x. *)
  (* Admitted. *)

  Lemma zero_derivative f r : nth_derivative f f r 0.
  Proof. simpl;auto. Qed.

  Lemma fst_derivative f g r : uniform_derivative_fun f g r -> nth_derivative f g r 1.
  Proof.
    intros.
    exists g;split;auto.
    apply zero_derivative.
  Qed.

 Lemma nth_derivative_S f g r n : (exists fn, nth_derivative f fn r n /\ uniform_derivative_fun fn g r) -> nth_derivative f g r (S n).
 Proof.
   intros.
   revert dependent f.
   induction n.
   - intros.
     destruct H as [fn [H1 H2]].
     exists g.
     split; [| apply zero_derivative].
     apply (derive_ext_fun _ fn);auto.
     intros.
     apply (H1 (real_to_I H));auto.
   - intros.
     destruct H as [fn [Fn1 Fn2]].
     destruct Fn1 as [f' [F'1 F'2]].
     exists f'.
     split;auto.
     apply IHn.
     exists fn;split;auto.
 Qed.

  Lemma Nreal_fact_neq0 n : Nreal (fact n) <> real_0.
  Proof.
    apply real_gt_neq.
    apply Nreal_pos.
    apply lt_O_fact.
  Qed.

  Lemma dSn n : Nreal (S n) <> 0.
  Proof. apply real_gt_neq; apply Nreal_pos;lia. Defined.

 Definition inv_factorial (n : nat): ^Real.
 Proof.
   apply (/ (Nreal_fact_neq0 n)).
 Defined.

 Lemma inv_factorial0 : inv_factorial 0 = real_1.
 Proof.
 Admitted.

 Lemma inv_factorialS n : inv_factorial (S n) = (/ dSn n) * inv_factorial n.
 Admitted.

 Lemma inv_factorial1 : inv_factorial 1 = real_1.
 Proof.
   rewrite inv_factorialS.
   rewrite inv_factorial0.
   assert (/ dSn 0 = / d1) as ->.
   admit.
   rewrite real_1_inv_1.
   ring_simplify;auto.
 Admitted.

 Definition is_taylor_polynomial a f r:= forall n, (n < length a)%nat -> (exists g, nth_derivative f g r n /\ nth n a 0 = inv_factorial n * (g 0)). 

 Lemma taylor_sub_polynomial a aN f r : is_taylor_polynomial (a ++ aN) f r -> is_taylor_polynomial a f r.
 Proof.
   intros [H1 H2].
 Admitted.

 Theorem TaylorsTheorem a f r M : is_taylor_polynomial a f r -> (exists g, nth_derivative f g r (length a) /\ (forall (x : I r), abs (g x) <= M)) -> forall (x : I r), dist (eval_poly a x) (f x) <= inv_factorial (length a) * M * npow r (length a).
 Proof.
 Admitted.
  (*  induction a. *)
  (*  - intros a M [H1 H2] [g [G1 G2]] x. *)
  (*    assert (abs 0 <= r) as H0. *)
  (*    admit. *)
  (*    assert (a = [(f 0)]). *)
  (*    { *)
  (*      apply (nth_ext _ _ 0 0);auto. *)
  (*      rewrite H1. *)
  (*      intros. *)
  (*      rewrite Nat.lt_1_r in H. *)
  (*      rewrite H. *)
  (*      simpl. *)
  (*      destruct (H2 0%nat) as [h [P1 ->]];try lia. *)
  (*      rewrite inv_factorial0. *)
  (*      ring_simplify. *)
  (*      specialize (P1 (real_to_I H0)). *)
  (*      simpl in P1. *)
  (*      rewrite P1;auto. *)
  (*    } *)
  (*    rewrite H. *)
  (*    rewrite inv_factorial1; simpl;ring_simplify. *)
  (*    replace (f 0 + x * real_0) with (f (real_to_I H0)) by (simpl;ring). *)
  (*    destruct G1 as [f' [G11 G12]]. *)
  (*    apply (real_le_le_le _ (M*dist (real_to_I H0) x)). *)
  (*    apply (lbc_fun _ _ r M  G11). *)
  (*    intros. *)
  (*    rewrite G12;auto. *)
  (*    simpl. *)
  (*    rewrite dist_symm. *)
  (*    unfold dist. *)
  (*    admit. *)
  (* - intros. *)
  (*   pose proof H as [L H']. *)
  (*   destruct (H' (S N)) as [fsn [fsnd asn]]; try lia. *)
  (*   assert (exists a', a = a' ++ [((inv_factorial (S N)) * fsn 0)]) as [a'  ->]. *)
  (*   admit. *)
  (*   pose proof (taylor_sub_polynomial _ _ _ _ _ H). *)
  (*   rewrite eval_eval2, eval_poly2_app, <-!eval_eval2. *)
  (*   simpl. *)
  (*   assert (length a' = S N) as ->. *)
  (*   admit. *)
  (*   assert (exists g, nth_derivative f g r (S N) /\ (forall (x : I r), abs (g x) <= M*r)). *)
  (*   { *)
  (*     exists fsn. *)
  (*     split;auto. *)
  (*     admit. *)
  (*   } *)
  (*   specialize (IHN _ _ H1 H2). *)
  (*   Admitted. *)
End HigherDerivatives.
Section IVP.
  Definition pivp0_solution p y r := (y 0) = 0 /\ uniform_derivative_fun y (fun t => (eval_poly p (y t))) r.

  Definition pivp_solution  p y y0 r := (y 0) = y0 /\ uniform_derivative_fun y (fun t => (eval_poly p (y t))) r.

  Lemma pivp_to_pivp0 p y y0 r : {p' : poly | pivp_solution p y y0 r <-> pivp0_solution p' (fun t => y t - y0) r }.
  Proof.
    destruct (shift_poly p (-y0)) as [p' P'].
    exists p'.
    split.
    - intros.
      split; [rewrite (proj1 H);ring_simplify;auto | ].
      intros eps epsgt0.
      destruct (proj2 H _ epsgt0) as [d [dgt0 D]].
      exists d.
      split;auto.
      intros.
      rewrite P'.
      replace(y x - y0 - - y0) with (y x) by ring.
      replace (y y1 - y0 - (y x - y0)) with (y y1 - y x) by ring.
      apply D;auto.
   -  intros.
      split; [replace y0 with (y 0 - (y 0 - y0)) by ring; rewrite (proj1 H);replace 0 with real_0 by auto; ring |]. 
      intros eps epsgt0.
      destruct (proj2 H _ epsgt0) as [d [dgt0 D]].
      exists d;split;auto.
      intros.
      replace (y y1 - y x) with (y y1 - y0 - (y x - y0)) by ring.
      replace (eval_poly p (y x)) with (eval_poly p' (y x - y0));[apply D;auto|].
      replace (y x) with ((y x - y0) - - y0 ) at 2 by ring.
      apply P'.
  Qed.
  
  Fixpoint pn p n := match n with
                     |  0 => p
                     | S n' => mult_coefficients p (derive_poly (pn p n'))
                    end.

  Lemma differentiable_bounded_fun f g r: uniform_derivative_fun f g r -> exists M, forall (x : I r), abs (f x) <= M.
  Proof.
    rewrite <-derivative_function_iff.
    intros.
    apply differentiable_bounded in H.
    destruct H as [M Mp].
    apply bounded_by_unfold in Mp.
    destruct Mp.
    exists M.
    intros.
    destruct x.
    simpl.
    destruct (H x r0) as [fx P].
    replace (f x) with fx.
    apply (H0 x);auto.
    apply pc_unit_mono.
    rewrite P;auto.
  Qed.

  Lemma pk_spec p (y : Real -> Real) r n : pivp0_solution p y r -> nth_derivative y (fun t  => eval_poly (pn p n) (y t)) r (S n).
  Proof.
    intros H.
    assert (exists r', (forall (t : I r), abs (y t) <= r')).
    {
      destruct (differentiable_bounded_fun _ _ _ (proj2 H)).
      exists x.
      apply H0.
    }
    destruct H0 as [r' B].
    induction n.
    apply fst_derivative; apply H.
    apply nth_derivative_S.
    exists (fun t => eval_poly (pn p n) (y t)).
    split;[apply IHn|].
    simpl.
    apply (derive_ext_fun2 _ (fun t => eval_poly p (y t) * eval_poly (derive_poly (pn p n)) (y t)));[intros;apply mult_coeff_spec|].
    apply (chain_rule _ _ _ _ r').
    apply derive_poly_spec.
    apply H.
    intros.
    apply (B (real_to_I H0)).
  Qed.

  Definition poly_norm (p : poly) : ^Real.
  Admitted.

  Lemma polynorm_le p : forall n, abs (nth n p real_0) <= poly_norm p.
  Admitted.

  Lemma polynorm_mult p q : poly_norm (mult_coefficients p q) = poly_norm p * poly_norm q.
  Admitted.

  Lemma polynorm_deriv_bound p : poly_norm (derive_poly p) <= (Nreal (length p))*poly_norm p.
  Admitted.

  Lemma polynorm_nonneg p : real_0 <= poly_norm p. 
  Admitted.

  Lemma polynorm_empty : poly_norm [] = real_0.
  Admitted.
  Lemma poly_deriv_bound (p : poly) M r : (forall n, abs (nth n p real_0) <= M * npow r n) -> (forall n, abs (nth n (derive_poly p) real_0) <= Nreal (S n) * M * npow r (S n)).
  Proof.
    intros.
    unfold derive_poly.
    destruct (poly_deriv_exists p) as [p' [P1 P2]].
    simpl.
    rewrite P2.
    rewrite abs_mult, abs_pos_id; try apply Nreal_nonneg.
    simpl.
    rewrite real_mult_assoc.
    apply real_le_mult_pos_le.
    rewrite <-Nreal_S; apply Nreal_nonneg.
    apply H.
  Qed.
  
  Lemma mult_coeffs_bound p1 p2 n  M1 M2 r : (forall m, abs (nth m p1 real_0) <= M1*npow r m) -> (forall m, (abs (nth m p2 real_0) <=  Nreal (fact (n+m+1)) * (npow (Nreal (m+1)) n) * M2 * (npow r m)))  -> forall m, abs (nth m (mult_coefficients p1 p2) real_0) <=  Nreal (fact (n+m+2)) * (npow (Nreal (m+1)) (n+1)) * M1 * M2 * npow r m.
  Proof.
    intros.
    assert (real_0 <= r).
    admit.
    assert (real_0 <= M1).
    admit.
    assert (real_0 <= M2).
    admit.
    destruct (Nat.lt_ge_cases m (length (mult_coefficients p1 p2))).
    rewrite length_mult_coefficients in H4.
    rewrite mult_coefficients_spec;auto.
    admit.

    rewrite nth_overflow;auto.
    rewrite abs_pos_id;try apply real_le_triv.
    apply real_le_pos_mult_pos_pos;try apply npow_nonneg;auto.
    apply real_le_pos_mult_pos_pos;auto.
    apply real_le_pos_mult_pos_pos;auto.
    apply real_le_pos_mult_pos_pos;try apply npow_nonneg;try apply Nreal_nonneg.
  Admitted.


  Lemma pn_bound p n M r : (forall m, abs (nth m p real_0) <= M * npow r m) -> forall m, abs (nth m (pn p n) real_0) <=  Nreal (fact (n + m+1)) * (npow (Nreal (S m)) n) *  (M * npow (M * r) n) * npow r m.
  Proof.
    intros H.
    induction n.
    intros.
    simpl.
    simpl;ring_simplify.
    apply (real_le_le_le _ _ _ (H m)).
    rewrite real_mult_assoc.
    replace (M*npow r m) with (real_1 * (M * npow r m)) at 1 by ring.
    apply real_le_mult_pos_le_le; [ apply real_lt_le;apply real_1_gt_0| apply real_le_pos_mult_pos_pos; [|apply npow_nonneg] | |apply real_le_triv].
    admit.
    admit.
    replace (real_1) with (Nreal (fact 1)) by (simpl;ring).
    apply Nreal_monotone.
    apply fact_le;lia.

    intros.
    pose proof (poly_deriv_bound (pn p n) ).
    simpl.
    apply (real_le_le_le _ (Nreal (fact (n+m+2)) * (npow (Nreal (m+1)) (n+1)) * M * (npow (M*r) (S n)) * (npow r m))).
    apply mult_coeffs_bound.
    intros.
    apply H.
    intros m'.
    
    (* replace (Nreal (fact (S n)) * (M * (npow (M * r)) (S n)) * npow r m') with ((Nreal (S n) * (Nreal (fact n) * M * npow (M*r) n)) * npow r (S m')). *)
    (* pose proof poly_deriv_bound. *)
    (* rewrite mult_coeffs_zero. *)
    (* rewrite abs_mult. *)
    (* apply real_le_mult_pos_le_le; try apply abs_pos. *)
    (* apply (real_le_le_le _  (M * npow r 0)); [apply H | simpl; ring_simplify; apply real_le_triv]. *)
    (* apply (real_le_le_le _ _ _ (poly_deriv_bound (pn p n) _ _ (IHn ))). *)
    Admitted.

  Lemma p0_bound p n M r : (forall m, abs (nth m p real_0) <= M * npow r m) -> abs (nth 0 (pn p n) real_0) <= Nreal (fact (n+1)) * M * npow (M*r) n.
  Proof.
    intros.
    apply (real_le_le_le _ _ _ (pn_bound _ _ _ _ H 0)).
    simpl.
    ring_simplify.
    replace (n+0+1)%nat with (n+1)%nat by lia.
    replace (real_1+real_0) with (real_1) by ring.
    rewrite npow_1.
    ring_simplify;auto.
    apply real_le_triv.
  Qed.

  Lemma Nreal_neq0 n : Nreal (S n) <> real_0.
  Proof.
    apply real_gt_neq.
    apply Nreal_pos.
    lia.
  Qed.
  
  Fixpoint an p n := match n with
                     |  0 => p
                     | S n' => pr1 _ _ (smul_poly (/ Nreal_neq0 n') (mult_coefficients p (derive_poly (an p n'))))
                    end.

  Lemma smul_length p x : length (pr1 _ _  (smul_poly x p)) = length p.
  Admitted.

  Lemma derive_poly_length p : length (derive_poly p) = (length p - 1)%nat.
  Admitted.

  Lemma smul_norm p x : poly_norm (pr1 _ _ (smul_poly x p)) = x * poly_norm p.
  Proof.
  Admitted.

 Lemma an_length p n : (length (an p n) = ((n+1)*(length p))-2*n)%nat.
  Proof.
    induction n; [simpl;lia|].
    simpl an.
    rewrite smul_length.
    rewrite length_mult_coefficients.
    rewrite derive_poly_length.
    rewrite IHn.
    simpl.
    ring_simplify.
    replace (n+0)%nat with n by lia.
    destruct (length p); try lia.
    destruct n0;lia.
  Qed.

  Lemma invSn_gt0 : forall n, (/ Nreal_neq0 n) > real_0.
  Admitted.

  Lemma an_norm p n : poly_norm (an p n) <= npow (Nreal (length p)*poly_norm p) (S n).
  Proof.
    induction n.

    simpl.
    destruct p;simpl.
    rewrite polynorm_empty.
    apply real_eq_le;ring.
    ring_simplify.
    add_both_side_by (-poly_norm (r::p)).
    apply real_le_pos_mult_pos_pos.
    apply polynorm_nonneg.
    apply Nreal_nonneg.

    simpl an.
    rewrite smul_norm.
    rewrite polynorm_mult.
    pose proof (polynorm_deriv_bound (an p n)).
    assert (poly_norm (derive_poly (an p n)) <= Nreal ((n+1)*length p) * (npow (Nreal (length p) * poly_norm p) (S n))).
    {
      apply (real_le_le_le _ _ _ H).
      rewrite an_length.
      apply (real_le_le_le _ (Nreal ((n+1) *length p)*poly_norm (an p n))).
      apply real_le_mult_pos_le_le; try apply Nreal_nonneg; try apply polynorm_nonneg; try apply real_le_triv.
      apply Nreal_monotone;lia.
      apply real_le_mult_pos_le; try apply Nreal_nonneg.
      apply IHn.
    }
    apply (real_le_le_le _ (((/ Nreal_neq0 n) * poly_norm p) *  (Nreal ((n+1)*length p) * (npow (Nreal (length p) * poly_norm p) (S n))))).
    rewrite <-real_mult_assoc.
    apply real_le_mult_pos_le.
    apply real_le_pos_mult_pos_pos.
    apply real_lt_le.
    apply invSn_gt0.
    apply polynorm_nonneg.
    apply H0.
    ring_simplify.
    simpl.
    apply real_le_mult_pos_le_le; try apply real_le_triv.
    apply real_le_pos_mult_pos_pos;  try apply Nreal_nonneg.
    apply real_le_pos_mult_pos_pos;  try apply polynorm_nonneg; try (apply real_lt_le;apply invSn_gt0).
    apply real_le_pos_mult_pos_pos;  try apply real_le_pos_mult_pos_pos;try apply Nreal_nonneg; try apply polynorm_nonneg.
    apply npow_nonneg.
    apply real_le_pos_mult_pos_pos;  try apply Nreal_nonneg; try apply polynorm_nonneg.
    rewrite real_mult_comm, Nreal_mult.
    rewrite (real_mult_comm (Nreal _)).
    rewrite real_mult_assoc.
    apply real_le_mult_pos_le;try apply Nreal_nonneg.
    rewrite <-real_mult_assoc.
    replace (Nreal (n+1) * / Nreal_neq0 n) with real_1.
    ring_simplify;apply real_le_triv.
    rewrite real_mult_comm.
    replace (n+1)%nat with (S n) by lia.
    rewrite real_mult_inv;auto.
  Qed.

  Lemma an_spec p n x : (eval_poly (an p n) x) = (/ Nreal_fact_neq0 (S n)) * (eval_poly (pn p n) x).
  Proof.
    induction n.
    simpl.
  Admitted.

  Definition an0 p n :=
    match n with
      | 0 => 0
      | S n' => (eval_poly (an p n') real_0)
      end.
  Lemma an0_spec p n : an0 p (S n) = (inv_factorial (S n)) * (eval_poly (pn p n) real_0).
  Admitted.

  Lemma eval_poly_zero p : eval_poly p real_0 = nth 0 p real_0.
  Proof.
    induction p;auto.
    simpl.
    ring_simplify;auto.
  Qed.
  
  Lemma an0_bound p n : abs (an0 p n) <= npow (Nreal (length p) * poly_norm p) n.
  Proof.
    destruct n;[apply real_lt_le; rewrite abs_pos_id; try apply real_1_gt_0;apply real_le_triv|].
    simpl an0.
    rewrite eval_poly_zero.
    apply (real_le_le_le _ _ _ (polynorm_le _ _)).
    apply an_norm.
  Qed.
  
  Lemma poly_deriv_bound' (p : poly) M: (forall n, abs (nth n p real_0) <= M) -> (forall n, abs (nth n (derive_poly p) real_0) <= Nreal (S n) * M).
  Proof.
    intros.
    unfold derive_poly.
    destruct (poly_deriv_exists p) as [p' [P1 P2]].
    simpl.
    rewrite P2.
    rewrite abs_mult, abs_pos_id; try apply Nreal_nonneg.
    simpl.
    apply real_le_mult_pos_le.
    rewrite <-Nreal_S; apply Nreal_nonneg.
    apply H.
  Qed.
  
  Lemma mult_coeffs_bound' p1 p2 M1 M2 : (forall m, abs (nth m p1 real_0) <= M1) -> (forall m, (abs (nth m p2 real_0) <=  M2)  -> forall m, abs (nth m (mult_coefficients p1 p2) real_0) <= Nreal (m+1)* M1 * M2).
  Proof.
  Admitted.

  Lemma pn_bound' p n M : (forall m, (m <= n)%nat -> abs (nth m p real_0) <= M) -> forall m, (m <= n)%nat -> abs (nth m (pn p n) real_0) <=  Nreal (fact (S n)) * (npow (Nreal (S n)) n) *  npow M (S n).
  Proof.
    intros.
    induction n.
    simpl.
    admit.
    simpl pn.
    specialize (IHn H H0).
    pose proof (poly_deriv_bound' _ _ )
  Lemma poly_M p : {M | (forall n, abs (nth n p real_0) <= M) /\ M > 0}.
  Proof.
  Admitted.

  Lemma nth_to_poly a m n : (m <= n)%nat -> nth m (to_poly a n) real_0 = (a m).
  Proof.
    induction n.
    simpl;auto.
  Admitted.

  Lemma pivp_ps_taylor_series p : forall y r, pivp0_solution p y r -> forall n, (is_taylor_polynomial (to_poly (an0 p) n) y r).
  Proof.
    intros y r H.
    induction n.
    - unfold to_poly.
      destruct H as [H H'].
      simpl.
      intros n H0.
      rewrite Nat.lt_1_r in H0.
      rewrite H0.
      exists y.
      split; [apply zero_derivative|].
      rewrite H.
      rewrite inv_factorial0.
      simpl;ring_simplify;auto.
   -  simpl.
      intros m M.
      rewrite length_to_poly in M.
      rewrite Nat.lt_succ_r in M.
      destruct (Lt.le_lt_or_eq_stt _ _ M).
      destruct (IHn m).
      rewrite length_to_poly;auto.
      exists x.
      rewrite nth_to_poly in H1; try lia.
      rewrite nth_to_poly; try lia.
      split; try apply H1.
      rewrite H0.
      exists (fun t  => eval_poly (pn p n) (y t)).
      split.
      apply pk_spec;auto.
      rewrite nth_to_poly; try lia.
      rewrite (proj1 H).
      apply an0_spec.
  Qed.

  Lemma y_bound p y r M : pivp0_solution p y r -> forall (x : I r), abs (eval_poly p x) <= M -> forall r', M*r' <= r -> forall (t : I r'), abs (y t) <= r.
  Proof.
    intros.
    destruct (differentiable_bounded_fun _ _ _ (proj2 H)) as [ymax Y].
    destruct (bound_polynomial p ymax) as [M' M'p].
    assert (r' <= r).
    admit.
    assert ((y t) <= M' * r').
    admit.
  Definition pivp_ps (p : poly) : bounded_ps.
  Proof.
    pose proof (poly_M p).
    revert X.
    (* apply M_lift. *)
    intros [M [Mp1 Mp2]].
    assert (/ (real_gt_neq _ _ Mp2) > 0).
    admit.
    apply (mk_bounded_ps (an0 p) 1 _ H).
    unfold an0.
    intros n.
    destruct n.
    admit.
    rewrite an_spec.
    rewrite abs_mult.
    apply (real_le_le_le _ (abs (/ Nreal_fact_neq0 (S n))* (Nreal (fact (n+1)) * M * npow (M) n))).
    apply real_le_mult_pos_le; try apply abs_pos.
    rewrite eval_poly_zero.
    replace M with (M * real_1) at 2 by ring.
    apply p0_bound.
    intros.
    rewrite npow_1;ring_simplify.
    apply Mp1.
  Admitted.


  Lemma y_bound p y r : r > 0 -> pivp0_solution p y r -> {r' : Real | r' > 0 /\ forall (t : I r'), abs (y t) <= r}.
  Proof.
    intros rgt0 H.
    destruct H as [H0 H].
    destruct (bound_polynomial p r) as [M Mp].
    assert (forall (x : I r), abs (eval_poly p x) <= M) as MP'.
    {
      intros.
      destruct x.
      apply Mp;auto.
    }
    assert (M >= 0).
    {
      apply (real_le_le_le _ (abs (eval_poly p 0))).
      apply abs_pos.
      apply Mp.
      rewrite abs_pos_id;[apply real_lt_le | apply real_le_triv];auto.
    }
    exists (r / (real_gt_neq _ _ (abs_plus_1_gt_0 M))).
    split; [apply real_div_gt_0;[|apply abs_plus_1_gt_0];auto|].
    intros.
    destruct t as [T Tp];simpl.
    apply (real_le_le_le _ (dist (y T) (y 0))); [rewrite H0;unfold dist; replace ((y T) - 0) with (y T) ;try apply real_le_triv |].
    admit.
    apply (real_le_le_le _ (M * dist T 0)).
    (* pose proof (lbc_fun _ _ _ M H MP'). *)
  Admitted.

  Definition pivp_ps_exists p : {a : bounded_ps | forall y r, pivp0_solution p y r  -> is_ps_for (fun t => (pc_unit _ (y t))) a}.
  Proof.
    exists (pivp_ps p).
    intros.
    Search is_ps_for.
    apply approx_is_ps.
    intros.
  Admitted.

  

  Fixpoint pn p n := match n with
                     |  0 => p
                     | S n' => mult_coefficients p (derive_poly (pn p n'))
                    end.

  
End IVP.
