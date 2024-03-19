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

  Lemma pivp_to_pivp0 p y0 : {p' : poly | forall y r, pivp_solution p y y0 r <-> pivp0_solution p' (fun t => y t - y0) r }.
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
  Proof.
    induction p.
    apply real_0.
    apply (Minmax.real_max (abs a) IHp).
  Defined.

  Lemma polynorm_empty : poly_norm [] = real_0.
  Proof.
    simpl;auto.
  Qed.

  Lemma polynorm_nonneg p : real_0 <= poly_norm p. 
  Proof.
    induction p.
    rewrite polynorm_empty;apply real_le_triv.
    simpl.
    destruct (Minmax.real_max_cand (abs a) (poly_norm p)) as [-> | ->].
    apply abs_pos.
    apply IHp.
  Qed.
  
  Lemma polynorm_le p : forall n, abs (nth n p real_0) <= poly_norm p.
  Proof.
   induction p.
   intros.
   rewrite polynorm_empty.
   rewrite nth_overflow;simpl;try lia.
   rewrite abs_pos_id;apply real_le_triv.
   simpl poly_norm.
   destruct n.
   simpl.
   apply Minmax.real_max_fst_ge.
   simpl.
   apply (real_le_le_le _ (poly_norm p)).
   apply IHp.
   apply Minmax.real_max_snd_ge.
  Qed.
  Lemma polynorm_mult p q : poly_norm (mult_coefficients p q) = poly_norm p * poly_norm q.
  Admitted.


  Lemma polynorm_deriv_bound p : poly_norm (derive_poly p) <= (Nreal (length p))*poly_norm p.
  Proof.
    simpl.
    induction p.
    unfold derive_poly.
    destruct (poly_deriv_exists []) as [p' [P1 P2]].
    simpl.
    simpl in P1.
    apply length_zero_iff_nil in P1.
    rewrite P1.
    rewrite polynorm_empty.
    apply real_eq_le;ring.
  Admitted.
    
  Lemma smul_length p x : length (pr1 _ _  (smul_poly x p)) = length p.
  Proof.
    induction p;simpl;auto.
    destruct (smul_poly x p).
    simpl in *.
    rewrite IHp;auto.
  Qed.
  Lemma derive_poly_length p : length (derive_poly p) = (length p - 1)%nat.
  Proof.
    unfold derive_poly.
    destruct (poly_deriv_exists p) as [p' [P1 P2]].
    simpl;auto.
  Qed.

  Lemma smul_norm p x : poly_norm (pr1 _ _ (smul_poly x p)) = abs x * poly_norm p.
  Proof.
    induction p.
    simpl.
    ring.
    simpl.
    destruct (smul_poly x p).
    simpl in *.
    rewrite IHp.
    rewrite abs_mult.
    rewrite real_max_hom; try apply abs_pos;auto.
  Qed.

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
    destruct p.
    simpl.
    apply real_eq_le;ring.
    ring_simplify.
    simpl length; simpl Nreal.
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
    rewrite abs_pos_id; try (apply real_lt_le;apply invSn_gt0).
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
  Lemma real_inv_inv p (pn0 : p <> 0) (pn1 : (/ pn0) <> 0) : (/ pn1) = p.
  Admitted.
  Lemma  test0 p : (Nreal (length p) * poly_norm p > 0).
  Admitted.
  Definition pivp_ps_exists_np (q : poly) (y0 : ^Real) : bounded_ps.
  Proof.
    destruct  (pivp_to_pivp0 q y0) as [p P].
    assert (Nreal (length p) * poly_norm p > 0).
    apply test0.
    assert (Nreal (length p) * poly_norm p <> 0).
    apply real_gt_neq;auto.
    assert (real_0 < / H0) by (apply real_pos_inv_pos;auto).
    assert (/ (real_gt_neq _ _ H1) = (Nreal (length p)) * poly_norm p).
    apply real_inv_inv.

    assert (bounded_seq (an0 p) 1 H1).
    {
      intros n.
      simpl;ring_simplify.
      rewrite H2.
      apply an0_bound.
    }
    apply (mk_bounded_ps (an0 p) _ _ H1 H3).

  Qed.
  Definition pivp_ps_exists q y0 : {a : bounded_ps | forall y r, pivp_solution q y y0 r  -> is_ps_for (fun t => (pc_unit _ ((y t) - y0))) a}.
  Proof.
    destruct  (pivp_to_pivp0 q y0) as [p P].
    assert (Nreal (length p) * poly_norm p > 0).
    admit.
    assert (Nreal (length p) * poly_norm p <> 0).
    admit.
    assert (real_0 < / H0).
    admit.
    assert (/ (real_gt_neq _ _ H1) = (Nreal (length p)) * poly_norm p).
    admit.
    assert (bounded_seq (an0 p) 1 H1).
    {
      intros n.
      simpl;ring_simplify.
      rewrite H2.
      apply an0_bound.
    }
    exists (mk_bounded_ps _ _ _ _ H3).
    intros.
    apply P in H4.
  Admitted.

  Lemma test p y y0 r ty: pivp_solution p y y0 r -> snd ty = y (fst (ty)).
  Admitted.

  Lemma local_solution (p : poly) (y0 : ^Real) : {ty1 : Real*Real | (fst ty1) > 0 /\ forall y r, pivp_solution p y y0 r  -> (snd ty1) = (y (fst ty1))}.
  Proof.
    pose proof (pivp_ps_exists_np p y0) as a.
    destruct (eval_val a (eval_radius a)) as [y1 P1].
    rewrite abs_pos_id;try apply real_le_triv.
    apply real_lt_le.
    apply eval_radius_gt0.
    apply fast_limit_limit in P1.
    exists ((eval_radius a), y1+y0).
    split.
    apply eval_radius_gt0.
    intros.
    apply (test _ _ _ _ _ H).
  Qed.
  Lemma solve_ivp (p : poly) y0 (n : nat) : {l : list (Real * Real) | length l = S n /\ forall y r, pivp_solution p y y0 r -> forall ty, In ty l -> (snd ty) = (y (fst ty))}.
   Proof.
   induction n.
   exists [(0, y0)];split;simpl;auto.
   intros.
   destruct H.
   destruct H0; [ |contradict H0].
   rewrite <- H0.
   simpl;rewrite H;auto.

   destruct IHn as [l [L1 L2]].
   destruct (local_solution p (snd (last l (0,0)))) as [[t yn] P].
   exists (l ++ [((fst (last l (0,0)))+t, yn)]).
   intros;split.
   rewrite app_length;simpl;lia.
   intros.
   apply (test _ _ _ _ _ H).
   Qed.

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
  
End IVP.


Section Examples.
Definition exp_example := pr1 _ _ (solve_ivp [3] 2 100).


End Examples.