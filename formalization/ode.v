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

  Lemma pk_spec p (y : Real -> Real) r r' n : (forall (t : I r), abs (y t) <= r' ) ->  pivp0_solution p y r -> nth_derivative y (fun t  => eval_poly (pn p n) (y t)) r (S n).
  Proof.
    intros B H.
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
    induction n.
    simpl.
  Admitted.

  Lemma dSn n : Nreal (S n) <> 0.
  Proof. apply real_gt_neq; apply Nreal_pos;lia. Qed.

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
  Lemma y_bound p y r : r > 0 -> pivp0_solution p y r -> {r' : Real | r' > 0 /\ forall (t : I r'), abs (y t) <= r}.
  Proof.
    intros rgt0 H.
    destruct H as [H0 H].
    destruct (bound_polynomial p r) as [M Mp].
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
    pose proof (lbc_fun _ _ _ M H).
  Admitted.

  Fixpoint pn p n := match n with
                     |  0 => p
                     | S n' => mult_coefficients p (derive_poly (pn p n'))
                    end.

  
End IVP.
