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
   unfold inv_factorial.
   apply (real_eq_mult_cancel (Nreal (fact 0))).
   simpl.
   replace (real_1 + real_0) with real_1 by ring.
   apply real_1_neq_0.
   rewrite real_mult_inv.
   simpl;ring_simplify;auto.
 Qed.

 Lemma inv_factorial1 : inv_factorial 1 = real_1.
 Proof.
   unfold inv_factorial.
   apply (real_eq_mult_cancel (Nreal (fact 1))).
   simpl.
   replace (real_1 + real_0) with real_1 by ring.
   apply real_1_neq_0.
   rewrite real_mult_inv.
   simpl;ring_simplify;auto.
 Qed.

 Lemma inv_factorialS n : inv_factorial (S n) = (/ dSn n) * inv_factorial n.
 Proof.
   unfold inv_factorial.
   apply (real_eq_mult_cancel (Nreal (fact n))).
   apply Nreal_fact_neq0.
   rewrite real_mult_assoc, real_mult_inv.
   apply (real_eq_mult_cancel (Nreal (fact (S n)))).
   apply Nreal_fact_neq0.
   rewrite real_mult_assoc, (real_mult_comm (Nreal _)), <-real_mult_assoc, real_mult_inv.
   ring_simplify.
   apply (real_eq_mult_cancel (Nreal (S n))).
   apply real_gt_neq.
   apply Nreal_pos;lia.
   rewrite real_mult_assoc, (real_mult_comm (Nreal (fact (S n)))), <-real_mult_assoc, real_mult_inv.
   simpl;ring_simplify;rewrite Nreal_hom, Nreal_mult;ring.
 Qed.

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
  Definition pivp_solution  p y y0 r := (y 0) = y0 /\ uniform_derivative_fun y (fun t => (eval_poly p (y t))) r.

  Definition pivp0_solution p y r := (y 0) = 0 /\ uniform_derivative_fun y (fun t => (eval_poly p (y t))) r.


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

  Lemma eval_poly_deriv_ext a b p1 p2 : length p1 = length p2 -> derive_poly (a :: p1) = derive_poly (b :: p2) -> p1 = p2.
  Proof.
    unfold derive_poly.
    intros.
    destruct (poly_deriv_exists (a :: p1)) as [p1' [P1 Q1]].
    destruct (poly_deriv_exists (b :: p2)) as [p2' [P2 Q2]].
    simpl in *.
    apply (nth_ext _ _ real_0 real_0);auto.
    intros.
    apply (real_eq_mult_cancel (Nreal (S n))).
    apply real_gt_neq; apply Nreal_pos;lia.
    rewrite !(real_mult_comm _ (Nreal _)).
    simpl.
    rewrite <-Q1.
    rewrite <-Q2.
    rewrite H0;auto.
  Qed.

  Lemma derivative_cont f f' r :  uniform_derivative_fun f f' r -> uniform_continuous_fun f' r.
  Proof.
    intros.
    apply derivative_function_iff in H.
    apply uniform_continuous_iff.
    apply (derivative_is_uniformly_continuous _ _ _ H).
  Qed.

  Lemma derivative_unique f g1 g2 r : r > 0 -> uniform_derivative_fun f g1 r -> uniform_derivative_fun f g2 r -> forall (x : I r), g1 x = g2 x. 
  Proof.
    intros.
    assert (g1 x - g2 x = real_0).
    - apply lim_zero_eq_zero.
      intros.
      pose proof (derivative_cont _ _ _ H0).
      destruct (H3 (eps / d2)) as [d0 [d0gt0 D0]].
      apply real_half_gt_zero;auto.
      destruct (H0 (((eps / d2) / d2))) as [d1 [d1gt0 D1]].
      apply real_half_gt_zero;apply real_half_gt_zero;auto.
      destruct (H1 ((eps / d2)/ d2)) as [d2' [d2gt0 D2]].
      apply real_half_gt_zero;apply real_half_gt_zero;auto.
      assert (exists d, d > 0 /\ d <= r /\ d <= d1 /\ d <= d2' /\ d <= d0) as [d [D'1 [D'2 [D'3 [D'4 D'5 ]]]]].
      {
        remember (Minmax.real_min r d1) as a.
        assert (a > 0 /\ a <= r /\ a <= d1) as [ap1 [ap2 ap3]].
        rewrite Heqa.
        split; [destruct (Minmax.real_min_cand r d1) as [-> | ->]|split;[apply Minmax.real_min_fst_le|apply Minmax.real_min_snd_le]];auto.
        remember (Minmax.real_min a d2') as b.
        assert (b > 0 /\ b <= r /\ b <= d1 /\ b <= d2' ) as [bp1 [bp2 [bp3 bp4]]].
        rewrite Heqb.
        split; [destruct (Minmax.real_min_cand a d2') as [-> | ->]|split;[apply (real_le_le_le _ _ _ (Minmax.real_min_fst_le _ _)) | split; [apply (real_le_le_le _ _ _ (Minmax.real_min_fst_le _ _))|apply Minmax.real_min_snd_le]]];auto.
        exists (Minmax.real_min b d0).
        split; [destruct (Minmax.real_min_cand b d0) as [-> | ->]|split;[apply (real_le_le_le _ _ _ (Minmax.real_min_fst_le _ _)) | split; [apply (real_le_le_le _ _ _ (Minmax.real_min_fst_le _ _))|split; [|apply Minmax.real_min_snd_le]]]];auto.
        apply (real_le_le_le _ _ _ (Minmax.real_min_fst_le _ _));auto.
      }
      assert (abs (x+d) <= r \/ abs (x - d) <= r).
      {
        destruct (real_lt_or_ge x 0).
        left.
        apply Minmax.real_abs_le_le_le.
        apply (real_le_le_le _ d);auto.
        add_both_side_by (-d);auto.
        apply real_lt_le;auto.
        add_both_side_by d.
        apply (real_le_le_le _ r).
        destruct x.
        simpl.
        apply Minmax.real_abs_le_neg_le;auto.
        add_both_side_by (-r);apply real_lt_le;auto.
        right.
        apply Minmax.real_abs_le_le_le.
        apply (real_le_le_le _ x).
        add_both_side_by (d-x).
        apply real_lt_le;auto.
        destruct x.
        simpl.
        apply Minmax.real_abs_le_pos_le;auto.
       apply (real_le_le_le _ d);auto.
       add_both_side_by (-d+x);auto.
      }
      assert (exists (y : I r), dist x y <= d1 /\ dist x y <= d2' /\ dist x y <= d0 /\ dist x y > 0) as [y [Y1 [Y2 [Y3 Y4]]]].
      {
        destruct H4; exists (real_to_I H4);simpl;unfold dist.
        replace (x-(x+d)) with (-d) by ring.
        rewrite <-abs_symm.
        rewrite abs_pos_id; [|apply real_lt_le];auto.
        replace (x-(x-d)) with d by ring.
        rewrite abs_pos_id; [|apply real_lt_le];auto.
      }
      apply (real_le_mult_pos_cancel (abs (y-x))).
      rewrite <-dist_abs;auto.
      rewrite <-abs_mult.
      replace ((g1 x - g2 x) * (y - x)) with (((f y - f x - g2 x * (y-x)) + (f x - f y - g1 y * (x -y))) + (g1 y - g1 x)*(x-y)) by ring.
      rewrite (half_twice_mult eps).
      apply (real_le_le_le _ _ _ (abs_tri _ _)).
      apply real_le_le_plus_le.
      rewrite (half_twice_mult (eps / real_2_neq_0)).
      apply (real_le_le_le _ _ _ (abs_tri _ _)).
      apply real_le_le_plus_le.
      apply D2;auto.
      rewrite (abs_symm (y-x)).
      replace (- (y-x)) with (x-y) by ring.
      apply D1; rewrite dist_symm;auto.
      rewrite abs_mult.
      rewrite (abs_symm (y-x)).
      replace (- (y-x)) with (x-y) by ring.
      rewrite !(real_mult_comm _ (abs (x-y))).
      apply real_le_mult_pos_le; try apply abs_pos.
      apply D0.
      rewrite dist_symm;auto.
   - replace (g1 x) with ((g1 x - g2 x) + g2 x) by ring;rewrite H2; ring.
  Qed.

  Lemma poly_deriv_eval_ext p1 p2 : (forall x, eval_poly p1 x = eval_poly p2 x) -> forall x, eval_poly (derive_poly p1) x = eval_poly (derive_poly p2) x.
  Proof.
    revert p2.
    intros.
    pose proof (derive_poly_spec p1).
    pose proof (derive_poly_spec p2).
    assert (forall r, uniform_derivative_fun (eval_poly p1) (eval_poly (derive_poly p2)) r).
    {
      intros.
      apply (derive_ext_fun _ (eval_poly p2)).
      intros;auto.
      apply H1.
    }
    assert (abs x <= abs x + real_1).
    {
      add_both_side_by (-abs x).
      apply real_lt_le.
      apply real_1_gt_0.
    }
    pose proof (derivative_unique (eval_poly p1) (eval_poly (derive_poly p1)) (eval_poly (derive_poly p2)) _ (abs_plus_1_gt_0 x) (H0 (abs x + real_1)) (H2 (abs x + real_1)) (real_to_I H3)).
    apply H4.
  Qed.

  Lemma derive_poly_length p : length (derive_poly p) = (length p - 1)%nat.
  Proof.
    unfold derive_poly.
    destruct (poly_deriv_exists p) as [p' [P1 P2]].
    simpl;auto.
  Qed.
  
  Lemma eval_poly_ext_helper p1 p2 n : length p1 = n -> length p2 = n -> (forall x, eval_poly p1 x = eval_poly p2 x) -> p1 = p2.
  Proof.
     revert p1; revert p2.
     induction n.
     intros.
     rewrite length_zero_iff_nil in H0,H;auto.
     rewrite H, H0;auto.

     intros.
     destruct p1.
     contradict H;simpl;lia.
     destruct p2.
     contradict H0;simpl;lia.
    assert (r0 = r) as ->.
    {
      specialize (H1 real_0).
      simpl in H1.
      ring_simplify in H1;auto.
    }
    replace p2 with p1; auto.
    apply (eval_poly_deriv_ext r r).
    simpl in *;lia.
    apply IHn; try (rewrite derive_poly_length;simpl in *;lia).
    apply poly_deriv_eval_ext.
    apply H1.
  Qed.

  Lemma eval_poly_ext p1 p2 : length p1 = length p2 -> (forall x, eval_poly p1 x = eval_poly p2 x) -> p1 = p2.
  Proof.
    intros.
    apply (eval_poly_ext_helper _ _ (length p1));auto.
  Qed.
  Definition scalar_mult_poly m p := pr1 _ _ (smul_poly m p).

  Lemma scalar_mult_poly_spec m p x: eval_poly (scalar_mult_poly m p) x = m * eval_poly p x.
  Proof.
    unfold scalar_mult_poly.
    destruct smul_poly.
    simpl;auto.
  Qed.
  Lemma smul_length x p : length (scalar_mult_poly x p) = length p.
  Proof.
    unfold scalar_mult_poly.
    induction p;simpl;auto.
    destruct (smul_poly x p).
    simpl in *.
    rewrite IHp;auto.
  Qed.
  Lemma scalar_mult_cons m a p : scalar_mult_poly m (a :: p) = (m*a) :: scalar_mult_poly m p.
  Proof.
    apply eval_poly_ext.
    simpl;rewrite !smul_length;simpl;auto.
    intros.
    simpl.
    rewrite scalar_mult_poly_spec.
    simpl.
    rewrite scalar_mult_poly_spec.
    ring.
  Qed.
  
  Lemma scalar_mult_nth m p n : nth n (scalar_mult_poly m p) real_0  = m* nth n p real_0.
  Proof.
    revert n.
    induction p.
    destruct n;simpl;ring.
    intros.
    rewrite scalar_mult_cons.
    destruct n.
    simpl;auto.
    simpl.
    apply IHp.
 Qed.

  Fixpoint dn p n := match n with
                     |  0 => p
                     | S n' => mult_coefficients p (derive_poly (dn p n'))
                    end.

  
 Lemma dn_length p n : (length (dn p n) = ((n+1)*(length p))-2*n)%nat.
  Proof.
    induction n; [simpl;lia|].
    simpl dn.
    rewrite length_mult_coefficients.
    rewrite derive_poly_length.
    rewrite IHn.
    simpl.
    ring_simplify.
    replace (n+0)%nat with n by lia.
    destruct (length p); try lia.
    destruct n0;lia.
  Qed.

  Fixpoint pn p n := match n with
                     |  0 => p
                     | S n' => scalar_mult_poly (/ dSn n) (mult_coefficients p (derive_poly (pn p n')))
                    end.
  
  Lemma pn_length p n : (length (pn p n)) = length (dn p n).
  Proof.
     induction n; [simpl; lia|].
     simpl.
     rewrite smul_length.
     rewrite !length_mult_coefficients.
     rewrite !derive_poly_length.
     rewrite IHn;lia.
  Qed.


  Lemma derive_poly_nth p n : nth n (derive_poly p) real_0 = (Nreal (S n)) * nth (S n) p real_0.
  Proof.
    unfold derive_poly.
    destruct (poly_deriv_exists p) as [p' [P1 P2]].
    simpl;auto.
  Qed.

  Lemma derive_scalar_mult p m : derive_poly (scalar_mult_poly m p) = scalar_mult_poly m (derive_poly p).
  Proof.
    apply (nth_ext _ _ real_0 real_0).
    rewrite derive_poly_length, !smul_length, derive_poly_length;auto.
    intros.
    rewrite derive_poly_nth.
    rewrite !scalar_mult_nth.
    rewrite derive_poly_nth.
    ring.
  Qed.
  Lemma mult_coeff_scalar_mult p q m : mult_coefficients p (scalar_mult_poly m q) = scalar_mult_poly m (mult_coefficients p q).
  Proof.
    apply eval_poly_ext.
    rewrite length_mult_coefficients, !smul_length, length_mult_coefficients;auto.
    intros.
    rewrite mult_coeff_spec, !scalar_mult_poly_spec, mult_coeff_spec.
    ring.
  Qed.
  Lemma pn_spec p n : pn p n = scalar_mult_poly (inv_factorial (S n)) (dn p n).
  Proof.
    apply (nth_ext _ _ real_0 real_0); [rewrite smul_length;apply pn_length|].
    induction n;intros.
    rewrite scalar_mult_nth;rewrite inv_factorial1; simpl; ring.
    simpl.
    rewrite !scalar_mult_nth.
    rewrite (inv_factorialS ( S n)).
    rewrite !real_mult_assoc.
    apply real_eq_mult_eq.
    apply nth_ext in IHn.
    rewrite IHn.
    rewrite derive_scalar_mult, mult_coeff_scalar_mult.
    rewrite scalar_mult_nth;auto.
    rewrite smul_length.
    apply pn_length.
  Qed.  

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

  Lemma dn_spec p (y : Real -> Real) r n : pivp0_solution p y r -> nth_derivative y (fun t  => eval_poly (dn p n) (y t)) r (S n).
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
    exists (fun t => eval_poly (dn p n) (y t)).
    split;[apply IHn|].
    simpl.
    apply (derive_ext_fun2 _ (fun t => eval_poly p (y t) * eval_poly (derive_poly (dn p n)) (y t)));[intros;apply mult_coeff_spec|].
    apply (chain_rule _ _ _ _ r').
    apply derive_poly_spec.
    apply H.
    intros.
    apply (B (real_to_I H0)).
  Qed.

  Definition pn0 p n :=
    match n with
      | 0 => 0
      | S n' => (eval_poly (pn p n') real_0)
      end.
  Lemma pn0_spec p n : pn0 p (S n) = (inv_factorial (S n)) * (eval_poly (dn p n) real_0).
  Proof.
    unfold pn0.
    rewrite pn_spec.
    rewrite scalar_mult_poly_spec;auto.
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
    

  Lemma smul_norm p x : poly_norm (scalar_mult_poly x p) = abs x * poly_norm p.
  Proof.
    unfold scalar_mult_poly.
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

  Lemma invSn_gt0 : forall n, (/ dSn n) > real_0.
  Proof.
    intros.
    apply real_pos_inv_pos2.
  Qed.

   Lemma nth_to_poly a m n : (m <= n)%nat -> nth m (to_poly a n) real_0 = (a m).
  Proof.
    induction n.
    simpl;auto.
  Admitted.
  Lemma pivp_ps_taylor_series p : forall y r, pivp0_solution p y r -> forall n, (is_taylor_polynomial (to_poly (pn0 p) n) y r).
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
      exists (fun t  => eval_poly (dn p n) (y t)).
      split.
      apply dn_spec;auto.
      rewrite nth_to_poly; try lia.
      rewrite (proj1 H).
      apply pn0_spec.
  Qed.

  Lemma pn_norm p n : poly_norm (pn p n) <= npow (Nreal (length p)*poly_norm p) (S n).
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

    simpl pn.
    rewrite smul_norm.
    rewrite polynorm_mult.
    pose proof (polynorm_deriv_bound (pn p n)).
    assert (poly_norm (derive_poly (pn p n)) <= Nreal ((n+1)*length p) * (npow (Nreal (length p) * poly_norm p) (S n))).
    {
      apply (real_le_le_le _ _ _ H).
      rewrite pn_length.
      rewrite dn_length.
      apply (real_le_le_le _ (Nreal ((n+1) *length p)*poly_norm (pn p n))).
      apply real_le_mult_pos_le_le; try apply Nreal_nonneg; try apply polynorm_nonneg; try apply real_le_triv.
      apply Nreal_monotone;lia.
      apply real_le_mult_pos_le; try apply Nreal_nonneg.
      apply IHn.
    }
    apply (real_le_le_le _ (((/ dSn n) * poly_norm p) *  (Nreal ((n+1)*length p) * (npow (Nreal (length p) * poly_norm p) (S n))))).
    rewrite <-real_mult_assoc.
    rewrite abs_pos_id; try (apply real_lt_le;apply invSn_gt0).
    apply real_le_mult_pos_le_le.
    apply real_le_pos_mult_pos_pos.
    apply real_lt_le.
    apply (invSn_gt0 (S n)).
    apply polynorm_nonneg.
    apply polynorm_nonneg.
    rewrite !(real_mult_comm _ (poly_norm p)).
    apply real_le_mult_pos_le.
    apply polynorm_nonneg.
    apply inv_le_ge.
    apply Nreal_pos;lia.
    simpl.
    add_both_side_by (- real_1 - Nreal n).
    apply real_lt_le.
    apply real_1_gt_0.
    apply H0.
    apply real_lt_le.
    apply (invSn_gt0 (S n)).
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
    rewrite real_mult_comm.
    replace (Nreal (n+1) * / dSn n) with real_1.
    ring_simplify;apply real_le_triv.
    rewrite real_mult_comm.
    replace (n+1)%nat with (S n) by lia.
    rewrite real_mult_inv;auto.
  Qed.



  Lemma eval_poly_zero p : eval_poly p real_0 = nth 0 p real_0.
  Proof.
    induction p;auto.
    simpl.
    ring_simplify;auto.
  Qed.
  
  Lemma pn0_bound p n : abs (pn0 p n) <= npow (Nreal (length p) * poly_norm p) n.
  Proof.
    destruct n;[apply real_lt_le; rewrite abs_pos_id; try apply real_1_gt_0;apply real_le_triv|].
    simpl pn0.
    rewrite eval_poly_zero.
    apply (real_le_le_le _ _ _ (polynorm_le _ _)).
    apply pn_norm.
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

  Lemma taylor_series_converges a f r : (forall n, is_taylor_polynomial (to_poly a n) f r) -> forall (x : I r), is_sum (ps a x) (f x).
  Proof.
    intros.
  Admitted.

  Definition pivp_ps_exists q y0 : {a : bounded_ps | forall y, pivp_solution q y y0 (eval_radius a)  -> is_ps_for (fun t => (pc_unit _ ((y t) - y0))) a}.
  Proof.
    destruct  (pivp_to_pivp0 q y0) as [p P].
    remember (abs (Nreal (length p) * poly_norm p) + real_1) as r.
    assert (r > 0).
    {
      rewrite Heqr.
      apply abs_plus_1_gt_0.
    }
    assert (r <> 0) by (apply real_gt_neq;auto).
    assert (real_0 < / H0) by (apply real_pos_inv_pos;auto).
    (* assert (/ (real_gt_neq _ _ H1) = (Nreal (length p)) * poly_norm p). *)
    (* admit. *)
    assert (bounded_seq (pn0 p) 1 H1).
    {
      intros n.
      simpl;ring_simplify.
      apply (real_le_le_le _ _ _ (pn0_bound p n)).
      apply npow_nonneg_le.
      apply real_le_pos_mult_pos_pos.
      apply Nreal_nonneg.
      apply polynorm_nonneg.
      apply (real_le_mult_pos_cancel (/ H0));auto.
      rewrite real_mult_inv.
      rewrite <-(abs_pos_id (_ * (poly_norm p))).
      apply (real_le_mult_pos_cancel r);auto.
      rewrite real_mult_assoc.
      rewrite real_mult_inv.
      ring_simplify.
      rewrite Heqr.
      add_both_side_by (- (abs (Nreal (length p) * poly_norm p)));apply real_lt_le;apply real_1_gt_0.
      apply real_le_pos_mult_pos_pos.
      apply Nreal_nonneg.
      apply polynorm_nonneg.
    }
    exists (mk_bounded_ps _ _ _ _ H2).
    intros.
    apply P in H3.
    unfold is_ps_for.
    unfold eval_radius in *.
    simpl in *.
    intros.
    pose proof (powerseries_pc_spec (pn0 p) x (y x - y0)).
    apply H6.
    pose proof (pivp_ps_taylor_series _ _ _ H3).
    pose proof (taylor_series_converges (pn0 p) (fun t => (y t) - y0) _ H7 (real_to_I H4)).
    apply H8.
  Qed.

  Lemma local_solution (p : poly) (y0 : ^Real) : {ty1 : Real*Real | (fst ty1) > 0 /\ exists r, r > 0 /\ (fst ty1) <= r /\ (forall y,  pivp_solution p y y0 r  -> (snd ty1) = (y (fst ty1)))}.
  Proof.
    destruct (pivp_ps_exists p y0) as [a A].
    destruct (eval_val a (eval_radius a)) as [y1 P1].
    rewrite abs_pos_id;try apply real_le_triv.
    apply real_lt_le.
    apply eval_radius_gt0.
    apply fast_limit_limit in P1.
    exists ((eval_radius a), y1+y0).
    split.
    apply eval_radius_gt0.
    simpl.
    exists (eval_radius a).
    split; [apply eval_radius_gt0|split;[apply real_le_triv|]].
    intros.
    specialize (A y H (eval_radius a)).
    apply (real_eq_plus_cancel (-y0)).
    ring_simplify.
    replace (-y0 + y (eval_radius a)) with (y (eval_radius a) - y0) by ring.
    apply pc_unit_mono.
    rewrite <-A.
    pose proof (powerseries_pc_spec (series a) (eval_radius a) y1).
    apply eq_sym.
    apply H0.
    apply P1.
    rewrite abs_pos_id.
    apply real_le_triv.
    apply real_lt_le.
    apply eval_radius_gt0.
    apply unit_defined.
  Qed.

  Lemma uniform_derivative_smaller_r f g r1 r2 : (r2 <= r1) -> uniform_derivative_fun f g r1 -> uniform_derivative_fun f g r2.
  Proof.
    intros.
    intros eps epsgt0.
    destruct (H0 _ epsgt0) as [d [H' H'']].
    exists d.
    split;auto.
    intros.
    assert (abs x <= r1 /\ (abs y) <= r1) as [X Y].
    destruct x;destruct y;split;apply (real_le_le_le  _ r2);auto.
    apply (H'' (real_to_I X) (real_to_I Y));auto.
  Qed.

  Lemma pivp_solution_smaller_r p y y0 r1 r2 : (r2 <= r1) -> pivp_solution p y y0 r1 -> pivp_solution p y y0 r2.
  Proof.
    intros.
    destruct H0.
    split;auto.
    apply (uniform_derivative_smaller_r _ _ r1 r2);auto.
  Qed.

  Lemma uniform_derivative_shift f g r t0 : uniform_derivative_fun f g r -> uniform_derivative_fun (fun t => (f (t0+t))) (fun t => (g (t0+t))) (r-(abs t0)).
  Proof.
    intros H eps epsgt0.
    destruct (H _ epsgt0) as [d [D1 D2]].
    exists d.
    split;auto.
    intros.
    assert (abs (t0+x) <= r /\ abs (t0+y) <= r) as [X Y].
    {
      destruct x;destruct y;simpl in *.
      split;apply (real_le_le_le _ _ _ (abs_tri _ _));add_both_side_by (- abs t0); apply (real_le_le_le _ (r-abs t0));auto;apply real_eq_le;ring.
    }
    replace (y - x) with (t0 + y - (t0+x)) by ring.
    apply (D2 (real_to_I X) (real_to_I Y)).
    simpl.
    unfold dist.
    replace (t0+x - (t0+y)) with (x-y) by ring.
    apply H0.
  Qed.

  Lemma pivp_solution_time_independent p y y0 r t0 : ((y t0) = y0 /\ uniform_derivative_fun y (fun t => (eval_poly p (y t))) r) -> pivp_solution p (fun t => y (t0+t)) y0 (r - abs t0).
  Proof.
    intros.
    destruct H.
    split.
    replace 0 with real_0 by auto;rewrite real_plus_comm, real_plus_unit;auto.
    apply (uniform_derivative_shift _ _ _ _ H0).
  Qed.  

  Lemma solve_ivp (p : poly) y0 (n : nat) : {l : list (Real * Real) | length l = S n /\
      (forall m, fst (nth m l (0,0)) >= 0)  /\
      (forall m, (m < n)%nat -> (fst (nth m l (0,0)) < (fst (nth (S m) l (0,0))))) /\
      exists r, (r > 0) /\ (fst (nth n l (0,0))) <= r /\  forall y, pivp_solution p y y0 r -> forall ty, In ty l ->  (snd ty) = (y (fst ty))}.
   Proof.
   induction n.
   - exists [(0, y0)];split;[|split; [|split]];simpl;auto.
     intros;destruct m;[|destruct m];simpl;auto;apply real_le_triv.
     intros;simpl;auto;intros;try lia.
     destruct (local_solution p y0) as [[t y1] [P1 P2]].
     destruct P2 as [r [rgt0 _]].
     exists r.
     split;auto;split.
     apply real_lt_le;auto.
     intros.
     destruct H0 as [<-|]; try contradict H0.
     simpl;rewrite (proj1 H);auto.
   - destruct IHn as [l [L1 [L2 [L3 L4]]]].
     destruct (local_solution p (snd (nth n l (0,0)))) as [[t yn] [P1 P2]].
     exists (l ++ [((fst (nth n l (0,0)))+t, yn)]).
     intros;split.
     rewrite app_length;simpl;lia.
     split; [|split].
     +  intros.
        destruct (Nat.lt_ge_cases m (S (length l))).
        destruct (Lt.le_lt_or_eq_stt _ _ H).
        rewrite app_nth1;try lia.
        apply L2.
        apply Nat.succ_inj in H0.
        rewrite H0.
        rewrite nth_middle.
        simpl.
        Search (_ <= _ + _ ).
        replace 0 with (real_0) at 3 by auto;replace real_0 with (real_0 + real_0) by ring.
        apply real_le_le_plus_le.
        apply L2.
        apply real_lt_le;auto.
        rewrite nth_overflow;simpl;[apply real_le_triv|rewrite app_length;simpl;lia].
     +  intros.
        rewrite Nat.lt_succ_r in H.
        apply Lt.le_lt_or_eq_stt in H.
        destruct H.
        rewrite !app_nth1; try lia.
        apply L3;auto.
        rewrite H.
        rewrite <- L1.
        rewrite nth_middle.
        rewrite app_nth1;try lia.
        simpl.
        add_both_side_by (- (fst (nth n l (0,0)))).
        apply P1.
     + destruct L4 as [r0 [r0gt0 R0]].
       destruct P2 as [r [rgt0 [tler R]]].
       exists (r0 + r).
       split; [apply real_gt0_gt0_plus_gt0;auto|].
       split.
       rewrite <-L1.
       rewrite nth_middle.
       simpl.
       apply real_le_le_plus_le;auto;apply R0.
       intros.
       apply in_app_or in H0.
       destruct H0.
       apply R0;auto.
       apply (pivp_solution_smaller_r _ _ _ (r0 + r));auto.
       add_both_side_by (-r0);apply real_lt_le;auto.

       simpl in H0.
       destruct H0;[|contradict H0].
       rewrite <-H0.
       simpl.
       simpl in R.
       specialize (R (fun t => (y (fst (nth n l (0,0))+t)))).
       apply R.
       remember (fst (nth n l (0,0))) as tsn.
       remember (snd (nth n l (0,0))) as ysn.
       simpl in *.
       pose proof (pivp_solution_time_independent p y ysn (r+abs tsn) tsn).
       replace r with (r + abs tsn - abs tsn) by ring.
       apply H1.
       split.
       rewrite Heqtsn, Heqysn.
       apply eq_sym.
       apply R0.
       apply (pivp_solution_smaller_r _ _ _ (r0+r));auto.
       add_both_side_by (-r0);apply real_lt_le;auto.
       apply nth_In;lia.
       destruct H.
       apply (uniform_derivative_smaller_r _ _ (r0+r));auto.
       rewrite real_plus_comm.
       add_both_side_by (-r).
       rewrite abs_pos_id.
       apply R0.
       rewrite Heqtsn.
       apply L2.
  Qed.
End IVP.


Section Examples.
Definition exp_example := pr1 _ _ (solve_ivp [3] 2 100).


End Examples.
