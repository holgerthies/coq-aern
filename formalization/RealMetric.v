Require Import Base.
Require Import Kleene.
Require Import RealAxioms.
Require Import RealRing.
Require Import RealOrder.
Require Import RealOrderTactic.
Require Import RealLimit1.



Require Import Psatz.
Require Import PeanoNat.



Definition abs_prop : forall x : Real, {y : Real | (x > Real0 -> y = x) /\ (x = Real0 -> y = Real0) /\ (x < Real0 -> y = - x)}.
Proof.
  intros x.

  apply Real_mslimit_P_lt_p.
  destruct (Realtotal_order x Real0).
  exists (- x).
  split.
  repeat split.
  intro p; contradict p; auto with Realiny.
  intro p; induction p; contradict H; auto with Realiny.
  intros.
  destruct H0 as [_ [_ H0]].
  induction (H0 H); apply eq_refl.
  destruct H.
  exists Real0.
  repeat split; auto with Realiny.
  intro p; induction H; contradict p; auto with Realiny.
  intros.
  destruct H0 as [_ [H0 _]].
  induction (H0 H); apply eq_refl.
  exists x.
  repeat split; auto with Realiny.
  intro p; contradict p; auto with Realiny.
  intros.
  destruct H0 as [H0 [_ _]].
  induction (H0 H); apply eq_refl.

  intro.
  pose proof (M_split x Real0 (prec (n + 2))).
  assert (prec n > Real0);
    auto with Realiny.

  assert (({x > Real0 - prec (n + 2)} + {Real0 > x - prec (n + 2)}) -> {e : Real | exists a : Real, ((x > Real0 -> a = x) /\ (x = Real0 -> a = Real0) /\ (x < Real0 -> a = - x)) /\ - prec n < e - a < prec n}).
  intro order.
  destruct order. 
  exists x.
  destruct (Realtotal_order x Real0).
  exists (- x).
  repeat split; auto with Realiny.
  intro j; contradict j; auto with Realiny.
  intro j; induction j; contradict H0; auto with Realiny.
  assert (x - - x =  x + x).
  ring.
  rewrite H1.
  replace (Real0 - prec (n + 2)) with ( - prec (n + 2)) in r by ring.
  assert (x + x > -prec (n + 2) + x).
  auto with Realiny.
  
  pose proof (Reallt_plus_r_lt x _ _ r).
  exact H2.
  assert (- prec (n + 2) + x > - prec (n + 2) + - prec (n +2 )).
  apply (Reallt_plus_lt).
  exact r.
  assert (x + x > - prec (n + 2) + - prec (n + 2)).
  apply (Reallt_lt_lt _ _ _ H3 H2).
  assert (- prec n < - prec (n + 2) + - prec (n + 2)).
  apply Reallt_anti_anti.
  ring_simplify.


  assert( prec (n+ 2) < prec (n +1)).
  replace (n+2)%nat with (S (n+1))%nat by auto.
  apply prec_S.
  
  pose proof (Reallt_mult_pos_lt (Real1 + Real1) _ _ Real2_pos  H5).
  assert ((Real1 + Real1) * prec (n +1) = prec n).
  replace (n+ 1)%nat with (S n).
  simpl.
  ring_simplify.
  replace ((Real1 + Real1) * (prec n / Real2_neq_Real0))
          with ((Real1 + Real1)*(prec n * /Real2_neq_Real0)) by auto.
  replace
    ( (Real1 + Real1) * (prec n * / Real2_neq_Real0))
    with
      ((Real1 + Real1) * (/ Real2_neq_Real0 * prec n )).
  replace
    ((Real1 + Real1) * (/ Real2_neq_Real0 * prec n))
    with
      (((Real1 + Real1) * (/ Real2_neq_Real0) * prec n)) by ring.
  replace
    ( (Real1 + Real1) * / Real2_neq_Real0) with Real1.
  ring.
  replace (Real1 + Real1) with Real2 by auto.
  replace (Real2 * / Real2_neq_Real0) with
      (/ Real2_neq_Real0 * Real2) by ring.
  symmetry.
  apply Realmult_inv.
  ring.
  pose proof (plus_n_Sm n O).
  rewrite<- H7.
  auto.
  rewrite<- H7.
  exact H6.
  apply (Reallt_lt_lt _ _ _ H5 H4).

  ring_simplify.

  pose proof (Reallt_mult_pos_lt (Real2) _ _ Real2_pos H0).
  ring_simplify in H1.
  pose proof (prec_pos n).
  apply (Reallt_lt_lt _ _ _ H1 H2).

  destruct H0.
  exists Real0.
  rewrite H0.
  
  repeat split; auto; try intro; try ring.
  apply Reallt_anti_anti.
  ring_simplify.
  apply prec_pos.
  ring_simplify.
  apply prec_pos.

  exists x.
  repeat split; auto; try intro; try ring.
  contradict H1; auto with Realiny.
  apply Reallt_anti_anti.
  ring_simplify.
  apply prec_pos.
  ring_simplify.
  apply prec_pos.


  exists (-x).
  destruct (Realtotal_order x Real0).
  exists (- x).
  repeat split; try intro; try auto with Realiny; try ring.
  contradict H1; auto with Realiny.
  rewrite H1; ring.
  ring_simplify.
  apply Reallt_anti_anti.
  ring_simplify.
  apply prec_pos.
  ring_simplify; apply prec_pos.

  destruct H0.
  exists Real0.
  rewrite H0.
  repeat split; try intro; try auto with Realiny; try ring; ring_simplify.
 
  apply Reallt_anti_anti.
  ring_simplify. 
  apply prec_pos.
  apply prec_pos.

  exists x.
  repeat split; try intro; try auto with Realiny; try ring; ring_simplify.
  contradict H1; auto with Realiny.
  apply Reallt_anti_anti.
  ring_simplify.
  assert ( x < prec (n +2)).
  assert ( x - prec (n + 2) < Real0).
  auto.
  

      
  pose proof (Reallt_plus_r_lt (prec (n + 2)) _ _ H1).
  ring_simplify in H2.
  exact H2.
  pose proof (Reallt_mult_r_pos_lt _ _ Real2 (Real2_pos) H1).
  replace (x * Real2) with (Real2 * x) in H2 by ring.
  assert (prec (n + 2) * Real2 < prec n).
  assert (prec (n + 2) * Real2 = prec (n + 1)).
  assert ((n + 2) = S( n+1))%nat.
  auto.
  rewrite H3.
  simpl.
  replace
    (prec (n + 1) / Real2_neq_Real0 * Real2)
    with
      (prec (n + 1) */ Real2_neq_Real0 * Real2) by auto.
  replace
    ( prec (n + 1) * / Real2_neq_Real0 * Real2)
    with
      ( prec (n + 1) * (/ Real2_neq_Real0 * Real2)) by ring.
  replace
    ( prec (n + 1) * (/ Real2_neq_Real0 * Real2)) with
      ( prec (n + 1) * (Real1)) by auto with Realiny.
  ring.
  rewrite H3.
  pose proof (plus_n_Sm n O).
  rewrite <- H4.
  replace (n+0)%nat with n by auto.
  apply prec_S.
  apply (Reallt_lt_lt _ _ _ H2 H3).
  assert( Real0 <  x) by auto.

  pose proof (Reallt_mult_r_pos_lt _ _ Real2 (Real2_pos) H1).
  ring_simplify in H2.
  apply Reallt_anti_anti.
  ring_simplify.
  pose proof (prec_pos n).
  apply Reallt_anti in H3.
  ring_simplify in H3.
  apply (Reallt_lt_lt _ _ _ H3 H2 ).
  
  (* lifting *)

  apply (liftM _ _  H0).
  apply M_split.
  apply prec_pos.

Defined.


  
  
Definition abs : Real -> Real.
Proof.
  intros x.
  destruct (abs_prop x).
  exact x0.
Defined.


Lemma abs_pos : forall x, Real0 <= abs x.
Proof.
  intros.
  unfold abs.
  destruct (abs_prop x).
  destruct a as [a [b c]].
  destruct (Realtotal_order x Real0).
  pose proof (c H).
  rewrite H0.
  left.
  apply Reallt_anti_anti.
  ring_simplify.
  exact H.
  destruct H.
  right.
  rewrite (b H); auto.

  left. rewrite( a H); auto.
Qed.



Definition dist : Real -> Real -> Real := fun x y => abs (x - y).

Lemma dist_pos_t : forall x y, Real0 <= dist x y.
Proof.
  intros.
  unfold dist.
  apply abs_pos.
Qed.


Global Hint Resolve abs_pos dist_pos_t: Realiny.


(* let us have a strong definition of dist then make other obligations derivable *)
Lemma dist_prop : forall z1 z2 : Real,
    (z1 > z2 -> dist z1 z2 = z1 - z2)
    /\ (z1 = z2 -> dist z1 z2 = Real0)
    /\ (z1 < z2 -> dist z1 z2 = z2 - z1).
Proof.
  intros.
  unfold dist.
  unfold abs.
  destruct ( abs_prop (z1 - z2)).
  repeat split.
  intro.
  destruct a as [a _].
  apply a.
  auto with Realiny.
  intro.
  destruct a as [_ [a _]].
  apply a.
  induction H.
  ring.
  destruct a as [_ [_ a]].
  intro.
  replace (z2 -z1) with (- (z1 - z2)) by ring.
  apply a.
  pose proof (Reallt_plus_r_lt (-z2) _ _ H).
  replace (z1 - z2) with (z1 + - z2) by ring.
  replace Real0 with (z2 + - z2) by ring.
  exact H0.
Qed.

   
Global Hint Resolve dist_prop: Realiny.

(* Parameter dist : Real -> Real -> Real. *)
(* Definition abs (z:Real) : Real := dist Real0 z. *)

Lemma Realmetric_inv : forall z1 z2 z3, dist z1 z2 = dist (z1 + z3) (z2 + z3).
Proof.
  intros z1 z2 z3.
  unfold dist.
  replace (z1 + z3 - (z2 + z3)) with (z1 - z2) by ring.
  apply eq_refl.
Qed.

  
Lemma dist_pos : forall z1 z2 : Real, dist z1 z2 >= Real0.
Proof.
  intros.
  destruct (dist_pos_t z1 z2).
  left; auto.
  right; auto.
Qed.

Lemma abs_symm : forall x, abs x = abs (-x).
Proof.
  unfold abs.
  intro.
  destruct (abs_prop x).
  destruct (abs_prop (-x)).
  destruct (Realtotal_order x Real0).
  destruct a as [_ [_ a]].
  destruct a0 as [a0 _ ].
  rewrite (a H).
  apply (Reallt_anti) in H.
  ring_simplify in H.
  apply a0 in H.
  rewrite H.
  apply eq_refl.

  destruct H.
  destruct a as [_ [a _]].
  destruct a0 as [_ [a0 _]].
  rewrite H in a, a0.
  rewrite (a (eq_refl _)).
  assert ( -Real0 = Real0) by ring.
  rewrite (a0 H0).
  apply eq_refl.
  
  destruct a as [a [_ _]].
  destruct a0 as [_ [_ a0]].
  rewrite (a H).
  apply (Reallt_anti) in H.
  ring_simplify in H.
  rewrite (a0 H).
  ring.
Qed.


Lemma abs_zero : forall x, abs x = Real0 <-> x = Real0.
Proof.
  intros.
  
  split.
  intro.
  unfold abs in H.
  destruct (abs_prop x).
  destruct (Realtotal_order x Real0).

  destruct a as [_ [_ a]].
  pose proof (a H0).
  rewrite H1 in H.
  apply (lp _ _ (fun x => - x)) in H.
  ring_simplify in H.
  rewrite H in H0.
  contradict H0; auto with Realiny.
  destruct H0.
  exact H0.
  destruct a as [a [_ _]].
  rewrite (a H0) in H.
  exact H.
  intro.
  unfold abs.
  destruct (abs_prop x).
  destruct a as [_ [a _ ]].
  auto.
Qed.


Lemma abs_tri : forall x y, (abs x) + abs y >= abs (x + y).
Proof.
  intros.
  
  destruct (Realtotal_order x Real0).
  destruct (Realtotal_order y Real0).
  unfold abs.
  destruct (abs_prop x).
  destruct (abs_prop y).
  destruct (abs_prop (x + y)).
  pose proof (Reallt_lt_plus_lt _ _ _  _  H H0).
  ring_simplify in H1.
  destruct a as [_ [_ a]].
  destruct a0 as [_ [_ a0]].
  destruct a1 as [_ [_ a1]].
  rewrite (a H).
  rewrite (a0 H0).
  rewrite (a1 H1).
  right.
  ring.
  destruct H0.
  rewrite H0.
  destruct (abs_zero Real0).
  rewrite (H2 (eq_refl _)).
  ring_simplify.
  replace (x + Real0) with x by ring.
  right; auto.

  unfold abs.
  destruct (abs_prop x).
  destruct (abs_prop y).
  destruct (abs_prop (x + y)).
  destruct a as [_ [_ a]].
  destruct a0 as [a0 [_ _]].
  rewrite (a H),  (a0 H0).

  
  destruct (Realtotal_order (x + y) Real0).
  destruct a1 as [_ [_ a1]]; rewrite (a1 H1).
  apply (Realge_add_r (x + y)   (-x + y) (- (x + y))).
  ring_simplify.
  left.
  apply (Reallt_mult_r_pos_lt _ _ _ (Real2_pos)) in H0.
  ring_simplify in H0.
  exact H0.

  destruct H1.
  destruct a1 as [_ [a1 _]]; rewrite (a1 H1).
  apply (Realge_add_r x).
  ring_simplify.
  left.
  apply (Reallt_lt_lt _ _ _ H H0).

  destruct a1 as [a1 [_ _]]; rewrite (a1 H1).
  apply (Realge_add_r (x-y)).
  ring_simplify.
  apply (Reallt_mult_r_pos_lt _ _ _ (Real2_pos)) in H.
  ring_simplify in H.
  left.
  replace ((Real1 + Real1) *x) with (x * (Real1 + Real1)) by ring.
  exact H.

  destruct H.
  rewrite H.
  destruct (abs_zero Real0).
  rewrite (H1 (eq_refl _)).
  ring_simplify.
  replace (Real0 + y) with y by ring.
  right; auto.


  destruct (Realtotal_order y Real0).
  unfold abs.
  destruct (abs_prop x).
  destruct (abs_prop y).
  destruct (abs_prop (x + y)).
  destruct a as [a [_ _]].
  destruct a0 as [_ [_ a0]].
  rewrite (a H),  (a0 H0).

  
  destruct (Realtotal_order (x + y) Real0).
  destruct a1 as [_ [_ a1]]; rewrite (a1 H1).
  apply (Realge_add_r (x + y)).
  ring_simplify.
  left.
  apply (Reallt_mult_r_pos_lt _ _ _ (Real2_pos)) in H.
  ring_simplify in H.
  exact H.

  destruct H1.
  destruct a1 as [_ [a1 _]]; rewrite (a1 H1).
  rewrite<- H1.
  apply (Realge_add_r ( y - x)).
  ring_simplify.
  apply (Reallt_mult_r_pos_lt _ _ _ (Real2_pos)) in H0.
  ring_simplify in H0.
  left.
  replace ((Real1 + Real1 ) * y) with (y *( Real1 + Real1)) by ring.
  exact H0.

  destruct a1 as [a1 [_ _]]; rewrite (a1 H1).
  apply (Realge_add_r ( y - x)).
  ring_simplify.
  apply (Reallt_mult_r_pos_lt _ _ _ (Real2_pos)) in H0.
  ring_simplify in H0.
 replace ((Real1 + Real1 ) * y) with (y *( Real1 + Real1)) by ring.
  left; exact H0.

  destruct H0.
  rewrite H0.
  destruct (abs_zero Real0).
  rewrite (H2 (eq_refl _)).
  ring_simplify.
  replace (x + Real0) with x by ring.
  right; auto.

  unfold abs.
  destruct (abs_prop x) , (abs_prop y), (abs_prop (x + y)).
  destruct a as [a [_ _]].
  destruct a0 as [a0 [_ _]].
  rewrite (a H),  (a0 H0).

  pose proof (Reallt_lt_plus_lt _ _ _ _ H H0).
  ring_simplify in H1.
  destruct a1 as [a1 _].
  rewrite (a1 H1).
  right; auto.
Qed.

  
  

Lemma dist_symm : forall z1 z2 : Real, dist z1 z2 = dist z2 z1.
Proof.
  intros; unfold dist.
  rewrite (abs_symm (z1 - z2)).
  replace (-(z1 - z2)) with (z2 - z1) by ring.
  apply eq_refl.
Qed.

    
Lemma dist_tri : forall z1 z2 z3, (dist z1 z2) + (dist z2 z3) >= dist z1 z3.
Proof.
  intros.
  unfold dist.
  pose proof (abs_tri (z1 - z2) (z2 - z3)).
  replace (z1 - z3) with (z1 - z2 + (z2 - z3)) by ring.
  exact H.
Qed.


Lemma dist_zero : forall z1 z2 : Real, dist z1 z2 = Real0 <-> z1 = z2.
Proof.
  intros.
  unfold dist.
  pose proof (abs_zero (z1 - z2)).
  split.
  destruct H.
  intro.
  pose proof (H H1).
  apply (lp _ _ (fun x => x + z2)) in H2.
  ring_simplify in H2.
  exact H2.
  intro.
  destruct H.
  apply (lp _ _ (fun x => x - z2)) in H0.
  ring_simplify in H0.
  exact (H1 H0).
Qed.

Global Hint Resolve  dist_pos dist_symm dist_tri dist_zero: Realiny.



Lemma Realmetric_sand : forall z1 z2 z3, z1-z3<=z2<=z1+z3 -> dist z1 z2 <= z3.
Proof.
  intros z1 z2 z3 p.
  


  
(* ddd *)
  destruct p as [p1 p2].
  destruct (dist_prop z1 z2) as [q1 [q2 q3]];
    destruct (Realtotal_order z1 z2) as [r1 | [r2 | r3]].
  rewrite (q3 r1).
  destruct p2.
  apply (Reallt_plus_lt (-z1) z2 (z1+z3)) in H.
  ring_simplify in H.
  replace (-z1+z2) with (z2-z1) in H by ring; left; exact H.
  rewrite H.
  ring_simplify; right; exact eq_refl.

  rewrite (q2 r2); rewrite r2 in p2.
  destruct p2.
  apply (Reallt_plus_lt (-z2) z2 (z2+z3)) in H.
  ring_simplify in H; left; exact H.
  apply (Realeq_plus_eq z2 (z2+z3) (-z2)) in H.
  ring_simplify in H; right; exact H.

  rewrite (q1 r3).
  add_both_side_by p1.
  add_both_side_by.
  replace (z1 - z2 - z3) with (-z2 + z1 - z3) by ring.
  exact p1.
Qed.
Global Hint Resolve Realmetric_sand: Realiny.


Lemma Realmetric_plus_inv : forall z1 z2 z3, dist z1 z2 = dist (z3 + z1) (z3 + z2).
Proof.
  intros z1 z2 z3;
    replace (z3+z1) with (z1+z3) by ring;
    replace (z3+z2) with (z2+z3) by ring; exact (Realmetric_inv z1 z2 z3).
Qed.
Global Hint Resolve Realmetric_plus_inv: Realiny.


Lemma Realmetric_or : forall z1 z2, dist z1 z2 = z1 - z2 \/ dist z1 z2 = z2 - z1.
Proof.
  intros z1 z2.
  destruct (Realtotal_order z1 z2) as [r1 | [r2 | r3]];
    destruct (dist_prop z1 z2) as [l1 [l2 l3]].
  right; rewrite (l3 r1); exact eq_refl.
  rewrite r2 at 2.
  left; ring_simplify.
  exact (l2 r2).
  left; rewrite (l1 r3); exact eq_refl.
Qed.
Global Hint Resolve Realmetric_or: Realiny.

Lemma Realmetric_Or : forall z1 z2, (dist z1 z2 = z1-z2 /\ z1 >= z2) \/
                                (dist z1 z2 = z2-z1 /\ z2 >= z1).
Proof.
  intros z1 z2.
  destruct (Realtotal_order z1 z2) as [r1 | [r2 | r3]];
    destruct (dist_prop z1 z2) as [l1 [l2 l3]].
  right; rewrite (l3 r1); exact (conj eq_refl (Realgt_ge  z2 z1 r1)).
  rewrite r2 at 2.
  left; split; ring_simplify.
  exact (l2 r2).
  right; exact r2.
  left; rewrite (l1 r3); exact (conj eq_refl (Realgt_ge z1 z2 r3)).
Qed.
Global Hint Resolve Realmetric_Or: Realiny.

Lemma Realmetric_gtgt_sand : forall z1 z2 z3, z3> Real0 -> z1-z3<z2<z1+z3 -> dist z1 z2 < z3.
Proof.
  intros z1 z2 z3 q p.
  destruct p as [p1 p2].
  destruct (Realmetric_Or z1 z2) as [[a b] | [a b]]; rewrite a.
  apply (Reallt_plus_lt (z3-z2) (z1-z3) z2) in p1.
  ring_simplify in p1.
  replace (-z2+z1) with (z1-z2) in p1 by ring.
  exact p1.
  apply (Reallt_plus_lt (-z1) z2 (z1+z3)) in p2.
  ring_simplify in p2.
  replace (-z1+z2) with (z2-z1) in p2 by ring.
  exact p2.
Qed.
Global Hint Resolve Realmetric_gtgt_sand: Realiny.


Lemma Realmetric_minus_inv : forall z1 z2 z3, dist z1 z2 = dist (z1 - z3) (z2 - z3).
Proof.
  intros z1 z2 z3;
  pose proof (Realmetric_inv z1 (z2) (-z3)) as H;
  replace (z1-z3) with (z1+-z3) by ring;
  replace (z2-z3) with (z2+-z3) by ring; exact H.    
Qed.
Global Hint Resolve Realmetric_minus_inv: Realiny.


Lemma lt_metric : forall x y, x < y -> dist x y = y - x.
Proof.
  intros x y p.
  destruct (Realmetric_Or x y) as [[P Q] | [P Q]].
  contradict Q; auto with Realiny.
  exact P.
Qed.
Global Hint Resolve lt_metric: Realiny.

Lemma le_metric : forall x y, x <= y -> dist x y = y - x.
Proof.
  intros x y p.
  destruct p.
  apply lt_metric; exact H.
  rewrite H.
  ring_simplify.
  rewrite (dist_zero y y); exact eq_refl.
Qed.
Global Hint Resolve le_metric: Realiny.

Lemma dist_0_1 : dist Real0 Real1 = Real1.
Proof.
  rewrite (lt_metric Real0 Real1 Real1_gt_Real0).
  ring.
Qed.
Global Hint Resolve dist_0_1: Realiny.

Lemma dist_1_0 : dist Real1 Real0 = Real1.
Proof.
  rewrite (dist_symm Real1 Real0).
  exact dist_0_1.
Qed.
Global Hint Resolve dist_1_0: Realiny.




  


Definition convex (x y w1 w2 : Real) : x < y -> w1 > Real0 -> w2 > Real0 -> Real.
Proof.
  intros p p1 p2.
  pose proof (Reallt_lt_plus_lt Real0 w1 Real0 w2 p1 p2).
  rewrite Realplus_unit in H.
  exact ((x*w1+y*w2)/(Realgt_neq (w1+w2) Real0 H)).
Defined.


Lemma convexity : forall x y w1 w2,
    forall (p:x < y) (q:w1 > Real0) (r:w2 > Real0),
      x < convex x y w1 w2 p q r < y.
Proof.
  intros.
  split.
  + unfold convex.
    apply (Reallt_mult_r_pos_lt x y w2 r) in p.
    apply (Reallt_plus_lt  (w1*x) (x*w2) (y*w2)) in p.
    assert (w1+w2 <> Real0) as Path by auto with Realiny.
    rewrite <- (irrl  _ Path (Realgt_neq (w1 + w2) Real0
    (eq_ind (Real0 + Real0) (fun t : Real => t < w1 + w2) (Reallt_lt_plus_lt Real0 w1 Real0 w2 q r) Real0
            (Realplus_unit Real0)))).
    
    apply (Reallt_plus_lt  w2 Real0 w1) in q.
    replace (w2+Real0) with w2 in q by ring.
    replace (w2+w1) with (w1+w2) in q by ring.
    pose proof (Reallt_lt_lt Real0 w2 (w1+w2) r q).
    replace (w1 * x + x * w2) with (x*(w1  + w2)) in p by ring.
    assert (/Path > Real0) by auto with Realiny.
    apply (Reallt_mult_r_pos_lt (x*(w1+w2)) (w1*x+y*w2) (/Path) H0) in p.
    rewrite Realmult_assoc, (Realmult_comm (w1+w2) (/Path)) in p.
    rewrite (Realmult_inv (w1 + w2) Path), Realmult_comm, Realmult_unit in p.
    replace (w1*x) with (x*w1) in p by ring.
    exact p.

  + unfold convex.
    apply (Reallt_mult_r_pos_lt x y w1 q) in p.
    apply (Reallt_plus_lt  (w2*y) (x*w1) (y*w1)) in p.
    assert (w1+w2 <> Real0) as Path by auto with Realiny.
    rewrite <- (irrl _ Path (Realgt_neq (w1 + w2) Real0
    (eq_ind (Real0 + Real0) (fun t : Real => t < w1 + w2) (Reallt_lt_plus_lt Real0 w1 Real0 w2 q r) Real0
            (Realplus_unit Real0)))).


    apply (Reallt_plus_lt  w1 Real0 w2) in r.
    replace (w1+Real0) with w1 in r by ring.
    pose proof (Reallt_lt_lt Real0 w1 (w1+w2) q r).
    replace (w2 * y + y * w1) with (y * (w1  + w2)) in p by ring.
    assert (/Path > Real0) by auto with Realiny.
    apply (Reallt_mult_r_pos_lt  (w2*y+x*w1) (y*(w1+w2)) (/Path) H0) in p.
    rewrite Realmult_assoc in p at 1.
    replace ((w1 + w2) * / Path) with (/Path*(w1+w2)) in p by auto with Realiny.
    rewrite (Realmult_inv (w1 + w2) Path) in p.
    replace (y*Real1) with y in p by ring.
    replace  (w2 * y + x * w1) with (x * w1 + y * w2) in p by ring.
    exact p.
Qed.
    


Lemma dist_le_prop : forall a b c, dist a b <= c <-> - c <= a - b <= c.
Proof.
  intros.
  split.
  intros.
  destruct (dist_prop a b).
  destruct H1.
  destruct (Realtotal_order a b).
  rewrite (H2 H3) in H.
  split; auto.
  apply (Realle_plus_le (a - b - c)) in H; ring_simplify in H; auto.
  apply (fun a => Realle_le_le _ _ _ a H).
  pose proof (Reallt_plus_lt (-a) _ _ H3).
  pose proof (Reallt_plus_lt (-b) _ _ H3).
  ring_simplify in H4; ring_simplify in H5.
  pose proof (Reallt_lt_lt _ _ _ H5 H4).
  replace (a - b) with (-b + a) by ring; replace (b - a) with (- a + b) by ring; left; auto.
  destruct H3.
  induction H3.
  rewrite (H1 (eq_refl)) in H.
  split; ring_simplify.
  apply (Realle_plus_le (-c )) in H.
  ring_simplify in H.
  auto.
  auto.
  rewrite (H0 H3) in H.
  split; auto.
  apply (Reallt_plus_lt (- b)) in H3.
  ring_simplify in H3.
  replace (-b + a) with (a - b) in H3 by ring.
  destruct H.
  pose proof (Reallt_lt_lt _ _ _ H3 H).
  apply (Reallt_plus_lt (-c)) in H4.
  ring_simplify in H4.
  left; apply (Reallt_lt_lt _ _ _ H4 H3).
  rewrite H.
  rewrite H in H3.
  pose proof (Reallt_lt_plus_lt _ _ _ _ H3 H3).
  apply (Reallt_plus_lt (-c)) in H4.
  ring_simplify in H4.
  left; auto.
  intro.
  pose proof (dist_prop a b).
  destruct H0.
  destruct H1.
  destruct (Realtotal_order a b).
  rewrite (H2 H3).
  destruct H.
  apply (Realle_plus_le (c + b - a)) in H.
  ring_simplify in H.
  exact H.
  destruct H3.
  induction H3.
  rewrite (H1 eq_refl).
  destruct H.
  ring_simplify in H3.
  exact H3.
  destruct H.
  rewrite (H0 H3).
  exact H4.
Defined.

  
