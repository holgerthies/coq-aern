Require Import Base.
Require Import Kleene.
Require Import RealAxioms.
Require Import RealRing.
Require Import RealOrder.
Require Import RealOrderTactic.
Require Import RealLimit0.
Require Import RealLimit1.



Require Import Psatz.
Require Import PeanoNat.



Section RealMetric.
  Variable T : ComplArchiSemiDecOrderedField.
  Notation R := (CarrierField T).

  (* Notation real_0__ := (  (let *)
  (*  (real, real_0, real_1, real_plus, real_mult, real_opp, real_inv, real_lt, _, _, _, _, _, *)
  (*   _, _, _, _, _, _, _, _, _, _, _, _) as s *)
  (*   return *)
  (*     (let *)
  (*        (real, real_0, real_1, real_plus, real_mult, real_opp, real_inv, real_lt, _, _, _, *)
  (*         _, _, _, _, _, _, _, _, _, _, _, _, _, _) := s in *)
  (*      real) := let (CarrierField, _, _) := T in CarrierField in *)
  (*                           real_0)). *)
  
  Ltac IZReal_tac t :=
    match t with
    | @real_0 R => constr:(0%Z)
    | @real_1 R => constr:(1%Z)
    | @IZreal R ?u =>
      match isZcst u with
      | true => u
      | _ => constr:(InitialRing.NotConstant)
      end
    | _ => constr:(InitialRing.NotConstant)
    end.

  Add Ring realRing : (realTheory R) (constants [IZReal_tac]).
  
  Notation real_ := (real R).
  Notation real_0_ := (@real_0 R).
  Notation real_1_ := (@real_1 R).
  Notation prec_ := (@prec R).
  Opaque real_0.
  Opaque real_1.


  Definition abs_prop : forall x : real_, {y : real_ | (x > real_0 -> y = x) /\ (x = real_0 -> y = real_0) /\ (x < real_0 -> y = - x)}.
  Proof.
    intros x.

    apply real_mslimit_P_lt_p.
    destruct (real_total_order x real_0).
    exists (- x).
    split.
    repeat split.
    intro p; contradict p; auto with real.
    intro p; induction p; contradict H; auto with real.
    intros.
    destruct H0 as [_ [_ H0]].
    induction (H0 H); apply eq_refl.
    destruct H.
    exists real_0.
    repeat split; auto with real.
    intro p; induction H; contradict p; auto with real.
    intros.
    destruct H0 as [_ [H0 _]].
    induction (H0 H); apply eq_refl.
    exists x.
    repeat split; auto with real.
    intro p; contradict p; auto with real.
    intros.
    destruct H0 as [H0 [_ _]].
    induction (H0 H); apply eq_refl.

    intro.
    pose proof (M_split _ x real_0 (prec (n + 2))).
    assert (prec_ n > real_0);
      auto with real.

    assert (({x > real_0 - prec_ (n + 2)} + {real_0 > x - prec_ (n + 2)}) -> {e : real_ | exists a : real_, ((x > real_0 -> a = x) /\ (x = real_0 -> a = real_0) /\ (x < real_0 -> a = - x)) /\ - prec_ n < e - a < prec_ n}).
    intro order.
    destruct order. 
    exists x.
    destruct (real_total_order x real_0).
    exists (- x).
    repeat split; auto with real.
    intro j; contradict j; auto with real.
    intro j; induction j; contradict H0; auto with real.
    assert (x - - x =  x + x).
    ring.
    rewrite H1.
    replace (real_0 - prec_ (n + 2)) with ( - prec_ (n + 2)) in r by ring.
    assert (x + x > -prec_ (n + 2) + x).
    auto with real.
    
    pose proof (real_lt_plus_r_lt _ x _ _ r).
    exact H2.
    assert (- prec_ (n + 2) + x > - prec_ (n + 2) + - prec_ (n +2 )).
    apply (real_lt_plus_lt).
    exact r.
    assert (x + x > - prec_ (n + 2) + - prec_ (n + 2)).
    apply (real_lt_lt_lt _ _ _ H3 H2).
    assert (- prec_ n < - prec_ (n + 2) + - prec_ (n + 2)).
    apply real_lt_anti_anti.
    replace (  - (- prec_ (n + 2) + - prec_ (n + 2)))
      with (   prec_ (n + 2) + prec_ (n + 2)) by ring.
    replace (- - prec_ n) with (prec_ n) by ring.
    replace (n + 2)%nat with (n + 1 + 1)%nat by lia.
    rewrite prec_twice.
    apply prec_monotone; lia.
    apply (real_lt_lt_lt _ _ _ H5 H4).
    replace (x - - x) with (x + x) by ring.
    pose proof (@real_lt_lt_plus_lt _ _ _ _ _ H0 H0).
    rewrite real_plus_unit in H1.
    pose proof (prec_pos T n).
    apply (real_lt_lt_lt _ _ _ H1 H2).

    exists x.
    repeat split; auto; try intro; try ring.
    contradict H1.
    destruct H0.
    rewrite H0; auto with real.
    auto with real.

    apply real_lt_anti_anti.
    replace (- - prec_ n) with (prec_ n) by ring.
    replace (- (x - x)) with real_0_ by ring.  
    apply prec_pos.
    replace ( (x - x)) with real_0_ by ring.  
    apply prec_pos.

    exists (-x).
    destruct (real_total_order x real_0).
    exists (- x).
    repeat split; try intro; try auto with real; try ring.
    contradict H1; auto with real.
    rewrite H1; ring.
    apply real_lt_anti_anti.
    replace (-(- x - - x)) with real_0_ by ring.
    replace (- - prec_ n) with (prec_ n) by ring.
    apply prec_pos.
    replace (- x - - x) with real_0_ by ring. 
    apply prec_pos.
    
    exists x.
    repeat split; try intro; try auto with real; try ring.
    contradict H1.
    destruct H0; auto with real.
    rewrite H0; auto with real.
    apply real_lt_anti_anti.
    replace (- (- x - x)) with (x + x) by ring.
    replace (- - prec_ n) with (prec_ n) by ring.
    apply (@real_lt_plus_lt _ (prec_ (n + 2))) in r.
    apply (@real_lt_lt_plus_lt _ _ _ _ _ r) in r.
    replace (prec_ (n + 2) + (x - prec_ (n + 2)) + (prec_ (n + 2) + (x - prec_ (n + 2)))) with
        (x + x) in r by ring.
    replace (prec_ (n + 2) + real_0_ + (prec_ (n + 2) + real_0_)) with (prec_ (n + 2) + prec_ (n + 2)) in r by ring.
    apply (@real_lt_lt_lt _ _ _ _ r).
    replace (n + 2)%nat with (n + 1 + 1)%nat by lia.
    rewrite prec_twice.
    apply prec_monotone; lia.
    destruct H0.
    rewrite H0.
    replace (- real_0_ - real_0_) with real_0_ by ring.
    apply prec_pos.
    apply (@real_lt_lt_plus_lt _  _ _ _ _ H0) in H0.
    apply (@real_lt_plus_lt _ (- x - x)) in H0.
    replace ( - x - x + (real_0_ + real_0_)) with (- x - x) in H0 by ring.
    replace (- x - x + (x + x)) with real_0_ in H0 by ring.
    apply (@real_lt_lt_lt _ _ _ _ H0).
    apply prec_pos.

    apply (liftM _ _  H0).
    apply M_split.
    apply prec_pos.
  Defined.


  
  
  Definition abs : real_ -> real_.
  Proof.
    intros x.
    destruct (abs_prop x).
    exact x0.
  Defined.


  Lemma abs_pos : forall x, real_0 <= abs x.
  Proof.
    intros.
    unfold abs.
    destruct (abs_prop x).
    destruct a as [a [b c]].
    destruct (real_total_order x real_0).
    pose proof (c H).
    rewrite H0.
    left.
    apply real_lt_anti_anti.
    ring_simplify.
    exact H.
    destruct H.
    right.
    rewrite (b H); auto.

    left. rewrite( a H); auto.
  Qed.



  Definition dist : real_ -> real_ -> real_ := fun x y => abs (x - y).

  Lemma dist_pos_t : forall x y, real_0 <= dist x y.
  Proof.
    intros.
    unfold dist.
    apply abs_pos.
  Qed.


  Local Hint Resolve abs_pos dist_pos_t: real.


  (* let us have a strong definition of dist then make other obligations derivable *)
  Lemma dist_prop : forall z1 z2 : real_,
      (z1 > z2 -> dist z1 z2 = z1 - z2)
      /\ (z1 = z2 -> dist z1 z2 = real_0)
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
    auto with real.
    intro.
    destruct a as [_ [a _]].
    apply a.
    induction H.
    ring.
    destruct a as [_ [_ a]].
    intro.
    replace (z2 -z1) with (- (z1 - z2)) by ring.
    apply a.
    pose proof (real_lt_plus_r_lt _ (-z2) _ _ H).
    replace (z1 - z2) with (z1 + - z2) by ring.
    replace real_0 with (z2 + - z2) by ring.
    exact H0.
  Qed.

  
  Local Hint Resolve dist_prop: real.

  (* Parameter dist : real_ -> real_ -> real_. *)
  (* Definition abs (z:real_) : real_ := dist real_0 z. *)

  Lemma real_metric_inv : forall z1 z2 z3, dist z1 z2 = dist (z1 + z3) (z2 + z3).
  Proof.
    intros z1 z2 z3.
    unfold dist.
    replace (z1 + z3 - (z2 + z3)) with (z1 - z2) by ring.
    apply eq_refl.
  Qed.

  
  Lemma dist_pos : forall z1 z2 : real_, dist z1 z2 >= real_0.
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
    destruct (real_total_order x real_0).
    destruct a as [_ [_ a]].
    destruct a0 as [a0 _ ].
    rewrite (a H).
    apply (real_lt_anti) in H.
    ring_simplify in H.
    apply a0 in H.
    rewrite H.
    apply eq_refl.

    destruct H.
    destruct a as [_ [a _]].
    destruct a0 as [_ [a0 _]].
    rewrite H in a, a0.
    rewrite (a (eq_refl _)).
    assert ( -real_0_ = real_0) by ring.
    rewrite (a0 H0).
    apply eq_refl.
    
    destruct a as [a [_ _]].
    destruct a0 as [_ [_ a0]].
    rewrite (a H).
    apply (real_lt_anti) in H.
    ring_simplify in H.
    rewrite (a0 H).
    ring.
  Qed.


  Lemma abs_zero : forall x, abs x = real_0 <-> x = real_0.
  Proof.
    intros.
    
    split.
    intro.
    unfold abs in H.
    destruct (abs_prop x).
    destruct (real_total_order x real_0).

    destruct a as [_ [_ a]].
    pose proof (a H0).
    rewrite H1 in H.
    apply (lp _ _ (fun x => - x)) in H.
    ring_simplify in H.
    rewrite H in H0.
    contradict H0; auto with real.
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
    
    destruct (real_total_order x real_0).
    destruct (real_total_order y real_0).
    unfold abs.
    destruct (abs_prop x).
    destruct (abs_prop y).
    destruct (abs_prop (x + y)).
    pose proof (real_lt_lt_plus_lt _ _ _  _  _ H H0).
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
    destruct (abs_zero real_0).
    rewrite (H2 (eq_refl _)).
    ring_simplify.
    replace (x + real_0) with x by ring.
    right; auto.

    unfold abs.
    destruct (abs_prop x).
    destruct (abs_prop y).
    destruct (abs_prop (x + y)).
    destruct a as [_ [_ a]].
    destruct a0 as [a0 [_ _]].
    rewrite (a H),  (a0 H0).

    
    destruct (real_total_order (x + y) real_0).
    destruct a1 as [_ [_ a1]]; rewrite (a1 H1).
    apply (real_ge_add_r _ (x + y)   (-x + y) (- (x + y))).
    ring_simplify.
    left.
    apply (real_lt_mult_r_pos_lt _ _ _ _ (real_2_pos _)) in H0.
    ring_simplify in H0.
    exact H0.

    destruct H1.
    destruct a1 as [_ [a1 _]]; rewrite (a1 H1).
    apply (real_ge_add_r _ x).
    ring_simplify.
    left.
    apply (real_lt_lt_lt _ _ _ H H0).

    destruct a1 as [a1 [_ _]]; rewrite (a1 H1).
    apply (real_ge_add_r _ (x-y)).
    replace (  - x + y + (x - y)) with real_0_ by ring.
    replace (x + y + (x - y)) with (x + x) by ring.
    apply (@real_lt_lt_plus_lt _ _ _ _ _ H) in H.
    left.
    replace (real_0_ + real_0_) with real_0_ in H by ring.
    exact H.

    destruct H.
    rewrite H.
    destruct (abs_zero real_0).
    rewrite (H1 (eq_refl _)).
    ring_simplify.
    replace (real_0 + y) with y by ring.
    right; auto.


    destruct (real_total_order y real_0).
    unfold abs.
    destruct (abs_prop x).
    destruct (abs_prop y).
    destruct (abs_prop (x + y)).
    destruct a as [a [_ _]].
    destruct a0 as [_ [_ a0]].
    rewrite (a H),  (a0 H0).

    
    destruct (real_total_order (x + y) real_0).
    destruct a1 as [_ [_ a1]]; rewrite (a1 H1).
    apply (real_ge_add_r _ (x + y)).
    ring_simplify.
    left.
    apply (real_lt_mult_r_pos_lt _  _ _ _ (real_2_pos _)) in H.
    ring_simplify in H.
    exact H.

    destruct H1.
    destruct a1 as [_ [a1 _]]; rewrite (a1 H1).
    rewrite<- H1.
    apply (real_ge_add_r _ ( y - x)).
    replace ( x + - y + (y - x)) with real_0_ by ring.
    replace (x + y + (y - x)) with (y + y) by ring.
    apply (@real_lt_lt_plus_lt _ _ _ _ _ H0) in H0.
    replace (real_0_ + real_0_) with real_0_ in H0 by ring.
    left; exact H0.
    
    destruct a1 as [a1 [_ _]]; rewrite (a1 H1).
    apply (real_ge_add_r _ ( y - x)).
    replace (x + - y + (y - x)) with real_0_ by ring.
    replace (x + y + (y - x)) with (y + y) by ring.
    apply (@real_lt_lt_plus_lt _ _ _ _ _ H0) in H0.
    replace (real_0_ + real_0_) with real_0_ in H0 by ring.
    left; exact H0.

    destruct H0.
    rewrite H0.
    destruct (abs_zero real_0).
    rewrite (H2 (eq_refl _)).
    ring_simplify.
    replace (x + real_0) with x by ring.
    right; auto.

    unfold abs.
    destruct (abs_prop x) , (abs_prop y), (abs_prop (x + y)).
    destruct a as [a [_ _]].
    destruct a0 as [a0 [_ _]].
    rewrite (a H),  (a0 H0).

    pose proof (real_lt_lt_plus_lt _ _ _ _ _ H H0).
    ring_simplify in H1.
    destruct a1 as [a1 _].
    rewrite (a1 H1).
    right; auto.
  Qed.

  
  

  Lemma dist_symm : forall z1 z2 : real_, dist z1 z2 = dist z2 z1.
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


  Lemma dist_zero : forall z1 z2 : real_, dist z1 z2 = real_0 <-> z1 = z2.
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

  Local Hint Resolve  dist_pos dist_symm dist_tri dist_zero: real.



  Lemma real_metric_sand : forall z1 z2 z3, z1-z3<=z2<=z1+z3 -> dist z1 z2 <= z3.
  Proof.
    intros z1 z2 z3 p.
    


    
    (* ddd *)
    destruct p as [p1 p2].
    destruct (dist_prop z1 z2) as [q1 [q2 q3]];
      destruct (real_total_order z1 z2) as [r1 | [r2 | r3]].
    rewrite (q3 r1).
    destruct p2.
    apply (real_lt_plus_lt (-z1) z2 (z1+z3)) in H.
    ring_simplify in H.
    replace (-z1+z2) with (z2-z1) in H by ring; left; exact H.
    rewrite H.
    ring_simplify; right; exact eq_refl.

    rewrite (q2 r2); rewrite r2 in p2.
    destruct p2.
    apply (real_lt_plus_lt (-z2) z2 (z2+z3)) in H.
    ring_simplify in H; left; exact H.
    apply (real_eq_plus_eq _ z2 (z2+z3) (-z2)) in H.
    ring_simplify in H; right; exact H.

    rewrite (q1 r3).
    add_both_side_by p1.
    add_both_side_by.
    replace (z1 - z2 - z3) with (-z2 + z1 - z3) by ring.
    exact p1.
  Qed.
  Local Hint Resolve real_metric_sand: real.


  Lemma real_metric_plus_inv : forall z1 z2 z3, dist z1 z2 = dist (z3 + z1) (z3 + z2).
  Proof.
    intros z1 z2 z3;
      replace (z3+z1) with (z1+z3) by ring;
      replace (z3+z2) with (z2+z3) by ring; exact (real_metric_inv z1 z2 z3).
  Qed.
  Local Hint Resolve real_metric_plus_inv: real.


  Lemma real_metric_or : forall z1 z2, dist z1 z2 = z1 - z2 \/ dist z1 z2 = z2 - z1.
  Proof.
    intros z1 z2.
    destruct (real_total_order z1 z2) as [r1 | [r2 | r3]];
      destruct (dist_prop z1 z2) as [l1 [l2 l3]].
    right; rewrite (l3 r1); exact eq_refl.
    rewrite r2 at 2.
    left; ring_simplify.
    exact (l2 r2).
    left; rewrite (l1 r3); exact eq_refl.
  Qed.
  Local Hint Resolve real_metric_or: real.

  Lemma real_metric_Or : forall z1 z2, (dist z1 z2 = z1-z2 /\ z1 >= z2) \/
                                       (dist z1 z2 = z2-z1 /\ z2 >= z1).
  Proof.
    intros z1 z2.
    destruct (real_total_order z1 z2) as [r1 | [r2 | r3]];
      destruct (dist_prop z1 z2) as [l1 [l2 l3]].
    right; rewrite (l3 r1); exact (conj eq_refl (real_gt_ge _ z2 z1 r1)).
    rewrite r2 at 2.
    left; split; ring_simplify.
    exact (l2 r2).
    right; exact r2.
    left; rewrite (l1 r3); exact (conj eq_refl (real_gt_ge _ z1 z2 r3)).
  Qed.
  Local Hint Resolve real_metric_Or: real.

  Lemma real_metric_gtgt_sand : forall z1 z2 z3, z3> real_0 -> z1-z3<z2<z1+z3 -> dist z1 z2 < z3.
  Proof.
    intros z1 z2 z3 q p.
    destruct p as [p1 p2].
    destruct (real_metric_Or z1 z2) as [[a b] | [a b]]; rewrite a.
    apply (real_lt_plus_lt (z3-z2) (z1-z3) z2) in p1.
    ring_simplify in p1.
    replace (-z2+z1) with (z1-z2) in p1 by ring.
    exact p1.
    apply (real_lt_plus_lt (-z1) z2 (z1+z3)) in p2.
    ring_simplify in p2.
    replace (-z1+z2) with (z2-z1) in p2 by ring.
    exact p2.
  Qed.
  Local Hint Resolve real_metric_gtgt_sand: real.


  Lemma real_metric_minus_inv : forall z1 z2 z3, dist z1 z2 = dist (z1 - z3) (z2 - z3).
  Proof.
    intros z1 z2 z3;
      pose proof (real_metric_inv z1 (z2) (-z3)) as H;
      replace (z1-z3) with (z1+-z3) by ring;
      replace (z2-z3) with (z2+-z3) by ring; exact H.    
  Qed.
  Local Hint Resolve real_metric_minus_inv: real.


  Lemma lt_metric : forall x y, x < y -> dist x y = y - x.
  Proof.
    intros x y p.
    destruct (real_metric_Or x y) as [[P Q] | [P Q]].
    contradict Q; auto with real.
    exact P.
  Qed.
  Local Hint Resolve lt_metric: real.

  Lemma le_metric : forall x y, x <= y -> dist x y = y - x.
  Proof.
    intros x y p.
    destruct p.
    apply lt_metric; exact H.
    rewrite H.
    ring_simplify.
    rewrite (dist_zero y y); exact eq_refl.
  Qed.

  Lemma dist_0_1 : dist real_0 real_1_ = real_1_.
  Proof.
    rewrite (lt_metric real_0 real_1_ real_1_gt_0).
    ring.
  Qed.

  Lemma dist_1_0 : dist real_1_ real_0 = real_1_.
  Proof.
    rewrite (dist_symm real_1_ real_0).
    exact dist_0_1.
  Qed.

  Definition convex (x y w1 w2 : real_) : x < y -> w1 > real_0 -> w2 > real_0 -> real_.
  Proof.
    intros p p1 p2.
    pose proof (real_lt_lt_plus_lt _ real_0 w1 real_0 w2 p1 p2).
    rewrite real_plus_unit in H.
    exact ((x*w1+y*w2)/(real_gt_neq (w1+w2) real_0 H)).
  Defined.

  Local Hint Resolve lt_metric: real.
  Local Hint Resolve le_metric: real.
  Local Hint Resolve dist_0_1: real.
  Local Hint Resolve dist_1_0: real.



  Lemma convexity : forall x y w1 w2,
      forall (p:x < y) (q:w1 > real_0) (r:w2 > real_0),
        x < convex x y w1 w2 p q r < y.
  Proof.
    intros.
    split.
    + unfold convex.
      apply (real_lt_mult_r_pos_lt _ x y w2 r) in p.
      apply (real_lt_plus_lt  (w1*x) (x*w2) (y*w2)) in p.
      assert (w1+w2 <> real_0) as Path by auto with real.
      rewrite <- (irrl  _ Path (real_gt_neq (w1 + w2) real_0
                                            (eq_ind (real_0 + real_0) (fun t : real_ => t < w1 + w2) (real_lt_lt_plus_lt _ real_0 w1 real_0 w2 q r) real_0
                                                    (real_plus_unit real_0)))).
      
      apply (real_lt_plus_lt  w2 real_0 w1) in q.
      replace (w2+real_0) with w2 in q by ring.
      replace (w2+w1) with (w1+w2) in q by ring.
      pose proof (real_lt_lt_lt real_0 w2 (w1+w2) r q).
      replace (w1 * x + x * w2) with (x*(w1  + w2)) in p by ring.
      assert (/Path > real_0).
      apply real_pos_inv_pos.
      apply H.
      apply (real_lt_mult_r_pos_lt _ (x*(w1+w2)) (w1*x+y*w2) (/Path) H0) in p.
      rewrite real_mult_assoc, (real_mult_comm (w1+w2) (/Path)) in p.
      rewrite (real_mult_inv (w1 + w2) Path), real_mult_comm, real_mult_unit in p.
      replace (w1*x) with (x*w1) in p by ring.
      exact p.

    + unfold convex.
      apply (real_lt_mult_r_pos_lt _ x y w1 q) in p.
      apply (real_lt_plus_lt  (w2*y) (x*w1) (y*w1)) in p.
      assert (w1+w2 <> real_0) as Path by auto with real.
      rewrite <- (irrl _ Path (real_gt_neq (w1 + w2) real_0
                                           (eq_ind (real_0 + real_0) (fun t : real_ => t < w1 + w2) (real_lt_lt_plus_lt _ real_0 w1 real_0 w2 q r) real_0
                                                   (real_plus_unit real_0)))).


      apply (real_lt_plus_lt  w1 real_0 w2) in r.
      replace (w1+real_0) with w1 in r by ring.
      pose proof (real_lt_lt_lt real_0 w1 (w1+w2) q r).
      replace (w2 * y + y * w1) with (y * (w1  + w2)) in p by ring.
      assert (/Path > real_0).
      apply real_pos_inv_pos.
      apply H.
      apply (real_lt_mult_r_pos_lt  _ (w2*y+x*w1) (y*(w1+w2)) (/Path) H0) in p.
      rewrite real_mult_assoc in p at 1.
      replace ((w1 + w2) * / Path) with (/Path*(w1+w2)) in p by auto with real.
      rewrite (real_mult_inv (w1 + w2) Path) in p.
      replace (y*real_1_) with y in p by ring.
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
    destruct (real_total_order a b).
    rewrite (H2 H3) in H.
    split; auto.
    apply (real_le_plus_le _ (a - b - c)) in H; ring_simplify in H; auto.
    apply (fun a => real_le_le_le _ _ _ _ a H).
    pose proof (real_lt_plus_lt (-a) _ _ H3).
    pose proof (real_lt_plus_lt (-b) _ _ H3).
    ring_simplify in H4; ring_simplify in H5.
    pose proof (real_lt_lt_lt _ _ _ H5 H4).
    replace (a - b) with (-b + a) by ring; replace (b - a) with (- a + b) by ring; left; auto.
    destruct H3.
    induction H3.
    rewrite (H1 (eq_refl)) in H.
    split; ring_simplify.
    apply (real_le_plus_le _ (-c )) in H.
    ring_simplify in H.
    auto.
    auto.
    rewrite (H0 H3) in H.
    split; auto.
    apply (real_lt_plus_lt (- b)) in H3.
    replace (-b + b) with real_0_ in H3 by ring.
    
    replace (-b + a) with (a - b) in H3 by ring.
    destruct H.
    pose proof (real_lt_lt_lt _ _ _ H3 H).
    apply (real_lt_plus_lt (-c)) in H4.
    replace (- c + real_0_) with (-c) in H4 by ring.
    replace (-c + c) with real_0_ in H4 by ring.
    left; apply (@real_lt_lt_lt _  _ _ _ H4 H3).
    rewrite H.
    rewrite H in H3.
    pose proof (real_lt_lt_plus_lt _ _ _ _ _ H3 H3).
    apply (real_lt_plus_lt (-c)) in H4.
    ring_simplify in H4.
    left; auto.
    intro.
    pose proof (dist_prop a b).
    destruct H0.
    destruct H1.
    destruct (real_total_order a b).
    rewrite (H2 H3).
    destruct H.
    apply (real_le_plus_le _ (c + b - a)) in H.
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
End RealMetric.

  

Global Hint Resolve abs_pos dist_pos_t: real.
Global Hint Resolve dist_prop: real.
Global Hint Resolve  dist_pos dist_symm dist_tri dist_zero: real.
Global Hint Resolve real_metric_sand: real.
Global Hint Resolve real_metric_plus_inv: real.
Global Hint Resolve real_metric_or: real.
Global Hint Resolve real_metric_Or: real.
Global Hint Resolve real_metric_gtgt_sand: real.
Global Hint Resolve real_metric_minus_inv: real.
Global Hint Resolve lt_metric: real.
Global Hint Resolve le_metric: real.
Global Hint Resolve dist_0_1: real.
Global Hint Resolve dist_1_0: real.

