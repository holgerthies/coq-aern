Require Import Base.
Require Import Kleene.
Require Import RealAxioms.
Require Import RealRing.

Open Scope Real_scope.

Section RealOrder.
  Variable T : ComplArchiSemiDecOrderedField.
  Definition R := CarrierField T.
  
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

  
  Lemma real_ge_triv : forall z : real R, z >= z.
  Proof.
    intro z;  right; exact eq_refl.
  Qed.
  Local Hint Resolve real_ge_triv: real.

  Lemma real_le_triv : forall z : real R, z <= z.
  Proof.
    intro z; right; exact eq_refl.
  Qed.
  Local Hint Resolve real_le_triv: real.

  Lemma real_lt_le : forall z1 z2 : real R, z1<z2 -> z1 <= z2.
  Proof.
    intros z1 z2 p; left; exact p.
  Qed.
  Local Hint Resolve real_lt_le: real.

  Lemma real_gt_ge : forall z1 z2 : real R, z1>z2 -> z1 >= z2.
  Proof.
    intros z1 z2 p; left; exact p.
  Qed.
  Local Hint Resolve real_gt_ge: real.

  Lemma real_eq_le : forall z1 z2 : real R, z1 = z2 -> z1 <= z2.
  Proof.
    intros z1 z2 p; rewrite p; right; exact eq_refl.
  Qed.
  Local Hint Resolve real_eq_le: real.

  Lemma real_eq_ge : forall z1 z2 : real R, z1 = z2 -> z1 >= z2.
  Proof.
    intros z1 z2 p; rewrite p; right; exact eq_refl.
  Qed.
  Local Hint Resolve real_eq_ge: real.

  Lemma real_le_plus_le : forall z x y : real R, x <= y -> z + x <= z + y.
  Proof.
    intros.
    destruct H.
    left.
    apply real_lt_plus_lt.
    exact H.
    right.
    apply (lp _ _ (fun x => z + x)) in H.
    exact H.
  Qed.


  Lemma real_ge_plus_ge : forall z x y : real R, x >= y -> z + x >= z + y.
  Proof.
    intros.
    destruct H.
    left.
    apply real_lt_plus_lt.
    exact H.
    right.
    apply (lp _ _ (fun x => z + x)) in H.
    exact H.
  Qed.

  Lemma real_eq_plus_eq : forall z1 z2 z3 : real R, z1 = z2 -> z1 + z3 = z2 + z3.
  Proof.
    intros z1 z2 z3 p.
    rewrite p.
    exact eq_refl.
  Qed.
  Local Hint Resolve real_eq_plus_eq: real.

  Lemma real_ge_le : forall z1 z2 : real R, z1 >= z2 -> z2 <= z1.
  Proof.
    intros z1 z2 p.
    destruct p.
    left; auto.
    right; rewrite H; exact eq_refl.
  Qed.
  Local Hint Resolve real_ge_le: real.

  Lemma real_le_ge : forall z1 z2 : real R, z1 <= z2 -> z2 >= z1.
  Proof.
    intros z1 z2 p.
    destruct p.
    left; auto.
    right; rewrite H; exact eq_refl.
  Qed.
  Local Hint Resolve real_le_ge: real.
 
  Lemma real_nle_ge : forall z1 z2 : real R, ~ z1 <= z2 -> z1 > z2.
  Proof.
    intros z1 z2 q.
    intuition.
    destruct (real_total_order z1 z2).
    assert (z1 <= z2).
    left; exact H.
    contradict (q H0).
    destruct H.
    assert (z1 <= z2).
    right; exact H.
    contradict (q H0).
    exact H.
  Qed.
  Local Hint Resolve real_nle_ge: real.

  Lemma real_nge_le : forall z1 z2 : real R, ~ z1 < z2 -> z1 >= z2.
  Proof.
    intros z1 z2 q.
    intuition.
    destruct (real_total_order z1 z2).
    contradict (q H).
    unfold ge.
    apply or_comm.
    auto.
  Qed.
  Local Hint Resolve real_nge_le: real.

  Lemma real_div_distr : forall z1 z2 z3 : real R, forall p : z3<>real_0,  z1/p + z2/p = (z1+z2)/p.
  Proof.
    intros z1 z2 z3 nz.
    replace ((z1+z2)/nz) with ((z1+z2)*/nz) by auto.
    rewrite real_mult_comm, real_mult_plus_distr.
    unfold real_div.
    ring.
  Qed.
Local Hint Resolve real_div_distr: real.

(* Check le_plus_le. *)

(* Lemma le_plus_le : forall z1 z2 z3, z1 <= z2 -> z1+z3 <= z2+z3. *)
(* Proof. *)
(*   intros z1 z2 z3 p. *)
(*   destruct p. *)
(*   apply (lt_plus_lt z3 z1 z2) in H. *)
(*   replace (z1+z3) with (z3+z1) by ring; *)
(*     replace (z2+z3) with (z3+z2) by ring; left; exact H. *)
(*   rewrite H; right; auto with real. *)
(* Qed. *)
(* Local Hint Resolve le_plus_le: real. *)

  
Lemma real_nlt_triv : forall x : real R, ~ x < x.
Proof.
  intro x.
  intuition.
  pose proof (real_lt_nlt x x H) as H1.
  contradict H.
  intuition.
Qed.
Local Hint Resolve real_nlt_triv: real.



Lemma real_2_gt_1 : @real_2 R  > real_1.
Proof.
  pose proof (@real_1_gt_0 R).
  pose proof (real_lt_plus_lt real_1 real_0 real_1 H).
  ring_simplify in H0.
  exact H0.
Qed.
Local Hint Resolve real_2_gt_1: real.




Lemma real_lt_neq : forall z1 z2 : real R, z1 < z2 -> z1 <> z2.
Proof.
  red.
  intros z1 z2 p q.
  apply (real_nlt_triv z1).
  pattern z1 at 2; rewrite q; trivial.
Qed.
Local Hint Resolve real_lt_neq: real.

Definition d2 := @real_2_neq_0 R.
Lemma real_minus_half : forall z : real R, z - z/d2 = z/d2.
Proof.
  intro z.
  pose proof (@real_2_neq_0 R).
  assert (z = z * real_2 / d2).
  replace (z*real_2/d2) with (z*real_2*/d2) by auto.
  replace (z*real_2*/d2) with (z * (real_2 * /d2)) by ring.
  replace (z * (real_2 * /d2)) with (z * (/d2 * real_2)) by ring.
  rewrite (real_mult_inv real_2 d2).
  ring.
  rewrite H0 at 1.
  replace ( z * real_2 / d2 - z / d2) with ( z * real_2 */ d2 - z */ d2) by auto.
  replace (( z * real_2 */ d2 - z */ d2)) with ( z * real_2 */ d2 + (- z) */ d2) by ring.
  replace (z/d2) with (z*/d2) by auto.
  replace ( z * real_2 * / d2 + - z * / d2) with ( /d2 * (z * real_2)  + - z * / d2) by ring.
  replace ( / d2 * (z * real_2) + - z * / d2) with ( / d2 * (z * real_2) + /d2 * (-z)) by ring.
  rewrite <- (real_mult_plus_distr (/d2) (z*real_2) (-z)).
  replace (z*real_2 +-z) with (z*(real_1+real_1) -z) by auto.
  replace (z*(real_1+real_1) -z) with z by ring.
  ring.
Qed.
Local Hint Resolve real_minus_half: real.
  
Lemma real_gt_nle: forall z1 z2 : real R, z1 > z2 -> ~ z1 <= z2.
Proof.
  intros z1 z2 p q; destruct q as [q1 | q2].
  contradict p; exact (real_lt_nlt z1 z2 q1).
  rewrite q2 in p; contradict p.
  apply real_nlt_triv.
Qed.
Local Hint Resolve real_gt_nle: real.

Lemma real_gt_ngt : forall z1 z2 : real R, z1 > z2 -> ~ z2 > z1.
Proof.
  intros z1 z2 p.
  contradict p; exact (real_lt_nlt z1 z2 p).
Qed.
Local Hint Resolve real_gt_ngt: real.

Lemma real_gt_nge : forall z1 z2 : real R, z1 > z2 -> ~ z2 >= z1.
Proof.
  intros z1 z2 p q; destruct q as [q1 | q2].
  contradict p; exact (real_lt_nlt z1 z2 q1).
  rewrite q2 in p; contradict p; apply real_nlt_triv.
Qed.
Local Hint Resolve real_gt_nge: real.

Lemma real_ge_ge_eq : forall z1 z2 : real R, z1 >= z2 -> z2 >= z1 -> z1 = z2.
Proof.
  intros z1 z2 o1 o2.
  destruct o1.
  contradict o2.
  auto with real.
  exact H.
Qed.

Lemma real_le_le_eq : forall z1 z2 : real R, z1 <= z2 -> z2 <= z1 -> z1 = z2.
Proof.
  intros z1 z2 o1 o2.
  destruct o1.
  contradict o2.
  auto with real.
  exact H.
Qed.

Lemma real_le_ge_eq : forall z1 z2 : real R, z1 <= z2 -> z1 >= z2 -> z1 = z2.
Proof.
  intros z1 z2 o1 o2.
  destruct o1.
  contradict o2.
  auto with real.
  exact H.
Qed.

Lemma real_ge_le_eq : forall z1 z2 : real R, z1 >= z2 -> z1 <= z2 -> z1 = z2.
Proof.
  intros z1 z2 o1 o2.
  destruct o1.
  contradict o2.
  auto with real.
  exact H.
Qed.
Local Hint Resolve real_ge_ge_eq real_ge_le_eq real_le_ge_eq real_le_le_eq: real.


Lemma real_le_lt_lt : forall z1 z2 z3 : real R, z1<=z2 -> z2 < z3 -> z1<z3.
Proof.
  intros z1 z2 z3 p1 p2.
  destruct (real_total_order z1 z2) as [q1 |[q2| q3]].
  apply (real_lt_lt_lt z1 z2 z3); auto with real.
  rewrite q2; exact p2.
  destruct p1.
  contradict q3; apply (real_lt_nlt); exact H.
  rewrite H in q3; contradict q3; apply real_nlt_triv. 
Qed.
Local Hint Resolve real_le_lt_lt: real.

Lemma real_lt_le_lt : forall z1 z2 z3 : real R, z1 < z2 -> z2 <= z3 -> z1 < z3.
Proof.
  intros z1 z2 z3 p1 p2.
  destruct p2 as [q1| q2].
  exact (real_lt_lt_lt z1 z2 z3 p1 q1).
  rewrite<- q2; exact p1.
Qed.
Local Hint Resolve real_lt_le_lt: real.

Lemma real_le_le_le : forall z1 z2 z3 : real R, z1 <= z2 -> z2 <= z3 -> z1 <= z3.
Proof.
  intros z1 z2 z3 p1 p2.
  destruct p1 as [p11 | p12]; destruct p2 as [p21 | p22]; auto with real.
  left; exact (real_lt_lt_lt z1 z2 z3 p11 p21).
  rewrite p22 in p11; left; exact p11.
  rewrite p12; left; exact p21.
  rewrite p12; rewrite <- p22; right; exact eq_refl.
Qed.
Local Hint Resolve real_le_le_le: real.

Lemma real_lt_plus_r_lt : forall r r1 r2 : real R, r1 < r2 -> r1 + r < r2 + r.
Proof.
  intros r r1 r2 p;
    replace (r1+r) with (r+r1) by ring;
    replace (r2+r) with (r+r2) by ring;
   exact (real_lt_plus_lt r r1 r2 p).
Qed.
Local Hint Resolve real_lt_plus_lt: real.


Lemma real_2_pos : @real_2 R > real_0.
Proof.
  pose proof (@real_1_gt_0 R).
  pose proof (real_lt_plus_r_lt real_1 real_0 real_1 H).
  replace (real_0+real_1) with (@real_1 R) in H0 by ring.
  pose proof (real_lt_lt_lt real_0 real_1 (real_1 + real_1) H H0).
  auto.
Qed.
Local Hint Resolve real_2_pos: real.

Lemma real_eq_eq_mult_eq : forall a b c d : real R, a = b -> c = d -> a*c = b*d.
Proof.
  intros.
  rewrite H; rewrite H0; exact eq_refl.
Qed.
Local Hint Resolve real_eq_eq_mult_eq: real.

Lemma real_half_gt_zero : forall a : real R, a > real_0 -> a / d2 > real_0. 
Proof.
  intros a p.
  pose proof (real_2_pos ).
  destruct (real_total_order (a/d2) real_0) as [p1 |[p2|p3]].
  apply (real_lt_mult_pos_lt real_2 (a/d2) real_0) in p1.
  replace (real_2*(a/d2)) with (real_2*(a*/d2)) in p1 by auto.
  replace (real_2*(a*/d2)) with (a *(/d2 * real_2)) in p1 by ring.
  rewrite (real_mult_inv real_2 d2) in p1.
  ring_simplify in p1.
  contradict p1.
  apply real_lt_nlt, p.
  exact real_2_pos.
  rewrite p2.
  pose proof (real_eq_eq_mult_eq (a/d2) real_0 real_2 real_2 p2 eq_refl).
  replace (a/d2*real_2) with (a*/d2*real_2) in H0 by auto.
  replace (a*/d2*real_2) with (a*(/d2*real_2)) in H0 by ring.
  rewrite (real_mult_inv real_2 d2) in H0.
  ring_simplify in H0.
  rewrite H0 in p.
  contradict p; apply real_nlt_triv. 
  exact p3.
Qed.
Local Hint Resolve real_half_gt_zero: real.


Lemma real_gt_half : forall a : real R, a > real_0 -> a > a / d2.
Proof.
  intros a p.
  pose proof (real_half_gt_zero a p).
  apply (real_lt_plus_lt (a/d2) real_0 (a/d2)) in H.
  rewrite (real_div_distr a a real_2 d2) in H.
  ring_simplify in H.
  replace (a + a) with (real_1 * a + real_1 * a) in H by ring.
  replace (real_1 * a + real_1 * a) with ((real_1+real_1)*a) in H by ring.
  replace (real_1+real_1) with (@real_2 R) in H by auto.
  replace (real_2*a/d2) with (real_2*a*/d2) in H by auto.
  replace (real_2*a*/d2) with (a*(/d2*real_2)) in H by ring.
  rewrite (real_mult_inv real_2 d2) in H.
  ring_simplify in H.
  exact H.
Qed.
Local Hint Resolve real_gt_half: real.
  
Lemma real_gt_minus_gt_zero : forall a b  : real R , a > b -> a - b > real_0.
Proof.
  intros a b p.
  replace (a-b) with (-b+a) by ring.
  replace real_0 with (-b+b) by ring.
  apply real_lt_plus_lt; auto with real.
Qed.
Local Hint Resolve real_gt_minus_gt_zero: real.


Lemma real_lt_lt_plus_lt : forall r1 r2 r3 r4 : real R, r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros r1 r2 r3 r4 p1 p2.
  pose proof (real_lt_plus_r_lt r3 r1 r2 p1).
  assert (r2+r3 < r2+r4).
  auto with real.
  exact (real_lt_lt_lt (r1+r3) (r2+r3) (r2+r4) H H0).
Qed.
Local Hint Resolve real_lt_lt_plus_lt: real. 

Definition padding : forall a b  : real R , a > b -> {ε  | ε > real_0 /\ a = ε + b}.
Proof.
  intros a b p; exists (a - b).
  constructor 1; auto with real; ring.
Defined.
Local Hint Resolve padding: real.


Lemma real_lt_anti : forall z1 z2 : real R, z1<z2 -> -z2< -z1.
Proof.
  intros z1 z2 p.
  apply (real_lt_plus_lt (-z1-z2) z1 z2) in p.
  ring_simplify in p; exact p.
Qed.
Local Hint Resolve real_lt_anti: real.

Lemma real_lt_anti_anti : forall z1 z2 : real R, - z1 < - z2 -> z2< z1.
Proof.
  intros z1 z2 p.
  replace z2 with (- - z2) by ring.
  replace z1 with (- - z1) by ring.
  apply real_lt_anti.
  exact p.
Qed.
Local Hint Resolve real_lt_anti_anti: real.





Lemma real_lt_add_r : forall z x y : real R, x + z < y + z -> x < y.
Proof.
  intros.
  pose proof (real_lt_plus_lt (-z) _ _ H).
  ring_simplify in H0.
  exact H0.
Qed.

Lemma real_gt_add_r : forall z x y : real R, x + z > y + z -> x > y.
Proof.
  intros.
  pose proof (real_lt_plus_lt (-z) _ _ H).
  ring_simplify in H0.
  exact H0.
Qed.

Lemma real_le_add_r : forall z x y : real R, x + z <= y + z -> x <= y.
Proof.
  intros.
  destruct H.
  left.
  exact (real_lt_add_r z x y H).
  right.
  pose proof (lp _ _ (fun k => k - z) _ _ H).
  simpl in H0.
  ring_simplify in H0.
  exact H0.
Qed.

Lemma real_ge_add_r : forall z x y : real R, x + z >= y + z -> x >= y.
Proof.
  intros.
  destruct H.
  left.
  exact (real_gt_add_r z x y H).
  right.
  pose proof (lp _ _ (fun k => k - z) _ _ H).
  simpl in H0.
  ring_simplify in H0.
  exact H0.
Qed. 

Definition d1 := @real_1_neq_0 R.
Lemma real_inv_unit : forall z : real R, z / d1 = z.
Proof.
  intro.
  replace z with (z*real_1) by ring.
  replace (z*real_1/d1) with (z*real_1*/d1) by auto.
  replace (z*real_1*/d1) with (z*(/d1*real_1)) by ring.
  replace (/d1*real_1) with (@real_1 R).
  exact eq_refl.
  apply eq_sym, real_mult_inv.
Qed.
Local Hint Resolve real_inv_unit: real.


Lemma square_pos : forall z : real R, z <> real_0 -> z *z > real_0.
Proof.
  intros.
  destruct (real_total_order z real_0) as [a|[b|c]].
  assert (z+(-z) < real_0+(-z)).
  apply (real_lt_plus_r_lt); exact a.
  ring_simplify in H0.
  pose proof (real_lt_mult_pos_lt (-z) real_0 (-z) H0 H0).
  ring_simplify in H1.
  ring_simplify.
  exact H1.
  contradict H; exact b.
  pose proof (real_lt_mult_pos_lt z real_0 z c c) as q; ring_simplify in q; ring_simplify; exact q.
Qed.

Lemma neq_sym : forall A (a b : A), a <> b -> b <> a.
Proof.
  intros.
  intro.
  rewrite H0 in H.
  apply H, eq_refl.
Defined.

  
Lemma real_pos_inv_pos2 : forall z : real R, forall p :  z > real_0, / (real_gt_neq z real_0 p) > real_0.
Proof.
  intros z p.
  pose proof (square_pos (/ (real_gt_neq z real_0 p))).
  assert (/(real_gt_neq z real_0 p) <> real_0) as H10.
  intro.
  pose proof (real_mult_inv z).
  assert (z <> real_0) as H12 by  (intro j; clear H H0; rewrite j in p; contradict p; apply real_nlt_triv; auto with real).
  pose proof (H1  H12) as H2.
  assert (path : H12 = (real_gt_neq z real_0 p)) by apply irrl.
  rewrite path in H2.
  rewrite H0 in H2; ring_simplify in H2; contradict H2; apply neq_sym, (@real_1_neq_0 R).
  pose proof (H H10) as H0.
  pose proof (real_lt_mult_pos_lt (/(real_gt_neq z real_0 p)*/(real_gt_neq z real_0 p)) real_0 z H0 p).
  replace (/(real_gt_neq z real_0 p)*/(real_gt_neq z real_0 p)*z) with (/(real_gt_neq z real_0 p)*(/(real_gt_neq z real_0 p)*z))  in H1 by ring.

  replace (/(real_gt_neq z real_0 p) *z) with (@real_1 R) in H1.
    
  ring_simplify in H1.
  exact H1.
  rewrite (real_mult_inv); auto.
Qed.
Local Hint Resolve real_pos_inv_pos2:real.

Lemma real_pos_inv_pos : forall z : real R, forall p : z > real_0, forall q : z <> real_0, / q > real_0.
Proof.
  intros.
  rewrite (irrl _ q (real_gt_neq z real_0 p)); auto with real.
Qed.
Local Hint Resolve real_pos_inv_pos : real.

Lemma real_lt_mult_r_pos_lt : forall z1 z2 z3 : real R, z3 > real_0 -> z1 < z2 -> z1 * z3 < z2 * z3.
Proof.
  intros.
  replace (z1*z3) with (z3*z1) by ring.
  replace (z2*z3) with (z3*z2) by ring.
  apply real_lt_mult_pos_lt; auto.
  Qed.
Local Hint Resolve real_lt_mult_r_pos_lt: real.


Lemma prec_S : forall n, @prec R (S n) < prec n.
Proof.
  intro n.
  induction n; simpl.
  replace (real_1+real_1) with (@real_2 R) by auto.
  exact (real_gt_half real_1 real_1_gt_0).
  simpl in IHn.
  replace (real_1+real_1) with (@real_2 R) by auto.
  replace (real_1+real_1) with (@real_2 R) in IHn by auto.
  pose proof (real_2_pos).
  assert (/d2 > real_0) by auto with real.
  apply (real_lt_mult_r_pos_lt (prec n / d2) (prec n)  (/d2) H0) in IHn.
  exact IHn.
Qed.
Local Hint Resolve prec_S: real.

Lemma prec_hom : forall n m, @prec R (n+m) = prec n * prec m.
Proof.
  intros n m.
  induction n.
  simpl. simpl.
  unfold prec.
  
  ring.
  rewrite (plus_Sn_m n m).
  simpl.
  rewrite IHn.
  unfold real_div.
  ring.
Qed.      
Local Hint Resolve prec_hom: real.

Definition dg0 {z : real R}(p:z>real_0) : z <> real_0 :=  real_gt_neq z real_0 p.
Lemma real_lt_mult_pos_move_rr : forall a b c : real R, forall p :a > real_0, b*a < c -> b < c / (dg0 p).
Proof.
  intros a b c p q.
  assert (/ (dg0 p) > real_0) by auto with real.
  apply (real_lt_mult_r_pos_lt (b*a)  c (/(dg0 p)) H) in q.
  replace (b*a*/(dg0 p)) with (b*(/(dg0 p)*a)) in q by ring.
  assert (a <> real_0).
  intro e; clear q H; rewrite e in p; apply (real_nlt_triv _ p).
  replace (/(dg0 p)*a) with (@real_1 R) in q.
  replace (b * real_1) with b in q by ring; exact q.
  rewrite (real_mult_inv); auto.
Qed.
Local Hint Resolve real_lt_mult_pos_move_rr: real.

Lemma real_lt_mult_pos_move_rl : forall a b c : real R, forall p :a > real_0, a*b < c -> b < c / (dg0 p).
Proof.
  intros a b c p q.
  replace (a*b) with (b*a) in q by ring.
  apply real_lt_mult_pos_move_rr; auto. 
Qed.
Local Hint Resolve real_lt_mult_pos_move_rl: real.

Lemma real_gt_mult_pos_move_rl : forall a b c : real R, forall p:a > real_0,  a*b > c -> b > c / (dg0 p).
  intros a b c p q.
  assert (/ (dg0 p) > real_0) by auto with real.
  replace (a*b) with (b*a) in q by ring.
  apply (real_lt_mult_r_pos_lt c (b*a) (/ (dg0 p)) H) in q.
  replace (b*a*/(dg0 p)) with (b*(/(dg0 p)*a)) in q by ring.
  assert (a <> real_0).
  intro e; clear q H; rewrite e in p; apply (real_nlt_triv _ p).
  replace (/(dg0 p)*a) with (@real_1 R) in q. 
  ring_simplify in q.
  auto with real.
  rewrite (real_mult_inv); auto.
Qed.
Local Hint Resolve real_gt_mult_pos_move_rl: real.

Lemma real_lt_mult_pos_move_rr_n
  : forall (a b c : real R) (p : a > real_0) (q : a <> real_0), b * a < c -> b < c / q.
Proof.
  intros.
  pose proof (irrl _ q (real_gt_neq a real_0 p)).
  rewrite H0.
  apply real_lt_mult_pos_move_rr; exact H.
Qed.
Local Hint Resolve real_lt_mult_pos_move_rr_n: real.



(** prec embedding is always positive **)
Lemma prec_pos : forall n, @prec R n > real_0.
Proof.
  intro.
  induction n.
  simpl; apply real_1_gt_0.
  simpl.
  replace (real_1+real_1) with (@real_2 R) by auto.
  auto with real.
Defined.
Local Hint Resolve prec_pos: real.


Lemma Nreal_hom : forall n m, @Nreal R (n+m) = Nreal n + Nreal m.
Proof.
  intros n m.
  induction n.
  simpl.
  rewrite real_plus_unit; auto.
  assert (S n + m = S (n+m))%nat as H by intuition.
  rewrite H.
  assert (forall n, @Nreal R (S n) = real_1 + Nreal n) by (intro; simpl; exact eq_refl).
  rewrite (H0 n). rewrite (H0 ((n+m)%nat)).
  rewrite IHn; ring.
Qed.
Local Hint Resolve Nreal_hom: real.

Lemma prec_twice : forall n, @prec R (n + 1) + prec (n + 1) = prec n.
Proof.
  intros.
  rewrite (prec_hom n 1).
  rewrite <- real_mult_plus_distr.
  simpl.
  unfold real_div.
  rewrite (real_mult_comm (real_1)).
  rewrite <- real_mult_plus_distr.
  rewrite real_mult_inv, real_mult_comm, real_mult_unit.
  auto.
Qed.

Lemma Nreal_pos : forall n, (n>0)%nat -> @Nreal R n > real_0.
Proof.
  intros n p.
  induction n.
  contradict p; exact (gt_irrefl 0).
  assert (S n = 1+n)%nat as q; intuition.
  rewrite q.
  rewrite (Nreal_hom 1%nat n).
  pose proof (@real_1_gt_0 R) as gtg.
  destruct n.
  simpl; ring_simplify; auto with real.

  pose proof (IHn (gt_Sn_O n)).
  pose proof (real_lt_lt_plus_lt real_0 real_1 real_0 (Nreal (S n)) gtg H) as H1; ring_simplify in H1.
  replace (Nreal (S n) + real_1) with (@real_1 R + Nreal (S n)) in H1 by ring.
  assert (@Nreal R 1 = real_1). simpl. ring.
  rewrite H0; exact H1.
Qed.
Local Hint Resolve Nreal_pos: real.


Lemma Nreal_S : forall n, @Nreal R (S n) = real_1 + Nreal n.
Proof.
  intro n.
  replace (S n)%nat with (1 + n)%nat by intuition.
  rewrite (Nreal_hom 1%nat n); simpl; ring.
Qed.

Lemma Nreal_mult : forall n m, @Nreal R (n * m) = Nreal n * Nreal m.
Proof.
  intros n m.
  induction n.
  simpl; ring.
  simpl.
  rewrite Nreal_hom .
  rewrite IHn.
  ring.
Qed.


Lemma IZ_asym : forall n, @IZreal R (-n) = - IZreal n.
Proof.
  intro n.
  unfold IZreal.
  unfold IPreal.
  unfold IPreal_2.  
  destruct n; simpl; ring.
Qed.
Require Import Coq.PArith.BinPos.
Lemma IZreal_s1 : forall p, @IZreal R (Z.pos (p~0)) = real_2 * (IZreal (Z.pos p)).
Proof.
  intro.
  unfold IZreal.
  simpl.
  unfold IPreal.
  
  unfold IPreal_2.

  destruct p;
  replace (real_1+real_1) with (@real_2 R) by auto; ring_simplify;
    exact eq_refl.
Qed.

Lemma IZreal_s2 : forall p, @IZreal R (Z.pos (p~1)) = real_2 * (IZreal (Z.pos p)) + real_1.
Proof.
  intro.
  unfold IZreal.
  unfold IPreal.  
  unfold IPreal_2.
  destruct p;
  replace (real_1+real_1) with (@real_2 R) by auto; ring_simplify; exact eq_refl.
Qed.

Lemma IP2_Nreal : forall p, real_2 * @Nreal R (Pos.to_nat p) = IPreal_2 p.
Proof.
  intro p.
  induction p.
  + rewrite Pos2Nat.inj_xI.
    rewrite Nreal_S.
    ring_simplify.
    rewrite Nreal_mult.
    ring_simplify.
    replace (real_2* Nreal 2 * Nreal (Pos.to_nat p)) with (@Nreal R 2 * (real_2 * Nreal (Pos.to_nat p))) by ring.
    rewrite IHp.
    simpl.
    unfold real_2.
    unfold IZreal.
    unfold IPreal.
    simpl.
    ring.
  + rewrite Pos2Nat.inj_xO.
    rewrite Nreal_mult.
    simpl .
    replace ((real_1+real_1)*real_2*@Nreal R (Pos.to_nat p)) with ((real_1+@real_1 R) *(real_2 * @Nreal R (Pos.to_nat p))) by ring.
    replace (real_2 * ((real_1 + (real_1 + real_0)) * Nreal (Pos.to_nat p))) with
        ((((@real_1 R + (real_1 + real_0))) * (real_2 * Nreal (Pos.to_nat p)))) by ring.
    rewrite IHp.
    ring.
  + simpl; ring_simplify; auto.
Qed.

Lemma IP_N : forall p, N (Pos.to_nat p) = IP p.
Proof.
  intro p.
  induction p.

  + unfold IP.
    rewrite <- IP2_N.
    rewrite Pos2Nat.inj_xI.
    rewrite N_S, N_mult.
    simpl N; ring_simplify.
    replace (1+1) with 2 by auto.
    ring.

  + unfold IP.
    rewrite <- IP2_N.
    rewrite Pos2Nat.inj_xO.
    rewrite  N_mult.
    simpl N; ring_simplify.
    replace (1+1) with 2 by auto.
    ring.

  + simpl; ring_simplify; auto.
Qed.

Lemma IZ_N : forall p, N (Pos.to_nat p) = IZ (Z.pos p).
Proof.
  intro p.
  rewrite IP_N.
  unfold IZ; exact eq_refl.
Qed.

Lemma IZ_pos_pos : forall p1 p2, IZ (Z.pos p1 + Z.pos p2) = IZ (Z.pos p1) + IZ (Z.pos p2).
Proof.
  intros p1 p2.
  replace (Z.pos p1 + Z.pos p2)%Z with (Z.pos (p1+p2))%Z by auto.
  rewrite<- IZ_N.
  rewrite Pos2Nat.inj_add.
  rewrite N_hom.
  rewrite IZ_N.
  rewrite IZ_N.
  exact eq_refl.
Qed.

Lemma IZ_neg : forall p, IZ (Z.neg p) = - IZ (Z.pos p).
Proof.
  intro p.
  unfold IZ; auto.
Qed.
Lemma eq_plus_cancel : forall a b c, b + a = c + a -> b = c.
Proof.
  intros a b c p.
  apply (eq_plus_eq (b+a) (c+a) (-a)) in p.
  ring_simplify in p; exact p.
Qed.

  
Lemma IZ_pos_neg : forall p1 p2, IZ (Z.pos p1 + Z.neg p2) = IZ (Z.pos p1) + IZ (Z.neg p2).
Proof.
  intros p1 p2.
  destruct (Pos.compare_spec p1 p2).
  +
    rewrite H; simpl.
    rewrite IZ_neg.
    rewrite Z.pos_sub_diag.
    replace (IZ 0) with 0 by auto.
    ring.
  +
    simpl.
    rewrite (Z.pos_sub_lt p1 p2 H).
    rewrite IZ_neg; rewrite IZ_neg.
    rewrite<- IZ_N.
    rewrite<- IZ_N.
    rewrite<- IZ_N.
    ring_simplify.
    assert (N (Pos.to_nat p2) = N( Pos.to_nat p2)) as H1 by exact eq_refl.
    apply (eq_plus_cancel (N (Pos.to_nat (p2-p1)) + N (Pos.to_nat p2))).
    ring_simplify.
    rewrite <- N_hom.
    rewrite Pos2Nat.inj_sub; auto.
    rewrite Nat.sub_add; auto.
    apply (Pos2Nat.inj_lt p1 p2) in H.
    apply Nat.lt_le_incl; auto.

  +
    simpl.
    rewrite (Z.pos_sub_gt p1 p2 H).
    rewrite IZ_neg.
    rewrite <- IZ_N.
    rewrite <- IZ_N.
    rewrite <- IZ_N.
    apply (eq_plus_cancel (N (Pos.to_nat p2))).
    ring_simplify.
    rewrite <- N_hom.
    rewrite Pos2Nat.inj_sub; auto.
    rewrite Nat.sub_add; auto.
    apply (Pos2Nat.inj_lt p2 p1) in H.
    apply Nat.lt_le_incl; auto.
Qed.

Lemma IZ_neg_pos : forall p1 p2, IZ (Z.neg p1 + Z.pos p2) = IZ (Z.neg p1) + IZ (Z.pos p2).
Proof.
  intros p1 p2.
  replace (Z.neg p1 + Z.pos p2)%Z with (Z.pos p2 + Z.neg p1)%Z by auto.
  rewrite IZ_pos_neg; ring.
Qed.

  
Lemma Zdouble_minus : forall z, (z = --z)%Z.
Proof.
  intro z.
  assert (-z + - (-z) = 0)%Z by intuition.
  assert (z+(-z + - - z) =z+0)%Z by intuition.
  replace (z+0)%Z with z in H0 by intuition.
  replace (z+(-z+--z))%Z with (z+-z+--z)%Z in H0 by intuition.
  replace (z+-z)%Z with 0%Z in H0 by intuition.
  simpl in H0.
  rewrite H0; exact eq_refl.
Qed.
Local Hint Resolve Zdouble_minus: arith.

Lemma IZ_hom : forall n m, IZ (n+m) = IZ n + IZ m.
Proof.
  intros n m.
  destruct n; destruct m; try apply IZ_pos_pos; try apply IZ_pos_neg; try apply IZ_neg_pos; try simpl; try ring.
  rewrite IZ_neg.
  rewrite IZ_neg.
  rewrite IZ_neg.
  replace (Z.pos (p+p0)) with (Z.pos p + Z.pos p0)%Z by auto.
  rewrite (IZ_pos_pos).
  ring.
Qed.  

Lemma IZ_pos : forall z, (z > 0)%Z -> IZ z > 0.
Proof.
  intros z p.
  destruct z.
  + contradict p; apply Zgt_irrefl.
  +
    rewrite <- IZ_N.
    apply N_pos.
    exact (Pos2Nat.is_pos p0).
  +
    contradict p; apply Zgt_asym; apply Z.lt_gt; exact (Pos2Z.neg_is_neg p0).
Qed.




Lemma 1_inv_1 : /d1 = 1.
Proof.
  replace (/d1) with (/d1 *1) by ring.
  pose proof (1_neq_0).
  replace (/d1 *1) with 1 by auto with real.
  exact eq_refl.
Qed.

Lemma div_1 : forall z : real R, z/d1 = z.
Proof.
  intro.
  replace (z/d1) with (z*/d1) by auto.
  rewrite 1_inv_1; ring.
Qed.
Lemma lt_mult_pos_cancel : forall z z1 z2 : real R, z > 0 -> z1 * z < z2 * z -> z1 < z2.
Proof.
  intros z z1 z2 p q.
  assert (z <> 0); auto with real.  
  
  apply (lt_mult_r_pos_lt (z1*z) (z2 *z) (/H)) in q; auto with real.
  rewrite mult_assoc in q.
  rewrite mult_assoc in q.
  rewrite (mult_comm z (/H)) in q.
  rewrite (real_mult_inv z H) in q.
  ring_simplify in q; exact q.
Qed.

Lemma gt0_merge_gt : forall z1 z2 : real R, z1 > 0 -> z2 > 0 -> z1 + z2 > 0.
Proof.
  intros.
  pose proof (lt_lt_plus_lt 0 z1 0 z2 H H0).
  ring_simplify in H1; exact H1.
Qed.
Local Hint Resolve gt0_merge_gt: real.


Lemma lt_lt_lt_lt : forall a b c d, a<b -> b<c -> c<d -> a<d.
Proof.
  intros a b c d p q r.
  exact (lt_lt_lt a b d p (lt_lt_lt b c d q r)).
Qed.
Local Hint Resolve lt_lt_lt_lt: real.


Lemma gt1_mult_gt_self : forall z1 z2 : real R, z1 > 1 -> z2 > 0 -> z1 * z2 > z2.
Proof.
  intros z1 z2 p q.
  pose proof (padding z1 1 p) as [epsilon [c1 c2]].
  rewrite c2.
  ring_simplify.
  replace z2 with (0 + z2) at 3 by ring.
  apply lt_plus_r_lt.
  pose proof (real_lt_mult_pos_lt epsilon 0 z2 c1 q).
  ring_simplify in H; exact H.
Qed.
Local Hint Resolve  gt1_mult_gt_self: real.


Lemma lt_pos_mult_pos_pos : forall z1 z2 : real R, z1 > 0 -> z2 > 0 -> z1 * z2 > 0.
Proof.
  intros.
  pose proof (real_lt_mult_pos_lt z1 0 z2 H H0).
  replace (z1*0) with 0 in H1 by ring; auto.
Qed.
Local Hint Resolve lt_pos_mult_pos_pos: real.
  
Lemma pos_square_gt_gt : forall z1 z2 : real R, z1 > 0 -> z2 > 0 -> z1*z1 > z2*z2 -> z1 > z2.
Proof.
  intros z1 z2 q p r.
  destruct (real_total_order z1 z2) as [s|[s|s]].
  + pose proof (real_lt_mult_pos_lt z1 z1 z2 q s).
    pose proof (lt_mult_r_pos_lt z1 z2 z2 p s).
    pose proof (lt_lt_lt (z1*z1) (z1*z2) (z2*z2) H H0).
    contradict H1; auto with real.

  + rewrite s in r; contradict r; auto with real.

  + exact s.
Qed.
Local Hint Resolve pos_square_gt_gt: real.

Lemma pos_square_eq_eq : forall z1 z2 : real R, z1 > 0 -> z2 > 0 -> z1*z1 = z2*z2 -> z1 = z2.
Proof.
  intros.
  destruct (real_total_order z1 z2) as [p|[p|p]].
  
  pose proof (real_lt_mult_pos_lt z1 z1 z2 H p).
  pose proof (lt_mult_r_pos_lt z1 z2 z2 H0 p).
  pose proof (lt_lt_lt (z1*z1) (z1*z2) (z2*z2) H2 H3).
  rewrite H1 in H4;
    contradict H4; auto with real.
  auto.
  pose proof (real_lt_mult_pos_lt z2 z2 z1 H0 p).
  pose proof (lt_mult_r_pos_lt z2 z1 z1 H p).
  pose proof (lt_lt_lt (z2*z2) (z2*z1) (z1*z1) H2 H3).
  rewrite H1 in H4;
    contradict H4; auto with real.
Qed.
Local Hint Resolve pos_square_eq_eq: real.


Lemma gt0_gt0_plus_gt0 : forall z1 z2 : real R, z1 > 0 -> z2 > 0 -> z1 + z2 > 0.
Proof.
  intros.
  auto with real.
Qed.
Local Hint Resolve gt0_gt0_plus_gt0: real.

Lemma lt_le_lt_lt : forall z1 z2 z3 z4 : real R, z1 <z2 -> z2 <= z3 -> z3 < z4 -> z1 < z4.
  intros.
  apply (lt_le_lt z1 z2 z3 H) in H0.
  exact (lt_lt_lt z1 z3 z4 H0 H1).
Qed.

Lemma lt_lt_le_lt : forall z1 z2 z3 z4 : real R, z1 <z2 -> z2 < z3 -> z3 <= z4 -> z1 < z4.
  intros.
  apply (lt_lt_lt z1 z2 z3 H) in H0.
  exact (lt_le_lt z1 z3 z4 H0 H1).
Qed.

Lemma le_le_plus_le : forall a b c d : real R, a <= b -> c <= d -> a + c <= b + d.
Proof.
  intros.
  apply (le_plus_le c) in H.
  apply (le_plus_le b) in H0.
  
  replace (c + a) with (a + c) in H by ring.
  replace (b + c) with (c + b) in H0 by ring.
  exact (le_le_le _ _ _ H H0).
Qed.


Lemma d2_pos : 0 < / d2.
Proof.
  assert (/d2 > 0); auto with real.  
Qed.
Local Hint Resolve d2_pos: real.
  
           
Lemma eq_mult_eq : forall z z1 z2 : real R, z1 = z2 -> z*z1=z*z2.
Proof.
  intros.
  auto with real.
Qed.


Lemma W_split : forall x y ε : real R, ε > 0 -> x>y-ε \/ y>x-ε.
Proof.
  intros x y ε p.
  destruct (real_total_order x y) as [H|[H|H]].
  + apply (lt_plus_lt (-ε + x) 0 ε) in p.
    ring_simplify in p.
    apply (lt_lt_lt (-ε + x) x y p) in H.
    replace (-ε+x) with (x-ε) in H by ring; right; exact H.
  + rewrite H.
    left.
    apply (lt_plus_lt (y-ε) 0 ε) in p.
    ring_simplify in p.
    exact p.
  + apply (lt_plus_lt (-ε + y) 0 ε) in p.
    ring_simplify in p.
    apply (lt_lt_lt (-ε + y) y x p) in H.
    replace (-ε+y) with (y-ε) in H by ring; left; exact H.
Defined.
Local Hint Resolve W_split : real.
(** string but multivalued split **)
Lemma M_split : forall x y ε : real R, ε > 0 -> M ({x>y-ε} + {y>x-ε}).
Proof.
  intros x y ε p.  
  apply (choose (x > y-ε) (y > x-ε)); auto with real.
Defined.

Local Hint Resolve M_split : real.

  
Lemma not_bounded : forall x : real R, [ y | y > x ].
Proof.
  intro x.
  apply (mjoin (x>0-1) (0>x-1)).
  + intros [c1|c2].
    ++ exists (x+1).
       pose proof (1_gt_0).
       apply (lt_plus_lt x 0 1) in H.
       ring_simplify in H.
       exact H.
    ++ exists (x+2).
       pose proof (2_pos).
       apply (lt_plus_lt x 0 2) in H.
       ring_simplify in H.
       exact H.
  + apply M_split .
    exact 1_gt_0.
Defined.


(*  Metric and Metric Completeness  *)

