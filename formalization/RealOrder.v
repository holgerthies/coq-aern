Require Import Base.
Require Import Monad.
Require Import ClassicalMonads.
Require Import Nabla.
Require Import Kleene.
Require Import MultivalueMonad.
Require Import RealAxioms.
Require Import RealRing.

Require Import Coq.PArith.BinPos.
Require Import Psatz.

Fixpoint Npow2 n :=
  match n with
  | O => 1%nat
  | S n => ((Npow2 n) * 2)%nat
  end.


  
Open Scope Real_scope.

Section RealOrder.
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

  (* equality reasoning *)

  Lemma real_eq_eq_mult_eq : forall a b c d : Real, a = b -> c = d -> a*c = b*d.
  Proof.
    intros.
    rewrite H; rewrite H0; exact eq_refl.
  Qed.

  Lemma real_eq_plus_eq : forall z1 z2 z3 : Real, z1 = z2 -> z1 + z3 = z2 + z3.
  Proof.
    intros z1 z2 z3 p.
    rewrite p.
    exact eq_refl.
  Qed.

  Lemma real_eq_mult_eq : forall z z1 z2 : Real, z1 = z2 -> z * z1 = z * z2.
  Proof.
    intros z1 z2 z3 p.
    rewrite p.
    exact eq_refl.
  Qed.

  Lemma real_eq_mult_eq_r : forall z z1 z2 : Real, z1 = z2 -> z1 * z = z2 * z.
  Proof.
    intros z1 z2 z3 p.
    rewrite p.
    exact eq_refl.
  Qed.

  Lemma real_eq_plus_cancel : forall a b c : Real, b + a = c + a -> b = c.
  Proof.
    intros a b c p.
    apply (real_eq_plus_eq (b+a) (c+a) (-a)) in p.
    ring_simplify in p; exact p.
  Qed.

  Lemma real_eq_mult_cancel : forall a b c : Real, a <> real_0 -> b * a = c * a -> b = c.
  Proof.
    intros a b c aNeq0 p.
    apply (real_eq_mult_eq_r (/aNeq0) (b*a) (c*a)) in p.
    rewrite real_mult_assoc in p.
    rewrite (real_mult_assoc (c)) in p.
    rewrite (real_mult_comm a) in p.
    rewrite real_mult_inv in p.
    ring_simplify in p; exact p.
  Qed.

  (* inequality reasoning *)
  
  Lemma real_ge_triv : forall z : Real, z >= z.
  Proof.
    intro z;  right; exact eq_refl.
  Qed.
  
  Lemma real_le_triv : forall z : Real, z <= z.
  Proof.
    intro z; right; exact eq_refl.
  Qed.

  Lemma real_lt_le : forall z1 z2 : Real, z1<z2 -> z1 <= z2.
  Proof.
    intros z1 z2 p; left; exact p.
  Qed.

  Lemma real_gt_ge : forall z1 z2 : Real, z1>z2 -> z1 >= z2.
  Proof.
    intros z1 z2 p; left; exact p.
  Qed.

  Lemma real_eq_le : forall z1 z2 : Real, z1 = z2 -> z1 <= z2.
  Proof.
    intros z1 z2 p; rewrite p; right; exact eq_refl.
  Qed.

  Lemma real_eq_ge : forall z1 z2 : Real, z1 = z2 -> z1 >= z2.
  Proof.
    intros z1 z2 p; rewrite p; right; exact eq_refl.
  Qed.

  Lemma real_le_plus_le : forall z x y : Real, x <= y -> z + x <= z + y.
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


  Lemma real_ge_plus_ge : forall z x y : Real, x >= y -> z + x >= z + y.
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

  Lemma real_ge_le : forall z1 z2 : Real, z1 >= z2 -> z2 <= z1.
  Proof.
    intros z1 z2 p.
    destruct p.
    left; auto.
    right; rewrite H; exact eq_refl.
  Qed.


  Lemma real_le_ge : forall z1 z2 : Real, z1 <= z2 -> z2 >= z1.
  Proof.
    intros z1 z2 p.
    destruct p.
    left; auto.
    right; rewrite H; exact eq_refl.
  Qed.
  
  Lemma real_nle_ge : forall z1 z2 : Real, ~ z1 <= z2 -> z1 > z2.
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

  Lemma real_nge_le : forall z1 z2 : Real, ~ z1 < z2 -> z1 >= z2.
  Proof.
    intros z1 z2 q.
    intuition.
    destruct (real_total_order z1 z2).
    contradict (q H).
    destruct H.
    right; apply eq_sym; auto.
    left; auto.
  Qed.

  Lemma real_div_distr : forall z1 z2 z3 : Real, forall p : z3<>real_0,  z1/p + z2/p = (z1+z2)/p.
  Proof.
    intros z1 z2 z3 nz.
    replace ((z1+z2)/nz) with ((z1+z2)*/nz) by auto.
    rewrite real_mult_comm, real_mult_plus_distr.
    unfold real_div.
    ring.
  Qed.

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

  
  Lemma real_nlt_triv : forall x : Real, ~ x < x.
  Proof.
    intro x.
    intuition.
    pose proof (real_lt_nlt x x H) as H1.
    contradict H.
    intuition.
  Qed.


  Lemma real_2_gt_1 : real_2  > real_1.
  Proof.
    pose proof (real_1_gt_0).
    pose proof (real_lt_plus_lt real_1 real_0 real_1 H).
    rewrite real_plus_comm, real_plus_unit in H0.
    exact H0.
  Qed.





  Lemma real_lt_neq : forall z1 z2 : Real, z1 < z2 -> z1 <> z2.
  Proof.
    red.
    intros z1 z2 p q.
    apply (real_nlt_triv z1).
    pattern z1 at 2; rewrite q; trivial.
  Qed.


  Definition d2 := real_2_neq_0.
  Lemma real_minus_half : forall z : Real, z - z/d2 = z/d2.
  Proof.
    intro z.
    pose proof (real_2_neq_0).
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



  
  Lemma real_gt_nle: forall z1 z2 : Real, z1 > z2 -> ~ z1 <= z2.
  Proof.
    intros z1 z2 p q; destruct q as [q1 | q2].
    contradict p; exact (real_lt_nlt z1 z2 q1).
    rewrite q2 in p; contradict p.
    apply real_nlt_triv.
  Qed.




  Lemma real_gt_ngt : forall z1 z2 : Real, z1 > z2 -> ~ z2 > z1.
  Proof.
    intros z1 z2 p.
    contradict p; exact (real_lt_nlt z1 z2 p).
  Qed.

  Lemma real_gt_nge : forall z1 z2 : Real, z1 > z2 -> ~ z2 >= z1.
  Proof.
    intros z1 z2 p q; destruct q as [q1 | q2].
    contradict p; exact (real_lt_nlt z1 z2 q1).
    rewrite q2 in p; contradict p; apply real_nlt_triv.
  Qed.




  Local Hint Resolve real_ge_triv real_le_triv real_lt_le: real.
  Local Hint Resolve real_gt_ge: real.
  Local Hint Resolve real_eq_le: real.
  Local Hint Resolve real_eq_ge: real.
  Local Hint Resolve real_eq_plus_eq: real.
  Local Hint Resolve real_ge_le: real.
  Local Hint Resolve real_le_ge: real.
  Local Hint Resolve real_nle_ge: real.
  Local Hint Resolve real_nge_le: real.
  Local Hint Resolve real_div_distr: real.
  Local Hint Resolve real_nlt_triv: real.
  Local Hint Resolve real_2_gt_1: real.
  Local Hint Resolve real_lt_neq: real.
  Local Hint Resolve real_minus_half: real.
  Local Hint Resolve real_gt_nle: real.
  Local Hint Resolve real_gt_ngt: real.
  Local Hint Resolve real_gt_nge: real.


  Lemma real_ge_ge_eq : forall z1 z2 : Real, z1 >= z2 -> z2 >= z1 -> z1 = z2.
  Proof.
    intros z1 z2 o1 o2.
    destruct o1.
    contradict o2.
    auto with real.
    apply eq_sym.
    exact H.
  Qed.

  Lemma real_le_le_eq : forall z1 z2 : Real, z1 <= z2 -> z2 <= z1 -> z1 = z2.
  Proof.
    intros z1 z2 o1 o2.
    destruct o1.
    contradict o2.
    auto with real.
    exact H.
  Qed.

  Lemma real_le_ge_eq : forall z1 z2 : Real, z1 <= z2 -> z1 >= z2 -> z1 = z2.
  Proof.
    intros z1 z2 o1 o2.
    destruct o1.
    contradict o2.
    auto with real.
    exact H.
  Qed.

  Lemma real_ge_le_eq : forall z1 z2 : Real, z1 >= z2 -> z1 <= z2 -> z1 = z2.
  Proof.
    intros z1 z2 o1 o2.
    destruct o1.
    contradict o2.
    auto with real.
    apply eq_sym.
    exact H.
  Qed.


  Lemma real_le_lt_lt : forall z1 z2 z3 : Real, z1<=z2 -> z2 < z3 -> z1<z3.
  Proof.
    intros z1 z2 z3 p1 p2.
    destruct (real_total_order z1 z2) as [q1 |[q2| q3]].
    apply (real_lt_lt_lt z1 z2 z3); auto with real.
    rewrite q2; exact p2.
    destruct p1.
    contradict q3; apply (real_lt_nlt); exact H.
    rewrite H in q3; contradict q3; apply real_nlt_triv. 
  Qed.

  Lemma real_lt_le_lt : forall z1 z2 z3 : Real, z1 < z2 -> z2 <= z3 -> z1 < z3.
  Proof.
    intros z1 z2 z3 p1 p2.
    destruct p2 as [q1| q2].
    exact (real_lt_lt_lt z1 z2 z3 p1 q1).
    rewrite<- q2; exact p1.
  Qed.

  Lemma real_le_le_le : forall z1 z2 z3 : Real, z1 <= z2 -> z2 <= z3 -> z1 <= z3.
  Proof.
    intros z1 z2 z3 p1 p2.
    destruct p1 as [p11 | p12]; destruct p2 as [p21 | p22]; auto with real.
    left; exact (real_lt_lt_lt z1 z2 z3 p11 p21).
    rewrite p22 in p11; left; exact p11.
    rewrite p12; left; exact p21.
    rewrite p12; rewrite <- p22; right; exact eq_refl.
  Qed.

  Lemma real_lt_plus_r_lt : forall r r1 r2 : Real, r1 < r2 -> r1 + r < r2 + r.
  Proof.
    intros r r1 r2 p;
      replace (r1+r) with (r+r1) by ring;
      replace (r2+r) with (r+r2) by ring;
      exact (real_lt_plus_lt r r1 r2 p).
  Qed.



  Lemma real_2_pos : real_2 > real_0.
  Proof.
    pose proof (real_1_gt_0).
    pose proof (real_lt_plus_r_lt real_1 real_0 real_1 H).
    replace (real_0+real_1) with real_1 in H0 by ring.
    pose proof (real_lt_lt_lt real_0 real_1 (real_1 + real_1) H H0).
    auto.
  Qed.


  Lemma real_half_gt_zero : forall a : Real, a > real_0 -> a / d2 > real_0. 
  Proof.
    intros a p.
    pose proof (real_2_pos ).
    destruct (real_total_order (a/d2) real_0) as [p1 |[p2|p3]].
    apply (real_lt_mult_pos_lt real_2 (a/d2) real_0) in p1.
    replace (real_2*(a/d2)) with (real_2*(a*/d2)) in p1 by auto.
    replace (real_2*(a*/d2)) with (a *(/d2 * real_2)) in p1 by ring.
    rewrite (real_mult_inv real_2 d2) in p1.
    replace (real_2 * real_0) with real_0 in p1 by ring.
    rewrite real_mult_comm, real_mult_unit in p1.
    contradict p1.
    apply real_lt_nlt, p.
    exact real_2_pos.
    rewrite p2.
    pose proof (real_eq_eq_mult_eq (a/d2) real_0 real_2 real_2 p2 eq_refl).
    replace (a/d2*real_2) with (a*/d2*real_2) in H0 by auto.
    replace (a*/d2*real_2) with (a*(/d2*real_2)) in H0 by ring.
    rewrite (real_mult_inv real_2 d2) in H0.
    replace (real_0 * real_2) with real_0 in H0 by ring.
    rewrite real_mult_comm, real_mult_unit in H0.
    rewrite H0 in p.
    contradict p; apply real_nlt_triv. 
    exact p3.
  Qed.



  Lemma real_gt_half : forall a : Real, a > real_0 -> a > a / d2.
  Proof.
    intros a p.
    pose proof (real_half_gt_zero a p).
    apply (real_lt_plus_lt (a/d2) real_0 (a/d2)) in H.
    rewrite (real_div_distr a a real_2 d2) in H.
    rewrite real_plus_comm, real_plus_unit in H.
    replace (a + a) with (real_1 * a + real_1 * a) in H by ring.
    replace (real_1 * a + real_1 * a) with ((real_1+real_1)*a) in H by ring.
    replace (real_1+real_1) with (real_2) in H by auto.
    replace (real_2*a/d2) with (real_2*a*/d2) in H by auto.
    replace (real_2*a*/d2) with (a*(/d2*real_2)) in H by ring.
    rewrite (real_mult_inv real_2 d2) in H.
    rewrite real_mult_comm, real_mult_unit in H.
    exact H.
  Qed.
  
  Lemma real_gt_minus_gt_zero : forall a b  : Real , a > b -> a - b > real_0.
  Proof.
    intros a b p.
    replace (a-b) with (-b+a) by ring.
    replace real_0 with (-b+b) by ring.
    apply real_lt_plus_lt; auto with real.
  Qed.


  Lemma real_lt_lt_plus_lt : forall r1 r2 r3 r4 : Real, r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
  Proof.
    intros r1 r2 r3 r4 p1 p2.
    pose proof (real_lt_plus_r_lt r3 r1 r2 p1).
    assert (r2+r3 < r2+r4).
    apply (real_lt_plus_lt).
    exact p2.
    exact (real_lt_lt_lt (r1+r3) (r2+r3) (r2+r4) H H0).
  Qed.


  Local Hint Resolve real_ge_ge_eq real_ge_le_eq real_le_ge_eq real_le_le_eq: real.
  Local Hint Resolve real_le_lt_lt: real.
  Local Hint Resolve real_lt_le_lt: real.
  Local Hint Resolve real_le_le_le: real.
  Local Hint Resolve real_lt_plus_lt: real.
  Local Hint Resolve real_2_pos: real.
  Local Hint Resolve real_eq_eq_mult_eq: real.
  Local Hint Resolve real_half_gt_zero: real.
  Local Hint Resolve real_gt_half: real.
  Local Hint Resolve real_gt_minus_gt_zero: real.
  Local Hint Resolve real_lt_lt_plus_lt: real. 


  Definition padding : forall a b  : Real , a > b -> {ε  | ε > real_0 /\ a = ε + b}.
  Proof.
    intros a b p; exists (a - b).
    constructor 1; auto with real; ring.
  Defined.



  Lemma real_lt_anti : forall z1 z2 : Real, z1<z2 -> -z2< -z1.
  Proof.
    intros z1 z2 p.
    apply (real_lt_plus_lt (-z1-z2) z1 z2) in p.
    replace  (- z1 - z2 + z1) with (-z2) in p by ring.
    replace (- z1 - z2 + z2) with (-z1) in p by ring.
    exact p.
  Qed.


  Lemma real_lt_anti_anti : forall z1 z2 : Real, - z1 < - z2 -> z2< z1.
  Proof.
    intros z1 z2 p.
    replace z2 with (- - z2) by ring.
    replace z1 with (- - z1) by ring.
    apply real_lt_anti.
    exact p.
  Qed.





  Lemma real_lt_add_r : forall z x y : Real, x + z < y + z -> x < y.
  Proof.
    intros.
    pose proof (real_lt_plus_lt (-z) _ _ H).
    replace (- z + (x + z)) with x in H0 by ring.
    replace (- z + (y + z)) with y in H0 by ring.
    
    exact H0.
  Qed.

  Lemma real_gt_add_r : forall z x y : Real, x + z > y + z -> x > y.
  Proof.
    intros.
    pose proof (real_lt_plus_lt (-z) _ _ H).
    replace (- z + (y + z)) with y in H0 by ring.
    replace (- z + (x + z)) with x in H0 by ring.
    exact H0.
  Qed.

  Lemma real_le_add_r : forall z x y : Real, x + z <= y + z -> x <= y.
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

  Lemma real_ge_add_r : forall z x y : Real, x + z >= y + z -> x >= y.
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

  Definition d1 := real_1_neq_0.
  Lemma real_inv_unit : forall z : Real, z / d1 = z.
  Proof.
    intro.
    replace z with (z*real_1) by ring.
    replace (z*real_1/d1) with (z*real_1*/d1) by auto.
    replace (z*real_1*/d1) with (z*(/d1*real_1)) by ring.
    replace (/d1*real_1) with (real_1).
    exact eq_refl.
    apply eq_sym, real_mult_inv.
  Qed.


  Lemma square_pos : forall z : Real, z <> real_0 -> z *z > real_0.
  Proof.
    intros.
    destruct (real_total_order z real_0) as [a|[b|c]].
    assert (z+(-z) < real_0+(-z)).
    apply (real_lt_plus_r_lt); exact a.
    rewrite real_plus_unit, real_plus_inv in H0.
    
    pose proof (real_lt_mult_pos_lt (-z) real_0 (-z) H0 H0).
    replace (- z * real_0) with real_0 in H1 by ring.
    replace (- z * - z) with (z * z) in H1 by ring.
    exact H1.
    contradict H; exact b.
    pose proof (real_lt_mult_pos_lt z real_0 z c c) as q.
    replace (z * real_0) with real_0 in q by ring.
    exact q.
  Qed.

  Lemma neq_sym : forall A (a b : A), a <> b -> b <> a.
  Proof.
    intros.
    intro.
    rewrite H0 in H.
    apply H, eq_refl.
  Defined.

  
  Lemma real_pos_inv_pos2 : forall z : Real, forall p :  z > real_0, / (real_gt_neq z real_0 p) > real_0.
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
    rewrite H0 in H2.
    replace (real_0 * z) with real_0 in H2 by ring.
    contradict H2; apply neq_sym, (real_1_neq_0 ).
    pose proof (H H10) as H0.
    pose proof (real_lt_mult_pos_lt (/(real_gt_neq z real_0 p)*/(real_gt_neq z real_0 p)) real_0 z H0 p).
    replace (/(real_gt_neq z real_0 p)*/(real_gt_neq z real_0 p)*z) with (/(real_gt_neq z real_0 p)*(/(real_gt_neq z real_0 p)*z))  in H1 by ring.
    replace (/(real_gt_neq z real_0 p) *z) with (real_1) in H1.

    replace (/ real_gt_neq z real_0 p * / real_gt_neq z real_0 p * real_0) with real_0 in H1 by ring.
    rewrite real_mult_comm, real_mult_unit in H1. 
    
    exact H1.
    rewrite (real_mult_inv); auto.
  Qed.
  
  Local Hint Resolve padding: real.
  Local Hint Resolve real_lt_anti: real.
  Local Hint Resolve real_lt_anti_anti: real.
  Local Hint Resolve real_inv_unit: real.
  Local Hint Resolve real_pos_inv_pos2:real.

  Lemma real_pos_inv_pos : forall z : Real, forall p : z > real_0, forall q : z <> real_0, / q > real_0.
  Proof.
    intros.
    rewrite (irrl _ q (real_gt_neq z real_0 p)); auto with real.
  Qed.

  Local Hint Resolve real_pos_inv_pos : real.

  Lemma real_lt_mult_r_pos_lt : forall z1 z2 z3 : Real, z3 > real_0 -> z1 < z2 -> z1 * z3 < z2 * z3.
  Proof.
    intros.
    replace (z1*z3) with (z3*z1) by ring.
    replace (z2*z3) with (z3*z2) by ring.
    apply real_lt_mult_pos_lt; auto.
  Qed.


  Lemma prec_S : forall n, prec (S n) < prec n.
  Proof.
    intro n.
    induction n; simpl.
    replace (real_1+real_1) with (real_2) by auto.
    exact (real_gt_half real_1 real_1_gt_0).
    simpl in IHn.
    replace (real_1+real_1) with (real_2) by auto.
    replace (real_1+real_1) with (real_2) in IHn by auto.
    pose proof (real_2_pos).
    assert (/d2 > real_0) by auto with real.
    apply (real_lt_mult_r_pos_lt (prec n / d2) (prec n)  (/d2) H0) in IHn.
    exact IHn.
  Qed.

  Lemma prec_hom : forall n m, prec (n+m) = prec n * prec m.
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

  Definition dg0 {z : Real}(p:z>real_0) : z <> real_0 :=  real_gt_neq z real_0 p.
  Lemma real_lt_mult_pos_move_rr : forall a b c : Real, forall p :a > real_0, b*a < c -> b < c / (dg0 p).
  Proof.
    intros a b c p q.
    assert (/ (dg0 p) > real_0) by auto with real.
    apply (real_lt_mult_r_pos_lt (b*a)  c (/(dg0 p)) H) in q.
    replace (b*a*/(dg0 p)) with (b*(/(dg0 p)*a)) in q by ring.
    assert (a <> real_0).
    intro e; clear q H; rewrite e in p; apply (real_nlt_triv _ p).
    replace (/(dg0 p)*a) with (real_1) in q.
    replace (b * real_1) with b in q by ring; exact q.
    rewrite (real_mult_inv); auto.
  Qed.

  Lemma real_lt_mult_pos_move_rl : forall a b c : Real, forall p :a > real_0, a*b < c -> b < c / (dg0 p).
  Proof.
    intros a b c p q.
    replace (a*b) with (b*a) in q by ring.
    apply real_lt_mult_pos_move_rr; auto. 
  Qed.

  Lemma real_gt_mult_pos_move_rl : forall a b c : Real, forall p:a > real_0,  a*b > c -> b > c / (dg0 p).
    intros a b c p q.
    assert (/ (dg0 p) > real_0) by auto with real.
    replace (a*b) with (b*a) in q by ring.
    apply (real_lt_mult_r_pos_lt c (b*a) (/ (dg0 p)) H) in q.
    replace (b*a*/(dg0 p)) with (b*(/(dg0 p)*a)) in q by ring.
    assert (a <> real_0).
    intro e; clear q H; rewrite e in p; apply (real_nlt_triv _ p).
    replace (/(dg0 p)*a) with (real_1) in q. 
    rewrite (real_mult_comm b), real_mult_unit in q.
    
    auto with real.
    rewrite (real_mult_inv); auto.
  Qed.

  Lemma real_lt_mult_pos_move_rr_n
    : forall (a b c : Real) (p : a > real_0) (q : a <> real_0), b * a < c -> b < c / q.
  Proof.
    intros.
    pose proof (irrl _ q (real_gt_neq a real_0 p)).
    rewrite H0.
    apply real_lt_mult_pos_move_rr; exact H.
  Qed.



  (** prec embedding is always positive **)
  Lemma prec_pos : forall n, prec n > real_0.
  Proof.
    intro.
    induction n.
    simpl; apply real_1_gt_0.
    simpl.
    replace (real_1+real_1) with (real_2) by auto.
    auto with real.
  Defined.


  Lemma Nreal_hom : forall n m, Nreal (n+m) = Nreal n + Nreal m.
  Proof.
    intros n m.
    induction n.
    simpl.
    rewrite real_plus_unit; auto.
    assert (S n + m = S (n+m))%nat as H by intuition.
    rewrite H.
    assert (forall n, Nreal (S n) = real_1 + Nreal n) by (intro; simpl; exact eq_refl).
    rewrite (H0 n). rewrite (H0 ((n+m)%nat)).
    rewrite IHn; ring.
  Qed.

  Lemma prec_twice : forall n, prec (n + 1) + prec (n + 1) = prec n.
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

  Lemma Nreal_pos : forall n, (n>0)%nat -> Nreal n > real_0.
  Proof.
    intros n p.
    induction n.
    contradict p; exact (gt_irrefl 0).
    assert (S n = 1+n)%nat as q; intuition.
    rewrite q.
    rewrite (Nreal_hom 1%nat n).
    pose proof (real_1_gt_0) as gtg.
    destruct n.
    simpl.
    rewrite real_plus_comm, real_plus_unit, real_plus_comm,  real_plus_unit.
    auto with real.

    pose proof (IHn (gt_Sn_O n)).
    pose proof (real_lt_lt_plus_lt real_0 real_1 real_0 (Nreal (S n)) gtg H) as H1.
    rewrite real_plus_unit in H1.
    
    assert (Nreal 1 = real_1). simpl. ring.
    rewrite H0; exact H1.
  Qed.


  Lemma Nreal_S : forall n, Nreal (S n) = real_1 + Nreal n.
  Proof.
    intro n.
    replace (S n)%nat with (1 + n)%nat by intuition.
    rewrite (Nreal_hom 1%nat n); simpl; ring.
  Qed.

  Lemma Nreal_mult : forall n m, Nreal (n * m) = Nreal n * Nreal m.
  Proof.
    intros n m.
    induction n.
    simpl; ring.
    simpl.
    rewrite Nreal_hom .
    rewrite IHn.
    ring.
  Qed.


  Lemma IZ_asym : forall n, IZreal (-n) = - IZreal n.
  Proof.
    intro n.
    unfold IZreal.
    unfold IPreal.
    unfold IPreal_2.  
    destruct n; simpl; ring.
  Qed.

  Lemma IZreal_s1 : forall p, IZreal (Z.pos (p~0)) = real_2 * (IZreal (Z.pos p)).
  Proof.
    intro.
    unfold IZreal.
    simpl.
    unfold IPreal.
    
    unfold IPreal_2.

    destruct p;
      replace (real_1+real_1) with (real_2) by auto; ring_simplify;
        exact eq_refl.
  Qed.

  Lemma IZreal_s2 : forall p, IZreal (Z.pos (p~1)) = real_2 * (IZreal (Z.pos p)) + real_1.
  Proof.
    intro.
    unfold IZreal.
    unfold IPreal.  
    unfold IPreal_2.
    destruct p;
      replace (real_1+real_1) with (real_2) by auto; ring_simplify; exact eq_refl.
  Qed.

  Lemma IP2_Nreal : forall p, real_2 * Nreal (Pos.to_nat p) = IPreal_2 p.
  Proof.
    intro p.
    induction p.
    + rewrite Pos2Nat.inj_xI.
      rewrite Nreal_S.
      ring_simplify.
      rewrite Nreal_mult.
      ring_simplify.
      replace (real_2* Nreal 2 * Nreal (Pos.to_nat p)) with (Nreal 2 * (real_2 * Nreal (Pos.to_nat p))) by ring.
      rewrite IHp.
      simpl.
      unfold real_2.
      unfold IZreal.
      unfold IPreal.
      simpl.
      ring.
    + rewrite Pos2Nat.inj_xO.
      rewrite Nreal_mult.
      simpl.
      rewrite <- IHp.
      ring.
    + simpl.
      rewrite real_plus_comm, real_plus_unit,  real_mult_comm,  real_mult_unit.
      auto.
  Qed.

  Lemma IPreal_Nreal : forall p, Nreal (Pos.to_nat p) = IPreal p.
  Proof.
    intro p.
    induction p.

    + unfold IPreal.
      rewrite <- IP2_Nreal.
      rewrite Pos2Nat.inj_xI.
      rewrite Nreal_S, Nreal_mult.
      simpl Nreal.
      unfold real_2.
      simpl.
      ring.
      
    + unfold IPreal.
      rewrite <- IP2_Nreal.
      rewrite Pos2Nat.inj_xO.
      rewrite  Nreal_mult.
      
      unfold real_2.
      unfold Nreal.
      simpl.
      ring.
    + simpl.
      rewrite real_plus_comm, real_plus_unit.
      auto.
  Qed.

  Lemma IZ_Nreal : forall p, Nreal (Pos.to_nat p) = IZreal (Z.pos p).
  Proof.
    intro p.
    rewrite IPreal_Nreal.
    unfold IZreal; exact eq_refl.
  Qed.

  Lemma IZreal_pos_pos : forall p1 p2, IZreal (Z.pos p1 + Z.pos p2) = IZreal (Z.pos p1) + IZreal (Z.pos p2).
  Proof.
    intros p1 p2.
    replace (Z.pos p1 + Z.pos p2)%Z with (Z.pos (p1+p2))%Z by auto.
    rewrite<- IZ_Nreal.
    rewrite Pos2Nat.inj_add.
    rewrite Nreal_hom.
    rewrite IZ_Nreal.
    rewrite IZ_Nreal.
    exact eq_refl.
  Qed.

  Lemma IZreal_neg : forall p, IZreal (Z.neg p) = - IZreal (Z.pos p).
  Proof.
    intro p.
    unfold IZreal; auto.
  Qed.
  
  Lemma IZreal_pos_neg : forall p1 p2, IZreal (Z.pos p1 + Z.neg p2) = IZreal (Z.pos p1) + IZreal (Z.neg p2).
  Proof.
    intros p1 p2.
    destruct (Pos.compare_spec p1 p2).
    +
      rewrite H; simpl.
      rewrite Z.pos_sub_diag.
      simpl.
      ring.
    +
      simpl.
      rewrite (Z.pos_sub_lt p1 p2 H).
      rewrite IZreal_neg.
      rewrite<- IZ_Nreal.
      ring_simplify.
      apply (real_eq_plus_cancel (Nreal (Pos.to_nat (p2-p1)) + Nreal (Pos.to_nat p2))).
      ring_simplify.
      rewrite real_plus_comm.
      rewrite <- real_plus_assoc.
      rewrite <- IPreal_Nreal.
      rewrite <- Nreal_hom.
      rewrite Pos2Nat.inj_sub; auto.
      replace ((Pos.to_nat p1 + (Pos.to_nat p2 - Pos.to_nat p1)))%nat with
          ((Pos.to_nat p2 - Pos.to_nat p1 + Pos.to_nat p1)%nat) by lia.
      
      rewrite Nat.sub_add; auto.
      apply (Pos2Nat.inj_lt p1 p2) in H.
      simpl.
      rewrite IPreal_Nreal.
      ring.
      lia.

    +
      simpl.
      rewrite (Z.pos_sub_gt p1 p2 H).
      rewrite <- IZ_Nreal.
      apply (real_eq_plus_cancel (Nreal (Pos.to_nat p2))).
      ring_simplify.
      rewrite <- Nreal_hom.
      rewrite Pos2Nat.inj_sub; auto.
      rewrite Nat.sub_add; auto.
      rewrite <- IPreal_Nreal.
      rewrite <- IPreal_Nreal.
      ring.
      lia.
  Qed.
  
  
  Lemma IZ_neg_pos : forall p1 p2, IZreal (Z.neg p1 + Z.pos p2) = IZreal (Z.neg p1) + IZreal (Z.pos p2).
  Proof.
    intros p1 p2.
    replace (Z.neg p1 + Z.pos p2)%Z with (Z.pos p2 + Z.neg p1)%Z by auto.
    rewrite IZreal_pos_neg; ring.
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


  Lemma IZreal_hom : forall n m, IZreal (n+m) = IZreal n + IZreal m.
  Proof.
    intros n m.
    destruct n; destruct m; try apply IZ_pos_pos; try apply IZ_pos_neg; try apply IZ_neg_pos; try simpl; try ring.
    apply IZreal_pos_pos.
    simpl.
    auto.
    pose proof IZreal_pos_neg.
    rewrite <- Pos2Z.add_pos_neg.
    rewrite  IZreal_pos_neg.    
    auto.
    assert ( IPreal (p + p0) = IPreal p + IPreal p0).
    apply IZreal_pos_pos.
    rewrite H.
    ring.
  Qed.  

  Lemma IZreal_pos : forall z, (z > 0)%Z -> IZreal z > real_0.
  Proof.
    intros z p.
    destruct z.
    + contradict p; apply Zgt_irrefl.
    +
      rewrite <- IZ_Nreal.
      apply Nreal_pos.
      exact (Pos2Nat.is_pos p0).
    +
      contradict p; apply Zgt_asym; apply Z.lt_gt; exact (Pos2Z.neg_is_neg p0).
  Qed.




  Lemma real_1_inv_1 : /d1 = real_1.
  Proof.
    replace (/d1) with (/d1 *real_1) by ring.
    pose proof (real_1_neq_0).
    replace (/d1 *real_1) with (real_1).
    exact eq_refl.
    apply eq_sym, real_mult_inv.
  Qed.

  Lemma div_1 : forall z : Real, z/d1 = z.
  Proof.
    intro.
    replace (z/d1) with (z*/d1) by auto.
    rewrite real_1_inv_1; ring.
  Qed.
  Lemma real_lt_mult_pos_cancel : forall z z1 z2 : Real, z > real_0 -> z1 * z < z2 * z -> z1 < z2.
  Proof.
    intros z z1 z2 p q.
    assert (z <> real_0).
    apply real_gt_neq, p.
    
    apply (real_lt_mult_r_pos_lt (z1*z) (z2 *z) (/H)) in q; auto with real.
    rewrite real_mult_assoc in q.
    rewrite real_mult_assoc in q.
    rewrite (real_mult_comm z (/H)) in q.
    rewrite (real_mult_inv z H) in q.
    ring_simplify in q; exact q.
  Qed.

  Lemma real_gt0_merge_gt : forall z1 z2 : Real, z1 > real_0 -> z2 > real_0 -> z1 + z2 > real_0.
  Proof.
    intros.
    pose proof (real_lt_lt_plus_lt real_0 z1 real_0 z2 H H0).
    rewrite real_plus_unit in H1.
    exact H1.
  Qed.


  Lemma real_lt_lt_lt_lt : forall a b c d : Real, a<b -> b<c -> c<d -> a<d.
  Proof.
    intros a b c d p q r.
    exact (real_lt_lt_lt a b d p (real_lt_lt_lt b c d q r)).
  Qed.



  Lemma real_gt1_mult_gt_self : forall z1 z2 : Real, z1 > real_1 -> z2 > real_0 -> z1 * z2 > z2.
  Proof.
    intros z1 z2 p q.
    pose proof (padding z1 real_1 p) as [epsilon [c1 c2]].
    rewrite c2.
    ring_simplify.
    replace z2 with (real_0 + z2) at 3 by ring.
    apply real_lt_plus_r_lt.
    pose proof (real_lt_mult_pos_lt epsilon real_0 z2 c1 q).
    replace (epsilon * real_0) with real_0 in H by ring.
    exact H.
  Qed.



  Lemma real_lt_pos_mult_pos_pos : forall z1 z2 : Real, z1 > real_0 -> z2 > real_0 -> z1 * z2 > real_0.
  Proof.
    intros.
    pose proof (real_lt_mult_pos_lt z1 real_0 z2 H H0).
    replace (z1*real_0) with (real_0) in H1 by ring; auto.
  Qed.

  Lemma real_le_pos_mult_pos_pos x y : real_0 <= x -> real_0 <= y -> real_0 <= x * y.
  Proof.
    intros.
    destruct H, H0.
    left; apply real_lt_pos_mult_pos_pos; auto.
    right. rewrite <- H0. ring.
    right. rewrite <- H. ring.
    right. rewrite <- H. ring.
  Qed.
    
  Lemma real_pos_square_gt_gt : forall z1 z2 : Real, z1 > real_0 -> z2 > real_0 -> z1*z1 > z2*z2 -> z1 > z2.
  Proof.
    intros z1 z2 q p r.
    destruct (real_total_order z1 z2) as [s|[s|s]].
    + pose proof (real_lt_mult_pos_lt z1 z1 z2 q s).
      pose proof (real_lt_mult_r_pos_lt z1 z2 z2 p s).
      pose proof (real_lt_lt_lt (z1*z1) (z1*z2) (z2*z2) H H0).
      contradict H1.
      apply real_lt_nlt, r.
    + rewrite s in r; contradict r.
      apply real_nlt_triv. 
     
    + exact s.
  Qed.
  Lemma real_pos_square_eq_eq : forall z1 z2 : Real, z1 > real_0 -> z2 > real_0 -> z1*z1 = z2*z2 -> z1 = z2.
  Proof.
    intros.
    destruct (real_total_order z1 z2) as [p|[p|p]].
    
    pose proof (real_lt_mult_pos_lt z1 z1 z2 H p).
    pose proof (real_lt_mult_r_pos_lt z1 z2 z2 H0 p).
    pose proof (real_lt_lt_lt (z1*z1) (z1*z2) (z2*z2) H2 H3).
    rewrite H1 in H4;
      contradict H4; auto with real.
    auto.
    pose proof (real_lt_mult_pos_lt z2 z2 z1 H0 p).
    pose proof (real_lt_mult_r_pos_lt z2 z1 z1 H p).
    pose proof (real_lt_lt_lt (z2*z2) (z2*z1) (z1*z1) H2 H3).
    rewrite H1 in H4;
      contradict H4; auto with real.
  Qed.

  Local Hint Resolve Zdouble_minus: arith.
  Local Hint Resolve real_lt_mult_r_pos_lt prec_S prec_hom real_lt_mult_pos_move_rr real_lt_mult_pos_move_rl real_gt_mult_pos_move_rl real_lt_mult_pos_move_rr_n prec_pos Nreal_hom Nreal_pos real_lt_mult_r_pos_lt prec_S prec_hom real_lt_mult_pos_move_rr real_lt_mult_pos_move_rl real_gt_mult_pos_move_rl real_lt_mult_pos_move_rr_n prec_pos Nreal_hom Nreal_pos  real_gt0_merge_gt real_lt_lt_lt_lt real_gt1_mult_gt_self real_lt_pos_mult_pos_pos real_pos_square_gt_gt real_pos_square_eq_eq: real.


  Lemma real_gt0_gt0_plus_gt0 : forall z1 z2 : Real, z1 > real_0 -> z2 > real_0 -> z1 + z2 > real_0.
  Proof.
    intros.
    auto with real.
  Qed.


  Lemma real_lt_le_lt_lt : forall z1 z2 z3 z4 : Real, z1 <z2 -> z2 <= z3 -> z3 < z4 -> z1 < z4.
    intros.
    apply (real_lt_le_lt z1 z2 z3 H) in H0.
    exact (real_lt_lt_lt z1 z3 z4 H0 H1).
  Qed.

  Lemma real_lt_lt_le_lt : forall z1 z2 z3 z4 : Real, z1 <z2 -> z2 < z3 -> z3 <= z4 -> z1 < z4.
    intros.
    apply (real_lt_lt_lt z1 z2 z3 H) in H0.
    exact (real_lt_le_lt z1 z3 z4 H0 H1).
  Qed.

  Lemma real_le_le_plus_le : forall a b c d : Real, a <= b -> c <= d -> a + c <= b + d.
  Proof.
    intros.
    apply (real_le_plus_le c) in H.
    apply (real_le_plus_le b) in H0.
    
    replace (c + a) with (a + c) in H by ring.
    replace (b + c) with (c + b) in H0 by ring.
    exact (real_le_le_le _ _ _ H H0).
  Qed.


  Lemma d2_pos : real_0 < / d2.
  Proof.
    assert (/d2 > real_0); auto with real.  
  Qed.

  Lemma W_split : forall x y ε : Real, ε > real_0 -> x>y-ε \/ y>x-ε.
  Proof.
    intros x y ε p.
    destruct (real_total_order x y) as [H|[H|H]].
    + apply (real_lt_plus_lt (-ε + x) real_0 ε) in p.
      ring_simplify in p.
      apply (real_lt_lt_lt (-ε + x) x y p) in H.
      replace (-ε+x) with (x-ε) in H by ring; right; exact H.
    + rewrite H.
      left.
      apply (real_lt_plus_lt (y-ε) real_0 ε) in p.
      ring_simplify in p.
      exact p.
    + apply (real_lt_plus_lt (-ε + y) real_0 ε) in p.
      ring_simplify in p.
      apply (real_lt_lt_lt (-ε + y) y x p) in H.
      replace (-ε+y) with (y-ε) in H by ring; left; exact H.
  Defined.


  Local Hint Resolve real_gt0_gt0_plus_gt0: real.
  Local Hint Resolve d2_pos: real.
  Local Hint Resolve W_split : real.


  (** string but multivalued split **)
  Lemma M_split : forall x y ε : Real, ε > real_0 -> ^M ({x>y-ε} + {y>x-ε}).
  Proof.
    intros x y ε p.  
    apply (choose (x > y-ε) (y > x-ε)); auto with real.
    apply real_lt_semidec.
    apply real_lt_semidec.
  Defined.

  Local Hint Resolve M_split : real.

  Lemma not_bounded : forall x : Real, ^M { y | y > x }.
  Proof.
    intro x.
    apply (mjoin (x>real_0-real_1) (real_0>x-real_1)).
    + intros [c1|c2].
      ++ exists (x+real_1).
         pose proof (real_1_gt_0).
         apply (real_lt_plus_lt x real_0 real_1) in H.
         ring_simplify in H.
         exact H.
      ++ exists (x+real_2).
         pose proof (real_2_pos).
         apply (real_lt_plus_lt x real_0 real_2) in H.
         ring_simplify in H.
         exact H.
    + apply M_split .
      exact real_1_gt_0.
  Defined.


  Lemma Nreal_Npow2_pos : forall n, Nreal (Npow2 n) > real_0. 
  Proof.
    intros.
    apply Nreal_pos.
    induction n.
    simpl; lia.
    simpl.
    lia.
  Qed.
  
    
  Lemma prec_Npow2_unit : forall n, prec n * Nreal (Npow2 n) = real_1.
  Proof.
    intros.
    induction n.
    simpl.
    ring.
    simpl.
    replace ((Npow2 n * 2))%nat with (Npow2 n + Npow2 n)%nat by lia.
    rewrite Nreal_hom.
    unfold real_div.
    replace (prec n */ real_2_neq_0 * (Nreal (Npow2 n) + Nreal (Npow2 n))) with
        (/ real_2_neq_0 * ((prec n) * ((Nreal (Npow2 n) + Nreal (Npow2 n))))) by ring.
    replace (/ real_2_neq_0 * ((prec n) * ((Nreal (Npow2 n) + Nreal (Npow2 n))))) with
        (/ real_2_neq_0 * ((prec n) * Nreal (Npow2 n) + (prec n) * Nreal (Npow2 n)))
      by ring.
    rewrite IHn.
    apply real_mult_inv.
  Qed.

  
  Lemma precinv : forall n (p : prec n <> real_0), /p = Nreal (Npow2 n).
  Proof.
    intros.
    pose proof (prec_Npow2_unit n).
    apply (lp _ _ (fun k => k * / p)) in H.
    replace (prec n * Nreal (Npow2 n) * / p) with (/p * prec n * Nreal (Npow2 n)) in H by ring.
    rewrite real_mult_inv in H.    
    rewrite real_mult_unit in H.
    rewrite real_mult_unit in H.
    exact (eq_sym H).
  Qed.
  
  Lemma nat_bound_above : forall x, x > real_0 -> exists n, x < Nreal n.
  Proof.
    intros.
    pose proof (dg0  H).
    pose proof (real_pos_inv_pos _ H H0).
    pose proof (real_Archimedean _ H1).
    destruct H2.
    exists (Npow2 x0).

    apply (real_lt_mult_pos_lt _ _ _ (Nreal_Npow2_pos x0)) in H2.
    rewrite real_mult_comm in H2.
    rewrite prec_Npow2_unit in H2.
    apply (real_lt_mult_pos_lt _ _ _ H) in H2.
    rewrite real_mult_comm, real_mult_unit in H2.
    replace (x * (Nreal (Npow2 x0) * / H0)) with (/H0 * x * (Nreal (Npow2 x0))) in H2 by ring.
    rewrite real_mult_inv in H2.
    rewrite real_mult_unit in H2.
    exact H2.
  Qed.
  
  
  
  Lemma IZreal_Nreal : forall n, Nreal  n = IZreal (Z.of_nat n).
  Proof.
    intros.
    induction n.
    simpl.
    auto.
    rewrite Nreal_S.
    replace (Z.of_nat (S n)) with (Z.of_nat (n) + 1)%Z by lia. 
    rewrite IZreal_hom.
    rewrite IHn.
    apply real_plus_comm.
  Qed.
    
  Lemma overlapping : forall a b c d x : Real, a < x < b -> d < c -> a < x < c \/ d < x < b.  
  Proof.
    intros.
    destruct (real_total_order x c).
    left.
    split; destruct H; auto.
    destruct H1.
    right.
    induction H1.
    destruct H.
    split; auto.
    right.
    split; destruct H; auto.
    apply (real_lt_lt_lt _ _ _ H0 H1).
  Qed.
  
  Lemma IZreal_opp : forall z, - IZreal z = IZreal (- z)%Z.
  Proof.
    intros.
    induction z.
    simpl; ring.
    replace (- Z.pos p)%Z with (Z.neg p) by lia.
    apply IZreal_neg.
    replace (- Z.neg p)%Z with (Z.pos p) by lia.    
    rewrite IZreal_neg.
    ring.
  Qed.
    
  Lemma IZreal_strict_monotone : forall a b, (a < b)%Z -> IZreal a < IZreal b.
  Proof.
    intros.
    apply (real_lt_add_r (-IZreal a)).
    replace (IZreal a + - IZreal a) with real_0 by ring.
    
    rewrite IZreal_opp. 
    rewrite <- IZreal_hom. 
    apply IZreal_pos.
    lia.
  Qed.
   
  Lemma Nreal_monotone : forall a b, (a <= b)%nat -> Nreal a <= Nreal b.
  Proof.
    intros.
    induction H.
    right; auto.
    apply (real_le_le_le _ _ _ IHle).
    simpl.
    left.
    pose proof (real_lt_plus_lt  (Nreal m) _ _ real_1_gt_0).
    replace (Nreal m + real_0) with (Nreal m) in H0 by ring.
    rewrite real_plus_comm.
    exact H0.
  Defined.

  Lemma Nreal_strict_monotone : forall a b, (a < b)%nat -> Nreal a < Nreal b.
  Proof.
    intros.
    induction H.
    simpl.
    apply (real_lt_add_r (- Nreal a)).
    replace (Nreal a + - Nreal a ) with real_0 by ring.
    replace (real_1 + Nreal a + - Nreal a) with real_1 by ring.
    apply real_1_gt_0.
    pose proof (real_lt_plus_lt  (Nreal m) _ _ real_1_gt_0).    
    apply (real_lt_lt_lt _ _ _ IHle).
    simpl.
    pose proof (real_lt_plus_lt  (Nreal m) _ _ real_1_gt_0).
    replace (Nreal m + real_0) with (Nreal m) in H0 by ring.
    rewrite real_plus_comm.
    exact H0.
  Defined.



  Lemma real_le_mult_pos_le : forall (r r1 r2 : Real), real_0 < r -> r1 <= r2 -> r * r1 <= r * r2.
  Proof.
    intros.
    destruct H0.
    left; exact (real_lt_mult_pos_lt _ _ _ H H0).
    rewrite H0.
    right; auto.
  Defined.
  
  Lemma IZreal_mult_hom_pos : forall z1 z2 : Z, (0 <= z2)%Z ->  IZreal (z1 * z2) = IZreal z1 * IZreal z2.
  Proof.
    intro.
    apply natlike_ind.
    replace (z1 * 0)%Z with 0%Z by lia.
    simpl; ring.
    intros.
    replace (z1 * Z.succ x)%Z with (z1 * x + z1)%Z by lia.
    replace (Z.succ x) with (x + 1)%Z by lia.
    rewrite IZreal_hom.
    rewrite IZreal_hom.
    rewrite H0.
    ring.
  Defined.
  

  Lemma IZreal_mult_hom : forall z1 z2 : Z, IZreal (z1 * z2) = IZreal z1 * IZreal z2.
  Proof.
    intros.
    assert (0 <= z2 \/ z2 <= 0)%Z by lia.
    destruct H.
    apply IZreal_mult_hom_pos; auto.
    pose (z := (- z2)%Z).
    assert (z2 = - z)%Z by lia.
    rewrite H0.
    replace (z1 * - z)%Z with (- (z1 * z))%Z by lia.
    rewrite IZ_asym.
    rewrite IZ_asym.
    assert (IZreal (z1 * z) = IZreal z1 * IZreal z).
    apply IZreal_mult_hom_pos; auto.
    lia.
    rewrite H1; ring.    
  Defined.

  Lemma IZreal_le_0 : forall z : Z, (0 <= z)%Z -> real_0 <= (IZreal z).
  Proof.
    apply natlike_ind.
    right; simpl; ring.
    intros.
    replace (Z.succ x) with (x + 1)%Z by lia.
    rewrite IZreal_hom.
    destruct H0.
    pose proof (real_lt_lt_plus_lt _ _ _ _ H0 real_1_gt_0).
    rewrite real_plus_unit in H1.
    left; exact H1.
    rewrite <- H0; left.
    replace (real_0 + IZreal 1) with real_1 by ring.
    apply real_1_gt_0.
  Defined.
  
  
  Lemma IZreal_le_aux : forall z1 z2 : Z, (z1 <= z2)%Z -> (IZreal z1) <= (IZreal z2).
  Proof.
    intros.
    pose (z := (z2 - z1)%Z).
    apply (real_le_add_r (- IZreal z1)).
    replace (IZreal z1 + - IZreal z1) with real_0 by ring.
    rewrite <- IZ_asym.
    rewrite <- IZreal_hom.
    replace (z2 + - z1)%Z with (z2 - z1)%Z by lia.
    fold z.
    assert (0 <= z)%Z by lia.
    apply IZreal_le_0.
    auto.
  Defined.
    
  
  Lemma IZreal_lt_aux : forall z1 z2 : Z, (z1 < z2)%Z -> (IZreal z1) < (IZreal z2).
  Proof.
    intros.
    pose (z := (z2 - z1 - 1)%Z).
    apply (real_lt_add_r (- IZreal (z1 + 1))).
    (* replace (IZreal z1 + - IZreal (z1 + 1)) with (- real_1_) by ring. *)
    rewrite <- IZ_asym.
    rewrite <- IZreal_hom.
    rewrite <- IZreal_hom.

    replace (z2 + - (z1 + 1))%Z with z by lia.
    replace ((z1 + - (z1 + 1)))%Z with ((-1))%Z by lia.
    unfold IZreal at 1.
    unfold IPreal.
    assert (0 <= z)%Z by lia.
    pose proof (IZreal_le_0 z H0).
    apply (real_lt_add_r (real_1)).
    replace (- real_1 + real_1) with real_0 by ring.
    destruct H1.
    pose proof (real_lt_lt_plus_lt _ _ _ _ H1 real_1_gt_0).
    rewrite real_plus_unit in H2.
    exact H2.
    rewrite <- H1.
    rewrite real_plus_unit.
    apply real_1_gt_0.
  Defined.
  

  Lemma IZreal_le : forall z1 z2 : Z, (IZreal z1) <= (IZreal z2) =  (z1 <= z2)%Z.
  Proof.
    intros.
    apply Prop_ext; intro.
    assert (z1 <= z2 \/ z2 < z1)%Z by lia.
    destruct H0; auto.
    pose proof (IZreal_lt_aux _ _ H0).
    contradiction (real_gt_nle _ _ H1 H).
    apply IZreal_le_aux.
    auto.
  Defined.
  
End RealOrder.




(*  Metric and Metric Completeness  *)


Global Hint Resolve real_ge_triv real_le_triv real_lt_le: real.
Global Hint Resolve real_gt_ge: real.
Global Hint Resolve real_eq_le: real.
Global Hint Resolve real_eq_ge: real.
Global Hint Resolve real_eq_plus_eq: real.
Global Hint Resolve real_ge_le: real.
Global Hint Resolve real_le_ge: real.
Global Hint Resolve real_nle_ge: real.
Global Hint Resolve real_nge_le: real.
Global Hint Resolve real_div_distr: real.
Global Hint Resolve real_nlt_triv: real.
Global Hint Resolve real_2_gt_1: real.
Global Hint Resolve real_lt_neq: real.
Global Hint Resolve real_minus_half: real.
Global Hint Resolve real_gt_nle: real.
Global Hint Resolve real_gt_ngt: real.
Global Hint Resolve real_gt_nge: real.
Global Hint Resolve real_ge_ge_eq real_ge_le_eq real_le_ge_eq real_le_le_eq: real.
Global Hint Resolve real_le_lt_lt: real.
Global Hint Resolve real_lt_le_lt: real.
Global Hint Resolve real_le_le_le: real.
Global Hint Resolve real_lt_plus_lt: real.
Global Hint Resolve real_2_pos: real.
Global Hint Resolve real_eq_eq_mult_eq: real.
Global Hint Resolve real_half_gt_zero: real.
Global Hint Resolve real_gt_half: real.
Global Hint Resolve real_gt_minus_gt_zero: real.
Global Hint Resolve real_lt_lt_plus_lt: real. 
Global Hint Resolve padding: real.
Global Hint Resolve real_lt_anti: real.
Global Hint Resolve real_lt_anti_anti: real.
Global Hint Resolve real_inv_unit: real.
Global Hint Resolve real_pos_inv_pos2:real.
Global Hint Resolve Zdouble_minus: arith.
Global Hint Resolve real_lt_mult_r_pos_lt prec_S prec_hom real_lt_mult_pos_move_rr real_lt_mult_pos_move_rl real_gt_mult_pos_move_rl real_lt_mult_pos_move_rr_n prec_pos Nreal_hom Nreal_pos real_gt0_merge_gt real_lt_lt_lt_lt real_gt1_mult_gt_self real_lt_pos_mult_pos_pos real_pos_square_gt_gt real_pos_square_eq_eq: real.
Global Hint Resolve real_gt0_gt0_plus_gt0: real.
Global Hint Resolve d2_pos: real.
Global Hint Resolve W_split : real.
(* Global Hint Resolve M_split : real. *)



Global Hint Resolve Nreal_Npow2_pos prec_Npow2_unit precinv nat_bound_above IZreal_Nreal overlapping IZreal_opp IZreal_strict_monotone Nreal_monotone Nreal_strict_monotone : real.
