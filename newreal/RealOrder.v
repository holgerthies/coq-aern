Require Import Base.
Require Import Kleene.
Require Import RealAxioms.
Require Import RealRing.

Open Scope Real_scope.


Lemma Realge_triv : forall z, z >= z.
Proof.
  intro z;  right; exact eq_refl.
Qed.
Hint Resolve Realge_triv: Realiny.

Lemma Realle_triv : forall z, z <= z.
Proof.
  intro z; right; exact eq_refl.
Qed.
Hint Resolve Realle_triv: Realiny.

Lemma Reallt_le : forall z1 z2, z1<z2 -> z1 <= z2.
Proof.
  intros z1 z2 p; left; exact p.
Qed.
Hint Resolve Reallt_le: Realiny.

Lemma Realgt_ge : forall z1 z2, z1>z2 -> z1 >= z2.
Proof.
  intros z1 z2 p; left; exact p.
Qed.
Hint Resolve Realgt_ge: Realiny.

Lemma Realeq_le : forall z1 z2, z1 = z2 -> z1 <= z2.
Proof.
  intros z1 z2 p; rewrite p; right; exact eq_refl.
Qed.
Hint Resolve Realeq_le: Realiny.

Lemma Realeq_ge : forall z1 z2, z1 = z2 -> z1 >= z2.
Proof.
  intros z1 z2 p; rewrite p; right; exact eq_refl.
Qed.
Hint Resolve Realeq_ge: Realiny.

Lemma Realeq_plus_eq : forall z1 z2 z3, z1 = z2 -> z1 + z3 = z2 + z3.
Proof.
  intros z1 z2 z3 p.
  rewrite p.
  exact eq_refl.
Qed.
Hint Resolve Realeq_plus_eq: Realiny.

Lemma Realge_le : forall z1 z2, z1 >= z2 -> z2 <= z1.
Proof.
  intros z1 z2 p.
  destruct p.
  left; auto.
  right; rewrite H; exact eq_refl.
Qed.
Hint Resolve Realge_le: Realiny.

Lemma Realle_ge : forall z1 z2, z1 <= z2 -> z2 >= z1.
Proof.
  intros z1 z2 p.
  destruct p.
  left; auto.
  right; rewrite H; exact eq_refl.
Qed.
Hint Resolve Realle_ge: Realiny.


  
  
Lemma Realnle_ge : forall z1 z2, ~ z1 <= z2 -> z1 > z2.
Proof.
  intros z1 z2 q.
  intuition.
  destruct (Realtotal_order z1 z2).
  assert (z1 <= z2).
  left; exact H.
  contradict (q H0).
  destruct H.
  assert (z1 <= z2).
  right; exact H.
  contradict (q H0).
  exact H.
Qed.
Hint Resolve Realnle_ge: Realiny.
  
Lemma Realdiv_distr : forall z1 z2 z3, forall p : z3<>Real0,  z1/p + z2/p = (z1+z2)/p.
Proof.
  intros z1 z2 z3 nz.
  replace ((z1+z2)/nz) with ((z1+z2)*/nz) by auto.
  rewrite Realmult_comm, Realmult_plus_distr.
  unfold Realdiv.
  ring.
Qed.
Hint Resolve Realdiv_distr: Realiny.

Lemma Realle_plus_le : forall z1 z2 z3, z1 <= z2 -> z1+z3 <= z2+z3.
Proof.
  intros z1 z2 z3 p.
  destruct p.
  apply (Reallt_plus_lt z3 z1 z2) in H.
  replace (z1+z3) with (z3+z1) by ring;
    replace (z2+z3) with (z3+z2) by ring; left; exact H.
  rewrite H; right; auto with Realiny.
Qed.
Hint Resolve Realle_plus_le: Realiny.

  
Lemma Realnlt_triv : forall x, ~ x < x.
Proof.
  intro x.
  intuition.
  pose proof (Reallt_nlt x x H) as H1.
  contradict H.
  intuition.
Qed.
Hint Resolve Realnlt_triv: Realiny.



Lemma Real2_gt_Real1 : Real2 > Real1.
Proof.
  pose proof (Real1_gt_Real0).
  pose proof (Reallt_plus_lt Real1 Real0 Real1 H).
  ring_simplify in H0.
  exact H0.
Qed.
Hint Resolve Real2_gt_Real1: Realiny.




Lemma Reallt_neq : forall z1 z2, z1 < z2 -> z1 <> z2.
Proof.
  red.
  intros z1 z2 p q.
  apply (Realnlt_triv z1).
  pattern z1 at 2; rewrite q; trivial.
Qed.
Hint Resolve Reallt_neq: Realiny.

Definition dReal2 := Real2_neq_Real0.
Lemma Realminus_half : forall z, z - z/dReal2 = z/dReal2.
Proof.
  intro z.
  pose proof Real2_neq_Real0.
  assert (z = z * Real2 / dReal2).
  replace (z*Real2/dReal2) with (z*Real2*/dReal2) by auto.
  replace (z*Real2*/dReal2) with (z * (Real2 * /dReal2)) by ring.
  replace (z * (Real2 * /dReal2)) with (z * (/dReal2 * Real2)) by ring.
  rewrite (Realmult_inv Real2 dReal2).
  ring.
  rewrite H0 at 1.
  replace ( z * Real2 / dReal2 - z / dReal2) with ( z * Real2 */ dReal2 - z */ dReal2) by auto.
  replace (( z * Real2 */ dReal2 - z */ dReal2)) with ( z * Real2 */ dReal2 + (- z) */ dReal2) by ring.
  replace (z/dReal2) with (z*/dReal2) by auto.
  replace ( z * Real2 * / dReal2 + - z * / dReal2) with ( /dReal2 * (z * Real2)  + - z * / dReal2) by ring.
  replace ( / dReal2 * (z * Real2) + - z * / dReal2) with ( / dReal2 * (z * Real2) + /dReal2 * (-z)) by ring.
  rewrite <- (Realmult_plus_distr (/dReal2) (z*Real2) (-z)).
  replace (z*Real2 +-z) with (z*(Real1+Real1) -z) by auto.
  replace (z*(Real1+Real1) -z) with z by ring.
  ring.
Qed.
Hint Resolve Realminus_half: Realiny.
  
Lemma Realgt_nle: forall z1 z2, z1 > z2 -> ~ z1 <= z2.
Proof.
  intros z1 z2 p q; destruct q as [q1 | q2].
  contradict p; exact (Reallt_nlt z1 z2 q1).
  rewrite q2 in p; contradict p; auto with Realiny.
Qed.
Hint Resolve Realgt_nle: Realiny.

Lemma Realgt_ngt : forall z1 z2, z1 > z2 -> ~ z2 > z1.
Proof.
  intros z1 z2 p.
  contradict p; exact (Reallt_nlt z1 z2 p).
Qed.
Hint Resolve Realgt_ngt: Realiny.

Lemma Realgt_nge : forall z1 z2, z1 > z2 -> ~ z2 >= z1.
Proof.
  intros z1 z2 p q; destruct q as [q1 | q2].
  contradict p; exact (Reallt_nlt z1 z2 q1).
  rewrite q2 in p; contradict p; auto with Realiny.
Qed.
Hint Resolve Realgt_nge: Realiny.

Lemma Realge_ge_eq : forall z1 z2, z1 >= z2 -> z2 >= z1 -> z1 = z2.
Proof.
  intros z1 z2 o1 o2.
  destruct o1.
  contradict o2.
  auto with Realiny.
  exact H.
Qed.

Lemma Realle_le_eq : forall z1 z2, z1 <= z2 -> z2 <= z1 -> z1 = z2.
Proof.
  intros z1 z2 o1 o2.
  destruct o1.
  contradict o2.
  auto with Realiny.
  exact H.
Qed.

Lemma Realle_ge_eq : forall z1 z2, z1 <= z2 -> z1 >= z2 -> z1 = z2.
Proof.
  intros z1 z2 o1 o2.
  destruct o1.
  contradict o2.
  auto with Realiny.
  exact H.
Qed.

Lemma Realge_le_eq : forall z1 z2, z1 >= z2 -> z1 <= z2 -> z1 = z2.
Proof.
  intros z1 z2 o1 o2.
  destruct o1.
  contradict o2.
  auto with Realiny.
  exact H.
Qed.
Hint Resolve Realge_ge_eq Realge_le_eq Realle_ge_eq Realle_le_eq: Realiny.


Lemma Realle_lt_lt : forall z1 z2 z3, z1<=z2 -> z2 < z3 -> z1<z3.
Proof.
  intros z1 z2 z3 p1 p2.
  destruct (Realtotal_order z1 z2) as [q1 |[q2| q3]].
  apply (Reallt_lt_lt z1 z2 z3); auto with Realiny.
  rewrite q2; exact p2.
  destruct p1.
  contradict q3; apply (Reallt_nlt); exact H.
  rewrite H in q3; contradict q3; auto with Realiny.
Qed.
Hint Resolve Realle_lt_lt: Realiny.

Lemma Reallt_le_lt : forall z1 z2 z3, z1 < z2 -> z2 <= z3 -> z1 < z3.
Proof.
  intros z1 z2 z3 p1 p2.
  destruct p2 as [q1| q2].
  exact (Reallt_lt_lt z1 z2 z3 p1 q1).
  rewrite<- q2; exact p1.
Qed.
Hint Resolve Reallt_le_lt: Realiny.

Lemma Realle_le_le : forall z1 z2 z3, z1 <= z2 -> z2 <= z3 -> z1 <= z3.
Proof.
  intros z1 z2 z3 p1 p2.
  destruct p1 as [p11 | p12]; destruct p2 as [p21 | p22]; auto with Realiny.
  left; exact (Reallt_lt_lt z1 z2 z3 p11 p21).
  rewrite p22 in p11; left; exact p11.
  rewrite p12; left; exact p21.
  rewrite p12; rewrite <- p22; right; exact eq_refl.
Qed.
Hint Resolve Realle_le_le: Realiny.

Lemma Reallt_plus_r_lt : forall r r1 r2:Real, r1 < r2 -> r1 + r < r2 + r.
Proof.
  intros r r1 r2 p;
    replace (r1+r) with (r+r1) by ring;
    replace (r2+r) with (r+r2) by ring;
    auto with Realiny.
Qed.
Hint Resolve Reallt_plus_lt: Realiny.


Lemma Real2_pos : Real2 > Real0.
Proof.
  pose proof (Real1_gt_Real0).
  pose proof (Reallt_plus_r_lt Real1 Real0 Real1 H).
  replace (Real0+Real1) with Real1 in H0 by ring.
  pose proof (Reallt_lt_lt Real0 Real1 (Real1 + Real1) H H0).
  auto.
Qed.
Hint Resolve Real2_pos: Realiny.

Lemma Realeq_eq_mult_eq : forall a b c d, a = b -> c = d -> a*c = b*d.
Proof.
  intros.
  rewrite H; rewrite H0; exact eq_refl.
Qed.
Hint Resolve Realeq_eq_mult_eq: Realiny.

Lemma Realhalf_gt_zero : forall a, a > Real0 -> a / dReal2 > Real0. 
Proof.
  intros a p.
  pose proof Real2_pos.
  destruct (Realtotal_order (a/dReal2) Real0) as [p1 |[p2|p3]].
  apply (Reallt_mult_pos_lt Real2 (a/dReal2) Real0) in p1.
  replace (Real2*(a/dReal2)) with (Real2*(a*/dReal2)) in p1 by auto.
  replace (Real2*(a*/dReal2)) with (a *(/dReal2 * Real2)) in p1 by ring.
  rewrite (Realmult_inv Real2 dReal2) in p1.
  ring_simplify in p1.
  contradict p1.
  auto with Realiny.
  exact Real2_pos.
  rewrite p2.
  pose proof (Realeq_eq_mult_eq (a/dReal2) Real0 Real2 Real2 p2 eq_refl).
  replace (a/dReal2*Real2) with (a*/dReal2*Real2) in H0 by auto.
  replace (a*/dReal2*Real2) with (a*(/dReal2*Real2)) in H0 by ring.
  rewrite (Realmult_inv Real2 dReal2) in H0.
  ring_simplify in H0.
  rewrite H0 in p.
  contradict p; auto with Realiny.
  exact p3.
Qed.
Hint Resolve Realhalf_gt_zero: Realiny.


Lemma Realgt_half : forall a, a > Real0 -> a > a / dReal2.
Proof.
  intros a p.
  pose proof (Realhalf_gt_zero a p).
  apply (Reallt_plus_lt (a/dReal2) Real0 (a/dReal2)) in H.
  rewrite (Realdiv_distr a a Real2 dReal2) in H.
  ring_simplify in H.
  replace (a + a) with (Real1 * a + Real1 * a) in H by ring.
  replace (Real1 * a + Real1 * a) with ((Real1+Real1)*a) in H by ring.
  replace (Real1+Real1) with Real2 in H by auto.
  replace (Real2*a/dReal2) with (Real2*a*/dReal2) in H by auto.
  replace (Real2*a*/dReal2) with (a*(/dReal2*Real2)) in H by ring.
  rewrite (Realmult_inv Real2 dReal2) in H.
  ring_simplify in H.
  exact H.
Qed.
Hint Resolve Realgt_half: Realiny.
  
Lemma Realgt_minus_gt_zero : forall a b : Real, a > b -> a - b > Real0.
Proof.
  intros a b p.
  replace (a-b) with (-b+a) by ring.
  replace Real0 with (-b+b) by ring.
  apply Reallt_plus_lt; auto with Realiny.
Qed.
Hint Resolve Realgt_minus_gt_zero: Realiny.


Lemma Reallt_lt_plus_lt : forall r1 r2 r3 r4, r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros r1 r2 r3 r4 p1 p2.
  pose proof (Reallt_plus_r_lt r3 r1 r2 p1).
  assert (r2+r3 < r2+r4).
  auto with Realiny.
  exact (Reallt_lt_lt (r1+r3) (r2+r3) (r2+r4) H H0).
Qed.
Hint Resolve Reallt_lt_plus_lt: Realiny. 

Definition padding : forall a b : Real, a > b -> {ε : Real | ε > Real0 /\ a = ε + b}.
Proof.
  intros a b p; exists (a - b).
  constructor 1; auto with Realiny; ring.
Defined.
Hint Resolve padding: Realiny.


Lemma Reallt_anti : forall z1 z2, z1<z2 -> -z2< -z1.
Proof.
  intros z1 z2 p.
  apply (Reallt_plus_lt (-z1-z2) z1 z2) in p.
  ring_simplify in p; exact p.
Qed.
Hint Resolve Reallt_anti: Realiny.

Lemma Reallt_anti_anti : forall z1 z2, - z1 < - z2 -> z2< z1.
Proof.
  intros z1 z2 p.
  replace z2 with (- - z2) by ring.
  replace z1 with (- - z1) by ring.
  apply Reallt_anti.
  exact p.
Qed.
Hint Resolve Reallt_anti_anti: Realiny.



Definition dReal1 := Real1_neq_Real0.
Lemma Realinv_unit : forall z, z / dReal1 = z.
Proof.
  intro.
  replace z with (z*Real1) by ring.
  replace (z*Real1/dReal1) with (z*Real1*/dReal1) by auto.
  replace (z*Real1*/dReal1) with (z*(/dReal1*Real1)) by ring.
  replace (/dReal1*Real1) with Real1 by auto with Realiny.
  exact eq_refl.
Qed.
Hint Resolve Realinv_unit: Realiny.


Lemma square_pos : forall z, z <> Real0 -> z *z > Real0.
Proof.
  intros.
  destruct (Realtotal_order z Real0) as [a|[b|c]].
  assert (z+(-z) < Real0+(-z)).
  apply (Reallt_plus_r_lt); exact a.
  ring_simplify in H0.
  pose proof (Reallt_mult_pos_lt (-z) Real0 (-z) H0 H0).
  ring_simplify in H1.
  ring_simplify.
  exact H1.
  contradict H; exact b.
  pose proof (Reallt_mult_pos_lt z Real0 z c c) as q; ring_simplify in q; ring_simplify; exact q.
Qed.


Lemma Realpos_inv_pos2 : forall z, forall p :  z > Real0, / (Realgt_neq z Real0 p) > Real0.
Proof.
  intros z p.
  pose proof (square_pos (/ (Realgt_neq z Real0 p))).
  assert (/(Realgt_neq z Real0 p) <> Real0) as H10.
  intro.
  pose proof (Realmult_inv z).
  assert (z <> Real0) as H12 by auto with Realiny.
  pose proof (H1  H12) as H2.
  pose proof (neq_path z Real0 H12 (Realgt_neq z Real0 p)) as path.
  rewrite path in H2.
  rewrite H0 in H2; ring_simplify in H2; contradict H2; auto with Realiny.
  pose proof (H H10) as H0.
  pose proof (Reallt_mult_pos_lt (/(Realgt_neq z Real0 p)*/(Realgt_neq z Real0 p)) Real0 z H0 p).
  replace (/(Realgt_neq z Real0 p)*/(Realgt_neq z Real0 p)*z) with (/(Realgt_neq z Real0 p)*(/(Realgt_neq z Real0 p)*z))  in H1 by ring.

  assert (z <> Real0) as H12 by auto with Realiny.
  replace (/(Realgt_neq z Real0 p) *z) with Real1 in H1 by auto with Realiny.
  
  ring_simplify in H1.
  exact H1.
Qed.
Hint Resolve Realpos_inv_pos2:Realiny.

Lemma Realpos_inv_pos : forall z, forall p : z > Real0, forall q : z <> Real0, / q > Real0.
Proof.
  intros.
  rewrite (neq_path z Real0 q (Realgt_neq z Real0 p)); auto with Realiny.
Qed.
Hint Resolve Realpos_inv_pos : Realiny.

Lemma Reallt_mult_r_pos_lt : forall z1 z2 z3, z3 > Real0 -> z1 < z2 -> z1 * z3 < z2 * z3.
Proof.
  intros.
  replace (z1*z3) with (z3*z1) by ring.
  replace (z2*z3) with (z3*z2) by ring.
  auto with Realiny.
Qed.
Hint Resolve Reallt_mult_r_pos_lt: Realiny.


Lemma prec_S : forall n, prec (S n) < prec n.
Proof.
  intro n.
  induction n; simpl.
  replace (Real1+Real1) with Real2 by auto.
  exact (Realgt_half Real1 Real1_gt_Real0).
  simpl in IHn.
  replace (Real1+Real1) with Real2 by auto.
  replace (Real1+Real1) with Real2 in IHn by auto.
  pose proof (Real2_pos).
  assert (/dReal2 > Real0) by auto with Realiny.
  apply (Reallt_mult_r_pos_lt (prec n / dReal2) (prec n)  (/dReal2) H0) in IHn.
  auto.
Qed.
Hint Resolve prec_S: Realiny.

Lemma prec_hom : forall n m, prec (n+m) = prec n * prec m.
Proof.
  intros n m.
  induction n.
  simpl; ring.
  rewrite (plus_Sn_m n m).
  simpl.
  rewrite IHn.
  unfold Realdiv.
  ring.
Qed.      
Hint Resolve prec_hom: Realiny.

Definition dg0 {z:Real}(p:z>Real0) : z <> Real0 :=  Realgt_neq z Real0 p.
Lemma Reallt_mult_pos_move_rr : forall a b c, forall p :a > Real0, b*a < c -> b < c / (dg0 p).
Proof.
  intros a b c p q.
  assert (/ (dg0 p) > Real0) by auto with Realiny.
  apply (Reallt_mult_r_pos_lt (b*a)  c (/(dg0 p)) H) in q.
  replace (b*a*/(dg0 p)) with (b*(/(dg0 p)*a)) in q by ring.
  assert (a <> Real0) by auto with Realiny.
  replace (/(dg0 p)*a) with Real1 in q by auto with Realiny.
  ring_simplify in q.
  auto with Realiny.
Qed.
Hint Resolve Reallt_mult_pos_move_rr: Realiny.

Lemma Reallt_mult_pos_move_rl : forall a b c, forall p :a > Real0, a*b < c -> b < c / (dg0 p).
Proof.
  intros a b c p q.
  replace (a*b) with (b*a) in q by ring.
  apply Reallt_mult_pos_move_rr; auto. 
Qed.
Hint Resolve Reallt_mult_pos_move_rl: Realiny.

Lemma Realgt_mult_pos_move_rl : forall a b c, forall p:a > Real0,  a*b > c -> b > c / (dg0 p).
  intros a b c p q.
  assert (/ (dg0 p) > Real0) by auto with Realiny.
  replace (a*b) with (b*a) in q by ring.
  apply (Reallt_mult_r_pos_lt c (b*a) (/ (dg0 p)) H) in q.
  replace (b*a*/(dg0 p)) with (b*(/(dg0 p)*a)) in q by ring.
  assert (a <> Real0) by auto with Realiny.
  replace (/(dg0 p)*a) with Real1 in q by auto with Realiny.
  ring_simplify in q.
  auto with Realiny.
Qed.
Hint Resolve Realgt_mult_pos_move_rl: Realiny.

Lemma Reallt_mult_pos_move_rr_n
  : forall (a b c : Real) (p : a > Real0) (q : a <> Real0), b * a < c -> b < c / q.
Proof.
  intros.
  pose proof (neq_path a Real0 q (Realgt_neq a Real0 p)).
  rewrite H0.
  apply Reallt_mult_pos_move_rr; exact H.
Qed.
Hint Resolve Reallt_mult_pos_move_rr_n: Realiny.


(** prec embedding is always positive **)
Lemma prec_pos : forall n, prec n > Real0.
Proof.
  intro.
  induction n.
  + auto with Realiny.
  + simpl.
    replace (Real1+Real1) with (Real2) by auto.
    auto with Realiny.
Defined.
Hint Resolve prec_pos: Realiny.


Lemma NReal_hom : forall n m, NReal (n+m) = NReal n + NReal m.
Proof.
  intros n m.
  induction n.
  simpl.
  auto with Realiny.
  assert (S n + m = S (n+m))%nat as H by intuition.
  rewrite H.
  assert (forall n, NReal (S n) = Real1 + NReal n) by (intro; simpl; exact eq_refl).
  rewrite (H0 n). rewrite (H0 ((n+m)%nat)).
  rewrite IHn; ring.
Qed.
Hint Resolve NReal_hom: Realiny.

Lemma NReal_pos : forall n, (n>0)%nat -> NReal n > Real0.
Proof.
  intros n p.
  induction n.
  contradict p; exact (gt_irrefl 0).
  assert (S n = 1+n)%nat as q; intuition.
  rewrite q.
  rewrite (NReal_hom 1%nat n).
  pose proof (Real1_gt_Real0) as gtg.
  destruct n.
  simpl; ring_simplify; auto with Realiny.

  pose proof (IHn (gt_Sn_O n)).
  pose proof (Reallt_lt_plus_lt Real0 Real1 Real0 (NReal (S n)) gtg H) as H1; ring_simplify in H1.
  replace (NReal (S n) + Real1) with (Real1 + NReal (S n)) in H1 by ring.
  assert (NReal 1 = Real1). simpl. ring.
  rewrite H0; exact H1.
Qed.
Hint Resolve NReal_pos: Realiny.


Lemma NReal_S : forall n, NReal (S n) = Real1 + NReal n.
Proof.
  intro n.
  replace (S n)%nat with (1 + n)%nat by intuition.
  rewrite (NReal_hom 1%nat n); simpl; ring.
Qed.

Lemma NReal_mult : forall n m, NReal (n * m) = NReal n * NReal m.
Proof.
  intros n m.
  induction n.
  simpl; ring.
  simpl.
  rewrite NReal_hom .
  rewrite IHn.
  ring.
Qed.


Lemma IZReal_asym : forall n, IZReal (-n) = - IZReal n.
Proof.
  intro n.
  unfold IZReal.
  unfold IPReal.
  unfold IPReal_2.  
  destruct n; simpl; ring.
Qed.
Require Import Coq.PArith.BinPos.
Lemma IZReal_s1 : forall p, IZReal (Z.pos (p~0)) = Real2 * (IZReal (Z.pos p)).
Proof.
  intro.
  unfold IZReal.
  simpl.
  unfold IPReal.
  
  unfold IPReal_2.

  destruct p;
  replace (Real1+Real1) with Real2 by auto; ring_simplify;
    exact eq_refl.
Qed.

Lemma IZReal_s2 : forall p, IZReal (Z.pos (p~1)) = Real2 * (IZReal (Z.pos p)) + Real1.
Proof.
  intro.
  unfold IZReal.
  unfold IPReal.  
  unfold IPReal_2.
  destruct p;
  replace (Real1+Real1) with Real2 by auto; ring_simplify; exact eq_refl.
Qed.

Lemma IPReal2_NReal : forall p, Real2 * NReal (Pos.to_nat p) = IPReal_2 p.
Proof.
  intro p.
  induction p.
  + rewrite Pos2Nat.inj_xI.
    rewrite NReal_S.
    ring_simplify.
    rewrite NReal_mult.
    ring_simplify.
    replace (Real2* NReal 2 * NReal (Pos.to_nat p)) with (NReal 2 * (Real2 * NReal (Pos.to_nat p))) by ring.
    rewrite IHp.
    simpl.
    ring_simplify.
    replace (Real1+Real1) with Real2 by auto.
    ring.

  + rewrite Pos2Nat.inj_xO.
    rewrite NReal_mult.
    simpl NReal.
    ring_simplify.
    replace ((Real1+Real1)*Real2*NReal (Pos.to_nat p)) with ((Real1+Real1) *(Real2 *NReal (Pos.to_nat p))) by ring.
    rewrite IHp.
    simpl; exact eq_refl.

  + simpl; ring_simplify; auto.
Qed.

Lemma IPReal_NReal : forall p, NReal (Pos.to_nat p) = IPReal p.
Proof.
  intro p.
  induction p.

  + unfold IPReal.
    rewrite <- IPReal2_NReal.
    rewrite Pos2Nat.inj_xI.
    rewrite NReal_S, NReal_mult.
    simpl NReal; ring_simplify.
    replace (Real1+Real1) with Real2 by auto.
    ring.

  + unfold IPReal.
    rewrite <- IPReal2_NReal.
    rewrite Pos2Nat.inj_xO.
    rewrite  NReal_mult.
    simpl NReal; ring_simplify.
    replace (Real1+Real1) with Real2 by auto.
    ring.

  + simpl; ring_simplify; auto.
Qed.

Lemma IZReal_NReal : forall p, NReal (Pos.to_nat p) = IZReal (Z.pos p).
Proof.
  intro p.
  rewrite IPReal_NReal.
  unfold IZReal; exact eq_refl.
Qed.

Lemma IZReal_pos_pos : forall p1 p2, IZReal (Z.pos p1 + Z.pos p2) = IZReal (Z.pos p1) + IZReal (Z.pos p2).
Proof.
  intros p1 p2.
  replace (Z.pos p1 + Z.pos p2)%Z with (Z.pos (p1+p2))%Z by auto.
  rewrite<- IZReal_NReal.
  rewrite Pos2Nat.inj_add.
  rewrite NReal_hom.
  rewrite IZReal_NReal.
  rewrite IZReal_NReal.
  exact eq_refl.
Qed.

Lemma IZReal_neg : forall p, IZReal (Z.neg p) = - IZReal (Z.pos p).
Proof.
  intro p.
  unfold IZReal; auto.
Qed.
Lemma Realeq_plus_cancel : forall a b c, b + a = c + a -> b = c.
Proof.
  intros a b c p.
  apply (Realeq_plus_eq (b+a) (c+a) (-a)) in p.
  ring_simplify in p; exact p.
Qed.

  
Lemma IZReal_pos_neg : forall p1 p2, IZReal (Z.pos p1 + Z.neg p2) = IZReal (Z.pos p1) + IZReal (Z.neg p2).
Proof.
  intros p1 p2.
  destruct (Pos.compare_spec p1 p2).
  +
    rewrite H; simpl.
    rewrite IZReal_neg.
    rewrite Z.pos_sub_diag.
    replace (IZReal 0) with Real0 by auto.
    ring.
  +
    simpl.
    rewrite (Z.pos_sub_lt p1 p2 H).
    rewrite IZReal_neg; rewrite IZReal_neg.
    rewrite<- IZReal_NReal.
    rewrite<- IZReal_NReal.
    rewrite<- IZReal_NReal.
    ring_simplify.
    assert (NReal (Pos.to_nat p2) = NReal( Pos.to_nat p2)) as H1 by exact eq_refl.
    apply (Realeq_plus_cancel (NReal (Pos.to_nat (p2-p1)) + NReal (Pos.to_nat p2))).
    ring_simplify.
    rewrite <- NReal_hom.
    rewrite Pos2Nat.inj_sub; auto.
    rewrite Nat.sub_add; auto.
    apply (Pos2Nat.inj_lt p1 p2) in H.
    apply Nat.lt_le_incl; auto.

  +
    simpl.
    rewrite (Z.pos_sub_gt p1 p2 H).
    rewrite IZReal_neg.
    rewrite <- IZReal_NReal.
    rewrite <- IZReal_NReal.
    rewrite <- IZReal_NReal.
    apply (Realeq_plus_cancel (NReal (Pos.to_nat p2))).
    ring_simplify.
    rewrite <- NReal_hom.
    rewrite Pos2Nat.inj_sub; auto.
    rewrite Nat.sub_add; auto.
    apply (Pos2Nat.inj_lt p2 p1) in H.
    apply Nat.lt_le_incl; auto.
Qed.

Lemma IZReal_neg_pos : forall p1 p2, IZReal (Z.neg p1 + Z.pos p2) = IZReal (Z.neg p1) + IZReal (Z.pos p2).
Proof.
  intros p1 p2.
  replace (Z.neg p1 + Z.pos p2)%Z with (Z.pos p2 + Z.neg p1)%Z by auto.
  rewrite IZReal_pos_neg; ring.
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
Hint Resolve Zdouble_minus: arith.

Lemma IZReal_hom : forall n m, IZReal (n+m) = IZReal n + IZReal m.
Proof.
  intros n m.
  destruct n; destruct m; try apply IZReal_pos_pos; try apply IZReal_pos_neg; try apply IZReal_neg_pos; try simpl; try ring.
  rewrite IZReal_neg.
  rewrite IZReal_neg.
  rewrite IZReal_neg.
  replace (Z.pos (p+p0)) with (Z.pos p + Z.pos p0)%Z by auto.
  rewrite (IZReal_pos_pos).
  ring.
Qed.  

Lemma IZReal_pos : forall z, (z > 0)%Z -> IZReal z > Real0.
Proof.
  intros z p.
  destruct z.
  + contradict p; apply Zgt_irrefl.
  +
    rewrite <- IZReal_NReal.
    apply NReal_pos.
    exact (Pos2Nat.is_pos p0).
  +
    contradict p; apply Zgt_asym; apply Z.lt_gt; exact (Pos2Z.neg_is_neg p0).
Qed.




Lemma Real1_inv_Real1 : /dReal1 = Real1.
Proof.
  replace (/dReal1) with (/dReal1 *Real1) by ring.
  pose proof (Real1_neq_Real0).
  replace (/dReal1 *Real1) with Real1 by auto with Realiny.
  exact eq_refl.
Qed.

Lemma div_Real1 : forall z, z/dReal1 = z.
Proof.
  intro.
  replace (z/dReal1) with (z*/dReal1) by auto.
  rewrite Real1_inv_Real1; ring.
Qed.
Lemma Reallt_mult_pos_cancel : forall z z1 z2, z > Real0 -> z1 * z < z2 * z -> z1 < z2.
Proof.
  intros z z1 z2 p q.
  assert (z <> Real0); auto with Realiny.  
  
  apply (Reallt_mult_r_pos_lt (z1*z) (z2 *z) (/H)) in q; auto with Realiny.
  rewrite Realmult_assoc in q.
  rewrite Realmult_assoc in q.
  rewrite (Realmult_comm z (/H)) in q.
  rewrite (Realmult_inv z H) in q.
  ring_simplify in q; exact q.
Qed.

Lemma Realgt0_merge_gt : forall z1 z2, z1 > Real0 -> z2 > Real0 -> z1 + z2 > Real0.
Proof.
  intros.
  pose proof (Reallt_lt_plus_lt Real0 z1 Real0 z2 H H0).
  ring_simplify in H1; exact H1.
Qed.
Hint Resolve Realgt0_merge_gt: Realiny.


Lemma Reallt_lt_lt_lt : forall a b c d, a<b -> b<c -> c<d -> a<d.
Proof.
  intros a b c d p q r.
  exact (Reallt_lt_lt a b d p (Reallt_lt_lt b c d q r)).
Qed.
Hint Resolve Reallt_lt_lt_lt: Realiny.


Lemma gt1_mult_gt_self : forall z1 z2, z1 > Real1 -> z2 > Real0 -> z1 * z2 > z2.
Proof.
  intros z1 z2 p q.
  pose proof (padding z1 Real1 p) as [epsilon [c1 c2]].
  rewrite c2.
  ring_simplify.
  replace z2 with (Real0 + z2) at 3 by ring.
  apply Reallt_plus_r_lt.
  pose proof (Reallt_mult_pos_lt epsilon Real0 z2 c1 q).
  ring_simplify in H; exact H.
Qed.
Hint Resolve  gt1_mult_gt_self: Realiny.


Lemma Reallt_pos_mult_pos_pos : forall z1 z2, z1 > Real0 -> z2 > Real0 -> z1 * z2 > Real0.
Proof.
  intros.
  pose proof (Reallt_mult_pos_lt z1 Real0 z2 H H0).
  replace (z1*Real0) with Real0 in H1 by ring; auto.
Qed.
Hint Resolve Reallt_pos_mult_pos_pos: Realiny.
  
Lemma pos_square_gt_gt : forall z1 z2, z1 > Real0 -> z2 > Real0 -> z1*z1 > z2*z2 -> z1 > z2.
Proof.
  intros z1 z2 q p r.
  destruct (Realtotal_order z1 z2) as [s|[s|s]].
  + pose proof (Reallt_mult_pos_lt z1 z1 z2 q s).
    pose proof (Reallt_mult_r_pos_lt z1 z2 z2 p s).
    pose proof (Reallt_lt_lt (z1*z1) (z1*z2) (z2*z2) H H0).
    contradict H1; auto with Realiny.

  + rewrite s in r; contradict r; auto with Realiny.

  + exact s.
Qed.
Hint Resolve pos_square_gt_gt: Realiny.

Lemma pos_square_eq_eq : forall z1 z2, z1 > Real0 -> z2 > Real0 -> z1*z1 = z2*z2 -> z1 = z2.
Proof.
  intros.
  destruct (Realtotal_order z1 z2) as [p|[p|p]].
  
  pose proof (Reallt_mult_pos_lt z1 z1 z2 H p).
  pose proof (Reallt_mult_r_pos_lt z1 z2 z2 H0 p).
  pose proof (Reallt_lt_lt (z1*z1) (z1*z2) (z2*z2) H2 H3).
  rewrite H1 in H4;
    contradict H4; auto with Realiny.
  auto.
  pose proof (Reallt_mult_pos_lt z2 z2 z1 H0 p).
  pose proof (Reallt_mult_r_pos_lt z2 z1 z1 H p).
  pose proof (Reallt_lt_lt (z2*z2) (z2*z1) (z1*z1) H2 H3).
  rewrite H1 in H4;
    contradict H4; auto with Realiny.
Qed.
Hint Resolve pos_square_eq_eq: Realiny.


Lemma gt0_gt0_plus_gt0 : forall z1 z2, z1 > Real0 -> z2 > Real0 -> z1 + z2 > Real0.
Proof.
  intros.
  auto with Realiny.
Qed.
Hint Resolve gt0_gt0_plus_gt0: Realiny.

Lemma Reallt_le_lt_lt : forall z1 z2 z3 z4, z1 <z2 -> z2 <= z3 -> z3 < z4 -> z1 < z4.
  intros.
  apply (Reallt_le_lt z1 z2 z3 H) in H0.
  exact (Reallt_lt_lt z1 z3 z4 H0 H1).
Qed.

Lemma Reallt_lt_le_lt : forall z1 z2 z3 z4, z1 <z2 -> z2 < z3 -> z3 <= z4 -> z1 < z4.
  intros.
  apply (Reallt_lt_lt z1 z2 z3 H) in H0.
  exact (Reallt_le_lt z1 z3 z4 H0 H1).
Qed.

Lemma dReal2_pos : Real0 < / dReal2.
Proof.
  assert (/dReal2 > Real0); auto with Realiny.  
Qed.
Hint Resolve dReal2_pos: Realiny.
  
           
Lemma Realeq_mult_eq : forall z z1 z2, z1 = z2 -> z*z1=z*z2.
Proof.
  intros.
  auto with Realiny.
Qed.


Lemma W_split : forall x y ε, ε > Real0 -> x>y-ε \/ y>x-ε.
Proof.
  intros x y ε p.
  destruct (Realtotal_order x y) as [H|[H|H]].
  + apply (Reallt_plus_lt (-ε + x) Real0 ε) in p.
    ring_simplify in p.
    apply (Reallt_lt_lt (-ε + x) x y p) in H.
    replace (-ε+x) with (x-ε) in H by ring; right; exact H.
  + rewrite H.
    left.
    apply (Reallt_plus_lt (y-ε) Real0 ε) in p.
    ring_simplify in p.
    exact p.
  + apply (Reallt_plus_lt (-ε + y) Real0 ε) in p.
    ring_simplify in p.
    apply (Reallt_lt_lt (-ε + y) y x p) in H.
    replace (-ε+y) with (y-ε) in H by ring; left; exact H.
Defined.
Hint Resolve W_split : Realiny.
(** string but multivalued split **)
Lemma M_split : forall x y ε, ε > Real0 -> M ({x>y-ε} + {y>x-ε}).
Proof.
  intros x y ε p.  
  apply (choose (x > y-ε) (y > x-ε)); auto with Realiny.
Defined.

Hint Resolve M_split : Realiny.

  
Lemma not_bounded : forall x, [ y | y > x ].
Proof.
  intro x.
  apply (mjoin (x>Real0-Real1) (Real0>x-Real1)).
  + intros [c1|c2].
    ++ exists (x+Real1).
       pose proof (Real1_gt_Real0).
       apply (Reallt_plus_lt x Real0 Real1) in H.
       ring_simplify in H.
       exact H.
    ++ exists (x+Real2).
       pose proof (Real2_pos).
       apply (Reallt_plus_lt x Real0 Real2) in H.
       ring_simplify in H.
       exact H.
  + apply M_split .
    exact Real1_gt_Real0.
Defined.


(* Real Metric and Metric Completeness  *)

