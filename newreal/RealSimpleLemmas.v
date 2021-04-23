Require Import Base.
Require Import Kleene.
Require Import RealAxioms.
Require Import RealRing.

Open Scope T_scope.

Lemma Tmetric_inv : forall z1 z2 z3, dist z1 z2 = dist (z1 + z3) (z2 + z3).
Proof.
Admitted.

Lemma dist_pos : forall z1 z2 : T, dist z1 z2 >= T0.
Proof.
Admitted.

Lemma dist_symm : forall z1 z2 : T, dist z1 z2 = dist z2 z1.
Proof.
Admitted.
  
Lemma dist_tri : forall z1 z2 r3, dist z1 r3 >= (dist z1 z2) + (dist z2 r3).
Proof.
Admitted.

Lemma dist_zero : forall z1 z2 : T, dist z1 z2 = T0 <-> z1 = z2.
Proof.
Admitted.

Hint Resolve  dist_pos dist_symm dist_tri dist_zero: Tiny.

Lemma Tge_triv : forall z, z >= z.
Proof.
  intro z;  right; exact eq_refl.
Qed.
Hint Resolve Tge_triv: Tiny.

Lemma Tle_triv : forall z, z <= z.
Proof.
  intro z; right; exact eq_refl.
Qed.
Hint Resolve Tle_triv: Tiny.

Lemma Tlt_le : forall z1 z2, z1<z2 -> z1 <= z2.
Proof.
  intros z1 z2 p; left; exact p.
Qed.
Hint Resolve Tlt_le: Tiny.

Lemma Tgt_ge : forall z1 z2, z1>z2 -> z1 >= z2.
Proof.
  intros z1 z2 p; left; exact p.
Qed.
Hint Resolve Tgt_ge: Tiny.

Lemma Teq_le : forall z1 z2, z1 = z2 -> z1 <= z2.
Proof.
  intros z1 z2 p; rewrite p; right; exact eq_refl.
Qed.
Hint Resolve Teq_le: Tiny.

Lemma Teq_ge : forall z1 z2, z1 = z2 -> z1 >= z2.
Proof.
  intros z1 z2 p; rewrite p; right; exact eq_refl.
Qed.
Hint Resolve Teq_ge: Tiny.

Lemma Teq_plus_eq : forall z1 z2 z3, z1 = z2 -> z1 + z3 = z2 + z3.
Proof.
  intros z1 z2 z3 p.
  rewrite p.
  exact eq_refl.
Qed.
Hint Resolve Teq_plus_eq: Tiny.

Lemma Tge_le : forall z1 z2, z1 >= z2 -> z2 <= z1.
Proof.
  intros z1 z2 p.
  destruct p.
  left; auto.
  right; rewrite H; exact eq_refl.
Qed.
Hint Resolve Tge_le: Tiny.

Lemma Tle_ge : forall z1 z2, z1 <= z2 -> z2 >= z1.
Proof.
  intros z1 z2 p.
  destruct p.
  left; auto.
  right; rewrite H; exact eq_refl.
Qed.
Hint Resolve Tle_ge: Tiny.


  
  
Lemma Tnle_ge : forall z1 z2, ~ z1 <= z2 -> z1 > z2.
Proof.
  intros z1 z2 q.
  intuition.
  destruct (Ttotal_order z1 z2).
  assert (z1 <= z2).
  left; exact H.
  contradict (q H0).
  destruct H.
  assert (z1 <= z2).
  right; exact H.
  contradict (q H0).
  exact H.
Qed.
Hint Resolve Tnle_ge: Tiny.
  
Lemma Tdiv_distr : forall z1 z2 z3, forall p : z3<>T0,  z1/p + z2/p = (z1+z2)/p.
Proof.
  intros z1 z2 z3 nz.
  replace ((z1+z2)/nz) with ((z1+z2)*/nz) by auto.
  rewrite Tmult_comm, Tmult_plus_distr.
  unfold Tdiv.
  ring.
Qed.
Hint Resolve Tdiv_distr: Tiny.

Lemma Tle_plus_le : forall z1 z2 z3, z1 <= z2 -> z1+z3 <= z2+z3.
Proof.
  intros z1 z2 z3 p.
  destruct p.
  apply (Tlt_plus_lt z3 z1 z2) in H.
  replace (z1+z3) with (z3+z1) by ring;
    replace (z2+z3) with (z3+z2) by ring; left; exact H.
  rewrite H; right; auto with Tiny.
Qed.
Hint Resolve Tle_plus_le: Tiny.

  
Lemma Tnlt_triv : forall x, ~ x < x.
Proof.
  intro x.
  intuition.
  pose proof (Tlt_nlt x x H) as H1.
  contradict H.
  intuition.
Qed.
Hint Resolve Tnlt_triv: Tiny.



Lemma T2_gt_T1 : T2 > T1.
Proof.
  pose proof (T1_gt_T0).
  pose proof (Tlt_plus_lt T1 T0 T1 H).
  ring_simplify in H0.
  exact H0.
Qed.
Hint Resolve T2_gt_T1: Tiny.




Lemma Tlt_neq : forall z1 z2, z1 < z2 -> z1 <> z2.
Proof.
  red.
  intros z1 z2 p q.
  apply (Tnlt_triv z1).
  pattern z1 at 2; rewrite q; trivial.
Qed.
Hint Resolve Tlt_neq: Tiny.

Definition dT2 := T2_neq_T0.
Lemma Tminus_half : forall z, z - z/dT2 = z/dT2.
Proof.
  intro z.
  pose proof T2_neq_T0.
  assert (z = z * T2 / dT2).
  replace (z*T2/dT2) with (z*T2*/dT2) by auto.
  replace (z*T2*/dT2) with (z * (T2 * /dT2)) by ring.
  replace (z * (T2 * /dT2)) with (z * (/dT2 * T2)) by ring.
  rewrite (Tmult_inv T2 dT2).
  ring.
  rewrite H0 at 1.
  replace ( z * T2 / dT2 - z / dT2) with ( z * T2 */ dT2 - z */ dT2) by auto.
  replace (( z * T2 */ dT2 - z */ dT2)) with ( z * T2 */ dT2 + (- z) */ dT2) by ring.
  replace (z/dT2) with (z*/dT2) by auto.
  replace ( z * T2 * / dT2 + - z * / dT2) with ( /dT2 * (z * T2)  + - z * / dT2) by ring.
  replace ( / dT2 * (z * T2) + - z * / dT2) with ( / dT2 * (z * T2) + /dT2 * (-z)) by ring.
  rewrite <- (Tmult_plus_distr (/dT2) (z*T2) (-z)).
  replace (z*T2 +-z) with (z*(T1+T1) -z) by auto.
  replace (z*(T1+T1) -z) with z by ring.
  ring.
Qed.
Hint Resolve Tminus_half: Tiny.
  
Lemma Tgt_nle: forall z1 z2, z1 > z2 -> ~ z1 <= z2.
Proof.
  intros z1 z2 p q; destruct q as [q1 | q2].
  contradict p; exact (Tlt_nlt z1 z2 q1).
  rewrite q2 in p; contradict p; auto with Tiny.
Qed.
Hint Resolve Tgt_nle: Tiny.

Lemma Tgt_ngt : forall z1 z2, z1 > z2 -> ~ z2 > z1.
Proof.
  intros z1 z2 p.
  contradict p; exact (Tlt_nlt z1 z2 p).
Qed.
Hint Resolve Tgt_ngt: Tiny.

Lemma Tgt_nge : forall z1 z2, z1 > z2 -> ~ z2 >= z1.
Proof.
  intros z1 z2 p q; destruct q as [q1 | q2].
  contradict p; exact (Tlt_nlt z1 z2 q1).
  rewrite q2 in p; contradict p; auto with Tiny.
Qed.
Hint Resolve Tgt_nge: Tiny.

Lemma Tge_ge_eq : forall z1 z2, z1 >= z2 -> z2 >= z1 -> z1 = z2.
Proof.
  intros z1 z2 o1 o2.
  destruct o1.
  contradict o2.
  auto with Tiny.
  exact H.
Qed.

Lemma Tle_le_eq : forall z1 z2, z1 <= z2 -> z2 <= z1 -> z1 = z2.
Proof.
  intros z1 z2 o1 o2.
  destruct o1.
  contradict o2.
  auto with Tiny.
  exact H.
Qed.

Lemma Tle_ge_eq : forall z1 z2, z1 <= z2 -> z1 >= z2 -> z1 = z2.
Proof.
  intros z1 z2 o1 o2.
  destruct o1.
  contradict o2.
  auto with Tiny.
  exact H.
Qed.

Lemma Tge_le_eq : forall z1 z2, z1 >= z2 -> z1 <= z2 -> z1 = z2.
Proof.
  intros z1 z2 o1 o2.
  destruct o1.
  contradict o2.
  auto with Tiny.
  exact H.
Qed.
Hint Resolve Tge_ge_eq Tge_le_eq Tle_ge_eq Tle_le_eq: Tiny.


Lemma Tle_lt_lt : forall z1 z2 z3, z1<=z2 -> z2 < z3 -> z1<z3.
Proof.
  intros z1 z2 z3 p1 p2.
  destruct (Ttotal_order z1 z2) as [q1 |[q2| q3]].
  apply (Tlt_lt_lt z1 z2 z3); auto with Tiny.
  rewrite q2; exact p2.
  destruct p1.
  contradict q3; apply (Tlt_nlt); exact H.
  rewrite H in q3; contradict q3; auto with Tiny.
Qed.
Hint Resolve Tle_lt_lt: Tiny.

Lemma Tlt_le_lt : forall z1 z2 z3, z1 < z2 -> z2 <= z3 -> z1 < z3.
Proof.
  intros z1 z2 z3 p1 p2.
  destruct p2 as [q1| q2].
  exact (Tlt_lt_lt z1 z2 z3 p1 q1).
  rewrite<- q2; exact p1.
Qed.
Hint Resolve Tlt_le_lt: Tiny.

Lemma Tle_le_le : forall z1 z2 z3, z1 <= z2 -> z2 <= z3 -> z1 <= z3.
Proof.
  intros z1 z2 z3 p1 p2.
  destruct p1 as [p11 | p12]; destruct p2 as [p21 | p22]; auto with Tiny.
  left; exact (Tlt_lt_lt z1 z2 z3 p11 p21).
  rewrite p22 in p11; left; exact p11.
  rewrite p12; left; exact p21.
  rewrite p12; rewrite <- p22; right; exact eq_refl.
Qed.
Hint Resolve Tle_le_le: Tiny.

Lemma Tlt_plus_r_lt : forall r r1 r2:T, r1 < r2 -> r1 + r < r2 + r.
Proof.
  intros r r1 r2 p;
    replace (r1+r) with (r+r1) by ring;
    replace (r2+r) with (r+r2) by ring;
    auto with Tiny.
Qed.
Hint Resolve Tlt_plus_lt: Tiny.


Lemma T2_pos : T2 > T0.
Proof.
  pose proof (T1_gt_T0).
  pose proof (Tlt_plus_r_lt T1 T0 T1 H).
  replace (T0+T1) with T1 in H0 by ring.
  pose proof (Tlt_lt_lt T0 T1 (T1 + T1) H H0).
  auto.
Qed.
Hint Resolve T2_pos: Tiny.

Lemma Teq_eq_mult_eq : forall a b c d, a = b -> c = d -> a*c = b*d.
Proof.
  intros.
  rewrite H; rewrite H0; exact eq_refl.
Qed.
Hint Resolve Teq_eq_mult_eq: Tiny.

Lemma Thalf_gt_zero : forall a, a > T0 -> a / dT2 > T0. 
Proof.
  intros a p.
  pose proof T2_pos.
  destruct (Ttotal_order (a/dT2) T0) as [p1 |[p2|p3]].
  apply (Tlt_mult_pos_lt T2 (a/dT2) T0) in p1.
  replace (T2*(a/dT2)) with (T2*(a*/dT2)) in p1 by auto.
  replace (T2*(a*/dT2)) with (a *(/dT2 * T2)) in p1 by ring.
  rewrite (Tmult_inv T2 dT2) in p1.
  ring_simplify in p1.
  contradict p1.
  auto with Tiny.
  exact T2_pos.
  rewrite p2.
  pose proof (Teq_eq_mult_eq (a/dT2) T0 T2 T2 p2 eq_refl).
  replace (a/dT2*T2) with (a*/dT2*T2) in H0 by auto.
  replace (a*/dT2*T2) with (a*(/dT2*T2)) in H0 by ring.
  rewrite (Tmult_inv T2 dT2) in H0.
  ring_simplify in H0.
  rewrite H0 in p.
  contradict p; auto with Tiny.
  exact p3.
Qed.
Hint Resolve Thalf_gt_zero: Tiny.


Lemma Tgt_half : forall a, a > T0 -> a > a / dT2.
Proof.
  intros a p.
  pose proof (Thalf_gt_zero a p).
  apply (Tlt_plus_lt (a/dT2) T0 (a/dT2)) in H.
  rewrite (Tdiv_distr a a T2 dT2) in H.
  ring_simplify in H.
  replace (a + a) with (T1 * a + T1 * a) in H by ring.
  replace (T1 * a + T1 * a) with ((T1+T1)*a) in H by ring.
  replace (T1+T1) with T2 in H by auto.
  replace (T2*a/dT2) with (T2*a*/dT2) in H by auto.
  replace (T2*a*/dT2) with (a*(/dT2*T2)) in H by ring.
  rewrite (Tmult_inv T2 dT2) in H.
  ring_simplify in H.
  exact H.
Qed.
Hint Resolve Tgt_half: Tiny.
  
Lemma Tgt_minus_gt_zero : forall a b : T, a > b -> a - b > T0.
Proof.
  intros a b p.
  replace (a-b) with (-b+a) by ring.
  replace T0 with (-b+b) by ring.
  apply Tlt_plus_lt; auto with Tiny.
Qed.
Hint Resolve Tgt_minus_gt_zero: Tiny.


Lemma Tlt_lt_plus_lt : forall r1 r2 r3 r4, r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros r1 r2 r3 r4 p1 p2.
  pose proof (Tlt_plus_r_lt r3 r1 r2 p1).
  assert (r2+r3 < r2+r4).
  auto with Tiny.
  exact (Tlt_lt_lt (r1+r3) (r2+r3) (r2+r4) H H0).
Qed.
Hint Resolve Tlt_lt_plus_lt: Tiny. 

Definition padding : forall a b : T, a > b -> {ε : T | ε > T0 /\ a = ε + b}.
Proof.
  intros a b p; exists (a - b).
  constructor 1; auto with Tiny; ring.
Defined.
Hint Resolve padding: Tiny.


Lemma Tlt_anti : forall z1 z2, z1<z2 -> -z2< -z1.
Proof.
  intros z1 z2 p.
  apply (Tlt_plus_lt (-z1-z2) z1 z2) in p.
  ring_simplify in p; exact p.
Qed.
Hint Resolve Tlt_anti: Tiny.

Definition dT1 := T1_neq_T0.
Lemma Tinv_unit : forall z, z / dT1 = z.
Proof.
  intro.
  replace z with (z*T1) by ring.
  replace (z*T1/dT1) with (z*T1*/dT1) by auto.
  replace (z*T1*/dT1) with (z*(/dT1*T1)) by ring.
  replace (/dT1*T1) with T1 by auto with Tiny.
  exact eq_refl.
Qed.
Hint Resolve Tinv_unit: Tiny.


Lemma square_pos : forall z, z <> T0 -> z *z > T0.
Proof.
  intros.
  destruct (Ttotal_order z T0) as [a|[b|c]].
  assert (z+(-z) < T0+(-z)).
  apply (Tlt_plus_r_lt); exact a.
  ring_simplify in H0.
  pose proof (Tlt_mult_pos_lt (-z) T0 (-z) H0 H0).
  ring_simplify in H1.
  ring_simplify.
  exact H1.
  contradict H; exact b.
  pose proof (Tlt_mult_pos_lt z T0 z c c) as q; ring_simplify in q; ring_simplify; exact q.
Qed.


Lemma Tpos_inv_pos2 : forall z, forall p :  z > T0, / (Tgt_neq z T0 p) > T0.
Proof.
  intros z p.
  pose proof (square_pos (/ (Tgt_neq z T0 p))).
  assert (/(Tgt_neq z T0 p) <> T0) as H10.
  intro.
  pose proof (Tmult_inv z).
  assert (z <> T0) as H12 by auto with Tiny.
  pose proof (H1  H12) as H2.
  pose proof (neq_path z T0 H12 (Tgt_neq z T0 p)) as path.
  rewrite path in H2.
  rewrite H0 in H2; ring_simplify in H2; contradict H2; auto with Tiny.
  pose proof (H H10) as H0.
  pose proof (Tlt_mult_pos_lt (/(Tgt_neq z T0 p)*/(Tgt_neq z T0 p)) T0 z H0 p).
  replace (/(Tgt_neq z T0 p)*/(Tgt_neq z T0 p)*z) with (/(Tgt_neq z T0 p)*(/(Tgt_neq z T0 p)*z))  in H1 by ring.

  assert (z <> T0) as H12 by auto with Tiny.
  replace (/(Tgt_neq z T0 p) *z) with T1 in H1 by auto with Tiny.
  
  ring_simplify in H1.
  exact H1.
Qed.
Hint Resolve Tpos_inv_pos2:Tiny.

Lemma Tpos_inv_pos : forall z, forall p : z > T0, forall q : z <> T0, / q > T0.
Proof.
  intros.
  rewrite (neq_path z T0 q (Tgt_neq z T0 p)); auto with Tiny.
Qed.
Hint Resolve Tpos_inv_pos.

Lemma Tlt_mult_r_pos_lt : forall z1 z2 z3, z3 > T0 -> z1 < z2 -> z1 * z3 < z2 * z3.
Proof.
  intros.
  replace (z1*z3) with (z3*z1) by ring.
  replace (z2*z3) with (z3*z2) by ring.
  auto with Tiny.
Qed.
Hint Resolve Tlt_mult_r_pos_lt: Tiny.


Lemma prec_S : forall n, prec (S n) < prec n.
Proof.
  intro n.
  induction n; simpl.
  replace (T1+T1) with T2 by auto.
  exact (Tgt_half T1 T1_gt_T0).
  simpl in IHn.
  replace (T1+T1) with T2 by auto.
  replace (T1+T1) with T2 in IHn by auto.
  pose proof (T2_pos).
  assert (/dT2 > T0) by auto with Tiny.
  apply (Tlt_mult_r_pos_lt (prec n / dT2) (prec n)  (/dT2) H0) in IHn.
  auto.
Qed.
Hint Resolve prec_S: Tiny.

Lemma prec_hom : forall n m, prec (n+m) = prec n * prec m.
Proof.
  intros n m.
  induction n.
  simpl; ring.
  rewrite (plus_Sn_m n m).
  simpl.
  rewrite IHn.
  unfold Tdiv.
  ring.
Qed.      
Hint Resolve prec_hom: Tiny.

Definition dg0 {z:T}(p:z>T0) : z <> T0 :=  Tgt_neq z T0 p.
Lemma Tlt_mult_pos_move_rr : forall a b c, forall p :a > T0, b*a < c -> b < c / (dg0 p).
Proof.
  intros a b c p q.
  assert (/ (dg0 p) > T0) by auto with Tiny.
  apply (Tlt_mult_r_pos_lt (b*a)  c (/(dg0 p)) H) in q.
  replace (b*a*/(dg0 p)) with (b*(/(dg0 p)*a)) in q by ring.
  assert (a <> T0) by auto with Tiny.
  replace (/(dg0 p)*a) with T1 in q by auto with Tiny.
  ring_simplify in q.
  auto with Tiny.
Qed.
Hint Resolve Tlt_mult_pos_move_rr: Tiny.

Lemma Tlt_mult_pos_move_rl : forall a b c, forall p :a > T0, a*b < c -> b < c / (dg0 p).
Proof.
  intros a b c p q.
  replace (a*b) with (b*a) in q by ring.
  apply Tlt_mult_pos_move_rr; auto. 
Qed.
Hint Resolve Tlt_mult_pos_move_rl: Tiny.

Lemma Tgt_mult_pos_move_rl : forall a b c, forall p:a > T0,  a*b > c -> b > c / (dg0 p).
  intros a b c p q.
  assert (/ (dg0 p) > T0) by auto with Tiny.
  replace (a*b) with (b*a) in q by ring.
  apply (Tlt_mult_r_pos_lt c (b*a) (/ (dg0 p)) H) in q.
  replace (b*a*/(dg0 p)) with (b*(/(dg0 p)*a)) in q by ring.
  assert (a <> T0) by auto with Tiny.
  replace (/(dg0 p)*a) with T1 in q by auto with Tiny.
  ring_simplify in q.
  auto with Tiny.
Qed.
Hint Resolve Tgt_mult_pos_move_rl: Tiny.

Lemma Tlt_mult_pos_move_rr_n
  : forall (a b c : T) (p : a > T0) (q : a <> T0), b * a < c -> b < c / q.
Proof.
  intros.
  pose proof (neq_path a T0 q (Tgt_neq a T0 p)).
  rewrite H0.
  apply Tlt_mult_pos_move_rr; exact H.
Qed.
Hint Resolve Tlt_mult_pos_move_rr_n: Tiny.


(** prec embedding is always positive **)
Lemma prec_pos : forall n, prec n > T0.
Proof.
  intro.
  induction n.
  + auto with Tiny.
  + simpl.
    replace (T1+T1) with (T2) by auto.
    auto with Tiny.
Defined.
Hint Resolve prec_pos: Tiny.


Lemma NT_hom : forall n m, NT (n+m) = NT n + NT m.
Proof.
  intros n m.
  induction n.
  simpl.
  auto with Tiny.
  assert (S n + m = S (n+m))%nat as H by intuition.
  rewrite H.
  assert (forall n, NT (S n) = T1 + NT n) by (intro; simpl; exact eq_refl).
  rewrite (H0 n). rewrite (H0 ((n+m)%nat)).
  rewrite IHn; ring.
Qed.
Hint Resolve NT_hom: Tiny.

Lemma NT_pos : forall n, (n>0)%nat -> NT n > T0.
Proof.
  intros n p.
  induction n.
  contradict p; exact (gt_irrefl 0).
  assert (S n = 1+n)%nat as q; intuition.
  rewrite q.
  rewrite (NT_hom 1%nat n).
  pose proof (T1_gt_T0) as gtg.
  destruct n.
  simpl; ring_simplify; auto with Tiny.

  pose proof (IHn (gt_Sn_O n)).
  pose proof (Tlt_lt_plus_lt T0 T1 T0 (NT (S n)) gtg H) as H1; ring_simplify in H1.
  replace (NT (S n) + T1) with (T1 + NT (S n)) in H1 by ring.
  assert (NT 1 = T1). simpl. ring.
  rewrite H0; exact H1.
Qed.
Hint Resolve NT_pos: Tiny.


Lemma NT_S : forall n, NT (S n) = T1 + NT n.
Proof.
  intro n.
  replace (S n)%nat with (1 + n)%nat by intuition.
  rewrite (NT_hom 1%nat n); simpl; ring.
Qed.

Lemma NT_mult : forall n m, NT (n * m) = NT n * NT m.
Proof.
  intros n m.
  induction n.
  simpl; ring.
  simpl.
  rewrite NT_hom .
  rewrite IHn.
  ring.
Qed.


Lemma IZT_asym : forall n, IZT (-n) = - IZT n.
Proof.
  intro n.
  unfold IZT.
  unfold IPT.
  unfold IPT_2.  
  destruct n; simpl; ring.
Qed.
Require Import Coq.PArith.BinPos.
Lemma IZT_s1 : forall p, IZT (Z.pos (p~0)) = T2 * (IZT (Z.pos p)).
Proof.
  intro.
  unfold IZT.
  simpl.
  unfold IPT.
  
  unfold IPT_2.

  destruct p;
  replace (T1+T1) with T2 by auto; ring_simplify;
    exact eq_refl.
Qed.

Lemma IZT_s2 : forall p, IZT (Z.pos (p~1)) = T2 * (IZT (Z.pos p)) + T1.
Proof.
  intro.
  unfold IZT.
  unfold IPT.  
  unfold IPT_2.
  destruct p;
  replace (T1+T1) with T2 by auto; ring_simplify; exact eq_refl.
Qed.

Lemma IPT2_NT : forall p, T2 * NT (Pos.to_nat p) = IPT_2 p.
Proof.
  intro p.
  induction p.
  + rewrite Pos2Nat.inj_xI.
    rewrite NT_S.
    ring_simplify.
    rewrite NT_mult.
    ring_simplify.
    replace (T2* NT 2 * NT (Pos.to_nat p)) with (NT 2 * (T2 * NT (Pos.to_nat p))) by ring.
    rewrite IHp.
    simpl.
    ring_simplify.
    replace (T1+T1) with T2 by auto.
    ring.

  + rewrite Pos2Nat.inj_xO.
    rewrite NT_mult.
    simpl NT.
    ring_simplify.
    replace ((T1+T1)*T2*NT (Pos.to_nat p)) with ((T1+T1) *(T2 *NT (Pos.to_nat p))) by ring.
    rewrite IHp.
    simpl; exact eq_refl.

  + simpl; ring_simplify; auto.
Qed.

Lemma IPT_NT : forall p, NT (Pos.to_nat p) = IPT p.
Proof.
  intro p.
  induction p.

  + unfold IPT.
    rewrite <- IPT2_NT.
    rewrite Pos2Nat.inj_xI.
    rewrite NT_S, NT_mult.
    simpl NT; ring_simplify.
    replace (T1+T1) with T2 by auto.
    ring.

  + unfold IPT.
    rewrite <- IPT2_NT.
    rewrite Pos2Nat.inj_xO.
    rewrite  NT_mult.
    simpl NT; ring_simplify.
    replace (T1+T1) with T2 by auto.
    ring.

  + simpl; ring_simplify; auto.
Qed.

Lemma IZT_NT : forall p, NT (Pos.to_nat p) = IZT (Z.pos p).
Proof.
  intro p.
  rewrite IPT_NT.
  unfold IZT; exact eq_refl.
Qed.

Lemma IZT_pos_pos : forall p1 p2, IZT (Z.pos p1 + Z.pos p2) = IZT (Z.pos p1) + IZT (Z.pos p2).
Proof.
  intros p1 p2.
  replace (Z.pos p1 + Z.pos p2)%Z with (Z.pos (p1+p2))%Z by auto.
  rewrite<- IZT_NT.
  rewrite Pos2Nat.inj_add.
  rewrite NT_hom.
  rewrite IZT_NT.
  rewrite IZT_NT.
  exact eq_refl.
Qed.

Lemma IZT_neg : forall p, IZT (Z.neg p) = - IZT (Z.pos p).
Proof.
  intro p.
  unfold IZT; auto.
Qed.
Lemma Teq_plus_cancel : forall a b c, b + a = c + a -> b = c.
Proof.
  intros a b c p.
  apply (Teq_plus_eq (b+a) (c+a) (-a)) in p.
  ring_simplify in p; exact p.
Qed.

  
Lemma IZT_pos_neg : forall p1 p2, IZT (Z.pos p1 + Z.neg p2) = IZT (Z.pos p1) + IZT (Z.neg p2).
Proof.
  intros p1 p2.
  destruct (Pos.compare_spec p1 p2).
  +
    rewrite H; simpl.
    rewrite IZT_neg.
    rewrite Z.pos_sub_diag.
    replace (IZT 0) with T0 by auto.
    ring.
  +
    simpl.
    rewrite (Z.pos_sub_lt p1 p2 H).
    rewrite IZT_neg; rewrite IZT_neg.
    rewrite<- IZT_NT.
    rewrite<- IZT_NT.
    rewrite<- IZT_NT.
    ring_simplify.
    assert (NT (Pos.to_nat p2) = NT( Pos.to_nat p2)) as H1 by exact eq_refl.
    apply (Teq_plus_cancel (NT (Pos.to_nat (p2-p1)) + NT (Pos.to_nat p2))).
    ring_simplify.
    rewrite <- NT_hom.
    rewrite Pos2Nat.inj_sub; auto.
    rewrite Nat.sub_add; auto.
    apply (Pos2Nat.inj_lt p1 p2) in H.
    apply Nat.lt_le_incl; auto.

  +
    simpl.
    rewrite (Z.pos_sub_gt p1 p2 H).
    rewrite IZT_neg.
    rewrite <- IZT_NT.
    rewrite <- IZT_NT.
    rewrite <- IZT_NT.
    apply (Teq_plus_cancel (NT (Pos.to_nat p2))).
    ring_simplify.
    rewrite <- NT_hom.
    rewrite Pos2Nat.inj_sub; auto.
    rewrite Nat.sub_add; auto.
    apply (Pos2Nat.inj_lt p2 p1) in H.
    apply Nat.lt_le_incl; auto.
Qed.

Lemma IZT_neg_pos : forall p1 p2, IZT (Z.neg p1 + Z.pos p2) = IZT (Z.neg p1) + IZT (Z.pos p2).
Proof.
  intros p1 p2.
  replace (Z.neg p1 + Z.pos p2)%Z with (Z.pos p2 + Z.neg p1)%Z by auto.
  rewrite IZT_pos_neg; ring.
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

Lemma IZT_hom : forall n m, IZT (n+m) = IZT n + IZT m.
Proof.
  intros n m.
  destruct n; destruct m; try apply IZT_pos_pos; try apply IZT_pos_neg; try apply IZT_neg_pos; try simpl; try ring.
  rewrite IZT_neg.
  rewrite IZT_neg.
  rewrite IZT_neg.
  replace (Z.pos (p+p0)) with (Z.pos p + Z.pos p0)%Z by auto.
  rewrite (IZT_pos_pos).
  ring.
Qed.  

Lemma IZT_pos : forall z, (z > 0)%Z -> IZT z > T0.
Proof.
  intros z p.
  destruct z.
  + contradict p; apply Zgt_irrefl.
  +
    rewrite <- IZT_NT.
    apply NT_pos.
    exact (Pos2Nat.is_pos p0).
  +
    contradict p; apply Zgt_asym; apply Z.lt_gt; exact (Pos2Z.neg_is_neg p0).
Qed.




Lemma T1_inv_T1 : /dT1 = T1.
Proof.
  replace (/dT1) with (/dT1 *T1) by ring.
  pose proof (T1_neq_T0).
  replace (/dT1 *T1) with T1 by auto with Tiny.
  exact eq_refl.
Qed.

Lemma div_T1 : forall z, z/dT1 = z.
Proof.
  intro.
  replace (z/dT1) with (z*/dT1) by auto.
  rewrite T1_inv_T1; ring.
Qed.
Lemma Tlt_mult_pos_cancel : forall z z1 z2, z > T0 -> z1 * z < z2 * z -> z1 < z2.
Proof.
  intros z z1 z2 p q.
  assert (z <> T0); auto with Tiny.  
  
  apply (Tlt_mult_r_pos_lt (z1*z) (z2 *z) (/H)) in q; auto with Tiny.
  rewrite Tmult_assoc in q.
  rewrite Tmult_assoc in q.
  rewrite (Tmult_comm z (/H)) in q.
  rewrite (Tmult_inv z H) in q.
  ring_simplify in q; exact q.
Qed.

Lemma Tgt0_merge_gt : forall z1 z2, z1 > T0 -> z2 > T0 -> z1 + z2 > T0.
Proof.
  intros.
  pose proof (Tlt_lt_plus_lt T0 z1 T0 z2 H H0).
  ring_simplify in H1; exact H1.
Qed.
Hint Resolve Tgt0_merge_gt: Tiny.


Lemma Tlt_lt_lt_lt : forall a b c d, a<b -> b<c -> c<d -> a<d.
Proof.
  intros a b c d p q r.
  exact (Tlt_lt_lt a b d p (Tlt_lt_lt b c d q r)).
Qed.
Hint Resolve Tlt_lt_lt_lt: Tiny.


Lemma gt1_mult_gt_self : forall z1 z2, z1 > T1 -> z2 > T0 -> z1 * z2 > z2.
Proof.
  intros z1 z2 p q.
  pose proof (padding z1 T1 p) as [epsilon [c1 c2]].
  rewrite c2.
  ring_simplify.
  replace z2 with (T0 + z2) at 3 by ring.
  apply Tlt_plus_r_lt.
  pose proof (Tlt_mult_pos_lt epsilon T0 z2 c1 q).
  ring_simplify in H; exact H.
Qed.
Hint Resolve  gt1_mult_gt_self: Tiny.


Lemma Tlt_pos_mult_pos_pos : forall z1 z2, z1 > T0 -> z2 > T0 -> z1 * z2 > T0.
Proof.
  intros.
  pose proof (Tlt_mult_pos_lt z1 T0 z2 H H0).
  replace (z1*T0) with T0 in H1 by ring; auto.
Qed.
Hint Resolve Tlt_pos_mult_pos_pos: Tiny.
  
Lemma pos_square_gt_gt : forall z1 z2, z1 > T0 -> z2 > T0 -> z1*z1 > z2*z2 -> z1 > z2.
Proof.
  intros z1 z2 q p r.
  destruct (Ttotal_order z1 z2) as [s|[s|s]].
  + pose proof (Tlt_mult_pos_lt z1 z1 z2 q s).
    pose proof (Tlt_mult_r_pos_lt z1 z2 z2 p s).
    pose proof (Tlt_lt_lt (z1*z1) (z1*z2) (z2*z2) H H0).
    contradict H1; auto with Tiny.

  + rewrite s in r; contradict r; auto with Tiny.

  + exact s.
Qed.
Hint Resolve pos_square_gt_gt: Tiny.

Lemma pos_square_eq_eq : forall z1 z2, z1 > T0 -> z2 > T0 -> z1*z1 = z2*z2 -> z1 = z2.
Proof.
  intros.
  destruct (Ttotal_order z1 z2) as [p|[p|p]].
  
  pose proof (Tlt_mult_pos_lt z1 z1 z2 H p).
  pose proof (Tlt_mult_r_pos_lt z1 z2 z2 H0 p).
  pose proof (Tlt_lt_lt (z1*z1) (z1*z2) (z2*z2) H2 H3).
  rewrite H1 in H4;
    contradict H4; auto with Tiny.
  auto.
  pose proof (Tlt_mult_pos_lt z2 z2 z1 H0 p).
  pose proof (Tlt_mult_r_pos_lt z2 z1 z1 H p).
  pose proof (Tlt_lt_lt (z2*z2) (z2*z1) (z1*z1) H2 H3).
  rewrite H1 in H4;
    contradict H4; auto with Tiny.
Qed.
Hint Resolve pos_square_eq_eq: Tiny.


Lemma gt0_gt0_plus_gt0 : forall z1 z2, z1 > T0 -> z2 > T0 -> z1 + z2 > T0.
Proof.
  intros.
  auto with Tiny.
Qed.
Hint Resolve gt0_gt0_plus_gt0: Tiny.

Lemma Tlt_le_lt_lt : forall z1 z2 z3 z4, z1 <z2 -> z2 <= z3 -> z3 < z4 -> z1 < z4.
  intros.
  apply (Tlt_le_lt z1 z2 z3 H) in H0.
  exact (Tlt_lt_lt z1 z3 z4 H0 H1).
Qed.

Lemma Tlt_lt_le_lt : forall z1 z2 z3 z4, z1 <z2 -> z2 < z3 -> z3 <= z4 -> z1 < z4.
  intros.
  apply (Tlt_lt_lt z1 z2 z3 H) in H0.
  exact (Tlt_le_lt z1 z3 z4 H0 H1).
Qed.

Lemma dT2_pos : T0 < / dT2.
Proof.
  assert (/dT2 > T0); auto with Tiny.  
Qed.
Hint Resolve dT2_pos: Tiny.
  
           
Lemma Teq_mult_eq : forall z z1 z2, z1 = z2 -> z*z1=z*z2.
Proof.
  intros.
  auto with Tiny.
Qed.


Lemma W_split : forall x y ε, ε > T0 -> x>y-ε \/ y>x-ε.
Proof.
  intros x y ε p.
  destruct (Ttotal_order x y) as [H|[H|H]].
  + apply (Tlt_plus_lt (-ε + x) T0 ε) in p.
    ring_simplify in p.
    apply (Tlt_lt_lt (-ε + x) x y p) in H.
    replace (-ε+x) with (x-ε) in H by ring; right; exact H.
  + rewrite H.
    left.
    apply (Tlt_plus_lt (y-ε) T0 ε) in p.
    ring_simplify in p.
    exact p.
  + apply (Tlt_plus_lt (-ε + y) T0 ε) in p.
    ring_simplify in p.
    apply (Tlt_lt_lt (-ε + y) y x p) in H.
    replace (-ε+y) with (y-ε) in H by ring; left; exact H.
Defined.
Hint Resolve W_split : Tiny.
(** string but multivalued split **)
Lemma M_split : forall x y ε, ε > T0 -> M ({x>y-ε} + {y>x-ε}).
Proof.
  intros x y ε p.  
  apply (choose (x > y-ε) (y > x-ε)); auto with Tiny.
Defined.

Hint Resolve M_split : Tiny.

  
Lemma not_bounded : forall x, [ y | y > x ].
Proof.
  intro x.
  apply (mjoin (x>T0-T1) (T0>x-T1)).
  + intros [c1|c2].
    ++ exists (x+T1).
       pose proof (T1_gt_T0).
       apply (Tlt_plus_lt x T0 T1) in H.
       ring_simplify in H.
       exact H.
    ++ exists (x+T2).
       pose proof (T2_pos).
       apply (Tlt_plus_lt x T0 T2) in H.
       ring_simplify in H.
       exact H.
  + apply M_split .
    exact T1_gt_T0.
Defined.


Lemma Tmetric_sand : forall z1 z2 z3, z1-z3<=z2<=z1+z3 -> dist z1 z2 <= z3.
Proof.
  intros z1 z2 z3 p.
  destruct p as [p1 p2].
  destruct (dist_prop z1 z2) as [q1 [q2 q3]];
    destruct (Ttotal_order z1 z2) as [r1 | [r2 | r3]].
  rewrite (q3 r1).
  destruct p2.
  apply (Tlt_plus_lt (-z1) z2 (z1+z3)) in H.
  ring_simplify in H.
  replace (-z1+z2) with (z2-z1) in H by ring; left; exact H.
  rewrite H.
  ring_simplify; right; exact eq_refl.

  rewrite (q2 r2); rewrite r2 in p2.
  destruct p2.
  apply (Tlt_plus_lt (-z2) z2 (z2+z3)) in H.
  ring_simplify in H; left; exact H.
  apply (Teq_plus_eq z2 (z2+z3) (-z2)) in H.
  ring_simplify in H; right; exact H.

  rewrite (q1 r3).
  apply (Tle_plus_le (z1-z3) z2 (z3-z2)) in p1.
  ring_simplify in p1.
  exact p1.
Qed.
Hint Resolve Tmetric_sand: Tiny.


Lemma Tmetric_plus_inv : forall z1 z2 z3, dist z1 z2 = dist (z3 + z1) (z3 + z2).
Proof.
  intros z1 z2 z3;
    replace (z3+z1) with (z1+z3) by ring;
    replace (z3+z2) with (z2+z3) by ring; exact (Tmetric_inv z1 z2 z3).
Qed.
Hint Resolve Tmetric_plus_inv: Tiny.


Lemma Tmetric_or : forall z1 z2, dist z1 z2 = z1 - z2 \/ dist z1 z2 = z2 - z1.
Proof.
  intros z1 z2.
  destruct (Ttotal_order z1 z2) as [r1 | [r2 | r3]];
    destruct (dist_prop z1 z2) as [l1 [l2 l3]].
  right; rewrite (l3 r1); exact eq_refl.
  rewrite r2 at 2.
  left; ring_simplify.
  exact (l2 r2).
  left; rewrite (l1 r3); exact eq_refl.
Qed.
Hint Resolve Tmetric_or: Tiny.

Lemma Tmetric_Or : forall z1 z2, (dist z1 z2 = z1-z2 /\ z1 >= z2) \/
                                (dist z1 z2 = z2-z1 /\ z2 >= z1).
Proof.
  intros z1 z2.
  destruct (Ttotal_order z1 z2) as [r1 | [r2 | r3]];
    destruct (dist_prop z1 z2) as [l1 [l2 l3]].
  right; rewrite (l3 r1); exact (conj eq_refl (Tgt_ge  z2 z1 r1)).
  rewrite r2 at 2.
  left; split; ring_simplify.
  exact (l2 r2).
  right; exact r2.
  left; rewrite (l1 r3); exact (conj eq_refl (Tgt_ge z1 z2 r3)).
Qed.
Hint Resolve Tmetric_Or: Tiny.

Lemma Tmetric_gtgt_sand : forall z1 z2 z3, z3> T0 -> z1-z3<z2<z1+z3 -> dist z1 z2 < z3.
Proof.
  intros z1 z2 z3 q p.
  destruct p as [p1 p2].
  destruct (Tmetric_Or z1 z2) as [[a b] | [a b]]; rewrite a.
  apply (Tlt_plus_lt (z3-z2) (z1-z3) z2) in p1.
  ring_simplify in p1.
  replace (-z2+z1) with (z1-z2) in p1 by ring.
  exact p1.
  apply (Tlt_plus_lt (-z1) z2 (z1+z3)) in p2.
  ring_simplify in p2.
  replace (-z1+z2) with (z2-z1) in p2 by ring.
  exact p2.
Qed.
Hint Resolve Tmetric_gtgt_sand: Tiny.


Lemma Tmetric_minus_inv : forall z1 z2 z3, dist z1 z2 = dist (z1 - z3) (z2 - z3).
Proof.
  intros z1 z2 z3;
  pose proof (Tmetric_inv z1 (z2) (-z3)) as H;
  replace (z1-z3) with (z1+-z3) by ring;
  replace (z2-z3) with (z2+-z3) by ring; exact H.    
Qed.
Hint Resolve Tmetric_minus_inv: Tiny.


Lemma lt_metric : forall x y, x < y -> dist x y = y - x.
Proof.
  intros x y p.
  destruct (Tmetric_Or x y) as [[P Q] | [P Q]].
  contradict Q; auto with Tiny.
  exact P.
Qed.
Hint Resolve lt_metric: Tiny.

Lemma le_metric : forall x y, x <= y -> dist x y = y - x.
Proof.
  intros x y p.
  destruct p.
  apply lt_metric; exact H.
  rewrite H.
  ring_simplify.
  rewrite (dist_zero y y); exact eq_refl.
Qed.
Hint Resolve le_metric: Tiny.

Lemma dist_0_1 : dist T0 T1 = T1.
Proof.
  rewrite (lt_metric T0 T1 T1_gt_T0).
  ring.
Qed.
Hint Resolve dist_0_1: Tiny.

Lemma dist_1_0 : dist T1 T0 = T1.
Proof.
  rewrite (dist_symm T1 T0).
  exact dist_0_1.
Qed.
Hint Resolve dist_1_0: Tiny.




Definition convex (x y w1 w2 : T) : x < y -> w1 > T0 -> w2 > T0 -> T.
Proof.
  intros p p1 p2.
  pose proof (Tlt_lt_plus_lt T0 w1 T0 w2 p1 p2).
  rewrite Tplus_unit in H.
  exact ((x*w1+y*w2)/(Tgt_neq (w1+w2) T0 H)).
Defined.


Lemma convexity : forall x y w1 w2,
    forall (p:x < y) (q:w1 > T0) (r:w2 > T0),
      x < convex x y w1 w2 p q r < y.
Proof.
  intros.
  split.
  + unfold convex.
    apply (Tlt_mult_r_pos_lt x y w2 r) in p.
    apply (Tlt_plus_lt  (w1*x) (x*w2) (y*w2)) in p.
    assert (w1+w2 <> T0) as Path by auto with Tiny.
    rewrite <- (neq_path (w1+w2) T0 Path (Tgt_neq (w1 + w2) T0
    (eq_ind (T0 + T0) (fun t : T => t < w1 + w2) (Tlt_lt_plus_lt T0 w1 T0 w2 q r) T0
            (Tplus_unit T0)))).
    
    apply (Tlt_plus_lt  w2 T0 w1) in q.
    replace (w2+T0) with w2 in q by ring.
    replace (w2+w1) with (w1+w2) in q by ring.
    pose proof (Tlt_lt_lt T0 w2 (w1+w2) r q).
    replace (w1 * x + x * w2) with (x*(w1  + w2)) in p by ring.
    assert (/Path > T0) by auto with Tiny.
    apply (Tlt_mult_r_pos_lt (x*(w1+w2)) (w1*x+y*w2) (/Path) H0) in p.
    rewrite Tmult_assoc, (Tmult_comm (w1+w2) (/Path)) in p.
    rewrite (Tmult_inv (w1 + w2) Path), Tmult_comm, Tmult_unit in p.
    replace (w1*x) with (x*w1) in p by ring.
    exact p.

  + unfold convex.
    apply (Tlt_mult_r_pos_lt x y w1 q) in p.
    apply (Tlt_plus_lt  (w2*y) (x*w1) (y*w1)) in p.
    assert (w1+w2 <> T0) as Path by auto with Tiny.
    rewrite <- (neq_path (w1+w2) T0 Path (Tgt_neq (w1 + w2) T0
    (eq_ind (T0 + T0) (fun t : T => t < w1 + w2) (Tlt_lt_plus_lt T0 w1 T0 w2 q r) T0
            (Tplus_unit T0)))).


    apply (Tlt_plus_lt  w1 T0 w2) in r.
    replace (w1+T0) with w1 in r by ring.
    pose proof (Tlt_lt_lt T0 w1 (w1+w2) q r).
    replace (w2 * y + y * w1) with (y * (w1  + w2)) in p by ring.
    assert (/Path > T0) by auto with Tiny.
    apply (Tlt_mult_r_pos_lt  (w2*y+x*w1) (y*(w1+w2)) (/Path) H0) in p.
    rewrite Tmult_assoc in p at 1.
    replace ((w1 + w2) * / Path) with (/Path*(w1+w2)) in p by auto with Tiny.
    rewrite (Tmult_inv (w1 + w2) Path) in p.
    replace (y*T1) with y in p by ring.
    replace  (w2 * y + x * w1) with (x * w1 + y * w2) in p by ring.
    exact p.
Qed.
    

