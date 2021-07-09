Require Export ZArith_base.
Require Import Base.
Require Import Kleene.

(* basic axioms for our type theory *)
Parameter Real : Set.

Declare Scope Real_scope.
Delimit Scope Real_scope with Real.
Bind Scope Real_scope with Real.

Local Open Scope Real_scope.

(* algebraic structure of Real *)
Parameter Real0 : Real.
Parameter Real1 : Real.
Parameter Realplus : Real -> Real -> Real.
Parameter Realmult : Real -> Real -> Real.
Parameter Realopp : Real -> Real.
Parameter Realinv : forall {z}, z <> Real0 -> Real.
Parameter Reallt : Real -> Real -> Prop.

(* real number comparison is semi-decidable *)
Axiom Reallt_semidec : forall x y : Real, semidec (Reallt x y).


(* Notations *)
Infix "+" := Realplus : Real_scope.
Infix "*" := Realmult : Real_scope.
Notation "- x" := (Realopp x) : Real_scope.
Notation "/ x" := (Realinv x) : Real_scope.

Infix "<" := Reallt : Real_scope.

Definition Realgt (x y:Real) : Prop := y < x.
Definition Realle (x y:Real) : Prop := x < y \/ x = y.
Definition Realge (x y:Real) : Prop := Realgt x y \/ x = y.
Definition Realminus (x y:Real) : Real := x + - y.
Definition Realdiv (x :Real) {y:Real} (p:y<>Real0) :  Real := x * / p.

Definition Realltb : Real -> Real -> K.
Proof.
  intros x y.
  exact (projP1 _ _ (Reallt_semidec x y)).
Defined.

Definition Realgtb (x y: Real) : K := Realltb y x.

Infix "-" := Realminus : Real_scope.
Infix "/" := Realdiv   : Real_scope.

Infix "<=" := Realle : Real_scope.
Infix ">=" := Realge : Real_scope.
Infix ">"  := Realgt : Real_scope.
Infix "<?" := Realltb : Real_scope.
Infix ">?" := Realgtb : Real_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : Real_scope.
Notation "x <= y < z"  := (x <= y /\ y <  z) : Real_scope.
Notation "x < y < z"   := (x <  y /\ y <  z) : Real_scope.
Notation "x < y <= z"  := (x <  y /\ y <= z) : Real_scope.

(**********)
(* Lemma Realltb_lt_t : forall x y : Real, Realltb x y = trueK <-> x < y. *)
(* Lemma Realltb_lt_f : forall x y : Real, Realltb x y = falseK <-> y < x. *)

(* Lemma Reallt_semidec : forall x y : Real, semidec (x < y). *)
(* Proof. *)
(*   intros x y. exists (x <? y). *)
(*   exact (Realltb_lt_t x y). *)
(* Qed. *)

Lemma Realgt_semidec : forall x y : Real, semidec (x > y).
Proof.
  intros x y.
  exact (Reallt_semidec y x).
Defined.



(* injection from nat and Z to Real *)
Inductive EZ :=
  Epos : nat -> EZ
| Ezero : EZ
| Eneg : nat -> EZ.

Fixpoint NReal (n : nat) : Real :=
  match n with
  | O => Real0
  | S n => Real1 + NReal n
  end.
Arguments NReal n%nat.

Fixpoint EZReal (z : EZ) : Real :=
  match z with
  | Epos n => NReal n
  | Ezero => Real0
  | Eneg n => - (NReal n)
  end.


(**********)
Fixpoint IPReal_2 (p:positive) : Real :=
  match p with
  | xH => Real1 + Real1
  | xO p => (Real1 + Real1) * IPReal_2 p
  | xI p => (Real1 + Real1) * (Real1 + IPReal_2 p)
  end.

Definition IPReal (p:positive) : Real :=
  match p with
  | xH => Real1
  | xO p => IPReal_2 p
  | xI p => Real1 + IPReal_2 p
  end.
Arguments IPReal p%positive : simpl never.

Definition IZReal (z:Z) : Real :=
  match z with
  | Z0 => Real0
  | Zpos n => IPReal n
  | Zneg n => - IPReal n
  end.
Arguments IZReal z%Z : simpl never.

(**********)
Fixpoint INReal (n:nat) : Real :=
  match n with
  | O => Real0
  | S O => Real1
  | S n => INReal n + Real1
  end.
Arguments INReal n%nat.
  




(* Classical axioms *)
Axiom Realplus_comm : forall r1 r2:Real, r1 + r2 = r2 + r1.
Axiom Realplus_assoc : forall r1 r2 r3:Real, r1 + r2 + r3 = r1 + (r2 + r3).
Axiom Realplus_inv : forall r:Real, r + - r = Real0.
Axiom Realplus_unit : forall r:Real, Real0 + r = r.
Axiom Realmult_comm : forall r1 r2:Real, r1 * r2 = r2 * r1.
Axiom Realmult_assoc : forall r1 r2 r3:Real, r1 * r2 * r3 = r1 * (r2 * r3).
Axiom Realmult_inv : forall (r:Real) (p : r <> Real0), / p * r = Real1.
Axiom Realmult_unit : forall r:Real, Real1 * r = r.
Axiom Realmult_plus_distr: forall r1 r2 r3:Real, r1 * (r2 + r3) = r1 * r2 + r1 * r3.
Axiom Real1_neq_Real0 : Real1 <> Real0.
Axiom Real1_gt_Real0 : Real1 > Real0.
Axiom Realtotal_order : forall r1 r2 : Real, r1 < r2 \/ r1 = r2 \/ r1 > r2.
Axiom Reallt_nlt : forall r1 r2 : Real, r1 < r2 -> ~ r2 < r1.
Axiom Reallt_lt_lt : forall r1 r2 r3:Real, r1 < r2 -> r2 < r3 -> r1 < r3.
Axiom Reallt_plus_lt : forall r r1 r2:Real, r1 < r2 -> r + r1 < r + r2.
Axiom Reallt_mult_pos_lt : forall r r1 r2:Real, Real0 < r -> r1 < r2 -> r * r1 < r * r2.
Definition W_nemp (c : Real -> Prop) := exists z, c z.
Definition W_upb (c : Real -> Prop) (u : Real) := forall z : Real, c z -> z <= u.
Definition W_upbd (c : Real -> Prop) := exists u, W_upb c u.
Definition W_sup (c : Real -> Prop) (s : Real)
  := W_upb c s /\ (forall s', W_upb c s' -> s <= s').
Axiom W_complete :
  forall c : Real -> Prop, W_nemp c ->  W_upbd c -> exists z, W_sup c z. 


Global Hint Resolve Realmult_plus_distr: Realiny.
Global Hint Resolve Realplus_comm Realplus_assoc Realplus_inv Realplus_unit: Realiny.
Global Hint Resolve Realmult_comm Realmult_assoc Realmult_inv Realmult_unit: Realiny.
Global Hint Resolve Real1_neq_Real0: Realiny.
Global Hint Resolve Real1_gt_Real0 Realtotal_order Reallt_nlt Reallt_lt_lt Reallt_plus_lt Reallt_mult_pos_lt: Realiny.
Global Hint Resolve Reallt_semidec Realgt_semidec W_complete: Realiny.



(* Accuracy embeding prec : n => 2^{-n} to axiomatize constructive limit *)
Definition Real2 : Real := IZReal 2.

Lemma Reallt_n_Sn : forall x, x < x + Real1.
Proof.
intro.
pose proof Real1_gt_Real0.
rewrite <- Realplus_unit at 1.
rewrite Realplus_comm.
apply (Reallt_plus_lt x).
auto with Realiny.
Qed.

Lemma Reallt_0_2 : Real0 < Real2.
Proof.
  unfold Real2.
  unfold IZReal.
  unfold IPReal.
  unfold IPReal_2.  
  apply Reallt_lt_lt with (Real0 + Real1).
  apply Reallt_n_Sn.
  rewrite Realplus_comm.
   apply Reallt_plus_lt.
   replace Real1 with (Real0 + Real1).
   apply Reallt_n_Sn.
   apply Realplus_unit.
Qed.

Lemma Realngt_triv : forall x, ~ x > x.
Proof.
  intro x.
  intuition.
  pose proof (Reallt_nlt x x H) as H1.
  contradict H.
  intuition.
Qed.

Lemma Realgt_neq : forall z1 z2, z1 > z2 -> z1 <> z2.
Proof.
  red.
  intros z1 z2 p q.
  apply (Realngt_triv z1).
  pattern z1 at 2; rewrite q; trivial.
Qed.
Global Hint Resolve Reallt_n_Sn Reallt_0_2 Realngt_triv Realgt_neq: Realiny.


  
Lemma Real2_neq_Real0 : Real2 <> Real0.
Proof.
  exact (Realgt_neq Real2 Real0 Reallt_0_2).
Qed.
Global Hint Resolve Real2_neq_Real0: Realiny.

Fixpoint prec (n : nat) : Real :=
  match n with
  | O => Real1
  | S m => (prec m) / Real2_neq_Real0
  end.
Arguments prec n%nat.


(* Classical Archimediean property *)
Axiom RealArchimedean : forall r : Real, r > Real0 -> exists n, prec n < r.




(* 
   Axiom for constructive metric completeness.
   Previous axiom changed to be a lemma. And, it is proven in RealLimit.v
 *)
Definition is_fast_cauchy (f : nat -> Real) := forall n m, - prec n - prec m <= f n - f m <= prec n + prec m.
Definition is_fast_limit (x : Real) (f : nat -> Real) := forall n, - prec n <= x - f n <= prec n.

Axiom C_limit :
  forall f : nat -> Real, is_fast_cauchy f -> {x | is_fast_limit x f}.
