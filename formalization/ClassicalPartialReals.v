Require Import Base Real ClassicalMonads ClassicalPartiality RealAssumption.
Require Import ZArith.

Declare Scope creal_scope.
Delimit Scope creal_scope with creal.
Open Scope creal_scope.

Definition c_Real := (Nabla ^Real).

Notation "x + y" := (@Nabla_lift_binary _ _ _ (fun a b => a + b)%Real x y) : creal_scope.
Notation "x - y" := (@Nabla_lift_binary _ _ _ (fun a b => a - b)%Real x y) : creal_scope.
Notation "x * y" := (@Nabla_lift_binary _ _ _ (fun a b => a * b)%Real x y) : creal_scope.
Notation "x < y" := (exists x' y', x = Nabla_unit _ x' /\ y = Nabla_unit _ y' /\ x' < y')%Real : creal_scope. 

(* for parsing and printing reals *)

Inductive my_cnt :=
  Cnt_zero | Cnt_succ : my_cnt -> my_cnt | Cnt_pred : my_cnt -> my_cnt.

Definition postiive_to_my_cnt : positive -> my_cnt.
Proof.
  apply Pos.peano_rect.
  exact (Cnt_succ (Cnt_zero)).
  intros _ x.  
  exact (Cnt_succ x).
Defined.

(* embedding from positive integer *)
Definition postiive_to_neg_my_cnt : positive -> my_cnt.
Proof.
  apply Pos.peano_rect.
  exact (Cnt_pred (Cnt_zero)).
  intros _ x.  
  exact (Cnt_pred x).
Defined.

Definition Z_to_my_cnt : Z -> my_cnt :=
  fun z => match z with
           | Z0 => Cnt_zero
           | Zpos p => postiive_to_my_cnt p
           | Zneg p => postiive_to_neg_my_cnt p
           end.

Fixpoint my_cnt_to_Z (c : my_cnt) : Z.
Proof.
  destruct c.
  exact 0%Z.
  exact (my_cnt_to_Z c + 1)%Z.
  exact (my_cnt_to_Z c - 1)%Z.
Defined.

Definition c_real_0 := Nabla_unit ^Real real_0.

Definition c_real_1 := Nabla_unit ^Real real_1.

Definition c_real_add1 := fun x => x + c_real_1.

Definition c_real_sub1 := fun x => x - c_real_1.

Number Notation c_Real Z_to_my_cnt my_cnt_to_Z (via my_cnt mapping [c_real_0 => Cnt_zero, c_real_add1 => Cnt_succ, c_real_sub1 => Cnt_pred]) : creal_scope.

Close Scope creal_scope.

Declare Scope pcreal_scope.
Delimit Scope pcreal_scope with pcreal.
Open Scope pcreal_scope.

Definition pc_Real := (pc ^Real).

Notation "x + y" := (pc_lift2 (fun a b : ^Real => a + b)%Real x y) : pcreal_scope.
Notation "x - y" := (pc_lift2 (fun a b => a - b)%Real x y) : pcreal_scope.
Notation "x * y" := (pc_lift2 (fun a b => a * b)%Real x y) : pcreal_scope.
Notation "x < y" := (exists x' y', defined_to x x' /\ defined_to y y' /\ x' < y')%Real : pcreal_scope. 
Notation "x > y" := (y < x)%pcreal : pcreal_scope.
Notation "x <= y" := (exists x' y', defined_to x x' /\ defined_to y y' /\ x' <= y')%Real : pcreal_scope. 
Notation "x >= y" := (y <= x)%pcreal : pcreal_scope.
Notation "x ≡ y" := (exists x' y', defined_to x x' /\ defined_to y y' /\ x' = y')%Real (at level 80) : pcreal_scope. 

Definition pc_real_0 := pc_unit ^Real real_0.

Definition pc_real_1 := pc_unit ^Real real_1.

Definition pc_real_add1 := fun x => x + pc_real_1.

Definition pc_real_sub1 := fun x => x - pc_real_1.

Number Notation pc_Real Z_to_my_cnt my_cnt_to_Z (via my_cnt mapping [pc_real_0 => Cnt_zero, pc_real_add1 => Cnt_succ, pc_real_sub1 => Cnt_pred]) : pcreal_scope.

Lemma pc_defined_to_is_hprop A : forall (x : pc A), is_hprop {x' | defined_to x x'}.
Proof.
  intros x [a p] [b q].
  assert (a = b).
  rewrite p in q.
  apply pc_unit_mono in q.
  auto.
  destruct H.
  assert (p = q) by apply irrl.
  destruct H.
  auto.
Defined.

Definition pc_recip : pc_Real -> pc_Real.
Proof.
  intro x.
  apply (pc_hprop_lem {x' | defined_to x x'} (pc_defined_to_is_hprop _ _)).
  intro.
  destruct X.
  destruct s.
  apply (pc_Prop_lem (x0 = real_0)).
  intro.
  destruct H.
  exact pc_bot.
  exact (pc_unit _ (/ n)).
  exact pc_bot.
Defined.


Notation "/ x" := (pc_recip x) : pcreal_scope.

Notation "x / y" := (x * / y) : pcreal_scope.  

Notation "- x" := (0 - x) : pcreal_scope.

Definition pc_dist := pc_lift2 dist.

Definition pc_abs := pc_lift abs.

Close Scope pcreal_scope.



