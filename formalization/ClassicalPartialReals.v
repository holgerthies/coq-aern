Require Import Base Real ClassicalMonads ClassicalPartiality RealAssumption.

Declare Scope pcreal_scope.
Open Scope pcreal_scope.
Delimit Scope pcreal_scope with pcreal.
                              
Definition pcReal := (pc ^Real).

Notation "x + y" := (pc_lift2 (fun a b => a + b)%Real x y) : pcreal_scope.
Notation "x - y" := (pc_lift2 (fun a b => a - b)%Real x y) : pcreal_scope.
Notation "x * y" := (pc_lift2 (fun a b => a * b)%Real x y) : pcreal_scope.
Notation "x < y" := (exists x' y', defined_to x x' /\ defined_to y y' /\ x' < y')%Real : pcreal_scope. 
Notation "x ≡ y" := (exists x' y', defined_to x x' /\ defined_to y y' /\ x' = y')%Real (at level 80) : pcreal_scope. 

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

Fixpoint my_cnt_to_option_Z (c : my_cnt) : Z.
Proof.
  destruct c.
  exact 0%Z.
  exact (my_cnt_to_option_Z c + 1)%Z.
  exact (my_cnt_to_option_Z c - 1)%Z.
Defined.

Definition pc_real_0 := pc_unit ^Real real_0.

Definition pc_real_1 := pc_unit ^Real real_1.

Definition pc_real_add1 := fun x => x + pc_real_1.

Definition pc_real_sub1 := fun x => x - pc_real_1.

Number Notation pcReal Z_to_my_cnt my_cnt_to_option_Z (via my_cnt mapping [pc_real_0 => Cnt_zero, pc_real_add1 => Cnt_succ, pc_real_sub1 => Cnt_pred]) : pcreal_scope.

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

Definition pc_recip : pc ^Real -> pc ^Real.
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

Lemma pc_real_plus_comm : forall r1 r2 : pcReal, r1 + r2 = r2 + r1.
Proof.
  intros.
  destruct (pc_case r1).
  rewrite H.
  rewrite pc_lift2_fst_bot.
  rewrite pc_lift2_snd_bot.
  auto.
  destruct (pc_case r2).
  rewrite H0.
  rewrite pc_lift2_fst_bot.
  rewrite pc_lift2_snd_bot.
  auto.
  destruct H, H0.
  rewrite H, H0.
  rewrite pc_unit_ntrans2.
  rewrite pc_unit_ntrans2.
  rewrite real_plus_comm.
  auto.
Defined.  
  
Lemma pc_real_plus_assoc : forall r1 r2 r3 : pcReal, r1 + r2 + r3 = r1 + (r2 + r3).
Proof.
  intros.
  destruct (pc_case r1).
  rewrite H.
  repeat (try rewrite pc_lift2_fst_bot; try rewrite pc_lift2_snd_bot); auto.
  destruct (pc_case r2).
  rewrite H0.
  repeat (try rewrite pc_lift2_fst_bot; try rewrite pc_lift2_snd_bot); auto.
  destruct (pc_case r3).
  rewrite H1.
  repeat (try rewrite pc_lift2_fst_bot; try rewrite pc_lift2_snd_bot); auto.
  destruct H, H0, H1.
  rewrite H, H0, H1.
  rewrite pc_unit_ntrans2.
  rewrite pc_unit_ntrans2.
  rewrite pc_unit_ntrans2.
  rewrite pc_unit_ntrans2.
  rewrite real_plus_assoc.
  auto.
Defined.  

Notation "- x" := (0 - x) : pcreal_scope.

Close Scope pcreal_scope.
