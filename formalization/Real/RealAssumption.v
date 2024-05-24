Require Import Real.
Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

Notation "^K" := (@K types) (at level 0).
Notation "^M" := (@M types) (at level 0).
Notation "^Real" := (@Real types) (at level 0).

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

Require Import ZArith.

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

Definition real_add1 : ^Real -> ^Real := fun x => x + real_1.

Definition real_sub1 : ^Real -> ^Real := fun x => x - real_1.

Definition _real_0 : ^Real := real_0.

Definition _real_1 : ^Real := real_1.

Definition REAL := (@Real types).

Number Notation REAL Z_to_my_cnt my_cnt_to_Z (via my_cnt mapping [_real_0 => Cnt_zero, real_add1 => Cnt_succ, real_sub1 => Cnt_pred]) : Real_scope.
