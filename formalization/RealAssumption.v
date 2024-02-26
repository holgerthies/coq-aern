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
