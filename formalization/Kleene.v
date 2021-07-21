Require Import Base.

(** Kleene type **)
Class LazyBool (LB : Type) :=
  {
    lazy_bool_true : LB;
    lazy_bool_false : LB;

    lazy_bool_neg : LB -> LB;
    lazy_bool_or : LB -> LB -> LB;
    lazy_bool_and : LB -> LB -> LB;

    lazy_bool_defined_is_bool : forall k,
        (k = lazy_bool_true \/ k = lazy_bool_false) -> ({k = lazy_bool_true} + {k = lazy_bool_false});
    lazy_bool_neg_up : forall k, (lazy_bool_neg k = lazy_bool_true) = (k = lazy_bool_false);
    lazy_bool_neg_down : forall k, (lazy_bool_neg k = lazy_bool_false) = (k = lazy_bool_true);

    lazy_bool_and_up : forall a b, (lazy_bool_and a b = lazy_bool_true) = (a = lazy_bool_true /\ b = lazy_bool_true);
    lazy_bool_and_down : forall a b, (lazy_bool_and a b = lazy_bool_false) = (a = lazy_bool_false \/ b = lazy_bool_false);

    lazy_bool_or_up : forall a b, (lazy_bool_or a b = lazy_bool_true) = (a = lazy_bool_true \/ b = lazy_bool_true);
    lazy_bool_or_down : forall a b, (lazy_bool_or a b = lazy_bool_false) = (a = lazy_bool_false /\ b = lazy_bool_false);
  }.
