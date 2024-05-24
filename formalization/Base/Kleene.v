Require Import Base.

(** Kleene type **)
Class LazyBool_K (types : RealTypes) :=
  {
    lazy_bool_true : @K types;
    lazy_bool_false : @K types;

    lazy_bool_neg : @K types -> @K types;
    lazy_bool_or : @K types -> @K types -> @K types;
    lazy_bool_and : @K types -> @K types -> @K types;

    lazy_bool_defined_is_bool : forall k,
        (k = lazy_bool_true \/ k = lazy_bool_false) -> ({k = lazy_bool_true} + {k = lazy_bool_false});
    lazy_bool_neg_up : forall k, (lazy_bool_neg k = lazy_bool_true) = (k = lazy_bool_false);
    lazy_bool_neg_down : forall k, (lazy_bool_neg k = lazy_bool_false) = (k = lazy_bool_true);

    lazy_bool_and_up : forall a b, (lazy_bool_and a b = lazy_bool_true) = (a = lazy_bool_true /\ b = lazy_bool_true);
    lazy_bool_and_down : forall a b, (lazy_bool_and a b = lazy_bool_false) = (a = lazy_bool_false \/ b = lazy_bool_false);

    lazy_bool_or_up : forall a b, (lazy_bool_or a b = lazy_bool_true) = (a = lazy_bool_true \/ b = lazy_bool_true);
    lazy_bool_or_down : forall a b, (lazy_bool_or a b = lazy_bool_false) = (a = lazy_bool_false /\ b = lazy_bool_false);
    lazy_bool_distinct : lazy_bool_false <> lazy_bool_true
  }.

Section K_Defs.

  Context {types : RealTypes} (lbK : LazyBool_K types).

  Definition lazy_bool_up : K -> Prop := fun b : K => b = lazy_bool_true.
  Definition lazy_bool_down : K -> Prop := fun b : K => b = lazy_bool_false.

  (* Search _ (K -> _). *)

End K_Defs.
