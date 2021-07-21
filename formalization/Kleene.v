Require Import Base.

(** Kleene type **)
Structure LazyBool : Type :=
  {
    lazy_bool :> Set;
    lazy_bool_true : lazy_bool;
    lazy_bool_false : lazy_bool;

    lazy_bool_neg : lazy_bool -> lazy_bool;
    lazy_bool_or : lazy_bool -> lazy_bool -> lazy_bool;
    lazy_bool_and : lazy_bool -> lazy_bool -> lazy_bool;

    lazy_bool_defined_is_bool : forall k,
        (k = lazy_bool_true \/ k = lazy_bool_false) -> ({k = lazy_bool_true} + {k = lazy_bool_false});
    lazy_bool_neg_up : forall k, (lazy_bool_neg k = lazy_bool_true) = (k = lazy_bool_false);
    lazy_bool_neg_down : forall k, (lazy_bool_neg k = lazy_bool_false) = (k = lazy_bool_true);

    lazy_bool_and_up : forall a b, (lazy_bool_and a b = lazy_bool_true) = (a = lazy_bool_true /\ b = lazy_bool_true);
    lazy_bool_and_down : forall a b, (lazy_bool_and a b = lazy_bool_false) = (a = lazy_bool_false \/ b = lazy_bool_false);

    lazy_bool_or_up : forall a b, (lazy_bool_or a b = lazy_bool_true) = (a = lazy_bool_true \/ b = lazy_bool_true);
    lazy_bool_or_down : forall a b, (lazy_bool_or a b = lazy_bool_false) = (a = lazy_bool_false /\ b = lazy_bool_false);
  }.

Parameter kleenean : LazyBool.
Definition kleenean_true := lazy_bool_true kleenean.
Definition kleenean_false := lazy_bool_false kleenean.
Definition kleenean_up : kleenean -> Prop := fun b : kleenean => b = kleenean_true.
Definition kleenean_down : kleenean -> Prop := fun b : kleenean => b = kleenean_false.
Definition kleenean_defined (k : kleenean) := kleenean_up k \/ kleenean_down k.
Definition kleenean_neg := lazy_bool_neg kleenean. 
Definition kleenean_and := lazy_bool_and kleenean.
Definition kleenean_or := lazy_bool_or kleenean.
Definition kleenean_defined_is_bool : forall k, kleenean_defined k -> {kleenean_up k} + {kleenean_down k}
  := lazy_bool_defined_is_bool kleenean.
Definition kleenean_neg_up :
  forall k : kleenean, kleenean_up (kleenean_neg k) = kleenean_down k
  := lazy_bool_neg_up kleenean.

Definition kleenean_neg_down :
  forall k : kleenean, kleenean_down (kleenean_neg k) = kleenean_up k
  := lazy_bool_neg_down kleenean.

Definition kleenean_and_up :
  forall a b : kleenean, kleenean_up (kleenean_and a b) = (kleenean_up a /\ kleenean_up b)
  := lazy_bool_and_up kleenean.

Definition kleenean_and_down :
  forall a b : kleenean, kleenean_down (kleenean_and a b) = (kleenean_down a \/ kleenean_down b)
  := lazy_bool_and_down kleenean.

Definition kleenean_or_up :
  forall a b : kleenean, kleenean_up (kleenean_or a b) = (kleenean_up a \/ kleenean_up b)
  := lazy_bool_or_up kleenean.

Definition kleenean_or_down :
  forall a b : kleenean, kleenean_down (kleenean_or a b) = (kleenean_down a /\ kleenean_down b)
  := lazy_bool_or_down kleenean.


Opaque kleenean_true kleenean_false kleenean_up kleenean_down kleenean_defined kleenean_neg kleenean_and kleenean_or kleenean_defined_is_bool kleenean_neg_up kleenean_neg_down kleenean_and_up kleenean_and_down kleenean_or_up kleenean_or_down.
