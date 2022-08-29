Require Import Base.
(** Multivalue monad **)
(* Functor structure: *)

Class Monad (types : RealTypes) :=
  {
    (* monad is a functor *)
    Monad_fun_map : forall A B, (A -> B) -> @M types A -> @M types B;
    Monad_functorial_comp : forall A B C (f : A -> B) (g : B -> C),
        Monad_fun_map _ _ (fun x => g (f x)) = fun x => (Monad_fun_map _ _ g) ((Monad_fun_map _ _ f) x);
    Monad_functorial_id :  forall A, (fun x : @M types A => x) = Monad_fun_map A A (fun x => x);

    (* monad has unit and mult *)
    Monad_unit : forall A : Type, A -> @M types A;
    Monad_mult : forall A : Type, @M types (@M types A) -> @M types A;

    (* unit and mult are nat. trans.  *)
    Monad_unit_ntrans : forall A B (f : A -> B) x, (Monad_fun_map A B f) (Monad_unit A x) = Monad_unit B (f x);

    Monad_mult_ntrans : forall A B (f : A -> B) x, Monad_mult B ((Monad_fun_map (@M types A) (@M types B) (Monad_fun_map A B f)) x) = (Monad_fun_map A B f) (Monad_mult A x);  

    (* coherence conditions *)
    Monad_coh1 : forall A x, Monad_mult A (Monad_unit (@M types A) x) = x;
    Monad_coh2 : forall A x, Monad_mult A (Monad_fun_map A (@M types A) (Monad_unit A)  x) = x;
    Monad_coh3 : forall A x, Monad_mult A (Monad_mult (@M types A) x) = Monad_mult A (Monad_fun_map (@M types (@M types A)) (@M types A) (Monad_mult A) x);

  }.

Generalizable Variable types.

Definition Monad_fun_map_dom `(Monad_M : Monad types) : forall A B, (A -> M B) -> M A -> M B :=
    fun A B f => fun x => Monad_mult B ((Monad_fun_map A (M B) f) x).

Section Monoid_hom.

Generalizable Variables typesF typesG.

Context `(fM : Monad typesF) `(gM : Monad typesG).

Definition F := @M typesF.
Definition G := @M typesG.

(* monad morphism as a monoidal morhism *)
Class Monoid_hom :=
  {
    Monoid_hom_nat_trans : forall A, F A -> G A;
    Monoid_hom_nat_trans_prop : forall A B (f : A -> B),
        (fun x => Monoid_hom_nat_trans B (Monad_fun_map _ _ f x)) =
                        (fun x => (Monad_fun_map _ _ f) (Monoid_hom_nat_trans A x));
    Monoid_hom_unit : forall A, (fun x => Monoid_hom_nat_trans A (Monad_unit A x)) = Monad_unit A; 
    Monoid_hom_mult : forall A, (fun x => Monoid_hom_nat_trans A (Monad_mult A x)) =
                                (fun x => Monad_mult A (Monoid_hom_nat_trans (G A) (Monad_fun_map _ _ (Monoid_hom_nat_trans A) x)));
  }.

(* note that this can be stronger than mono in nat. trans. in general setting *)
Definition Monoid_hom_is_mono (m : Monoid_hom) :=
  forall A, is_mono (Monoid_hom_nat_trans A).

Definition Monoid_hom_is_equiv (m : Monoid_hom) :=
  forall A, is_equiv (Monoid_hom_nat_trans A).

(* Definition Monoid_equiv (F G : Monad) := *)
(*   {f : Monoid_hom F G | forall A, is_mono (Monoid_hom_nat_trans F G f A)}. *)

End Monoid_hom.
