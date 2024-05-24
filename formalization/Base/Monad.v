Require Import Base.
(** Multivalue monad **)
(* Functor structure: *)

Class Monad (m : Type -> Type) :=
  {
    (* monad is a functor *)
    Monad_fun_map : forall A B, (A -> B) -> m A -> m B;
    Monad_functorial_comp : forall A B C (f : A -> B) (g : B -> C),
        Monad_fun_map _ _ (fun x => g (f x)) = fun x => (Monad_fun_map _ _ g) ((Monad_fun_map _ _ f) x);
    Monad_functorial_id :  forall A, (fun x : m A => x) = Monad_fun_map A A (fun x => x);

    (* monad has unit and mult *)
    Monad_unit : forall A : Type, A -> m A;
    Monad_mult : forall A : Type, m (m A) -> m A;

    (* unit and mult are nat. trans.  *)
    Monad_unit_ntrans : forall A B (f : A -> B) x, (Monad_fun_map A B f) (Monad_unit A x) = Monad_unit B (f x);

    Monad_mult_ntrans : forall A B (f : A -> B) x, Monad_mult B ((Monad_fun_map (m A) (m B) (Monad_fun_map A B f)) x) = (Monad_fun_map A B f) (Monad_mult A x);  

    (* coherence conditions *)
    Monad_coh1 : forall A x, Monad_mult A (Monad_unit (m A) x) = x;
    Monad_coh2 : forall A x, Monad_mult A (Monad_fun_map A (m A) (Monad_unit A)  x) = x;
    Monad_coh3 : forall A x, Monad_mult A (Monad_mult (m A) x) = Monad_mult A (Monad_fun_map (m (m A)) (m A) (Monad_mult A) x);

  }.

Definition Monad_fun_map_dom {m : Type -> Type} {Monad_m : Monad m} : forall A B, (A -> m B) -> m A -> m B :=
    fun A B f => fun x => Monad_mult B ((Monad_fun_map A (m B) f) x).

Section Monoid_hom.

Context {F : Type -> Type} (fM : Monad F) {G : Type -> Type} (gM : Monad G).

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
Definition Monoid_hom_is_mono (mh : Monoid_hom) :=
  forall A, is_mono (Monoid_hom_nat_trans A).

Definition Monoid_hom_is_equiv (mh : Monoid_hom) :=
  forall A, is_equiv (Monoid_hom_nat_trans A).

(* Definition Monoid_equiv (F G : Monad) := *)
(*   {f : Monoid_hom F G | forall A, is_mono (Monoid_hom_nat_trans F G f A)}. *)

End Monoid_hom.
