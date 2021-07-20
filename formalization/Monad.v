Require Import Base.
(** Multivalue monad **)
(* Functor structure: *)

Structure Monad : Type :=
  {
    (* monad is a functor *)
    Monad_obj_map : Type -> Type; 
    Monad_fun_map : forall A B, (A -> B) -> Monad_obj_map A -> Monad_obj_map B;
    Monad_functorial_comp : forall A B C (f : A -> B) (g : B -> C),
        Monad_fun_map _ _ (fun x => g (f x)) = fun x => (Monad_fun_map _ _ g) ((Monad_fun_map _ _ f) x);
    Monad_functorial_id :  forall A, (fun x : Monad_obj_map A => x) = Monad_fun_map A A (fun x => x);

    (* monad has unit and mult *)
    Monad_unit : forall A : Type, A -> Monad_obj_map A;
    Monad_mult : forall A : Type, Monad_obj_map (Monad_obj_map A) -> Monad_obj_map A;

    (* unit and mult are nat. trans.  *)
    Monad_unit_ntrans : forall A B (f : A -> B) x, (Monad_fun_map A B f) (Monad_unit A x) = Monad_unit B (f x);

    Monad_mult_ntrans : forall A B (f : A -> B) x, Monad_mult B ((Monad_fun_map (Monad_obj_map A) (Monad_obj_map B) (Monad_fun_map A B f)) x) = (Monad_fun_map A B f) (Monad_mult A x);  

    (* coherence conditions *)
    Monad_coh1 : forall A x, Monad_mult A (Monad_unit (Monad_obj_map A) x) = x;
    Monad_coh2 : forall A x, Monad_mult A (Monad_fun_map A (Monad_obj_map A) (Monad_unit A)  x) = x;
    Monad_coh3 : forall A x, Monad_mult A (Monad_mult (Monad_obj_map A) x) = Monad_mult A (Monad_fun_map (Monad_obj_map (Monad_obj_map A)) (Monad_obj_map A) (Monad_mult A) x);

  }.

(* monad morphism as a monoidal morhism *)
Structure Monoid_hom (F G : Monad) :=
  {
    Monoid_hom_nat_trans : forall A, Monad_obj_map F A -> Monad_obj_map G A;
    Monoid_hom_nat_trans_prop : forall A B (f : A -> B),
        (fun x => Monoid_hom_nat_trans B (Monad_fun_map F _ _ f x)) =
                        (fun x => (Monad_fun_map G _ _ f) (Monoid_hom_nat_trans A x));
    Monoid_hom_unit : forall A, (fun x => Monoid_hom_nat_trans A (Monad_unit F A x)) = Monad_unit G A; 
    Monoid_hom_mult : forall A, (fun x => Monoid_hom_nat_trans A (Monad_mult F A x)) =
                                (fun x => Monad_mult G A (Monoid_hom_nat_trans (Monad_obj_map G A) (Monad_fun_map F _ _ (Monoid_hom_nat_trans A) x)));
  }.

(* note that this can be stronger than mono in nat. trans. in general setting *)
Definition Monoid_hom_is_mono {F G : Monad} (m : Monoid_hom F G) :=
  forall A, is_mono (Monoid_hom_nat_trans F G m A).

Definition Monoid_hom_is_equiv {F G : Monad} (m : Monoid_hom F G) :=
  forall A, is_equiv (Monoid_hom_nat_trans F G m A).

(* Definition Monoid_equiv (F G : Monad) := *)
(*   {f : Monoid_hom F G | forall A, is_mono (Monoid_hom_nat_trans F G f A)}. *)

