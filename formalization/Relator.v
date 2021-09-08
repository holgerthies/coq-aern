Require Import Real.
Require Import Nabla.
Require Import Reals.

(*
  Unlike the ideal classical reals described in the paper,
  Coq's classical real R is partial; i.e., 1/0 is a valid term of tyle R.
  Hence, we define totalR as sub-object of R which are total.
  For the purpose, we defien a classical predicate is_total : R -> Prop, 
  and define totalR := {x : R | is_total x}.
  We axiomatize our relator as a function of type relator : Real -> totalR.
 *)



(** totality *)
Inductive is_total : R -> Prop :=
  is_total_constant0 : is_total R0
| is_total_constant1 : is_total R1
| is_total_addition : forall x y, is_total x -> is_total y -> is_total (x + y)
| is_total_multiplication : forall x y, is_total x -> is_total y -> is_total (x * y)
| is_total_division : forall x, is_total x -> (x <> R0) -> is_total (/ x)
| is_total_subtraction : forall x, is_total x -> is_total (-x )
| is_total_limit : forall (x :R), (forall n, exists y,  is_total y /\ (Rabs (y - x) < (/ 2 ^ n))%R) -> is_total x.

Lemma is_total_minus : forall x y, is_total x -> is_total y ->  is_total (x - y)%R.
Proof.
  intros.
  apply is_total_addition; auto.
  apply is_total_subtraction; auto.
Qed.
Lemma is_total_division2 : forall x y, is_total x -> is_total y -> (y <> R0) -> is_total (x/y)%R.
Proof.
  intros.
  apply is_total_multiplication.
  exact H.
  apply is_total_division.
  exact H0.
  exact H1.
Qed.
               

Definition totalR := {x : R | is_total x}.
Definition totalR0 : totalR := exist (fun x => is_total x) R0 is_total_constant0.
Definition totalR1 : totalR := exist (fun x => is_total x) R1 is_total_constant1.
Definition totalRadd : totalR -> totalR -> totalR.
Proof.
  intros [x tx] [y ty].
  exists (x + y)%R.
  exact (is_total_addition x y tx ty).
Defined.

Definition totalRmult : totalR -> totalR -> totalR.
Proof.
  intros [x tx] [y ty].
  exists (x * y)%R.
  exact (is_total_multiplication x y tx ty).
Defined.

Definition totalRlt : totalR -> totalR -> Prop.
Proof.
  intros [x tx] [y ty].
  exact (x < y)%R.
Defined.

Definition totalRsub : totalR -> totalR.
Proof.
  intros [x tx].
  exists (- x)%R.
  exact (is_total_subtraction x tx).
Defined.

Definition totalRdiv : {x : totalR | x <> totalR0} -> totalR.
Proof.
  intros [x p].
  destruct x as [x tx].
  exists (/ x)%R.
  assert (x <> R0).
  intro H.
  unfold totalR0 in p.
  contradict p.
  apply (sigma_eqP _ _ _ _ _ _ H).
  apply irrl.  
  exact (is_total_division x tx H).
Defined.



(** relator *)

Section Relator.
  Generalizable Variables K M Real.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
          {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
          {M_MultivalueMonad : MultivalueMonad}
          {Real : Type}
          {SemiDecOrderedField_Real : SemiDecOrderedField Real}
          {ComplArchiSemiDecOrderedField_Real : ComplArchiSemiDecOrderedField}.

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

  
  Parameter relator : Real -> Nabla.nabla totalR.
  Axiom relator_mono : forall x y, relator x = relator y -> x = y.
  Axiom relator_epi : forall y, exists x, y = relator x. 
  Lemma relator_mono_neg : forall x y, x <> y -> relator x <> relator y.
  Proof.
    intros.
    intro.
    apply relator_mono in H0.
    exact (H H0).
  Defined.



  (* axioms for characterizing relator *)
  Axiom relator_constant0 : relator real_0 = Nabla.nabla_unit _ totalR0.
  Axiom relator_constant1 : relator real_1 = Nabla.nabla_unit _ totalR1.
  Axiom relator_addition : forall x y, relator (x + y) = (Nabla.lift_binary _ _ _ totalRadd) (relator x) (relator y).
  Axiom relator_multiplication : forall x y, relator (x * y) = (Nabla.lift_binary _ _ _ totalRmult) (relator x) (relator y).
  Axiom relator_subtraction : forall x, relator (-x) = (Nabla.lift_unary _ _ totalRsub) (relator x).

  Definition relator_div_tmp : forall x (p : x <> real_0), Nabla.nabla totalR.
  Proof.
    intros.
    assert (Nabla.nabla ({x : totalR | x <> totalR0})).
    apply Nabla.transport_ex.
    apply (Nabla.fancy_lift_unary _ _ (relator x)).
    intros.
    exists (Nabla.nabla_unit _ z).
    unfold Nabla.transport_fiber.
    intros.
    intro.
    pose proof (Nabla.nabla_mono _ _ _ H0).
    rewrite H2 in H1.
    rewrite H1 in H.
    contradict p.
    pose proof (relator_constant0).
    rewrite <- H3 in H.
    apply relator_mono.
    exact H.

    apply (Nabla.lift_unary {x : totalR | x <> totalR0} _).
    intro.
    exact (totalRdiv H).
    exact X.
  Defined.

  Axiom relator_division : forall x (p : x <> real_0), relator (/ p) = relator_div_tmp x p.

  Axiom relator_lt : forall x y, x < y = Nabla.lift_domain_binary _ _ _ totalRlt Nabla.Prop_is_nabla_modal (relator x) (relator y). 






  Section transfer.

    Definition transfer_fiberT : (Real -> Type) -> (Nabla.nabla totalR -> Type).
    Proof.
      intros P x.
      exact (forall y, x = relator y -> P y).
    Defined.
    

    Definition transfer_fiberP : (Real -> Prop) -> (Nabla.nabla totalR -> Prop).
    Proof.
      intros P x.
      exact (forall y, x = relator y -> P y).
    Defined.

    
    Definition transfer_forallP : forall (P : Real -> Prop),
        (forall x : Nabla.nabla totalR,(transfer_fiberP P x)) -> (forall x : Real, P x).
    Proof.
      unfold transfer_fiberP.    
      intros.
      pose proof (H (relator x)).
      apply (H0 x (eq_refl _)).
    Defined.

    
    Definition transfer_existsP : forall (P : Real -> Prop), (exists x : Nabla.nabla totalR, (transfer_fiberP P x)) -> (exists x : Real, P x).
    Proof.
      unfold transfer_fiberP.    
      intros.
      destruct H.
      pose proof (relator_epi x).
      destruct H0.
      exists x0.
      exact (H _ H0).
    Defined.
    
    


    
    (* Definition transfer_forallT : forall (P : Real -> Type), (forall x : Nabla.nabla totalR, Nabla.nabla (transfer_fiberT P x)) -> (forall x : Real, P x). *)
    (* Proof. *)
    (*   unfold transfer_fiberT.     *)
    (*   intros. *)
    
    
    

    
    (* Definition transfer_forallT : forall (P : Real -> Type), (forall x : Nabla.nabla totalR, Nabla.nabla (transfer_fiberT P x)) -> (forall x : Real, P x). *)
    (* Proof. *)
    (*   unfold transfer_fiberT.     *)
    (*   intros. *)
    
    
    
  End transfer.
End Relator.
  
