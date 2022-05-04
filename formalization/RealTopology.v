Require Import Real.
Require Import Enumerable.
Require Import rounding.

Section Dyadics.
  
  Generalizable Variables K M Real.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
          {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
          {M_MultivalueMonad : MultivalueMonad}
          {Real : Type}
          {SemiDecOrderedField_Real : SemiDecOrderedField Real}
          {ComplArchiSemiDecOrderedField_Real : ComplArchiSemiDecOrderedField}.


  (* Definition Dyadic : Set := Z * nat. *)
  Definition Dyadic (n : nat) := Z.
  Definition Dyadics := {n & Dyadic n}.
  Definition Dyadic_to_Real (n : nat) := fun z : Dyadic n => (IZreal z) * (prec n).
  Definition Dyadics_to_Real : Dyadics -> Real.
  Proof.
    intros [n z].
    exact (Dyadic_to_Real n z).
  Defined.

  Lemma Dyadic_is_enum : forall n, is_enum (Dyadic n).
  Proof.
    intro n.
    apply Z_is_enum.
  Defined.
  
  Lemma Dyadics_is_enum : is_enum Dyadics.
  Proof.
    apply enum_sigma_is_enum.
    apply nat_is_enum.
    apply Dyadic_is_enum.
  Defined.

  Lemma M_Dyadics_is_dense : forall x m, M {d | dist x (Dyadics_to_Real d) < prec m}.
  Proof.
    intros x m.
    pose proof (M_approx_seq_lt x m).
    unfold Dyadics_to_Real, Dyadic_to_Real.
    apply (fun k => M_lift _ _ k X).
    intro.
    destruct H.
    exists (existT _   m x0).
    rewrite real_mult_comm.
    rewrite dist_symm.
    exact r.  
  Defined.

  Lemma W_Dyadics_is_dense : forall x m, exists d, dist x (Dyadics_to_Real d) < prec m.
  Proof.
    intros x m.
    apply M_existence_to_classical.
    apply (M_Dyadics_is_dense x m).
  Defined.
  
  
End Dyadics.

Require Import Continuity.

Section Opens.
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

  Definition Opens X := X -> S.
  Definition O_in {X} := fun (x : X) (o : Opens X) => is_S_defined (o x). 

  Definition M_countable_choice_S : forall f : nat -> S, (exists n, is_S_defined (f n)) -> M {n | is_S_defined (f n)}.
  Proof.
    intros.
    unfold S in f.
    pose proof (M_countable_choice (fun n => @projP1 _ _  (f n))).
    assert ( (exists n : nat, lazy_bool_up ((fun n0 : nat => projP1 K (fun k : K => k <> lazy_bool_false) (f n0)) n))).
    destruct H.
    exists x.
    unfold is_S_defined  in H.
    unfold S_top in H.
    rewrite H.
    simpl.
    apply eq_refl.
    pose proof (X H0).
    clear X H0.
    apply (fun k => M_lift _ _ k X0).
    intro.
    destruct H0.
    exists x.
    unfold is_S_defined.
    unfold S_top.
    unfold lazy_bool_up in l.
    destruct (f x).
    simpl in l.
    apply (sigma_eqP _ _ _ _ _ _ l).
    apply irrl.
  Defined.

  Definition M_enum_choice_S : forall X (f : X -> S), is_enum X -> (exists n, is_S_defined (f n)) -> M {n | is_S_defined (f n)}.
  Proof.
    intros.
    destruct X0.
    pose proof (M_countable_choice_S (fun n => f (x n)) ).
    simpl in X0.
    assert (exists n : nat, is_S_defined (f (x n))).
    destruct H.
    destruct (s x0).
    exists x1.
    rewrite e.
    exact H.
    apply X0 in H0.
    apply (fun k => M_lift _ _ k H0).
    intro.
    destruct H1.
    exists (x x0).
    exact i.
  Defined.
  

  Lemma nat_open_choice : forall o : Opens nat, (exists n, O_in n o) -> M {n | O_in n o}.
  Proof.
    intros.
    exact (M_enum_choice_S nat _ nat_is_enum H).
  Defined.
  
  Lemma Real_open_choice : forall o : Opens Real, (exists x, O_in x o) -> M {x | O_in x o}. 
  Proof.
    intros.
    assert (exists d, O_in (Dyadics_to_Real d) o).
    +
      destruct H.
      pose proof (M_existence_to_classical _ _ (Continuity_principle o x H)).
      destruct H0.
      pose proof (W_Dyadics_is_dense x x0).
      destruct H1.
      pose proof (H0 _ H1).
      exists x1.
      exact H2.
    +
      pose proof (M_enum_choice_S Dyadics _ Dyadics_is_enum H0).
      apply (fun k => M_lift _ _ k X).
      intro.
      destruct H1.
      exists (Dyadics_to_Real x).
      exact i.
  Defined.
        
      
End Opens.

Section Subsets.
  
  Generalizable Variables K M Real.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
          {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
          {M_MultivalueMonad : MultivalueMonad}
          {Real : Type}
          {SemiDecOrderedField_Real : SemiDecOrderedField Real}
          {ComplArchiSemiDecOrderedField_Real : ComplArchiSemiDecOrderedField}.


  (* sub`set`s expressed by classical char function *)
  Definition subsets X := X -> Prop.
  Definition opens X := {p : X -> Prop & {s : X -> S | forall x, p x = is_S_defined (s x)} }.
  Definition closeds X := {p : X -> Prop & {s : X -> S | forall x, p x = is_S_undefined (s x)} }.
  Definition opens_top X : opens X.
  Proof.
    exists (fun x => True).
    exists (fun x => S_top).
    intro.
    unfold is_S_defined.
    apply Prop_ext; intros; auto.
  Defined.

  Definition opens_bot X : opens X.
  Proof.
    exists (fun x => False).
    exists (fun x => S_bot).
    intro.
    unfold is_S_defined.
    apply Prop_ext; intros.
    contradict H.
    unfold S_bot in H.
    unfold S_top in H.
    apply (lp _ _ (fun f => @projP1 _ _ f)) in H.
    simpl in H.
    apply eq_sym in H.
    contradict (lazy_bool_true_neq_undef H).
  Defined.

  Definition is_nbhd {X} (x : X) (o : opens X)
    := projT1 o x.

  Definition is_dense {X} (d : X -> Prop) :=
    forall x o, is_nbhd x o -> exists y, is_nbhd y o /\ (d y).
  

  
  Definition compacts X :=
    {p : X -> Prop & {s : (opens {x : X | p x}) -> S | forall O, is_S_defined (s O) = (O = opens_top _)}}.

  Definition overts X :=
    {p : X -> Prop & {s : (opens {x : X | p x}) -> S | forall O, is_S_defined (s O) = (O = opens_bot _)}}.
  (* Definition enum_dense_subset_overt_aux : forall X (p : X -> Prop), *)
  (*     is_enum {x | p x} -> is_dense p -> *)
  (*     (opens {x : X | True}) -> S. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply  S_countable_up. *)
  (*   intro n. *)
  (*   destruct X0. *)
  (*   pose proof (x n). *)
    
    
  (* Lemma enum_dense_subset_overt : forall X (p : X -> Prop), *)
  (*     is_enum {x | p x} -> is_dense p -> *)
  (*     {s : (opens {x : X | p x}) -> S | forall O, is_S_defined (s O) = (O = opens_bot _)}. *)
  (* Proof. *)
  (*   intros. *)
    
    
  
  Definition compacts_singleton {X} (x : X) : compacts X.
  Proof.
    exists (fun y => x = y).
    exists (fun o : opens {x0 : X | x = x0} => projP1 _ _ (projT2 o) (exist _ x eq_refl)).
    intros.
    apply Prop_ext; intros.
    destruct O.
    simpl in H.
    destruct s.
    simpl in H.
    simpl.
    unfold opens_top.
    assert (x0 = (fun _ : {x2 : X | x = x2} => True)).
    apply fun_ext.
    intro.
    rewrite e.
    apply Prop_ext; intros; auto.
    assert ( (exist (fun x0 : X => x = x0) x eq_refl) = x2).
    destruct x2.
    apply (sigma_eqP _ _ _ _ _ _ e0).
    apply irrl.
    rewrite H1 in H.
    exact H.
    
    apply (sigma_eqT _ _ _ _ _ _  H0).
    unfold tpp.
    destruct (  eq_rect x0 (fun y : {x2 : X | x = x2} -> Prop => {s : {x2 : X | x = x2} -> S | forall x2 : {x2 : X | x = x2}, y x2 = is_S_defined (s x2)}) (exist (fun s : {x2 : X | x = x2} -> S => forall x2 : {x2 : X | x = x2}, x0 x2 = is_S_defined (s x2)) x1 e)).
    assert (x2 = (fun _ : {x3 : X | x = x3} => S_top)).
    apply fun_ext; intros; auto.
    unfold is_S_defined in e0.
    rewrite <- e0.
    auto.
    apply (sigma_eqP _ _ _ _ _ _ H1).
    apply irrl.

    destruct O.
    simpl.
    destruct s.
    simpl.
    rewrite<- e.
    unfold opens_top in H.
    apply (lp _ _ (fun k => projT1 k)) in H.
    simpl in H.
    rewrite H.
    auto.
  Defined.
  
