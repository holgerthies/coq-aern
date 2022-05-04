Require Import Real.
Require Export Sierpinski.

Section Continuity.
  
  Generalizable Variables K M Real.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
          {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
          {M_MultivalueMonad : MultivalueMonad}
          {Real : Type}
          {SemiDecOrderedField_Real : SemiDecOrderedField Real}
          {ComplArchiSemiDecOrderedField_Real : ComplArchiSemiDecOrderedField}
          .

  
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

  Axiom Continuity_principle :
    forall (o : Real -> S) x, is_S_defined (o x) -> M{n | forall y, dist x y < prec n -> is_S_defined (o y)}. 

  Definition W_is_cont_at_nm (f : Real -> Real) (x : Real) : Prop
    := forall m, exists n, forall y, dist x y < prec n -> dist (f x) (f y) < prec m.

  Definition C_is_cont_at_nm (f : Real -> Real) (x : Real)
    := forall m, M{n | forall y, dist x y < prec n -> dist (f x) (f y) < prec m}.

  Lemma C_cont_at_nm_W_cont_at_nm : forall (f : Real -> Real) x, C_is_cont_at_nm f x -> W_is_cont_at_nm f x.
  Proof.
    intros.
    intros m.
    apply M_existence_to_classical.
    exact (X m).
  Defined.
  
  
  Definition W_is_cont_nm f := forall x, W_is_cont_at_nm f x.
  
  Definition C_is_cont_nm f := forall x, C_is_cont_at_nm f x.

  Lemma C_cont_nm_W_cont_nm_W : forall f, C_is_cont_nm f -> W_is_cont_nm f.
  Proof.
    intros f X x.
    apply C_cont_at_nm_W_cont_at_nm.
    exact (X x).
  Defined.
  
  Lemma real_lt_S_semidec : forall x y, S_semidec (x < y).
  Proof.
    intros.
    apply K_semidec_is_S_semidec.
    apply real_lt_semidec.
  Defined.

  Lemma Continuity_principle_S_semidec :
    forall (o : Real -> Prop),
      (forall x, S_semidec (o x)) ->
      forall x, o x -> M{n | forall y, dist x y < prec n -> o y}.
  Proof.
    intros.
    pose proof
         (Continuity_principle (fun y => @projP1 _ _ (X y)) x).
    simpl in X0.
    destruct (X x).
    simpl in X0.
    rewrite e in X0.
    apply X0 in H.
    clear X0.
    clear e.
    apply (fun k => M_lift _ _ k H).
    intro.
    destruct H0.
    exists x1.
    intro.
    pose proof (i y).
    intro.
    pose proof (H0 H1).
    destruct (X y).
    simpl in H2.
    rewrite e in H2; auto.
  Defined.
    
  Lemma C_cont_nm : forall f, C_is_cont_nm f.
  Proof.
    intros f x m.
    pose proof (Continuity_principle_S_semidec (fun y => dist (f x) (f y) < prec m) (fun x0 => real_lt_S_semidec _ _) (x)).
    simpl in X.
    apply X.
    pose proof (dist_prop (f x) (f x)) as [_ [j _]].
    rewrite (j (eq_refl)).
    apply prec_pos.
  Defined.

End Continuity.
