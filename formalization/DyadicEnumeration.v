Require Import Real.
Require Import rounding.

Section DyadicEnumeration.
  
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


  Definition Dyadic : Set := Z * nat.
  Definition Dyadic_to_Real := fun d : Dyadic => (IZreal (fst d)) * (prec (snd d)).
  
  Definition bool_nat_nat_Cantor_pair_decode : nat -> bool * (nat * nat).
  Admitted.

  Definition bool_nat_nat_Cantor_pair_encode : bool * (nat * nat) -> nat.
  Admitted.

  Lemma bool_nat_nat_Cantor_pair_sound : forall b n m,
      bool_nat_nat_Cantor_pair_decode (bool_nat_nat_Cantor_pair_encode (b, (n, m))) = (b, (n, m)).
  Proof.
  Admitted.
  

  
  Definition global_Dyadic_enumeration_defi : nat -> Dyadic.
  Proof.
    intro n.
    destruct (bool_nat_nat_Cantor_pair_decode n) as [b [i j]]. 
    destruct b.
    exact (Z.of_nat i, j).
    exact ((- (Z.of_nat i))%Z, j).
  Defined.

  Lemma global_Dyadic_enumeration :
    forall d : Dyadic, exists n, global_Dyadic_enumeration_defi n = d.
  Proof.
  Admitted.


  Lemma M_Dyadic_is_dense : forall x m, M {d | dist x (Dyadic_to_Real d) < prec m}.
  Proof.
    intros x m.
    pose proof (M_approx_seq_lt x m).
    unfold Dyadic_to_Real.
    apply (fun k => M_lift _ _ k X).
    intro.
    destruct H.
    exists (x0, m).
    simpl.
    rewrite real_mult_comm.
    rewrite dist_symm.
    exact r.  
  Defined.

  Lemma W_Dyadic_is_dense : forall x m, exists d, dist x (Dyadic_to_Real d) < prec m.
  Proof.
    intros x m.
    apply M_existence_to_classical.
    apply (M_Dyadic_is_dense x m).
  Defined.
  
  
End DyadicEnumeration.
