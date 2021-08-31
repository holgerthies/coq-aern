(* this file proves various properties of subsets of real numbers *)

Require Import Real.



Section RealSubsets.
  
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


  Definition real_subset := Real -> Prop.
  Definition complement : real_subset -> real_subset := fun P x => ~ P x.
  Definition is_open : real_subset -> Prop := fun P => forall x, P x -> exists n, forall y, dist x y < prec n -> P y.
  Definition is_closed S := is_open (complement S).
  Definition w_approx (P : Real -> Prop) (n : nat) (x : Real) : Prop
    := exists y, P y /\ dist x y <= prec n.

  (* a predicate [P : Real -> Prop] is complete if for any converging seqeunce
   [f : nat -> real_] such that [w_approx P n (f n)] holds for all [n : nat],
   the limit point satisfies [P x]. For example, [Real \ {0}] is not complete. *)
  Definition is_seq_closed (P : Real -> Prop) :=
    forall f : nat -> Real,
      is_fast_cauchy f -> (forall n, w_approx P n (f n)) -> (forall x, is_fast_limit x f -> P x).

  Definition is_closed_is_seq_complete : forall P, is_closed P -> is_seq_closed P.
  Proof.
    intros P H f c j a b.
    destruct (lem (P a)); auto.
    pose proof (H _ H0).
    destruct H1.
    
    pose proof (j (S (S x))).
    unfold w_approx in H2.
    destruct H2.
    destruct H2.
    pose proof (H1 x0).
    contradict H2.
    apply H4.
    pose proof (b (S (S x))).
    (* pose proof (proj2 (dist_le_prop a (f (S (S x))) (prec (S (S x)))) H2). *)
    pose proof (dist_tri a (f (S (S x))) x0).
    pose proof (real_le_le_plus_le _ _ _ _ H2 H3).
    apply (real_ge_le) in H5.
    pose proof (real_le_le_le _ _ _ H5 H6).
    apply (real_le_lt_lt _ _ _ H7).
    assert ( prec (S (S x)) + prec (S (S x)) = prec (S x)).
    simpl.
    unfold real_div.
    replace (prec x * / real_2_neq_0 * / real_2_neq_0 +
             prec x * / real_2_neq_0 * / real_2_neq_0) with (prec x * (/ real_2_neq_0 * (real_1 + real_1) ) * / real_2_neq_0) by ring.
    rewrite real_mult_inv.
    ring_simplify.
    auto.
    rewrite H8.
    apply prec_S.
  Defined.
End RealSubsets.

