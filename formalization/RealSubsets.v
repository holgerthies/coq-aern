(* this file proves various properties of subsets of real numbers *)

Require Import Real.



Section RealSubsets.
  
  Context {T : ComplArchiSemiDecOrderedField}.
  Notation R := (CarrierField T).
  
  Ltac IZReal_tac t :=
    match t with
    | @real_0 R => constr:(0%Z)
    | @real_1 R => constr:(1%Z)
    | @IZreal R ?u =>
      match isZcst u with
      | true => u
      | _ => constr:(InitialRing.NotConstant)
      end
    | _ => constr:(InitialRing.NotConstant)
    end.

  Add Ring realRing : (realTheory R) (constants [IZReal_tac]).
  
  Notation real_ := (real R).
  Notation real_0_ := (@real_0 R).
  Notation real_1_ := (@real_1 R).
  Notation prec_ := (@prec R).


  Definition real_subset := real_ -> Prop.
  Definition complement : real_subset -> real_subset := fun P x => ~ P x.
  Definition is_open : real_subset -> Prop := fun P => forall x, P x -> exists n, forall y, dist x y < prec_ n -> P y.
  Definition is_closed S := is_open (complement S).
  Definition w_approx (P : real_ -> Prop) (n : nat) (x : real_) : Prop
    := exists y, P y /\ dist x y <= prec_ n.

  (* a predicate [P : real_ -> Prop] is complete if for any converging seqeunce
   [f : nat -> real_] such that [w_approx P n (f n)] holds for all [n : nat],
   the limit point satisfies [P x]. For example, [real_ \ {0}] is not complete. *)
  Definition is_seq_closed (P : real_ -> Prop) :=
    forall f : nat -> real_,
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
    (* pose proof (proj2 (dist_le_prop a (f (S (S x))) (prec_ (S (S x)))) H2). *)
    pose proof (dist_tri a (f (S (S x))) x0).
    pose proof (real_le_le_plus_le _ _ _ _ H2 H3).
    apply (real_ge_le) in H5.
    pose proof (real_le_le_le _ _ _ H5 H6).
    apply (real_le_lt_lt _ _ _ H7).
    assert ( prec_ (S (S x)) + prec_ (S (S x)) = prec_ (S x)).
    simpl.
    unfold real_div.
    replace (prec_ x * / real_2_neq_0 * / real_2_neq_0 +
             prec_ x * / real_2_neq_0 * / real_2_neq_0) with (prec_ x * (/ real_2_neq_0 * (real_1 + real_1) ) * / real_2_neq_0) by ring.
    rewrite real_mult_inv.
    ring_simplify.
    auto.
    rewrite H8.
    apply prec_S.
  Defined.
End RealSubsets.

