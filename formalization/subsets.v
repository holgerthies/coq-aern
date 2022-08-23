(* this file proves various properties of subsets of real numbers *)

Require Import Real Euclidean List Minmax.


  Generalizable Variables K M Real.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
          {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
          {M_MultivalueMonad : MultivalueMonad}
          {Real : Type}
          {SemiDecOrderedField_Real : SemiDecOrderedField Real}
          {ComplArchiSemiDecOrderedField_Real : ComplArchiSemiDecOrderedField}.

Section Subsets.
  

  Context (d : nat).

  Definition euclidean_subset :=  (@euclidean Real d) -> Prop.
  Definition union (A B : euclidean_subset) := fun x => A x \/ B x.
  Definition intersection (A B : euclidean_subset) := fun x => A x /\ B x.
  Definition intersects (A B : euclidean_subset) := exists x, intersection A B x.
  Definition is_subset (A B : euclidean_subset) := forall x, A x -> B x.

  Definition empty_set : euclidean_subset := fun x => False.

  Definition ball := ((@euclidean Real d) * Real)%type.
  Definition ball_to_subset (b : ball)  : euclidean_subset := (fun x => (euclidean_max_dist x (fst b)) < (snd b)).  

  Definition diam (L : list ball) := (fold_right (fun b1 r => (real_max (snd b1) r)) real_0 L).
  Definition is_compact (M : euclidean_subset) := {L : nat -> list ball |
                                                    forall n, diam (L n) <= prec n /\
                                                    forall n b,  In b (L n)-> intersects (ball_to_subset b) M /\
                                                    forall n,  is_subset M (fold_right (fun b s => union (ball_to_subset b) s) empty_set (L n))
                                                    }. 

End Subsets.

Section Examples.
  Lemma split_euclidean2 (P : (@euclidean Real 2)) : { x & {y | P = (Euclidean.cons x (Euclidean.cons y Euclidean.nil))}}.
  Proof.
    pose proof  (dim_succ_destruct P).
    destruct X as [x P'].
    destruct P' as [P0 P1].
    pose proof (dim_succ_destruct P0).
    destruct X as [y P2].
    exists x.
    exists y.
    rewrite P1.
    destruct P2.
    f_equal.
    rewrite e.
    f_equal.
    apply dim_zero_destruct.
  Defined.

  Definition make_euclidean2 (x y : Real) := Euclidean.cons x (Euclidean.cons y Euclidean.nil).
  Definition make_ball (x y r : Real) : ball 2 := ((make_euclidean2 x y), r).

  Definition T : (euclidean_subset 2).
    unfold euclidean_subset.
    intro P.
    destruct (split_euclidean2 P) as [x [y P']].
    apply ((real_le real_0 x) /\ (real_le real_0 y) /\ (real_le (x + y) real_1)).
  Defined.

  Definition process (b : ball 2) : (ball 2) * (ball 2) * (ball 2).
  Proof.
    pose ((snd b) / real_2_neq_0) as r'.
    destruct (split_euclidean2 (fst b)) as [x [y P']].
    split.
    split.
    split.
    apply (make_euclidean2 (x-r') (y-r')).
    apply r'.
    split.
    apply (make_euclidean2 (x-r') (y+r')).
    apply r'.
    split.
    apply (make_euclidean2 (x+r') (y-r')).
    apply r'.
 Defined.

  Fixpoint coverIter (n : nat) (b : (ball 2)) : (list (ball 2)).
  Proof.  
    induction n as [| n' result].    
    apply (b :: nil).
    pose (process b).
    destruct p as [[p1 p2] p3].
    pose (coverIter n' p2) as l2.
    pose (coverIter n' p3) as l3.
    apply (p1 :: (app l2 l3)).
  Defined.
  Definition coverT (n : nat) : list (ball 2) := coverIter n (make_ball (real_1 / real_2_neq_0) (real_1 / real_2_neq_0) (real_1 / real_2_neq_0)).


    
End Examples.
 
 
