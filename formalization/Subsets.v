Require Import Real.
Require Import Minmax.
Require Import MultiLimit.
Require Import Euclidean.
Require Import Psatz.

Section Subsets.

  Generalizable Variables K M Real.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
    {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
    {M_MultivalueMonad : MultivalueMonad}
    {Real : Type}
    {SemiDecOrderedField_Real : SemiDecOrderedField Real}
    {ComplArchiSemiDecOrderedField_Real : ComplArchiSemiDecOrderedField}.


  Add Ring realRing : realTheory.
  
  Definition csubset (n : nat) := @euclidean Real n -> Prop. 

  Definition union {n : nat} : (csubset n) -> (csubset n) -> (csubset n).
  Proof.
    intros S T x.
    exact (S x \/ T x).
  Defined.

  Definition intersection {n : nat} : (csubset n) -> (csubset n) -> (csubset n).
  Proof.
    intros S T x.
    exact (S x /\ T x).
  Defined.

  Definition is_subset {n : nat} : (csubset n) -> (csubset n) -> Prop :=
    fun S T => forall x, S x -> T x.

  Infix "∪" := union (at level 80).
  Infix "∩" := intersection (at level 80).
  Infix "⊆" := is_subset (at level 85).
  
  Definition Hausdorff_dist_bound {n : nat} (S T : csubset n) d :=
    (forall x, S x -> exists y, T y /\ euclidean_max_dist x y <= d) /\
      (forall y, T y -> exists x, S x /\ euclidean_max_dist x y <= d).

  Definition emptyset {n : nat} : csubset n := fun x => False.
  Definition singleton {n : nat} x : csubset n := fun y => y = x.
  
  Require Import List.
  
  Fixpoint list_union {n : nat}  (l : list (csubset n)) : csubset n :=
    match l with
    | h :: t => union h (list_union t)
    | _ => (fun _ => False)
    end.

  Fixpoint lift {A B} (l : list A) (f : A -> B) : list B :=
    match l with
    | h :: t => (f h) :: (lift t f)
    | _ => nil
    end.

  Definition closed_ball {n : nat} (c : euclidean n) (r : Real) :=
    fun x => euclidean_max_dist x c <= r.

End Subsets.

Section Compact.
  Generalizable Variables K M Real.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
    {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
    {M_MultivalueMonad : MultivalueMonad}
    {Real : Type}
    {SemiDecOrderedField_Real : SemiDecOrderedField Real}
    {ComplArchiSemiDecOrderedField_Real : ComplArchiSemiDecOrderedField}.

  Add Ring realRing : realTheory.
  
  Definition is_compact {n : nat} (K : csubset n) := forall p,
      {B : list (euclidean n) &
             (Forall (fun k => exists y, K y /\ euclidean_max_dist k y <= prec p) B)
           /\ forall y, K y -> Exists (fun k => euclidean_max_dist k y <= prec p) B}.

  Lemma is_compact_closed_ball {d : nat} :
    forall c r, @is_compact d (closed_ball c r).  
  Proof.
    intros.
    intro p.
    induction p.
  Admitted.
  
  Lemma is_compact_lim {d : nat} :
    forall k : csubset d,
      (forall n : nat, {X : csubset d & prod (is_compact X) (Hausdorff_dist_bound X k (prec n))})  
      -> is_compact k.
  Proof.
    intros.
    intro p.
    destruct (X (S p)).
    destruct p0.
    destruct (i (S p)).
    exists x0.

    split.
    destruct a.
    assert (forall k0,
               (exists y : euclidean d, x y /\ euclidean_max_dist k0 y <= prec (S p)) ->
               exists y : euclidean d, k y /\ euclidean_max_dist k0 y <= prec p).
    intros.
    destruct H1.
    destruct H1.
    destruct h.
    pose proof (H3 x1 H1).
    destruct H5.
    exists x2.
    destruct H5; split; auto.
    pose proof (euclidean_max_dist_tri k0 x1 x2).
    pose proof (real_le_le_plus_le _ _ _ _ H2 H6).
    replace (S p) with (p + 1)%nat in H8.
    rewrite prec_twice in H8.
    apply (real_le_le_le _ _ _ H7 H8).
    lia.
    apply (Forall_impl _ H1 H).
    destruct a.
    intros.
    destruct h.
    pose proof (H3 y H1).
    destruct H4.
    destruct H4.
    pose proof (H0 x1 H4).
    assert (forall k0,
               (euclidean_max_dist k0 x1 <= prec (S p)) ->
               euclidean_max_dist k0 y <= prec p).
    intros.
    pose proof (euclidean_max_dist_tri k0 x1 y).
    pose proof (real_le_le_plus_le _ _ _ _ H7 H5).
    replace (S p) with (p + 1)%nat in H9 by lia.
    rewrite prec_twice in H9.
    apply (real_le_le_le _ _ _ H8 H9).
    apply (Exists_impl _ H7 H6).
  Defined.  

End Compact.
