Require Import Lia.
Require Import Real Euclidean List Minmax Subsets.
Section Subsets.

  Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

  #[local] Notation "^K" := (@K types) (at level 0).
  #[local] Notation "^M" := (@M types) (at level 0).
  #[local] Notation "^Real" := (@Real types) (at level 0).
  #[local] Definition sofReal := @sofReal types casofReal.
  #[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).
  #[local] Notation "^euclidean" := (@euclidean types) (at level 0).

  Add Ring realRing : (realTheory ).
  
  Context (d : nat).


  (* 2^-n closed ball centered at x fits in 2^-m closed ball centered at f x *)  
  Definition fits (f : Real -> Real) x n m :=
    forall y, dist x y <= prec n -> dist (f x) (f y) <= prec m.

  Axiom continuity_principle : forall (f : Real -> Real) x m,
      ^M {n | fits f x n m}.
  
  Axiom uniform_continuity_principle :
    forall f a b m,
    exists N, forall x, a <= x <= b  -> M_all (fun x :  {n | fits f x n m} => (projP1 _ _ x < N)%nat) (continuity_principle f x m).
  
  Definition compact_cover (f : Real -> Real) n :=
    M_paths
      (fun _ => Real)
      (fun _ x y => x < y /\ forall z, x <= z <= y -> dist (f y) (f z) <= prec n)
      (M_unit _ real_0)
  .

  Check compact_cover.

