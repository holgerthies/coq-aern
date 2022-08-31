(* this file proves various properties of subsets of real numbers *)
Require Import Lia.
Require Import Real Euclidean List Minmax Subsets.

Section SierpinskiTriangle.

Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).
#[local] Definition sofReal := @sofReal types casofReal.
#[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).
#[local] Notation "^euclidean" := (@euclidean types) (at level 0).
#[local] Notation "^ball" := (@ball types) (at level 0).

  Definition ST_v1 := make_euclidean2 (- real_1) real_1.
  Definition ST_v2 := make_euclidean2 (- real_1) (- real_1).
  Definition ST_v3 := make_euclidean2 real_1 (- real_1).

  Definition has_ST_v123 (s : euclidean_subset 2) : Prop :=
    (s ST_v1) \/ (s ST_v2) \/ (s ST_v3).

  Definition ST_weighted_pt (c1 c2 c3 : ^Real) : ^euclidean 2.
    destruct (split_euclidean2 ST_v1) as [x1 [y1 _]].
    destruct (split_euclidean2 ST_v2) as [x2 [y2 _]].
    destruct (split_euclidean2 ST_v3) as [x3 [y3 _]].
    pose (c1 * x1 + c2 * x2 + c3 * x3) as x.
    pose (c1 * y1 + c2 * y2 + c3 * y3) as y.
    apply (make_euclidean2 x y).
  Defined.

  Definition inside_ST_hull (s : euclidean_subset 2) : Prop :=
    forall pt : ^euclidean 2, s pt -> exists c1 c2 c3 : ^Real, pt = (ST_weighted_pt c1 c2 c3) /\ c1 >= real_0 /\ c1 >= real_0 /\ c3 >= real_0.

  Definition point_point_mid (p1 : ^euclidean 2) (p2 : ^euclidean 2) : ^euclidean 2.
    destruct (split_euclidean2 p1) as [x1 [y1 _]].
    destruct (split_euclidean2 p2) as [x2 [y2 _]].
    apply (make_euclidean2 ((x1 + x2) / real_2_neq_0) ((y1 + y2) / real_2_neq_0)).
  Defined.

  Definition point_ball_mid (p : ^euclidean 2) (b : ^ball 2) : ^ball 2.
    destruct b as [bc br].
    apply (pair (point_point_mid p bc) (br / real_2_neq_0)).
  Defined.

  Definition ST_selfSimilar (s : euclidean_subset 2) : Prop :=
    forall pt : ^euclidean 2, 
    s pt = s (point_point_mid ST_v1 pt)
    /\ 
    s pt = s (point_point_mid ST_v2 pt)
    /\ 
    s pt = s (point_point_mid ST_v3 pt).  

  Definition ST (s : euclidean_subset 2) : Prop :=
    has_ST_v123 s /\ inside_ST_hull s /\ ST_selfSimilar s.

  Definition ST_split_ball (b : ball 2) :=
    (point_ball_mid ST_v1 b) :: 
    (point_ball_mid ST_v2 b) :: 
    (point_ball_mid ST_v3 b) :: nil.

  Fixpoint STn n : list (ball 2) := 
    match n with
    | 0 => (make_ball real_0 real_0 real_1) :: nil 
           (* the initial cover is the square ([-1,1],[-1,1]) *) 
    | (S n') => List.concat (List.map ST_split_ball (STn n'))
    end.

  Lemma ST_compact : forall s, (ST s) -> is_compact 2 s.
  Admitted.
  
End SierpinskiTriangle.
