(* this file proves various prperties of subsets of real numbers *)
Require Import Lia.
Require Import Real Euclidean List Minmax Classical.Subsets Sierpinski Testsearch Dyadic.
Require Import RealAssumption.
Require Import List.
Import ListNotations.
Section Open.

Context {X : Type}.

Definition open (A : (@csubset X)) := forall x, {s : sierp | (sierp_up s)  <-> A x}. 

Lemma open_semidec A : open A -> forall x, semidec (A x).
Proof.
  unfold open.
  intros.
  destruct (X0 x).
  destruct x0.
  exists x0.
  apply i.
Defined.

Lemma semidec_open A : (forall x, semidec (A x)) -> open A.
Proof.
  intros.
  intros x.
  destruct (sierp_from_semidec (X0 x)).
  exists x0;auto.
Defined.

Definition open_cf {A} (P : open A) : X -> sierp.
Proof.
  intros x.
  destruct (P x).
  apply x0.
Defined.

Lemma open_emptyset : open (fun x => False).
Proof.
  apply semidec_open.
  intros.
  exists lazy_bool_false.
  split;unfold lazy_bool_up;intros;contradict H;auto.
  apply lazy_bool_distinct.
Qed.

Lemma open_cf_exists {A} : open A -> {f : X -> sierp | forall x, (sierp_up (f x)) <-> A x}.
Proof.
  intros P.
  exists (open_cf P).
  intros x.
  unfold open_cf.
  destruct P.
  apply i.
Defined.

Lemma open_countable_union {A} : (forall n, open (A n)) -> open (countable_union A).
Proof.
  intros.
  intro x.
  destruct (eventually_true (fun n => (proj1_sig (X0 n x)))) as [s P].
  exists s.
  rewrite P.
  split;intros.
  - destruct H as [n H].
    pose proof (proj2_sig (X0 n x)).
    exists n.
    apply H0.
    exact H.
  - destruct H as [n H].
    pose proof (proj2_sig (X0 n x)).
    exists n.
    apply H0.
    exact H.
Defined.

Lemma open_union A B : open A -> open B -> open (union A B).
Proof.
  assert (union A B = countable_union (fun n => match n with | 0 => A | _ => B end)).
  {
    apply fun_ext.
    intros x.
    unfold union,countable_union.
    apply Prop_ext.
    intros [].
    exists 0%nat;auto.
    exists 1%nat;auto.
    intros [].
    destruct x0; [left|right];auto.
  }
  intros.
  rewrite H.
  apply open_countable_union.
  intros n.
  destruct n; simpl;auto.
Defined.
Lemma open_intersection {A B}: open A -> open B -> open (intersection A B).
Proof.
  intros openA openB x.
  destruct (openA x) as [s1 S1].
  destruct (openB x) as [s2 S2].
  exists (proj1_sig (sierp_and s1 s2)).
  rewrite (proj2_sig (sierp_and s1 s2)).
  unfold intersection.
  rewrite S1, S2.
  split;auto.
Defined.
End Open.

Section Closed.

Context {X : Type}.
Definition closed (A : (@csubset X)) := open (complement A).

Lemma closed_union {A B} : closed A -> closed B -> closed (union A B).
Proof.
  intros cA cB x.
  pose proof (open_intersection cA cB).
  destruct (X0 x) as [s H].
  exists s.
  rewrite H.
  split;intros.
  destruct H0.
  intros P.
  destruct P;auto.
  unfold complement, union in H0.
  split;intros P;apply H0;auto.
Defined.

Lemma closed_countable_intersection {A} : (forall n, closed (A n)) -> closed (countable_intersection A).
Proof.
  intros H x.
  destruct (open_countable_union H x) as [s P].
  exists s.
  rewrite P.
  split;intros.
  intros Q.
  destruct H0 as [n H0].
  apply H0.
  apply Q.
  apply Classical_Pred_Type.not_all_ex_not.
  apply H0.
Defined.

Lemma closed_intersection A B : closed A -> closed B -> closed (intersection A B).
Proof.
  intros.
  unfold closed.
  intros x.
  destruct (open_union _ _ X0 X1 x).
  exists x0.
  rewrite i.
  unfold complement, union,intersection.
  rewrite classical_tautology_neg_and;split;auto.
Qed.
 Lemma points_closed_ineq_semidec x : (closed (singleton x) -> (forall y, semidec (x <> y))).
 Proof.
   intros.
   destruct (X0 y).
   unfold sierp_up in i.
   destruct x0.
   simpl in i.
   exists x0.
   rewrite i.
   split;auto.
 Defined.
 Lemma ineq_semidec_points_closed x :  (forall y, semidec (x <> y)) -> (closed (singleton x)).
   intros H y.
   destruct (sierp_from_semidec (H y)).
   exists x0.
   rewrite i.
   split;auto.
 Defined.
End Closed.

Section Compact.

Context {X : Type}.

Definition compact (A : (@csubset X)) := forall B, open B -> {k : sierp | sierp_up k <-> (@is_subset X A B)}. 

Lemma is_compact_union M1 M2 : compact M1 -> compact M2 -> compact (union M1 M2).
Proof.
    intros H1 H2 A Aopen.
    destruct (H1 A Aopen) as [k1 P1].
    destruct (H2 A Aopen) as [k2 P2].
    destruct (sierp_and k1 k2) as [x [X1 X2]].
    exists x.
    split; intros.
    intros a P.
    destruct P; [apply P1| apply P2];auto;apply X1;auto.
    apply X2.
    rewrite union_subset in H.
    split;[apply P1 | apply P2];apply H.
Defined.
Lemma subset_intersection A B C : is_subset (intersection A B) C <-> is_subset A (@union X (complement B) C).
Proof.
  unfold is_subset, union, complement, intersection.
  split;intros.
  apply Classical_Prop.imply_to_or.
  intros.
  apply H;auto.
  destruct H0.
  destruct (H x H0);auto.
  contradict H1;auto.
Qed.

Lemma is_compact_intersection M1 M2 : compact M1 -> closed M2 -> compact (intersection M1 M2).
Proof.
  intros H1 H2 A Aopen.
  destruct (H1 (union (complement M2) A)).
  apply open_union;auto.
  exists x.
  rewrite subset_intersection.
  apply i.
Qed.

Lemma compact_closed A : (forall (x y : X), semidec (x <> y)) -> compact A -> closed A.
Proof.
  intros T1 H x.
  pose proof (ineq_semidec_points_closed _ (T1 x)).
    destruct (H _ X0).
    exists x0.
    rewrite i.
    unfold is_subset, complement, singleton.
    split.
    intros H2 Ax.
    specialize (H2 x Ax).
    contradict H2;auto.

    intros.
    contradict H1.
    rewrite <-H1;auto.
 Defined.

Lemma singleton_compact x : compact (singleton x). 
Proof.
  unfold compact, singleton, open.
  intros.
  destruct (X0 x).
  exists x0.
  rewrite i.
  unfold is_subset.
  split;intros;auto.
  rewrite <-H0;auto.
Qed.
  Axiom continuity : forall {X} (f : (nat -> X) -> sierp) (x : (nat -> X)), sierp_up (f x) -> ^M {m | forall y, (forall n, (n <= m)%nat -> x n = y n) -> sierp_up (f y)}.

  Lemma compact_fin_cover K U : compact K -> (forall n, (open (U n))) -> is_subset K (countable_union U) -> ^M { m | forall x, K x -> exists n, (n <= m)%nat /\ (U n x)}.
  Proof.
    intros.
    assert {T : (nat -> X -> sierp) -> (X -> sierp) | forall x y, sierp_up ((T x) y) <-> (countable_union (fun n y =>  sierp_up (x n y)) y)  } as [T H0].
    {
       assert (forall (x : nat -> X -> sierp) n, open (fun y => sierp_up (x n y))) by (unfold open;intros;exists (x n x0);split;auto).
       exists (fun x => (fun y => (pr1 _ _ (open_countable_union (X2 x) y)))).
       intros.
       destruct (open_countable_union (X2 x) y);auto.
    } 
    assert {g : (nat -> X -> sierp) -> sierp | forall x, sierp_up (g x) <-> is_subset K (countable_union (fun n => (fun y => sierp_up (x n y))))  } as [g G].
    {
      assert (forall x, open (fun y => sierp_up (T x y))) by (unfold open;intros;exists (T x x0);split;auto).
      exists (fun x => (pr1 _ _ (X0 _ (X2 x)))).
      intros.
      destruct (X0 _ (X2 x));simpl;auto.
      split;auto.
      - intros.
        unfold is_subset, countable_union.
        intros.
        apply H0.
        apply i;auto.
     - intros.
       apply i.
       unfold is_subset.
       intros.
       apply H0.
       apply H1;auto.
    }
    assert (sierp_up (g (fun n => (fun y => (pr1 _ _ (X1 n y)))))).
    {
      apply G.
      unfold is_subset.
      intros.
      unfold countable_union.
      destruct (H x H1).
      exists x0.
      destruct (X1 x0 x);simpl;apply i;auto.
    }
    pose proof (continuity _ _ H1).
    revert X2.
    apply M_lift.
    intros [m M].
    exists m.
    intros.
    assert {y : nat -> X -> sierp | (forall n, (n <= m)%nat -> (fun a=> (pr1 _ _ (X1 n a))) = y n) /\ forall n x, sierp_up (y n x) -> (n <= m)%nat} as [y Y].
    {
      exists (fun n => if (n <=? m) then (fun a => (pr1 _ _ (X1 n a))) else (fun a => pr1 _ _ (open_emptyset a))).
      split.
      intros.
      apply fun_ext.
      intros.
      rewrite (leb_correct _ _ H3);auto.
      intros.
      destruct (le_lt_dec n m);auto.
      contradict H3.
      rewrite (leb_correct_conv);auto.
      destruct (open_emptyset x0).
      simpl.
      rewrite i;auto.
    }
    assert (sierp_up (g y)).
    {
      apply M.
      intros.
      apply Y;auto.
    }
    destruct (proj1 (G y) H3 x H2).
    exists x0.
    assert (x0 <=m)%nat.
    apply (proj2 Y x0 x);auto.
    split;auto.
    assert (sierp_up (pr1 _ _ (X1 x0 x))) by (destruct (proj1 Y _ H5);auto).
    destruct (X1 x0 x);apply i;auto.
 Qed.

End Compact.

Section Overt.

  Context {X : Type}.
  Definition overt (A : (@csubset X)) := forall B, open B -> {k : sierp | sierp_up k <-> (@intersects X A B)}. 

  Lemma singleton_overt x : overt (singleton x).
  Proof.
    intros A openA.
    destruct (openA x).
    exists x0.
    rewrite i.
    unfold intersects, intersection, singleton.
    split;intros.
    exists x;split;auto.
    destruct H as [x' [-> H]];auto.
  Defined.

  Lemma overt_nonempty_semidec A : overt A -> semidec (exists x, A x).
  Proof.
    intros.
    destruct (X0 (fun x => True)).
    exists (sierp_from_kleenean (neq_sym _ _ _ lazy_bool_distinct)).
    unfold sierp_up, sierp_from_kleenean;split;auto.
    destruct x.
    exists x.
    rewrite i.
    unfold intersects, intersection;split; intros [];exists x0;auto;apply H.
  Defined.

  Lemma overt_intersection_eq_semidec : (forall A B, overt A -> overt B -> overt (intersection A B)) -> (forall (x y : X), semidec (x = y)).
  Proof.
    intros.
    specialize (X0 _ _ (singleton_overt x) (singleton_overt y)).
    apply overt_nonempty_semidec in X0.
    destruct X0.
    exists x0.
    rewrite i.
    unfold intersection, singleton.
    split;intros.
    destruct H as [x' [-> ->]];auto.
    exists x;split;auto.
 Qed.
End Overt.


Section Examples.
  
  Example cantor_exists_open : open (fun (n : (nat -> bool)) => exists m, (n m) = true).
  Proof.
    apply open_countable_union.
    intros n x.
    apply sierp_from_semidec.
    unfold lazy_bool_up.
    destruct (x n).
    exists lazy_bool_true;split;auto.
    exists lazy_bool_false;split;intros;contradict H;auto.
    apply lazy_bool_distinct.
 Qed.

  Definition extends (a : list bool) (x : (nat -> bool)) := forall n, (n < length a)%nat -> x n = nth n a true.

  Lemma one_point_fixed_clopen n b : open (fun (x : (nat -> bool)) => x n = b) * closed (fun (x : (nat -> bool)) => x n = b).
  Proof.
    assert (forall b', {k | (lazy_bool_up _ k) <-> b' = b}).
    {
      intros.
      exists (if (bool_eq b' b) then lazy_bool_true else lazy_bool_false).
      destruct b; destruct b';simpl;unfold lazy_bool_up;split;auto;intros;contradict H; try apply lazy_bool_distinct; try apply Bool.diff_false_true.
      apply Bool.diff_true_false.
    }
    split;intros x.
    destruct (X (x n));apply sierp_from_semidec.
    exists x0;auto.
    destruct (X (negb (x n)));apply sierp_from_semidec.
    exists x0.
    unfold complement.
    rewrite i.
    split;intros.
    rewrite <-H.
    apply neq_sym.
    apply Bool.no_fixpoint_negb.
    unfold lazy_bool_up.
    destruct (x n); destruct b;simpl;auto.
    contradict H;auto.
 Qed.
    

 Lemma extends_intersection a0 a x : extends (a0 :: a) x <-> (x 0%nat) = a0 /\ extends a (fun n => x (S n)).  
  Proof.
    revert a0 x.
    induction a.
    - unfold extends.
      simpl.
      split.
      intros H.
      split.
      destruct (H 0%nat);try lia;auto.
      intros;lia.
      intros [H1 H2] n N.
      rewrite Nat.lt_1_r in N.
      rewrite N;auto.
   - intros.
     rewrite IHa.
     unfold extends.
     split.
     intros.
     split; [|split].
     apply (H 0%nat);simpl;lia.
     apply (H 1%nat);simpl;lia.
     intros.
     apply (H (S (S n))).
     simpl;lia.
     intros [H1 [H2 H3]] n N.
     destruct n;simpl;auto.
     destruct n;simpl;auto.
     apply H3;simpl in *;lia.
  Qed.

  Lemma extends_intersection' a0 a : extends (a0 :: a) = intersection (fun (x : (nat -> bool)) => x O = a0) (fun x => (extends a (fun n => x (S n)))).
  Proof.
    apply fun_ext.
    intros.
    unfold intersection.
    apply Prop_ext;apply extends_intersection.
  Qed.

  Example cantor_base_clopen a : open (extends a) * closed (extends a). 
  Proof.
    induction a.
    - unfold extends.
      split;intros x;apply sierp_from_semidec.
      exists (lazy_bool_true);unfold lazy_bool_up;split;simpl;auto;lia.
      exists (lazy_bool_false);unfold lazy_bool_up.
      split;intros.
      contradict H.
      apply lazy_bool_distinct.
      unfold complement in H.
      contradict H;simpl;lia.
   - rewrite extends_intersection'.
     split.
     apply open_intersection.
     apply one_point_fixed_clopen.
     intros x.
     destruct IHa.
     destruct (o (fun n => x (S n))).
     exists x0;auto.
     apply closed_intersection.
     apply one_point_fixed_clopen.
     destruct IHa.
     intros x.
     destruct (c (fun n => (x (S n)))).
     exists x0;auto.
  Qed.

  (* Cantor space closed => WKL *)

  Definition prefix (L1 L2 : list bool) := exists (L3 : (list bool)), L2 = L1 ++ L2.
  
  Definition binary_tree T := (T []) /\ forall a b, T b -> prefix a b -> T a.

  Definition infinite (T : (list bool -> Prop)) := forall n, exists a, T a /\ (length a >= n)%nat.
  Definition path (T : list bool -> Prop) (p : nat -> bool)  := forall a, extends a p -> T a. 

  Definition decidable (T : (list bool -> Prop)) := forall x, {b : bool | b = true <-> T x}.

  Lemma extends_decidable x : decidable (fun a => (extends a x)).
  Proof.
    intros a.
    revert x.
    induction a.
    exists true.
    split;auto;unfold extends;intros _;simpl;lia.
    intros.
    destruct (IHa (fun n => x (S n))).
    exists (andb (bool_eq (x 0%nat) a) x0).
    rewrite Bool.andb_true_iff.
    rewrite ((extends_intersection a a0 x)).
    rewrite i.
    split;intros [H1 H2];split;auto.
    apply bool_eq_ok;auto.
    rewrite H1;destruct a;auto.
  Qed.

  Definition WKL := forall T, binary_tree T -> infinite T -> {p | path T p }.

  Lemma enumerable_lists : enumerable (list bool).
  Admitted.

  Lemma path_closed T : (decidable T) -> closed (path T).
  Proof.
    intros H x.
    assert (decidable (fun a => extends a x /\ not (T a))).
    {
      intros a.
      destruct (extends_decidable x a).
      destruct (H a).
      exists (andb x0 (negb x1)).
      rewrite Bool.andb_true_iff.
      rewrite <-i, <-i0.
      rewrite Bool.negb_true_iff.
      rewrite Bool.not_true_iff_false;split;auto.
    }
    destruct (enumerable_lists) as [l L].
    destruct (cantor_exists_open (fun n => (pr1 _ _ (H0 (l n))))).
    exists x0.
    rewrite i.
    split.
    - intros [m M].
      destruct (H0 (l m));simpl in *.
      intros P.
      specialize (P (l m)).
      contradict M.
      rewrite i0.
      intros [H1 H2].
      apply H2;auto.
   - intros.
     unfold complement, path in H1.
     rewrite classical_tautology_neg_all in H1.
     destruct H1.
     destruct (L x1).
     exists x2.
     destruct (H0 (l x2));simpl.
     apply i0.
     apply Classical_Prop.imply_to_and;rewrite H2;auto.
  Qed.
  
  Lemma compact_WKL : compact (fun (x : nat -> bool) => True) -> WKL.

  Proof.
   unfold WKL.
   intros.
   
  (* Axiom continuity : forall X (f : (nat -> X) -> sierp) (x : (nat -> X)),   *)

  (* Definition pair_nat : nat -> nat -> nat. *)
  (* Proof. *)
  (*   intros n m. *)
  (*   destruct (enumerable_pair _ _ enumerable_nat enumerable_nat). *)
  (*   specialize (e (n,m)). *)
  (*   Search (exists _ , _) ({_ | _}). *)
  (*   apply ConstructiveEpsilon.constructive_indefinite_ground_description_nat_direct in e. *)
  (*   destruct e. *)
  (*   apply x0. *)
  (*   intros. *)
  (*   destruct (x n0). *)
  (*   simpl. *)
  (*   destruct (Nat.eq_dec n1 n)  as [-> |];auto. *)
  (*   destruct (Nat.eq_dec n2 m)  as [-> |];auto. *)
  (*   right. *)
  (*   rewrite pair_equal_spec;intros [];auto. *)
  (*   right. *)
  (*   rewrite pair_equal_spec;intros [];auto. *)
  (* Defined. *)

  (* Lemma continuous_sequence_to_sierp X (f : (nat -> X) -> sierp) (x : nat -> X) : is_totally_represented_space X -> sierp_up (f x) -> {m | forall y, (forall n, (n <= m)%nat -> x n = y n) -> sierp_up (f y)}. *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct (totally_represented_sequence _ X0) as [r R]. *)
  (*   assert {g : (nat -> nat) -> sierp | forall x, sierp_up (g x) <-> sierp_up (f (r x))} as [g G]. *)
  (*   admit. *)
  (*   destruct (R x) as [x0 [R1 R2]]. *)
  (*   destruct (continuous_baire_to_sierp g x0) as [m M]. *)
  (*   apply G;rewrite R1;auto. *)
  (*   exists m. *)
  (*   intros. *)
  (*   destruct (R y) as [y0 [R1' R2']]. *)
  (*   rewrite <- R1'. *)
  (*   apply G. *)
  (*   apply M. *)
  (*   intros. *)
  (*   intros. *)
    
  (* Lemma continuous_baire2_to_sierp (f : (nat -> nat -> nat) -> sierp) (x : nat -> (nat -> nat)) : sierp_up (f x) -> {m | forall y, (forall n, (n <= m)%nat -> x n = y n)  ->  sierp_up (f y) }. *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct (continuous_baire_to_sierp (fun (x : nat -> nat) => (f (fun n m => x (pair_nat n m)))) (fun n => x (unpair_nat1 n) (unpair_nat2 n))). *)
  (*   - replace (fun n m => x (unpair_nat1 (pair_nat n m)) (unpair_nat2 (pair_nat n m))) with x;auto. *)
  (*     apply fun_ext;intros;apply fun_ext;intros. *)
  (*     rewrite pair_unpair1, pair_unpair2;auto. *)
  (*   - exists x0. *)
  (*     intros. *)
  (*     specialize (s (fun n => (y (unpair_nat1 n) (unpair_nat2 n)))). *)
  (*   replace y with (fun n m => y (unpair_nat1 (pair_nat n m)) (unpair_nat2 (pair_nat n m))). *)
  (*   apply s. *)
  (*   intros. *)
  (*   rewrite H0;auto. *)
  (*   pose proof (unpair_le n). *)
  (*   lia. *)
  (*   apply fun_ext;intros;apply fun_ext;intros. *)
  (*   rewrite pair_unpair1, pair_unpair2;auto. *)
  (* Qed. *)


  (* Lemma continuity_baire : forall (f : ((nat -> nat) -> nat)) (x : (nat -> nat)), {m | forall y,  (forall n, (n <= m)%nat -> x n = y n) -> f x = f y}. *)
  (* Proof. *)
  (*   intros. *)
  (*   assert (forall n y, {s : sierp | sierp_up s <-> f y = n}). *)
  (*   { *)
  (*     intros. *)
  (*     apply sierp_from_semidec. *)
  (*     unfold lazy_bool_up. *)
  (*     destruct (Nat.eq_dec (f y) n); [exists lazy_bool_true | exists lazy_bool_false];split; auto. *)
  (*     intros. *)
  (*     contradict H;apply lazy_bool_distinct. *)
  (*     lia. *)
  (*   } *)
  (*   destruct (continuous_baire_to_sierp (fun y => (pr1 _ _ (X (f x) y))) x). *)
  (*   - destruct (X (f x) x). *)
  (*     apply i;auto. *)
  (*  - exists x0. *)
  (*    intros. *)
  (*    specialize (s y H). *)
  (*    destruct (X (f x) y). *)
  (*    apply eq_sym. *)
  (*    apply i. *)
  (*    apply s. *)
  (* Qed. *)

  (* (* Lemma continuity_baire2 (f : (nat -> nat -> nat) -> nat) (x : nat -> (nat -> nat)) : {m | forall y, (forall n, (n <= m)%nat -> x n = y n)  ->  f x = f y }. *) *)
  (* (* Proof. *) *)
  (* (*   destruct (continuity_baire (fun (x : nat -> nat) => (f (fun n m => x (pair_nat n m)))) (fun n => x (unpair_nat1 n) (unpair_nat2 n))). *) *)
  (* (*   exists x0. *) *)
  (* (*   intros. *) *)
  (* (*   specialize (e (fun n => (y (unpair_nat1 n) (unpair_nat2 n)))). *) *)
  (* (*   replace x with (fun n m => x (unpair_nat1 (pair_nat n m)) (unpair_nat2 (pair_nat n m))). *) *)
    
  (* (*   replace y with (fun n m => y (unpair_nat1 (pair_nat n m)) (unpair_nat2 (pair_nat n m))). *) *)
  (* (*   apply e. *) *)
  (* (*   intros. *) *)
  (* (*   rewrite H;auto. *) *)
  (* (*   pose proof (unpair_le n). *) *)
  (* (*   lia. *) *)
  (* (*   apply fun_ext;intros;apply fun_ext;intros. *) *)
  (* (*   rewrite pair_unpair1, pair_unpair2;auto. *) *)
  (* (*   apply fun_ext;intros;apply fun_ext;intros. *) *)
  (* (*   rewrite pair_unpair1, pair_unpair2;auto. *) *)
  (* (* Qed. *) *)

  (* Lemma sierp_from_nat_sequence : forall (f : (nat -> nat)), {s : sierp | sierp_up s <-> exists n, f n = 1%nat}. *)
  (* Proof. *)
  (*   intros. *)
  (*   assert (forall n, {s : sierp |  sierp_up s <-> f n = 1%nat}). *)
  (*   { *)
  (*     intros. *)
  (*     apply sierp_from_semidec. *)
  (*     unfold lazy_bool_up. *)
  (*     destruct (Nat.eq_dec (f n) 1%nat); [exists lazy_bool_true | exists lazy_bool_false];split; auto;intros;contradict H;auto. *)
  (*     apply lazy_bool_distinct. *)
  (*   } *)
  (*   destruct (eventually_true (fun n => (pr1 _ _ (X n)))). *)
  (*   exists x. *)
  (*   rewrite i. *)
  (*   split;intros [];exists x0;destruct (X x0);simpl;apply i0;auto. *)
  (* Qed. *)

  (* Axiom sierp_equality : forall s1 s2, sierp_up s1 <-> sierp_up s2 -> s1 = s2.  *)

  (* Lemma continuity_open : forall (f : (nat -> sierp) -> sierp) (x : nat -> sierp), sierp_up (f x) -> ^M {m | forall y, (forall n, (n <= m)%nat -> x n = y n) -> sierp_up (f y)}. *)
  (* Proof. *)
  (*   intros. *)
  (*   assert ({g : (nat -> nat -> nat) -> sierp | (forall y, sierp_up (g y) -> forall s, (forall n, sierp_up (s n) <-> exists m, (y n m) = 1%nat) -> sierp_up (f s)) /\ (forall s, sierp_up (f s) -> (forall y, (forall n, sierp_up (s n) <-> exists m, (y n m) = 1%nat) -> sierp_up (g y)))}) as [g [G1 G2]]. *)
  (*   { *)
  (*     exists (fun x => (f (fun n => (pr1 _ _ (sierp_from_nat_sequence (x n)))))). *)
  (*     split. *)
  (*     - intros. *)
  (*       replace s with (fun n => pr1 _ _ (sierp_from_nat_sequence (y n))). *)
  (*       apply H0. *)
  (*       apply fun_ext. *)
  (*       intros. *)
  (*       destruct (sierp_from_nat_sequence (y x0));simpl. *)
  (*       apply sierp_equality. *)
  (*       rewrite H1,i;split;intros [];exists x2;auto. *)
  (*     - intros. *)
  (*       replace (fun n => pr1 _ _ (sierp_from_nat_sequence (y n))) with s;auto. *)
  (*       apply fun_ext. *)
  (*       intros. *)
  (*       destruct (sierp_from_nat_sequence (y x0));simpl. *)
  (*       apply sierp_equality. *)
  (*       rewrite H1,i;split;intros [];exists x2;auto. *)
  (*     } *)
  (*   pose proof (continuous_baire2_to_sierp g). *)
  (*   assert (forall y, ^M ({x' : nat->nat -> nat | forall n, (sierp_up (y n) <-> exists m, (x' n m) = 1%nat)})).  *)
  (*   { *)
  (*     intros. *)
  (*     assert (forall n, ^M {x' : nat -> nat | sierp_up (y n) <-> exists m, (x' m) = 1%nat}). *)
  (*     - intros. *)
  (*       apply sierp_to_nat_sequence. *)
  (*     - apply M_countable_lift in X. *)
  (*       revert X. *)
  (*       apply M_lift. *)
  (*       intros. *)
  (*       exists (fun n => (pr1 _ _ (H1 n))). *)
  (*       intros. *)
  (*       destruct (H1 n);auto. *)
  (*   } *)
  (*   pose proof (X x). *)
  (*   revert X0. *)
  (*   apply M_lift. *)
  (*   intros [x' H1]. *)
  (*   assert (sierp_up (g x')) by (apply (G2 x);auto). *)
  (*   destruct (H0 _  H2) as [m M]. *)
  (*   exists m. *)
  (*   intros. *)
  (*   assert (^M ({y' : nat -> nat -> nat | (forall n, sierp_up (y n) <-> exists m, (y' n m) = 1%nat) /\ forall n, (n <= m)%nat -> x' n = y' n})). *)
  (*   { *)
  (*     pose proof (X y). *)
  (*     revert X0. *)
  (*     apply M_lift. *)
  (*     intros [y0 Y0]. *)
  (*     exists (fun p => if (p <=? m) then (x' p) else (y0 p)). *)
  (*     split. *)
  (*     - intros. *)
  (*       rewrite Y0. *)
  (*       split; intros [m0 M0]. *)
  (*       + destruct (le_gt_dec n m). *)
  (*         rewrite (leb_correct _ _ l). *)
  (*         rewrite <-H1. *)
  (*         rewrite H3;auto. *)
  (*         apply Y0. *)
  (*         exists m0;auto. *)
  (*         rewrite leb_correct_conv;try lia. *)
  (*         exists m0;auto. *)
  (*      + destruct (le_gt_dec n m). *)
  (*         rewrite (leb_correct _ _ l) in M0. *)
  (*        rewrite <-Y0. *)
  (*        rewrite <-H3;auto. *)
  (*        apply H1. *)
  (*        exists m0;auto. *)
  (*       rewrite leb_correct_conv in M0;try lia. *)
  (*       exists m0;auto. *)
  (*    - intros. *)
  (*      rewrite leb_correct;auto. *)
  (*   } *)
  (*   apply M_hprop_elim_f. *)
  (*   unfold is_hprop. *)
  (*   apply irrl. *)
  (*   revert X0. *)
  (*   apply M_lift. *)
  (*   intros [y' [Y1 Y2]]. *)
  (*   apply (G1 y'). *)
  (*   apply M. *)
  (*   apply Y2. *)
  (*   apply Y1. *)
  (* Qed. *)
  (* Example cantor_closed : closed (fun (x: (nat -> bool)) => forall n, (x n) = true -> forall m, (n <> m)%nat -> (x m) = false). *)
  (* Proof. *)
  (*   intros x. *)
  (*   unfold complement. *)
  (*   destruct (cantor_exists_open x). *)

End Examples.