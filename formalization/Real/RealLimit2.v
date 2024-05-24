(* provides limit operations written with dist function *)
Require Import Base.
Require Import Monad.
Require Import ClassicalMonads.
Require Import Nabla.
Require Import Kleene.
Require Import MultivalueMonad.
Require Import RealAxioms.
Require Import RealRing.
Require Import RealOrder.
Require Export RealOrderTactic.
Require Export RealLimit0.
Require Import RealLimit1.
Require Export RealMetric.

Section RealLimit2.

Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).

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



  Definition is_fast_cauchy (f : nat -> Real) := forall n m, dist (f n) (f m) <= prec n + prec m.
  Definition is_fast_limit (x : Real) (f : nat -> Real) := forall n, dist x (f n) <= prec n.


  Lemma is_fast_cauchy_iff_p : forall f, is_fast_cauchy f <-> is_fast_cauchy_p f.
  Proof.
    intros.
    split.
    intros H n m.
    pose proof (proj1 (dist_le_prop (f n) (f m) (prec n + prec m)) (H n m)).
    replace (- prec n - prec m) with (- (prec n + prec m)) by ring.
    auto.
    intros H n m .
    apply (proj2 (dist_le_prop (f n) (f m) (prec n + prec m)) ).
    pose proof (H n m ).
    replace (- prec n - prec m) with (- (prec n + prec m)) in H0 by ring.
    auto.
  Defined.

  
  (* 

   there are various limit operations provided by the library.
   [T_limit] : defined by  
   *)
  Definition real_limit :
    forall f : nat -> Real, is_fast_cauchy f -> {x | is_fast_limit x f}.
  Proof.
    intros.
    assert (is_fast_cauchy_p f).
    intros n k.
    pose proof (proj1 (dist_le_prop (f n) (f k) (prec n + prec k)) (H n k)).
    replace (-prec n - prec k ) with (- (prec n + prec k)) by ring.
    auto.
    destruct (real_limit_p _ H0).
    exists x.
    intro n.
    exact (proj2 (dist_le_prop x (f n) (prec n)) (i n)).
  Defined.

  Definition real_limit_P :
    forall (P : Real -> Prop), (exists! z, P z) ->
                               (forall n, {e | (exists a : Real, P a /\ dist e a <= prec n) }) -> {a : Real | P a}.
  Proof.
    intros.
    apply (real_limit_P_p P H).
    intro.
    destruct (X n).
    exists x.
    destruct e.
    exists x0.
    destruct H0.
    split; auto.
    exact (proj1 (dist_le_prop x x0 (prec n)) H1).
  Defined.
  



  Definition real_limit_P_lt :
    forall (P : Real -> Prop), (exists! z, P z) ->
                               (forall n, {e | (exists a : Real, P a /\ dist e a < prec n) }) -> {a : Real | P a}.
  Proof.
    intros.
    apply (real_limit_P_lt_p P H).
    intro.
    rename X into H0.
    destruct (H0 n).
    exists x.
    destruct e.
    exists x0.
    destruct H1.
    
    split; auto.
    destruct (dist_prop x x0).
    destruct H4.
    destruct (real_total_order x x0).
    split.
    apply real_lt_anti_anti.
    ring_simplify.
    pose proof (H5 H6).
    replace (-x + x0) with (x0 - x) by ring.
    rewrite <- H7.
    exact H2.

    assert (x - x0 < real_0).
    apply (real_lt_plus_r_lt (-x0) ) in H6.
    replace (x0 +- x0) with real_0 in H6 by ring.
    exact H6.
    assert (prec n > real_0) by (apply prec_pos). 
    exact (real_lt_lt_lt  _ _ _  H7 H8).

    destruct H6.
    rewrite H6.
    replace (x0 - x0) with real_0 by ring.
    split; auto with real.
    apply real_lt_anti_anti.
    replace (- real_0) with real_0 by ring.
    replace (- - prec n) with (prec n) by ring.
    apply prec_pos.
    apply prec_pos.

    pose proof (H3 H6).
    rewrite <- H7.
    split; auto.
    
    ring_simplify in H7.
    pose proof (dist_pos_t  x x0).
    assert (- prec n < real_0).
    apply real_lt_anti_anti.
    replace (- real_0) with real_0 by ring.
    replace (- - prec n) with (prec n) by ring.
    apply prec_pos.
    destruct H8.
    apply (real_lt_lt_lt _ _ _ H9 H8).
    rewrite<- H8.
    exact H9.
  Defined.

  Definition real_mslimit_P :
    forall (P : Real -> Prop),
      (exists! z, P z) ->
      ((forall n, ^M {e  | (exists a : Real, P a /\ dist e a <= prec n)}) -> {a : Real | P a}).
  Proof.
    intros.
    apply (M_countable_lift)  in X.
    apply M_hprop_elim_f.
    intros x y.
    destruct H, x, y.
    destruct H.
    induction (H0 x1 p0).
    induction (H0 x p).
    induction (irrl _ p p0).
    apply eq_refl.
    assert (exists z : Real, P z).
    destruct H.
    exists x.
    destruct H.
    exact H.

    
    assert ((forall n : nat, {e : Real | exists a : Real, P a /\ dist e a <= prec n}) -> {a : Real | P a} ).
    intro H1.

    apply  (real_limit_P P H H1).
    apply (M_lift _ _ X0 X).
  Defined.



  Definition real_mslimit_P_lt :
    forall (P : Real -> Prop),
      (exists! z, P z) ->
      ((forall n, ^M {e  | (exists a : Real, P a /\ dist e a < prec n)}) -> {a : Real | P a}).
  Proof.
    intros.
    apply (M_countable_lift)  in X.
    apply M_hprop_elim_f.
    intros x y.
    destruct H, x, y.
    destruct H.
    induction (H0 x1 p0).
    induction (H0 x p).
    induction (irrl _ p p0).
    apply eq_refl.
    assert (exists z : Real, P z).
    destruct H.
    exists x.
    destruct H.
    exact H.

    
    assert ((forall n : nat, {e : Real | exists a : Real, P a /\ dist e a < prec n}) -> {a : Real | P a} ).
    intro.

    apply  (real_limit_P_lt P H X0).
    apply (M_lift _ _ X0 X).
  Defined.




  Definition M_is_fast_cauchy (f : nat -> M Real) := forall n m, M_all (fun x => M_all (fun y => dist x y <= prec n + prec m) (f m)) (f n).


  
  (* Definition M_is_fast_cauchy_section : forall (f : nat -> M Real), M_is_fast_cauchy -> M {f : nat -> Real *)

  (*                                              n m, (M_all (fun x => M_all (fun y => dist x y <= prec n + prec m) (f n)) (f m)) *)

  
  Definition M_is_fast_limit_all (x : Real) (f : nat -> M Real) : Prop
    := forall n, M_all (fun y => dist x y <= prec n) (f n).

  Definition M_is_fast_limit_some (x : Real) (f : nat -> M Real) : Prop
    := forall n, M_some (fun y => dist x y <= prec n) (f n).


  Definition real_mslimit :
    forall f : nat -> ^M Real, M_is_fast_cauchy f -> ^M {x | M_is_fast_limit_some x f}.
  Proof.
    intros.
    pose proof (countable_selection _ f).
    apply (fun g => M_lift _ _ g X).
    intro; clear X.
    rename X0 into H0.
    destruct H0.
    assert (is_fast_cauchy x).
    intros i j.
    pose proof (m i).
    pose proof (m j).
    pose proof (H i j).
    pose proof (M_all_destruct_2 H2 H0 H1).
    simpl in H3.
    exact H3.
    destruct (real_limit x H0) as [y l].
    exists y.
    intro n.
    rewrite M_some_picture_1.
    exists (x n).
    pose proof (m n).
    rewrite M_in_picture_1 in H1.
    split; auto.
  Defined.
  

  
  Definition real_mslimit_all :
    forall f : nat -> M Real, M_is_fast_cauchy f -> {x | M_is_fast_limit_all x f}.
  Proof.
    intros.
    pose proof (countable_selection _ f).
    apply M_hprop_elim_f.
    intros x y.
    destruct x, y.
    apply sigma_eqP2.
    apply (proj1 (dist_zero x x0)).
    destruct (dist_pos x x0); auto.
    pose proof (padding _ _ H0) as [e [i j]].
    
    pose proof (real_Archimedean _ i).
    destruct H1 as [k].
    ring_simplify in j.
    pose proof (M_W_destruct (f (k + 1)%nat)).
    destruct H2.
    rewrite <- M_in_picture_1 in H2.
    pose proof (M_all_destruct (m (k+1)%nat) H2).
    pose proof (M_all_destruct (m0 (k+1)%nat) H2).
    simpl in H3, H4.
    rewrite dist_symm in H4.
    pose proof (real_le_le_plus_le _ _ _ _ H3 H4).
    rewrite prec_twice in H5.
    pose proof (real_le_le_le _ _ _ (real_ge_le _ _ (dist_tri _ _ _ )) H5).
    rewrite j in H6.
    contradiction (real_gt_nle _ _ H1 H6).
    apply (fun g => M_lift _ _ g X).
    intro H0; clear X.
    
    destruct H0.
    assert (is_fast_cauchy x).
    intros i j.
    pose proof (m i).
    pose proof (m j).
    pose proof (H i j).
    pose proof (M_all_destruct_2 H2 H0 H1).
    simpl in H3.
    exact H3.

    destruct (real_limit x H0) as [y l].
    exists y.
    
    
    intros j.
    pose proof (m j).
    pose proof (l j).
    rewrite M_all_picture_1.
    intros.
    destruct (real_total_order (dist y a) (prec j)).
    left; auto.
    destruct H4.
    right; auto.
    (* going for contradiction *)
    pose proof (padding _ _ H4) as H5.
    destruct H5.
    destruct a0.
    pose proof (real_Archimedean _ H5).
    destruct H7.
    pose proof (l (x1 + 1)%nat).
    pose proof (H j (x1 + 1)%nat).
    rewrite <- M_in_picture_1 in H3.
    pose proof (M_all_destruct_2 H9  H3 (m (x1 + 1)%nat)).
    simpl in H10.
    pose proof (dist_tri y (x (x1 + 1)%nat) a).
    rewrite dist_symm in H10.
    pose proof (real_le_le_plus_le _ _ _ _ H8 H10).
    apply real_ge_le in H11.
    pose proof (real_le_le_le _ _ _ H11 H12).
    replace (prec (x1 + 1) + (prec j + prec (x1 + 1))) with (prec x1 + prec j) in H13.
    rewrite H6 in H13.
    apply (real_le_plus_le (- prec j)) in H13.
    ring_simplify in H13.
    contradiction (real_gt_nle _ _ H7 H13).
    replace (prec (x1 + 1) + (prec j + prec (x1 + 1))) with (prec (x1 + 1) + prec (x1 + 1) +  prec j) by ring.
    rewrite prec_twice; auto.
  Defined.
  
    
  (* Goal forall f: nat -> M Real,  *)
  
End RealLimit2.





