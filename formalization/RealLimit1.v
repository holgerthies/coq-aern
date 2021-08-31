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


Section RealLimit1.
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



  (* classical limit *)
  Definition fast_lower_set (f : nat -> Real) := fun x => exists n, x <= f n - prec n.
  Lemma fast_lower_set_nemp : forall f, is_fast_cauchy_p f -> W_is_non_empty (fast_lower_set f).
  Proof.
    intros.
    exists (f(0) - prec O).
    unfold fast_lower_set.
    exists 0.
    right; auto.
  Qed.

  Lemma lower_set_upbd : forall f, is_fast_cauchy_p f -> W_is_bounded_above (fast_lower_set f).
  Proof.
    intros.
    exists (f(0) + prec 0).
    intro.
    intro.
    destruct H0.
    pose proof (H x 0).
    destruct H1.
    clear H1.
    apply (real_le_plus_le (f 0 - prec x)) in H2.
    replace ( f 0 - prec x + (f x - f 0)) with (f x - prec x) in H2 by ring.
    replace (f 0 - prec x + (prec x + prec 0)) with (f 0 + prec 0) in H2 by ring.
    exact (real_le_le_le _ _ _ H0 H2).
  Defined.


  Definition W_limit : forall f : nat -> Real, is_fast_cauchy_p f -> exists x, is_fast_limit_p x f.
  Proof.
    intros.
    pose proof (W_complete (fast_lower_set f) (fast_lower_set_nemp f H) (lower_set_upbd f H)).
    destruct H0.
    exists x.
    unfold is_fast_limit_p.
    intro.
    unfold W_is_sup in H0.
    unfold fast_lower_set in H0.
    unfold W_is_upper_bound in H0.
    destruct H0.
    split.
    pose proof (H0 (f n - prec n)).
    assert (exists n0 : nat, f n - prec n <= f n0 - prec n0).
    exists n.
    right.
    auto.
    pose proof (H2 H3).
    apply (real_le_plus_le (- f n )) in H4.
    replace (- f n + (f n - prec n)) with (- prec n) in H4 by ring.
    replace ( - f n + x) with (x - f n) in H4 by ring.
    exact H4.

    pose proof (H1 (prec n + f n)).
    assert ((forall z : Real, (exists n : nat, z <= f n - prec n) -> z <= prec n + f n)).
    intro.
    intro.
    destruct H3.
    pose proof (H n x0).
    destruct H4.  
    apply (real_le_plus_le (f x0 + prec n)) in H4.
    replace (f x0 + prec n + (- prec n - prec x0)) with (f x0 - prec x0) in H4 by ring.
    replace ( f x0 + prec n + (f n - f x0)) with (prec n + f n) in H4 by ring.
    exact (real_le_le_le _ _ _ H3 H4).
    
    pose proof (H2 H3).
    apply (real_le_plus_le (- f n)) in H4.
    replace (- f n + x)  with (x - f n) in H4 by ring.
    replace (- f n + (prec n + f n)) with (prec n) in H4 by ring.
    exact H4.
  Defined.
  
  Lemma limit_is_unique : forall (f : nat -> Real) x y, is_fast_limit_p x f -> is_fast_limit_p y f -> x = y.
  Proof.
    intros.
    unfold is_fast_limit_p in H, H0.
    destruct (real_total_order x y) as [c1|[c2|c3]].
    pose proof (padding y x c1) as H2.
    destruct H2 as [eps [p1 p2]].
    pose proof (real_Archimedean _ p1).
    destruct H1.
    assert (prec x0 < y - x).
    apply (lp _ _ (fun k => k - x)) in p2.
    ring_simplify in p2.
    rewrite p2; auto.
    pose proof (H (x0 +1)%nat).
    pose proof (H0 (x0 + 1)%nat).
    destruct H3, H4.
    pose proof (real_le_le_plus_le _ _ _ _ H3 H6).
    apply (real_le_plus_le (prec (x0 + 1) + f (x0 + 1)%nat - x)) in H7.
    replace 
      (prec (x0 + 1) + f (x0 + 1)%nat - x + (- prec (x0 + 1) + (y - f (x0 + 1)%nat)))
      with (y - x) in H7 by ring.
    replace
      (prec (x0 + 1) + f (x0 + 1)%nat - x + (x - f (x0 + 1)%nat + prec (x0 + 1)))
      with (prec (x0 + 1) + prec (x0 + 1)) in H7 by ring.
    rewrite prec_twice in H7.
    induction (real_gt_nle _ _ H2 H7).

    exact c2.


    pose proof (padding x y c3) as H2.
    destruct H2 as [eps [p1 p2]].
    pose proof (real_Archimedean _ p1).
    destruct H1.
    assert (prec x0 < x - y).
    apply (lp _ _ (fun k => k - y)) in p2.
    ring_simplify in p2.
    rewrite p2; auto.
    pose proof (H (x0 +1)%nat).
    pose proof (H0 (x0 + 1)%nat).
    destruct H3, H4.
    pose proof (real_le_le_plus_le _ _ _ _ H5 H4).
    apply (real_le_plus_le (prec (x0 + 1) + f (x0 + 1)%nat - y)) in H7.
    replace 
      (prec (x0 + 1) + f (x0 + 1)%nat - y + (x - f (x0 + 1)%nat + - prec (x0 + 1)))
      with (x - y) in H7 by ring.
    replace
      (prec (x0 + 1) + f (x0 + 1)%nat - y + (prec (x0 + 1) + (y - f (x0 + 1)%nat)))
      with (prec (x0 + 1) + prec (x0 + 1)) in H7 by ring.
    rewrite prec_twice in H7.
    induction (real_gt_nle _ _ H2 H7).
  Qed.


  
  (* Axiom limit : *)
  (*   forall f : nat -> Real, *)
  (*     (forall n m, - prec n - prec m < f n - f m < prec n + prec m) -> *)
  (*     {x | forall n, - prec n < x - f n < prec n}. *)

  (* constructive limit axiom *)

  (* Lemma limit_only_if_fast_cauchy : forall (f  x, is_fast_limit_p x f -> is_fast_cauchy_p f. *)
  (* Proof. *)
  (*   intros f x H n m. *)
  (*   pose proof (H n). *)
  (*   pose proof (H m). *)
  (*   destruct H0, H1. *)
  (*   split. *)
  (*   pose proof (@real_le_le_plus_le _ _ _ _ H2 H1). *)
  (*   apply (@real_le_plus_le (-x + f n - prec n)) in H4. *)
  (*   ring_simplify in H4. *)
  (*   exact H4. *)
  (*   pose proof (@real_le_le_plus_le _ _ _ _ H0 H3). *)
  (*   apply (@real_le_plus_le (f n + prec n - x)) in H4. *)
  (*   ring_simplify in H4. *)
  (*   exact H4. *)
  (* Qed. *)



  Lemma real_limit_P_lt_p :
    forall (P : Real -> Prop),
      (exists! z, P z) ->
      ((forall n, {e : Real | (exists a : Real, P a /\ - prec n < e - a < prec n)}) ->
       {a : Real | P a}).
  Proof.
    intros P f p.
    assert (is_fast_cauchy_p (fun n => projP1 _ _ (p n))).
    destruct f.
    apply (limit_only_if_fast_cauchy _ x).
    intros n.
    destruct (p n).
    simpl.
    destruct e.

    destruct H0.
    destruct H.
    rewrite (H2 _ H0).
    destruct H1.
    split.
    left.
    apply (real_lt_plus_lt (-prec n + x1 - x0)) in H3.
    ring_simplify in H3.
    exact H3.
    left.
    apply (real_lt_plus_lt (prec n + x1 - x0)) in H1.
    ring_simplify in H1.
    exact H1.

    exists (projP1 _ _ (real_limit_p _ H)). 
    destruct f.
    assert (
        (projP1 Real
                (fun x0 : Real =>
                   is_fast_limit_p x0
                                   (fun n : nat => projP1 Real (fun e : Real => exists a : Real, P a /\ - prec n < e - a < prec n) (p n)))
                (real_limit_p
                   (fun n : nat => projP1 Real (fun e : Real => exists a : Real, P a /\ - prec n < e - a < prec n) (p n)) H))
        =
        x).
    destruct ((real_limit_p
                            (fun n : nat => projP1 Real (fun e : Real => exists a : Real, P a /\ - prec n < e - a < prec n) (p n)) H)).
    simpl.
    assert (is_fast_limit_p x (fun n : nat => projP1 Real (fun e : Real => exists a : Real, P a /\ - prec n < e - a < prec n) (p n))).
    intros n.
    destruct (p n).
    simpl.
    destruct e.
    destruct H0.

    destruct H1.
    rewrite (H2 _ H1).
    split.
    destruct H3.
    left.
    apply (real_lt_plus_lt (-prec n + x2 - x1)) in H4.
    ring_simplify in H4.
    exact H4.
    destruct H3.
    left.
    apply (real_lt_plus_lt (prec n + x2 - x1)) in H3.
    ring_simplify in H3.
    exact H3.
    apply (limit_is_unique _ _ _ i H1).
    rewrite H1.
    destruct H0.
    exact H0.
  Defined.

  Lemma real_limit_P_p :
    forall (P : Real -> Prop),
      (exists! z, P z) ->
      ((forall n, {e : Real | (exists a : Real, P a /\ - prec n <= e - a <= prec n)}) ->
       {a : Real | P a}).
  Proof.
    intros P f p.
    assert (is_fast_cauchy_p (fun n => projP1 _ _ (p n))).
    destruct f.
    apply (limit_only_if_fast_cauchy _ x).
    intros n.
    destruct (p n).
    simpl.
    destruct e.

    destruct H0.
    destruct H.
    rewrite (H2 _ H0).
    destruct H1.
    split.
    apply (real_le_plus_le (-prec n + x1 - x0)) in H3.
    ring_simplify in H3.
    exact H3.
    apply (real_le_plus_le (prec n + x1 - x0)) in H1.
    ring_simplify in H1.
    exact H1.

    exists (projP1 _ _ (real_limit_p _ H)). 
    destruct f.
    assert (
        (projP1 Real
                (fun x0 : Real =>
                   is_fast_limit_p x0
                                   (fun n : nat => projP1 Real (fun e : Real => exists a : Real, P a /\ - prec n <= e - a <= prec n) (p n)))
                (real_limit_p
                              (fun n : nat => projP1 Real (fun e : Real => exists a : Real, P a /\ - prec n <= e - a <= prec n) (p n)) H))
        =
        x).
    destruct ((real_limit_p
                            (fun n : nat => projP1 Real (fun e : Real => exists a : Real, P a /\ - prec n <= e - a <= prec n) (p n)) H)).
    simpl.
    assert (is_fast_limit_p  x (fun n : nat => projP1 Real (fun e : Real => exists a : Real, P a /\ - prec n <= e - a <= prec n) (p n))).
    intros n.
    destruct (p n).
    simpl.
    destruct e.
    destruct H0.

    destruct H1.
    rewrite (H2 _ H1).
    split.
    destruct H3.

    apply (real_le_plus_le (-prec n + x2 - x1)) in H4.
    ring_simplify in H4.
    exact H4.
    destruct H3.
    apply (real_le_plus_le (prec n + x2 - x1)) in H3.
    ring_simplify in H3.
    exact H3.
    apply (limit_is_unique _ _ _ i H1).
    rewrite H1.
    destruct H0.
    exact H0.
  Defined.


  Definition real_mslimit_P_p :
    forall (P : Real -> Prop),
      (exists! z, P z) ->
      ((forall n, M {e  | (exists a : Real, P a /\ -prec n <= e - a <= prec n)}) -> {a : Real | P a}).
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
    assert ((forall n : nat, {e : Real | exists a : Real, P a /\ - prec n <= e - a <= prec n}) -> {a : Real | P a} ).
    intro.

    apply  (real_limit_P_p P H X0).
    apply (M_lift _ _ X0 X).
  Defined.


  Definition real_mslimit_P_lt_p :
    forall (P : Real -> Prop),
      (exists! z, P z) ->
      ((forall n, M {e  | (exists a : Real, P a /\ -prec n < e - a < prec n)}) -> {a : Real | P a}).
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
    assert ((forall n : nat, {e : Real | exists a : Real, P a /\ - prec n < e - a < prec n}) -> {a : Real | P a} ).
    intro.

    apply  (real_limit_P_lt_p P H X0).
    apply (M_lift _ _ X0 X).
  Defined.

End RealLimit1.
