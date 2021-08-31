Require Import Real.
Require Import RealSubsets.
(* computing a multivalued function using limit; e.g., complex sqrt *)


Require Import Psatz.

(* for a classical description of real numbers [P : Real -> Prop],
   [x : Real] approximates it by [prec n] *)
(* Definition w_approx (P : Real -> Prop) (n : nat) (x : Real) : Prop *)
(*   := exists y, P y /\ dist x y <= prec n. *)

(* (* a predicate [P : Real -> Prop] is complete if for any converging seqeunce *)
(*    [f : nat -> Real] such that [w_approx P n (f n)] holds for all [n : nat], *)
(*    the limit point satisfies [P x]. For example, [Real \ {0}] is not complete. *) *)
(* Definition closed_predicate (P : Real -> Prop) := *)
(*   forall f : nat -> Real, *)
(*     is_fast_cauchy f -> (forall n, w_approx P n (f n)) -> (forall x, is_fast_limit x f -> P x). *)



Section MultiLimit.
  
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


  (* from a multivalued procedure apporximating, we get approximating sequences *)
  Lemma consecutive_converging_fast_cauchy : forall f : nat -> Real,
      (forall n, dist (f n) (f (S n)) <= prec (S n)) -> is_fast_cauchy f.
  Proof.
    intros f H.
    apply (proj2 (is_fast_cauchy_iff_p  _)).
    intros n1 m1.
    
    assert (forall n m k,  (n <= m)%nat -> (k = m - n)%nat ->  - prec n - prec m <= f n - f m <= prec n + prec m).
    intros n m k H0 e.
    assert (m  = k + n)%nat by (rewrite e; lia).
    induction (eq_sym H1).
    assert (- prec n + prec (n + k) <=  f n - f (k + n)%nat <= prec n - prec (n + k)). 
    induction k.
    replace (n + 0)%nat with n by lia; replace (0 + n)%nat with n by lia; split; simpl.
    replace (-prec n + prec n) with real_0 by ring.
    replace (f n - f n) with real_0 by ring.
    right; auto.
    replace (prec n - prec n) with real_0 by ring.
    replace (f n - f n) with real_0 by ring.
    right; auto.
    assert ( k = (k + n - n)%nat) by lia.
    assert ((k + n)%nat = (k + n)%nat) by apply eq_refl.
    assert (n <= k + n)%nat by lia.
    pose proof (IHk H4 H2 H3).
    clear e H1 H0 IHk H2 H3 H4.
    split.
    destruct H5.
    pose proof (H (k + n)%nat).

    
    pose proof ( proj1 (dist_le_prop _ _ _) H2).
    clear H2.
    destruct H3.
    pose proof (real_le_le_plus_le _ _ _ _ H0 H2).
    ring_simplify in H4.
    assert (
        - prec n + prec (n + S k)
        <=  - prec n + prec (n + k) - prec (S (k + n))).
    right.
    rewrite<- (prec_twice (n + k)).
    replace (n + S k )%nat with (n + k + 1)%nat by lia.
    replace (S (k + n ))%nat with (n + k + 1)%nat by lia.
    ring.
    exact (real_le_le_le _ _ _ H5 H4).
    destruct H5.
    pose proof (H (k + n)%nat).
    pose proof (proj1 (dist_le_prop _ _ _) H2).
    clear H2.
    destruct H3.
    pose proof (real_le_le_plus_le _ _ _ _ H1 H3).
    ring_simplify in H4.
    assert (
        prec n - prec (n + k) + prec (S (k + n)) <=
        prec n - prec (n + S k)).
    right.
    rewrite<- (prec_twice (n + k)).
    replace (n + S k )%nat with (n + k + 1)%nat by lia.
    replace (S (k + n ))%nat with (n + k + 1)%nat by lia.
    ring.
    exact (real_le_le_le _ _ _ H4 H5).
    destruct H2.
    split.
    apply (fun a => real_le_le_le _ _ _ a H2).
    pose proof (real_lt_lt_plus_lt _ _ _ _ (prec_pos (k + n)) (prec_pos (k + n))). 
    apply (real_lt_plus_lt (-prec n - prec (k + n))) in H4.
    ring_simplify in H4.
    replace (n + k)%nat with (k + n)%nat by lia.
    left; auto.
    apply (fun a => real_le_le_le _ _ _ H3 a).
    pose proof (real_lt_lt_plus_lt  _ _ _ _ (prec_pos (k + n)) (prec_pos (k + n))). 
    apply (real_lt_plus_lt (prec n - prec (k + n))) in H4.
    ring_simplify in H4.
    replace (n + k)%nat with (k + n)%nat by lia.
    left; auto.
    assert (J : (n1 <= m1 \/ m1 <= n1)%nat) by lia; destruct J.

    apply (H0 _ _ (m1 - n1)%nat H1  eq_refl).
    pose proof (H0 _ _  (n1 - m1)%nat H1 eq_refl).
    destruct H2 as [H2 H3].
    apply (real_le_plus_le (prec m1 + prec n1 - (f m1) + (f n1))) in H2.
    ring_simplify in H2.
    apply (real_le_plus_le (- prec m1 - prec n1 + (f n1) - (f m1))) in H3.
    ring_simplify in H3.
    replace (prec n1 + prec m1) with (prec m1 + prec n1) by ring;
      replace (- prec n1 - prec m1) with (- prec m1 - prec n1) by ring.
    replace (- f m1 + f n1) with (f n1 - f m1) in H2 by ring.
    split; auto.
  Defined.


  (* for a complete predicate [P : real_ -> Prop], when we give an initial searching point
   [ M {x : real_ | w_approx P O x}] and a procedure that refines it,
   [f : forall n x, w_approx P n x -> M {y : real_ | w_approx P (S n) y /\ dist_ x y <= prec n}],
   (see that f is a function that [ (f n) x p] is roughly a multivalued real number [y]
   such that (1) [y] approximates [P] by [prec (n + 1)] and (2) [|x-y| <= prec n] when 
   [x] is [prec n] approximation of [P]) it gives us a multivalued real numbers 
   that are in [P] *)
  Definition real_mlimit_P : forall P : Real -> Prop,
      is_seq_closed P ->
      M {x : Real | w_approx P O x} ->
      (forall n x, w_approx P n x ->
                   M {y : Real | w_approx P (S n) y /\ dist x y <= prec (S n)}) ->
      M {x : Real | P x}. 
  Proof.
    intros P c X f.
    assert ((forall n (x : {x : Real | w_approx P n x}),
                M {y : { y : Real | w_approx P (S n) y} | dist (projP1 _ _ x) (projP1 _ _ y) <= prec  (S n)})).
    intros.
    destruct x.
    pose proof (f n x w).
    apply (M_lift {y : Real | w_approx P (S n) y /\ dist x y <= prec (S n)}).
    intro.
    rename X1 into H.
    destruct H.
    destruct a.
    exists (exist _ x0 H).
    simpl.
    exact H0.
    exact X0.
    pose proof (M_paths _ _ X X0).
    simpl in X1.
    apply (M_lift_dom {x | w_approx P 0 x}).
    intro.
    apply (M_lift {f : forall n : nat, {x : Real | w_approx P n x}
                 | forall m : nat,
                     dist (projP1 Real (fun x : Real => w_approx P m x) (f m))
                           (projP1 Real (fun y : Real => w_approx P (S m) y) (f (S m))) <= prec (S m)}).
    intro.
    rename X2 into H.
    rename X3 into H0.
    destruct H.
    destruct H0.
    simpl in r.
    assert (is_fast_cauchy (fun n => projP1 _ _ (x0 n))).
    apply consecutive_converging_fast_cauchy.
    exact r.
    pose proof (real_limit _ H).
    rename X2 into H0.
    destruct H0.
    exists x1.
    pose proof (c (fun n => projP1 _ _ (x0 n)) H ).
    assert (forall n : nat, w_approx P n ((fun n0 : nat => projP1 Real (w_approx P n0) (x0 n0)) n)).
    intro.
    destruct (x0 n).
    simpl.
    exact w0.
    apply (H0 H1).
    exact i.
    exact X1.
    exact X.
  Defined.


End MultiLimit.
