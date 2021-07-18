(* provides limit operations written with dist function *)
Require Export Base.
Require Export Kleene.
Require Import MultivalueMonad.
Require Export RealAxioms.
Require Export RealRing. 
Require Export RealOrder.
Require Export RealOrderTactic.
Require Export RealLimit0.
Require Export RealLimit1.
Require Export RealMetric.

Section RealLimit2.
  Context {T : ComplArchiSemiDecOrderedField}.
  Notation R := (CarrierField T).

  (* Notation real_0__ := (  (let *)
  (*  (real, real_0, real_1, real_plus, real_mult, real_opp, real_inv, real_lt, _, _, _, _, _, *)
  (*   _, _, _, _, _, _, _, _, _, _, _, _) as s *)
  (*   return *)
  (*     (let *)
  (*        (real, real_0, real_1, real_plus, real_mult, real_opp, real_inv, real_lt, _, _, _, *)
  (*         _, _, _, _, _, _, _, _, _, _, _, _, _, _) := s in *)
  (*      real) := let (CarrierField, _, _) := T in CarrierField in *)
  (*                           real_0)). *)
  
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
  Opaque real_0.
  Opaque real_1.
  
  Definition is_fast_cauchy (f : nat -> real_) := forall n m, dist (f n) (f m) <= prec_ n + prec_ m.
  Definition is_fast_limit (x : real_) (f : nat -> real_) := forall n, dist x (f n) <= prec_ n.


  Lemma is_fast_cauchy_iff_p : forall f, is_fast_cauchy f <-> is_fast_cauchy_p f.
  Proof.
    intros.
    split.
    intros H n m.
    pose proof (proj1 (dist_le_prop (f n) (f m) (prec_ n + prec_ m)) (H n m)).
    replace (- prec_ n - prec_ m) with (- (prec_ n + prec_ m)) by ring.
    auto.
    intros H n m .
    apply (proj2 (dist_le_prop (f n) (f m) (prec_ n + prec_ m)) ).
    pose proof (H n m ).
    replace (- prec_ n - prec_ m) with (- (prec_ n + prec_ m)) in H0 by ring.
    auto.
  Defined.

  
  (* 

   there are various limit operations provided by the library.
   [T_limit] : defined by  
   *)
  Definition real_limit :
    forall f : nat -> real_, is_fast_cauchy f -> {x | is_fast_limit x f}.
  Proof.
    intros.
    assert (is_fast_cauchy_p f).
    intros n k.
    pose proof (proj1 (dist_le_prop (f n) (f k) (prec_ n + prec_ k)) (H n k)).
    replace (-prec_ n - prec_ k ) with (- (prec_ n + prec_ k)) by ring.
    auto.
    destruct (real_limit_p _ _ H0).
    exists x.
    intro n.
    exact (proj2 (dist_le_prop x (f n) (prec_ n)) (i n)).
  Defined.

  Definition real_limit_P :
    forall (P : real_ -> Prop), (exists! z, P z) ->
                               (forall n, {e | (exists a : real_, P a /\ dist e a <= prec_ n) }) -> {a : real_ | P a}.
  Proof.
    intros.
    apply (real_limit_P_p P H).
    intro.
    destruct (H0 n).
    exists x.
    destruct e.
    exists x0.
    destruct H1.
    split; auto.
    exact (proj1 (dist_le_prop x x0 (prec_ n)) H2).
  Defined.
  



  Definition real_limit_P_lt :
    forall (P : real_ -> Prop), (exists! z, P z) ->
                               (forall n, {e | (exists a : real_, P a /\ dist e a < prec_ n) }) -> {a : real_ | P a}.
  Proof.
    intros.
    apply (real_limit_P_lt_p P H).
    intro.
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

    assert (x - x0 < real_0_).
    apply (real_lt_plus_r_lt (-x0) ) in H6.
    ring_simplify in H6.
    exact H6.
    assert (prec_ n > real_0_) by (apply prec_pos). 
    exact (real_lt_lt_lt  _ _ _  H7 H8).

    destruct H6.
    rewrite H6.
    replace (x0 - x0) with real_0_ by ring.
    split; auto with real.
    apply real_lt_anti_anti.
    replace (- real_0) with real_0_ by ring.
    replace (- - prec_ n) with (prec_ n) by ring.
    apply prec_pos.
    apply prec_pos.

    pose proof (H3 H6).
    rewrite <- H7.
    split; auto.
    
    ring_simplify in H7.
    pose proof (dist_pos_t  x x0).
    assert (- prec_ n < real_0_).
    apply real_lt_anti_anti.
    replace (- real_0) with real_0_ by ring.
    replace (- - prec_ n) with (prec_ n) by ring.
    apply prec_pos.
    destruct H8.
    apply (real_lt_lt_lt _ _ _ H9 H8).
    rewrite<- H8.
    exact H9.
  Defined.

  Definition real_mslimit_P :
    forall (P : real_ -> Prop),
      (exists! z, P z) ->
      ((forall n, [e  | (exists a : real_, P a /\ dist e a <= prec_ n)]) -> {a : real_ | P a}).
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
    assert (exists z : real_, P z).
    destruct H.
    exists x.
    destruct H.
    exact H.

    
    assert ((forall n : nat, {e : real_ | exists a : real_, P a /\ dist e a <= prec_ n}) -> {a : real_ | P a} ).
    intro.

    apply  (real_limit_P P H H1).
    apply (M_lift _ _ H1 X).
  Defined.



  Definition real_mslimit_P_lt :
    forall (P : real_ -> Prop),
      (exists! z, P z) ->
      ((forall n, [e  | (exists a : real_, P a /\ dist e a < prec_ n)]) -> {a : real_ | P a}).
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
    assert (exists z : real_, P z).
    destruct H.
    exists x.
    destruct H.
    exact H.

    
    assert ((forall n : nat, {e : real_ | exists a : real_, P a /\ dist e a < prec_ n}) -> {a : real_ | P a} ).
    intro.

    apply  (real_limit_P_lt P H H1).
    apply (M_lift _ _ H1 X).
  Defined.

End RealLimit2.





