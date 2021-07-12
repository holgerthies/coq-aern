(* provides limit operations written with dist function *)
Require Export Base.
Require Export Kleene.
Require Export RealAxioms.
Require Export RealRing. 
Require Export RealOrder.
Require Export RealOrderTactic.
Require Export RealLimit1.
Require Export RealMetric.

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
Definition Real_limit :
  forall f : nat -> Real, is_fast_cauchy f -> {x | is_fast_limit x f}.
Proof.
  intros.
  assert (is_fast_cauchy_p f).
  intros n k.
  pose proof (proj1 (dist_le_prop (f n) (f k) (prec n + prec k)) (H n k)).
  replace (-prec n - prec k ) with (- (prec n + prec k)) by ring.
  auto.
  destruct (Real_limit_p _ H0).
  exists x.
  intro n.
  exact (proj2 (dist_le_prop x (f n) (prec n)) (i n)).
Defined.

Definition Real_limit_P :
  forall (P : Real -> Prop), (exists! z, P z) ->
                             (forall n, {e | (exists a : Real, P a /\ dist e a <= prec n) }) -> {a : Real | P a}.
Proof.
  intros.
  apply (Real_limit_P_p P H).
  intro.
  destruct (H0 n).
  exists x.
  destruct e.
  exists x0.
  destruct H1.
  split; auto.
  exact (proj1 (dist_le_prop x x0 (prec n)) H2).
Defined.
 



Definition Real_limit_P_lt :
  forall (P : Real -> Prop), (exists! z, P z) ->
    (forall n, {e | (exists a : Real, P a /\ dist e a < prec n) }) -> {a : Real | P a}.
Proof.
  intros.
  apply (Real_limit_P_lt_p P H).
  intro.
  destruct (H0 n).
  exists x.
  destruct e.
  exists x0.
  destruct H1.
  
  split; auto.
  destruct (dist_prop x x0).
  destruct H4.
  destruct (Realtotal_order x x0).
  split.
  apply Reallt_anti_anti.
  ring_simplify.
  pose proof (H5 H6).
  replace (-x + x0) with (x0 - x) by ring.
  rewrite <- H7.
  exact H2.

  assert (x - x0 < Real0).
  apply (Reallt_plus_r_lt (-x0) ) in H6.
  ring_simplify in H6.
  exact H6.
  assert (prec n > Real0) by auto with Realiny.
  exact (Reallt_lt_lt  _ _ _  H7 H8).

  destruct H6.
  rewrite H6.
  replace (x0 - x0) with Real0 by ring.
  split; auto with Realiny.
  apply Reallt_anti_anti.
  ring_simplify.
  apply prec_pos.
  apply prec_pos.

  pose proof (H3 H6).
  rewrite <- H7.
  split; auto.
  
  
  auto with Realiny.
  
  ring_simplify.
  
  
  auto with Realiny.
  
  auto with Realiny.
  
  
  ring_simplify in H7.
  pose proof (dist_pos_t x x0).
  assert (- prec n < Real0).
  apply Reallt_anti_anti.
  ring_simplify.
  apply prec_pos.
  destruct H8.
  apply (Reallt_lt_lt _ _ _ H9 H8).
  rewrite<- H8.
  exact H9.
Defined.

Definition Real_mslimit_P :
  forall (P : Real -> Prop),
    (exists! z, P z) ->
    ((forall n, [e  | (exists a : Real, P a /\ dist e a <= prec n)]) -> {a : Real | P a}).
Proof.
  intros.
  apply (countableLiftM)  in X.
  apply singletonM.
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
  intro.

  apply  (Real_limit_P P H H1).
  apply (liftM _ _ H1 X).
Defined.



Definition Real_mslimit_P_lt :
  forall (P : Real -> Prop),
    (exists! z, P z) ->
    ((forall n, [e  | (exists a : Real, P a /\ dist e a < prec n)]) -> {a : Real | P a}).
Proof.
  intros.
  apply (countableLiftM)  in X.
  apply singletonM.
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

  apply  (Real_limit_P_lt P H H1).
  apply (liftM _ _ H1 X).
Defined.






