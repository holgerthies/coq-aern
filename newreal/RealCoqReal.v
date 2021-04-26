Require Import Real.
Require Import Reals.

(* Parameter classical : Real -> R. *)

(* (* structure homomorphism *) *)
(* Axiom classical_const0 : classical Real0 = R0. *)
(* Axiom classical_const1 : classical Real1 = R1. *)
(* Axiom classical_addition : forall x y, classical (x + y) = (classical x + classical y)%R. *)
(* Axiom classical_multiplication : forall x y, classical (x * y) = (classical x * classical y)%R. *)
(* Axiom classical_subtraction : forall x, classical (- x) = (- classical x)%R. *)
(* Axiom classical_division : forall x (p : x <> Real0), classical (/ p) = (/classical x)%R. *)

(* Axiom classical_lt : forall x y, (x < y) <-> (classical x < classical y)%R. *)

(* (* order completion... *) *)
(* Definition Prop_convert :  (Real -> Prop) -> (R -> Prop). *)
(* Proof. *)
(*   intros. *)
(*   exact (forall x : Real, classical x = H -> X x ). *)
(* Defined. *)


(* Axiom transport_eq : forall x y :R, x = y -> forall a b, classical a = x -> classical b = y -> a = b. *)
(* Axiom transport_forall : forall P : Real -> Prop, (forall x : R, (Prop_convert P) x) -> (forall x : Real, P x). *)
(* Axiom transport_exists : forall P : Real -> Prop, (exists x : R, (Prop_convert P) x) -> (exists x : Real, P x). *)
(* Goal Real1 + Real0 = Real1. *)
(* Proof. *)
(*   assert (R1 + R0 = R1)%R. *)
(*   ring. *)
(*   apply (transport_eq _ _ H). *)
(*   apply classical_addition. *)
(*   exact classical_constant1. *)
(*   exact relator_constant0. *)
(*   exact relator_constant1. *)
(* Qed. *)


(* Goal forall x : Real, exists y : Real, x = - y. *)
(* Proof. *)
(*   intros. *)
(*   apply transport_exists. *)
(*   unfold mymy. *)
(*   apply (transport_forall). *)
(*   intro. *)
(*   unfold mymy. *)
(*   intro. *)
(*   intro. *)
(*   destruct (ana x). *)
(*   exists (- x0)%R. *)
(*   intro. *)
(*   intro. *)
  
  
(*   admit. *)
(*   exact x. *)


(* Axiom classical_multiplication : classical Real0 = R0. *)
(* Axiom classical_const0 : classical Real0 = R0. *)
(* Axiom classical_const0 : classical Real0 = R0. *)
(* Axiom classical_const0 : classical Real0 = R0. *)
(* Axiom classical_const0 : classical Real0 = R0. *)


Parameter relator : Real -> R -> Prop.

(* relator homomorphism *)
Axiom relator_constant0 : relator Real0 R0.
Axiom relator_constant1 : relator Real1 R1.
Axiom relator_addition : forall x y a b, relator x a -> relator y b -> relator (x + y) (a + b)%R.
Axiom relator_multiplication : forall x y a b, relator x a -> relator y b -> relator (x * y) (a * b)%R.
Axiom relator_subtraction : forall x a, relator x a ->  relator (-x) (-a)%R.
Axiom relator_diviison : forall x (p : x <> Real0) a b, relator x a -> relator (/ p) (/b)%R. 

(* relator is an anafunction *)
Axiom ana : forall x : Real, exists! y : R, relator x y.

Axiom transport_eq : forall x y : R, (x = y -> forall a b, relator a x -> relator b y -> a = b). 
Definition transport_fiber : (Real -> Prop) -> (R -> Prop).
Proof.
  intros.
  exact (forall x : Real, relator x H -> X x).
Defined.


Axiom transport_forall : forall P : Real -> Prop, (forall x : R, (transport_fiber P) x) -> (forall x : Real, P x).
Axiom transport_exists : forall P : Real -> Prop, (exists x : R, (transport_fiber P) x) -> (exists x : Real, P x).
Axiom transport : forall P : R -> Prop, (forall x, P x) -> (forall x y, relator x y -> P y).

Goal Real1 + Real0 = Real1.
Proof.
  assert (R1 + R0 = R1)%R.
  ring.
  apply (transport_eq _ _ H).
  apply relator_addition.
  exact relator_constant1.
  exact relator_constant0.
  exact relator_constant1.
Qed.

Require Import Psatz.


Goal forall x : Real, exists y : Real, x = - y.
Proof.
  apply transport_forall.
  intro.
  intro.
  intro.
  apply transport_exists.
  exists (- x)%R.
  intro.
  intro.
  apply (transport_eq x x (eq_refl _) x0 (-x1)).
  exact H.
  pose proof (relator_subtraction _ _ H0).
  
  replace (- - x)%R with x in H1 by lra.
  exact H1.
Qed.

