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

(* Axiom transport_eq : forall x y : R, (x = y -> forall a b, relator a x -> relator b y -> a = b).  *)

Axiom transport_eq : forall a b : Real, (forall x y, relator a x -> relator b y -> x = y) -> a = b.

Definition transport_fiber : (Real -> Prop) -> (R -> Prop).
Proof.
  intros.
  exact (forall x : Real, relator x H -> X x).
Defined.


Axiom transport_forall : forall P : Real -> Prop, (forall x : R, (transport_fiber P) x) -> (forall x : Real, P x).
Axiom transport_exists : forall P : Real -> Prop, (exists x : R, (transport_fiber P) x) -> (exists x : Real, P x).
Axiom transport : forall P : R -> Prop, (forall x, P x) -> (forall x y, relator x y -> P y).

Ltac classical :=
  match goal with
  | |- @eq Real ?x ?y => apply transport_eq; repeat intro (* (fail "not implemented yet") *)
  | |- exists x : Real, ?A => apply transport_exists; repeat intro
  | |- forall x : Real, ?A => apply transport_forall; repeat intro
  (* | |- ?A => match A with *)
  (*          | ?a = ?b => fail "haha" *)
  (*          | _ => fail "FAIL" A *)
  (*          end  *)


  end.

(* Ltac relate s := *)
(*   match (type of s) with *)
(*   | relator x y => *)
  
(*   end *)
    



(* Goal Real1 + Real0 = Real1. *)
(* Proof. *)
(*   classical. *)
(*   assert (R1 + R0 = R1)%R. *)
(*   ring. *)
(*   exact relator_constant1. *)
(*   exact relator_constant0. *)
(*   exact relator_constant1. *)
(* Qed. *)

Require Import Psatz.

Definition test : forall P: Real -> Prop, forall Q : R -> Prop, (forall x y, relator x y -> Q y -> P x) -> (exists x : R, Q x) -> (exists x : R, forall y : Real, relator y x -> P y).
Proof.
  intros.
  destruct H0.
  exists x.
  intro.
  intro.
  exact (H y x H1 H0).
Defined.

  
Fixpoint sqrt_approx x0 n x := match n with
                               | 0%nat => x0
                               | (S n') => let P := (sqrt_approx x0 n' x) in
                                          (/ Real2_neq_Real0) * (P + (x / P))
                               end.


  
Goal forall x : Real, exists y : Real, x = - y.
Proof.
  classical.
  classical.
  unfold transport_fiber.

  apply (test _ (fun x1 : R => x = (- x1)%R)).
  intros.
  classical.
  admit.
  
  exists (-x)%R.
  lra.
  
  
  unfold transport_fiber.
  
  INTRO.
  
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

