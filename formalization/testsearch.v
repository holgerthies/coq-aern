From mathcomp Require Import all_ssreflect.
Require Import ConstructiveEpsilon.
Require Import PeanoNat.

(* ******************************************** *)
(* search for nat with decidable precidate P *)
(* ******************************************** *)

(* Adapted code from https://softwarefoundations.cis.upenn.edu/current/lf-current/Logic.html *)
Theorem restricted_excluded_middle : forall P b,
(P <-> b = true) -> {P} + {~ P}.
Proof.
intros P [] H.
- left. rewrite H. reflexivity.
- right. rewrite H. intros contra. discriminate contra.
Defined.

Theorem lem_nat_eq : forall (n m : nat),
  {n = m} + {n <> m}.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply Nat.eqb_eq.
Defined.
(* End of adapted code *)

Definition testLPO1 : { n:nat |  n = 10%N }.
Proof.
  apply constructive_indefinite_ground_description_nat.
  move => n.
  apply lem_nat_eq.
  by exists 10%N.
Defined.

Compute let (a,_) := testLPO1 in a.
(* 
	 = 10
     : nat
*)

Require Import Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellNatInteger.
Extraction Language Haskell.

(* Extraction "Main" testLPO1. *)

Require Import Kleene.
Require Import Psatz.
Require Import Nat.

(* ******************************************** *)
(* search for nat with "choosable" precidate P *)
(* ******************************************** *)

Definition mjoinM (p q : Prop) (T : Type) : ({p}+{q} -> M T) ->  M ({p}+{q}) -> M T.
Proof.
  intros f x.
  exact (lift_domM _ _ f x).
Defined.


Definition linear_search_choose 
  (P : nat -> Prop)
  (P_decM : (forall n : nat, M ({P n.+1} + {~ P n}))) 
  := 
fix linear_search (m : nat) (b : before_witness P m) {struct b} :
	M {n : nat | P n} := 
  mjoinM _ _ _ 
    (fun P_dec =>
      match P_dec with
      | left yes_next => unitM _ (exist [eta P] m.+1 yes_next)
      | right no => linear_search m.+1 (inv_before_witness P m b no)
      end)
    (P_decM m).

Definition constructive_search_choose_nat
  : forall P : nat -> Prop,
      (forall n : nat, M ({P n.+1} + {~ P n}) ) ->
      (exists n : nat, P n) -> 
      M {n : nat | P n}
  :=
    fun 
    (P : nat -> Prop) 
    (P_decM : forall n : nat, M ({P n.+1} + {~ P n}))
    (e : exists n : nat, P n) =>
  linear_search_choose P P_decM 0 (let (n, p) := e in O_witness P n (stop P n p)).


(* ******************************************** *)
(* Code exracted from ConstructiveEpsilon for reference: *)
(* ******************************************** *)

(* 

Inductive before_witness (P : nat -> Prop) (n : nat) : Prop :=
	stop : P n -> before_witness P n
  | next : before_witness P n.+1 -> before_witness P n.

Definition inv_before_witness
  : forall (P : nat -> Prop) (n : nat),
  before_witness P n -> ~ P n -> before_witness P n.+1
  :=
fun (P : nat -> Prop) (n : nat) (b : before_witness P n) =>
match b with
| @stop _ _ p =>
	fun not_p : ~ P n =>
    match not_p p return (before_witness P n.+1) with
    end
| @next _ _ b0 => fun=> b0
end.

Definition constructive_indefinite_ground_description_nat
  : forall P : nat -> Prop,
      (forall n : nat, {P n} + {~ P n}) ->
      (exists n : nat, P n) -> {n : nat | P n}
  :=
fun (P : nat -> Prop) 
  (P_dec : forall n : nat, {P n} + {~ P n})
  (e : exists n : nat, P n) =>
linear_search P P_dec 0 (let (n, p) := e in O_witness P n (stop P n p)).
      
      
Definition constructive_indefinite_ground_description_nat
  : forall P : nat -> Prop,
  (forall n : nat, {P n} + {~ P n}) ->
  (exists n : nat, P n) -> {n : nat | P n}
  :=
fun (P : nat -> Prop) 
    (P_dec : forall n : nat, {P n} + {~ P n})
    (e : exists n : nat, P n) =>
  linear_search P P_dec 0 (let (n, p) := e in O_witness P n (stop P n p)).

Definition O_witness
  : forall (P : nat -> Prop) (n : nat),
  before_witness P n -> before_witness P 0
:=
fun P : nat -> Prop =>
  fix O_witness (n : nat) : before_witness P n -> before_witness P 0 :=
    match n as n0 return (before_witness P n0 -> before_witness P 0) with
    | 0 => id
    | n0.+1 => fun b : before_witness P n0.+1 => O_witness n0 (next P n0 b)
    end.

Definition linear_search
  : forall P : nat -> Prop,
  (forall n : nat, {P n} + {~ P n}) ->
  forall m : nat, before_witness P m -> {n : nat | P n}
  :=
fun (P : nat -> Prop) (P_dec : forall n : nat, {P n} + {~ P n}) =>
    fix linear_search (m : nat) (b : before_witness P m) {struct b} :
	  {n : nat | P n} :=
      match P_dec m with
      | left yes => exist [eta P] m yes
      | right no => linear_search m.+1 (inv_before_witness P m b no)
      end.

Definition constructive_indefinite_ground_description_nat
  : forall P : nat -> Prop,
  (forall n : nat, {P n} + {~ P n}) ->
  (exists n : nat, P n) -> {n : nat | P n}  
  :=
  fun (P : nat -> Prop) (P_dec : forall n : nat, {P n} + {~ P n})
    (e : exists n : nat, P n) =>
  linear_search P P_dec 0 (let (n, p) := e in O_witness P n (stop P n p))
     : forall P : nat -> Prop,
         (forall n : nat, {P n} + {~ P n}) ->
  (exists n : nat, P n) -> {n : nat | P n}. 
  
  *)
