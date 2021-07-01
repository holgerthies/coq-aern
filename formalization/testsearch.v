From mathcomp Require Import all_ssreflect.
Require Import ConstructiveEpsilon.
Require Import PeanoNat.

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