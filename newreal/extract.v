Require Import Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellNatInteger.
Require Import Real.
Require Import IVT.
Require Import Minmax.
Require Import sqrt.


(* Real is Real, K is LazyBoolean, and M T is T *)
Extract Inlined Constant Real => "CReal".
Extract Inlined Constant K => "CKleenean".
Extract Constant M "a" => " a ".

Extract Inlined Constant Nat.log2 => "(integer . integerLog2)".

(* Axioms for Kleenean *)
Extract Inlined Constant trueK => "true".
Extract Inlined Constant falseK => "false".
                                   
(* Axioms for Multivalueness *)
Extract Inlined Constant unitM => "id".
Extract Inlined Constant multM => "id".
Extract Inlined Constant liftM => "id".

Extract Inlined Constant choose => "select".
Extract Inlined Constant countableM => "id".
Extract Inlined Constant singletonM => "id".



(* Exact Real Number Operations *)
Extract Inlined Constant Real0 => "(creal 0)".
Extract Inlined Constant Real1 => "(creal 1)".

Extract Inlined Constant Realplus => "add".
Extract Inlined Constant Realmult => "mul".
Extract Inlined Constant Realopp => "negate".
Extract Inlined Constant Realinv => "recip".
Extract Inlined Constant Realltb => "(<)".
Extract Inlined Constant limit => "limit".



Extract Inductive bool => "Bool" [ "True" "False" ].
Extract Inductive sumbool => "Bool" [ "True" "False" ].

(* some shortcuts for efficiency. Not necessary *)
Extract Inlined Constant  Real2 => "(creal 2)".
Extract Inlined Constant  Real3 => "(creal 3)".
Extract Inlined Constant Realminus => "sub".
Extract Inlined Constant Realdiv => "divide".
Extract Inlined Constant prec => "((creal 0.5)^)".


(* ExtractConstant M => " ".        (*  *) *)

Extract Inductive sigT => "(,)" ["(,)"].
Extraction Language Haskell.

Extract Inductive prod => "(,)"  [ "(,)" ].



(* Sewon's lab seminar talk material*)
(* Maximum *)

(* root finding function *)
Recursive Extraction  CIVT.


(* maximum *)
Recursive Extraction Realmax.

(* sqrt *)
Recursive Extraction restr_sqrt.
