Require Import Extraction.
Require Import RealAxioms.
Require Import Kleene.
Require Import IVT.
Require Import Minmax.


(* Real is Real, K is LazyBoolean, and M T is T *)
Extract Inlined Constant Real => "Real".
Extract Inlined Constant K => "LazyBoolean".
Extract Constant M "'a" => " 'a ".

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
Extract Inlined Constant Real0 => "0".
Extract Inlined Constant Real1 => "1".

Extract Inlined Constant Realplus => "plus".
Extract Inlined Constant Realmult => "mult".
Extract Inlined Constant Realopp => "opp".
Extract Inlined Constant Realinv => "inv".
Extract Inlined Constant Realltb => "lt".
Extract Inlined Constant slimit => "lim".



Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].

(* some shortcuts for efficiency. Not necessary *)
Extract Inlined Constant  Real2 => "2".
Extract Inlined Constant  Real3 => "3".
Extract Inlined Constant Realminus => "minus".
Extract Inlined Constant Realdiv => "div".
Extract Inlined Constant prec => "prec".


(* ExtractConstant M => " ".        (*  *) *)

Extract Inductive sigT => "prod" ["pair"].
Extraction Language Haskell.

Extract Inductive prod => "(*)"  [ "(,)" ].



(* Sewon's lab seminar talk material*)
(* Maximum *)

(* root finding function *)
Recursive Extraction  CIVT.


(* maximum *)
Recursive Extraction CMax.
