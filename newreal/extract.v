Require Import Extraction.
Require Import RealAxioms.
Require Import Kleene.
Require Import IVT.




Extract Inlined Constant Real => "Real".
Extract Inlined Constant Realminus => "minus".
Extract Inlined Constant Realplus => "plus".
Extract Inlined Constant Realmult => "mult".
Extract Inlined Constant K => "LazyBoolean".
Extract Inlined Constant Real0 => "0".
Extract Inlined Constant Real1 => "1".
Extract Inlined Constant Realopp => "opp".
Extract Inlined Constant Realinv => "inv".
Extract Inlined Constant Realltb => "lt".
Extract Inlined Constant Realdiv => "div".
Extract Inlined Constant choose => "choose".
Extract Inlined Constant mslimit => "limit".

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inlined Constant  Real2 => "2".
Extract Inlined Constant  Real3 => "3".
Extract Inlined Constant  unitM => "".
Extract Inlined Constant  lift_domM => "".

Extract Inductive sigT => "prod" ["pair"].
Extraction Language Haskell.


(* Sewon's lab seminar talk material*)
(* Maximum *)
Recursive Extraction CIVT.


