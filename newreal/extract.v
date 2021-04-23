Require Import Extraction.
Require Import BasicAxioms.
Require Import Kleene.
Require Import IVT.




Extract Inlined Constant T => "Real".
Extract Inlined Constant Tminus => "minus".
Extract Inlined Constant Tplus => "plus".
Extract Inlined Constant Tmult => "mult".
Extract Inlined Constant K => "LazyBoolean".
Extract Inlined Constant T0 => "0".
Extract Inlined Constant T1 => "1".
Extract Inlined Constant Topp => "opp".
Extract Inlined Constant Tinv => "inv".
Extract Inlined Constant Tltb => "lt".
Extract Inlined Constant Tdiv => "div".
Extract Inlined Constant choose => "choose".
Extract Inlined Constant mslimit => "limit".

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inlined Constant  T2 => "2".
Extract Inlined Constant  T3 => "3".
Extract Inlined Constant  unitM => "".
Extract Inlined Constant  lift_domM => "".

Extract Inductive sigT => "prod" ["pair"].
Extraction Language Haskell.


(* Sewon's lab seminar talk material*)
(* Maximum *)
Recursive Extraction CIVT.


