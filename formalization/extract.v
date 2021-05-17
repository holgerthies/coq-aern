Require Import Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellNatInteger.
Require Import Real.
Require Import IVT.
Require Import Minmax.
Require Import sqrt.

Extraction Language Haskell.

(* Real is Real, K is LazyBoolean, and M T is T *)
Extract Inlined Constant Real => "CReal".
Extract Inlined Constant K => "CKleenean".

(* Axioms for Kleenean *)
Extract Inlined Constant trueK => "(ckleenean True)".
Extract Inlined Constant falseK => "(ckleenean False)".
                                   
Extract Inlined Constant kneg => "not".
Extract Inlined Constant kland => "(&&)".
Extract Inlined Constant klor => "(||)".

Extract Inlined Constant choose => "select".

(* Axioms for Multivalueness *)
Extract Constant M "a" => " a ".
Extract Inlined Constant unitM => "id".
Extract Inlined Constant multM => "id".
Extract Inlined Constant liftM => "id".

(* Extract Inlined Constant mjoin => "id". *)
Extract Inlined Constant countableLiftM => "id".
Extract Inlined Constant singletonM => "id".

(* Exact Real Number Operations *)
Extract Inlined Constant Real0 => "0".
Extract Inlined Constant Real1 => "1".

Extract Inlined Constant Realplus => "(+)".
Extract Inlined Constant Realmult => "(*)".
Extract Inlined Constant Realopp => "negate".
Extract Inlined Constant Realinv => "recip".
Extract Inlined Constant Reallt_semidec => "(<)".
Extract Inlined Constant Realgt_semidec => "(>)".
Extract Inlined Constant limit => "limit".

Extract Inductive bool => "Bool" [ "True" "False" ].
Extract Inductive sumbool => "Bool" [ "True" "False" ].

(* some shortcuts for efficiency. Not necessary *)
Extract Inlined Constant  Real2 => "2".
Extract Inlined Constant  Real3 => "3".
Extract Inlined Constant Realminus => "(-)".
Extract Inlined Constant Realdiv => "(/)".
Extract Inlined Constant prec => "(0.5^)".

Extract Inductive sigT => "(,)" ["(,)"].
Extract Inductive prod => "(,)"  [ "(,)" ].

Extract Inlined Constant Nat.log2 => "(integer . integerLog2)".

(* Sewon's lab seminar talk material*)
(* Maximum *)

(* root finding function *)
Extraction "IVT" CIVT.

(* maximum *)
Extraction "Max" Realmax.

(* sqrt *)
Extraction "Sqrt" restr_sqrt.

(* Require Import Nabla. *)

(* Require Import Coq.Reals.Abstract.ConstructiveMinMax. *)

(* Recursive Extraction CRmin. *)

(*

The Haskell module will require the following packages:
- collect-errors >= 0.1.2
- mixed-types-num >= 0.5.2
- aern2-mp >= 0.2
- aern2-real >= 0.2
- integer-logarithms

In the generated Haskell files, add the following imports:

import Prelude hiding (pred, succ, (==),(/=),(<),(<=),(>),(>=),not,(&&),(||))
import Numeric.OrdGenericBool
import MixedTypesNumPrelude (ifThenElse, integer)
import Math.NumberTheory.Logarithms (integerLog2)
import AERN2.Real

*)
