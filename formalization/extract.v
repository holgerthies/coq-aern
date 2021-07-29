Require Import Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellNatInteger.
Require ExtrHaskellZInteger.
Extraction Language Haskell.

Require Import Real.

(* Real is Real, K is LazyBoolean, and M T is T *)
Extract Inlined Constant Real => "AERN2.CReal".
Extract Inlined Constant K => "AERN2.CKleenean".

(* Axioms for Kleenean *)
Extract Inlined Constant trueK => "(AERN2.ckleenean Prelude.True)".
Extract Inlined Constant falseK => "(AERN2.ckleenean Prelude.False)".
                                   
Extract Inlined Constant kneg => "OGB.not".
Extract Inlined Constant kland => "(OGB.&&)".
Extract Inlined Constant klor => "(OGB.||)".

Extract Inlined Constant select => "AERN2.select".

(* Axioms for Multivalueness *)
Extract Constant M "a" => " a ".
Extract Inlined Constant unitM => "Prelude.id".
Extract Inlined Constant multM => "Prelude.id".
Extract Inlined Constant liftM => "Prelude.id".

Extract Inlined Constant mjoin => "Prelude.id".
Extract Inlined Constant countableLiftM => "Prelude.id".
Extract Inlined Constant singletonM => "Prelude.id".

(* Exact Real Number Operations *)
Extract Inlined Constant Real0 => "0".
Extract Inlined Constant Real1 => "1".

Extract Inlined Constant Realplus => "(Prelude.+)".
Extract Inlined Constant Realmult => "(Prelude.*)".
Extract Inlined Constant Realopp => "Prelude.negate".
Extract Inlined Constant Realinv => "Prelude.recip".
Extract Inlined Constant Reallt_semidec => "(OGB.<)".
Extract Inlined Constant Realgt_semidec => "(OGB.>)".
Extract Inlined Constant limit => "AERN2.limit".

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

(* some shortcuts for efficiency. Not necessary *)
Extract Inlined Constant  Real2 => "2".
Extract Inlined Constant Realminus => "(Prelude.-)".
Extract Inlined Constant Realdiv => "(Prelude./)".
Extract Inlined Constant prec => "(0.5 Prelude.^)".

Extract Inductive sigT => "(,)" ["(,)"].
Extract Inductive prod => "(,)"  [ "(,)" ].

Extract Inlined Constant Nat.log2 => "(MNP.integer Prelude.. Logs.integerLog2)".

(* Sewon's lab seminar talk material*)
(* Maximum *)

(* root finding function *)
Require Import IVT.
Extraction "IVT" CIVT.

(* maximum *)
Require Import Minmax.
Extraction "Max" Realmax.

(* sqrt *)
Require Import sqrt.
Extraction "Sqrt" restr_sqrt.

(* Require Import Nabla. *)

(* Require Import Coq.Reals.Abstract.ConstructiveMinMax. *)

(* Recursive Extraction CRmin. *)

(*

The Haskell module will require the following packages:
- cdar-mBound >= 0.1.0.1
- collect-errors >= 0.1.4
- mixed-types-num >= 0.5.3
- aern2-mp >= 0.2.1
- aern2-real >= 0.2.1
- integer-logarithms

In the generated Haskell files, add the following imports:

import qualified Numeric.OrdGenericBool as OGB
import MixedTypesNumPrelude (ifThenElse)
import qualified MixedTypesNumPrelude as MNP
import qualified Math.NumberTheory.Logarithms as Logs
import qualified AERN2.Real as AERN2

*)
