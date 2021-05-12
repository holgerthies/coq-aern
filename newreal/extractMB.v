Require Import Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellNatInteger.
Require Import Real.
Require Import IVT.
Require Import Minmax.
Require Import sqrt.


(* Real is Real, K is LazyBoolean, and M T is T *)
Extract Inlined Constant Real => "(WithCurrentPrec (CN MPBall) p)".
Extract Inlined Constant K => "(CN MxP.Kleenean)".
Extract Constant M "a" => " a ".

Extract Inlined Constant Nat.log2 => "(MxP.integer . integerLog2)".

(* Axioms for Kleenean *)
(* Extract Inlined Constant trueK => "true".
Extract Inlined Constant falseK => "false". *)
                                   
(* Axioms for Multivalueness *)
Extract Inlined Constant unitM => "id".
Extract Inlined Constant multM => "id".
Extract Inlined Constant liftM => "id".

Extract Inlined Constant choose => "select".
Extract Inlined Constant mjoin => "liftTakeErrors".
(* mjoin is more-or-less the identity function, 
but it needs to correctly propagate CN and WithCurrentPrec wrappers. *)
Extract Inlined Constant countableM => "id".
Extract Inlined Constant singletonM => "id".



(* Exact Real Number Operations *)
Extract Inlined Constant Real0 => "0".
Extract Inlined Constant Real1 => "1".

Extract Inlined Constant Realplus => "(+)".
Extract Inlined Constant Realmult => "(*)".
Extract Inlined Constant Realopp => "negate".
Extract Inlined Constant Realinv => "recip".
Extract Inlined Constant Realltb => "(MxP.<)".
Extract Inlined Constant limit => "limit".

(* Extract Inductive bool => "(CN Bool)" [ "(cn True)" "(cn False)" ]. *)
Extract Inductive sumbool => "(CN Bool)" [ "True" "False" ].

(* some shortcuts for efficiency. Not necessary *)
Extract Inlined Constant  Real2 => "2".
Extract Inlined Constant  Real3 => "3".
Extract Inlined Constant Realminus => "(-)".
Extract Inlined Constant Realdiv => "(/)".
Extract Inlined Constant prec => "(0.5^)".


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

(*

The Haskell module will require the following packages:
- collect-errors >= 0.1.2
- mixed-types-num >= 0.5
- aern2-mp >= 0.2
- aern2-real >= 0.2
- integer-logarithms

The generated Haskell file needs the following edits to make it work:

(1) Replace the first three lines with:

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
module ${ModuleName} where
import qualified Prelude
import Prelude hiding (pred, succ)
import qualified MixedTypesNumPrelude as MxP
import MixedTypesNumPrelude (ifThenElse)
import Numeric.CollectErrors (CN,liftTakeErrors)
import AERN2.Limit
import AERN2.MP
import AERN2.MP.Dyadic ()
import AERN2.MP.WithCurrentPrec
import AERN2.Real(select)
import AERN2.Real.Type
import Math.NumberTheory.Logarithms (integerLog2)

(2) Add "(HasCurrentPrecision p) => " to every function signature that features
the type variable "p", eg:

realgtb :: (HasCurrentPrecision p) => (WithPrecision (CN MPBall) p)
	       ->
           (WithPrecision (CN MPBall) p)
           -> (CN MxP.Kleenean)
realgtb z1 z2 =
  (MxP.<) z2 z1

(3) To use the generated functions to compute a real number, use eg:

testRealmax1 :: CN MPBall
testRealmax1 = runWithPrec (prec 1000000) $ realmax (pi-pi) 0

testRealmax2 :: CReal
testRealmax2 = crealFromWithCurrentPrec $ realmax (pi-pi) 0

*)
