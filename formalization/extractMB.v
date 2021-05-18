Require Import Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellNatInteger.
Require Import Real.
Require Import IVT.
Require Import Minmax.
Require Import sqrt.

Extraction Language Haskell.

(* Real is Real, K is LazyBoolean, and M T is T *)
Extract Inlined Constant Real => "(WithCurrentPrec (CN MPBall) p)".
Extract Inlined Constant K => "(CN Kleenean)".

(* Axioms for Kleenean *)
Extract Inlined Constant trueK => "(cn $ kleenean True)".
Extract Inlined Constant falseK => "(cn $ kleenean False)".
                                   
Extract Inlined Constant kneg => "not".
Extract Inlined Constant kland => "(&&)".
Extract Inlined Constant klor => "(||)".

Extract Inlined Constant choose => "select".

(* Axioms for Multivalueness *)
Extract Constant M "a" => " a ".
Extract Inlined Constant unitM => "id".
Extract Inlined Constant multM => "id".
Extract Inlined Constant liftM => "id".

Extract Inlined Constant mjoin => "liftTakeErrors".
(* mjoin is more-or-less the identity function, 
but it needs to correctly propagate CN and WithCurrentPrec wrappers. *)
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

(* Extract Inductive bool => "(CN Bool)" [ "(cn True)" "(cn False)" ]. *)
Extract Inductive sumbool => "(CN Bool)" [ "True" "False" ].
(* The missing CN in the constants is compensated for 
   by our mapping for mjoin. *)

(* some shortcuts for efficiency. Not necessary *)
Extract Inlined Constant  Real2 => "2".
Extract Inlined Constant  Real3 => "3".
Extract Inlined Constant Realminus => "(-)".
Extract Inlined Constant Realdiv => "(/)".
Extract Inlined Constant prec => "(0.5^)".

Extract Inductive sigT => "(,)" ["(,)"].
Extract Inductive prod => "(,)"  [ "(,)" ].

Extract Inlined Constant Nat.log2 => "(integer . integerLog2)".

(* Maximum *)

(* root finding function *)
Extraction "IVTMB" CIVT.

(* maximum *)
Extraction "MaxMB" Realmax.

(* sqrt *)
Extraction "SqrtMB" restr_sqrt.

(*

The Haskell module will require the following packages:
- collect-errors >= 0.1.2
- mixed-types-num >= 0.5.2
- aern2-mp >= 0.2
- aern2-real >= 0.2
- integer-logarithms

The generated Haskell files need the following edits to make them work:

(1) Add the following language options at the start of the file:

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

(2) Add the following imports after "import qualified Prelude":

import Prelude hiding (pi, pred, succ, (==),(/=),(<),(<=),(>),(>=),not,(&&),(||))
import Numeric.OrdGenericBool
import MixedTypesNumPrelude (ifThenElse, integer, Kleenean(..), kleenean)
import Math.NumberTheory.Logarithms (integerLog2)
import Numeric.CollectErrors (CN,cn,liftTakeErrors)
import AERN2.MP
import AERN2.MP.Dyadic ()
import AERN2.MP.WithCurrentPrec
import AERN2.Real

(3) Add "(HasCurrentPrecision p) => " to every function signature that features
the type variable "p", eg:

realgtb :: (HasCurrentPrecision p) => (WithPrecision (CN MPBall) p)
	       ->
           (WithPrecision (CN MPBall) p)
           -> (CN Kleenean)
realgtb z1 z2 =
  (<) z2 z1

(4) To use the generated functions to compute a real number, use eg:

testRealmax1 :: CN MPBall
testRealmax1 = runWithPrec (prec 1000000) $ realmax (pi-pi) 0

testRealmax2 :: CReal
testRealmax2 = crealFromWithCurrentPrec $ realmax (pi-pi) 0

*)
