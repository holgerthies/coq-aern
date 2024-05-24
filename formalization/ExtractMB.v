(* 
   Currently, this module is BROKEN.

   Experimental extraction using iRRAM-style real numbers as intervals with 
   a fixed precision and fast re-start when it is found that the precision is insufficient.
   It relies on a hack to quickly propagate a failure due to insufficient precision.
   The hack is that the M monad is not used for non-determinism but for efficiently 
   signalling such a failure.  This works sometimes but not always. 
*)

Require Import Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellNatInteger.
Require ExtrHaskellZInteger.
Require Import Real.
Require Import IVT.
Require Import Minmax.
Require Import sqrt.
Require Import testsearch.

Extraction Language Haskell.

(* Real is Real, K is LazyBoolean, and M T is T *)
Extract Inlined Constant Real => "(WithCurrentPrec (CN MPBall) p)".
Extract Inlined Constant K => "Kleenean".

(* Axioms for Kleenean *)
Extract Inlined Constant trueK => "(kleenean True)".
Extract Inlined Constant falseK => "(kleenean False)".
                                   
Extract Inlined Constant kneg => "not".
Extract Inlined Constant kland => "(&&)".
Extract Inlined Constant klor => "(||)".

Extract Inlined Constant choose => "select".

(* Axioms for Multivalueness *)
Extract Constant M "a" => " CN a ".
Extract Inlined Constant unitM => "cn".
Extract Inlined Constant multM => "join".
Extract Inlined Constant liftM => "Prelude.fmap".

Extract Inlined Constant mjoin => "Prelude.fmap".
(* Extract Inlined Constant mjoin => "liftTakeErrors". *)
(* mjoin is more-or-less the identity function, 
but it needs to correctly propagate CN and WithCurrentPrec wrappers. *)

(* Extract Inlined Constant countableLiftM => "(\f -> cn (unCN . f))". *)
(* Extract Inlined Constant singletonM => "unCN". *)

(* Exact Real Number Operations *)
Extract Inlined Constant Real0 => "0".
Extract Inlined Constant Real1 => "1".

Extract Inlined Constant Realplus => "(+)".
Extract Inlined Constant Realmult => "(*)".
Extract Inlined Constant Realopp => "negate".
Extract Inlined Constant Realinv => "recip".
Extract Inlined Constant Reallt_semidec => "(<)".
Extract Inlined Constant Realgt_semidec => "(>)".
Extract Inlined Constant Real_limit_p => "limit".
(* Extract Inlined Constant slimit => "limit". *)
(* Extract Inlined Constant mslimit => "limit". *)

(* Extract Inductive bool => "Bool" [ "True" "False" ]. *)
Extract Inductive sumbool => "Bool" [ "True" "False" ].
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

(* magnitude *)
Extraction "MagnitudeMB" magnitude.

(*

The Haskell module will require the following packages:
- cdar-mBound >= 0.1.0.1
- collect-errors >= 0.1.4
- mixed-types-num >= 0.5.3
- aern2-mp >= 0.2.1
- aern2-real >= 0.2.1
- integer-logarithms

The generated Haskell files need the following edits to make them work:

(1) Add the following language options at the start of the file:

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

(2) Add the following imports after "import qualified Prelude":

import Prelude hiding (pred, succ, (==),(/=),(<),(<=),(>),(>=),not,(&&),(||))
import Control.Monad (join)
import Numeric.OrdGenericBool
import MixedTypesNumPrelude (ifThenElse, integer, Kleenean(..), kleenean)
import Math.NumberTheory.Logarithms (integerLog2)
import Numeric.CollectErrors (CN,cn,liftTakeErrors)
import AERN2.MP
import AERN2.MP.Dyadic ()
import AERN2.MP.WithCurrentPrec
import AERN2.Real hiding (pi)

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
testRealmax2 = creal $ WithAnyPrec $ realmax (pi-pi) 0

*)
