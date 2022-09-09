{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Tn where

import qualified Prelude
import Prelude ((+),(-),(/))
import qualified Prelude as P
import MixedTypesNumPrelude (ifThenElse)
import qualified Numeric.OrdGenericBool as OGB
import qualified Unsafe.Coerce as UC
import qualified Control.Monad
import qualified Data.Functor
import qualified MixedTypesNumPrelude as MNP
import qualified Math.NumberTheory.Logarithms as Logs
import qualified AERN2.Real as AERN2

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

nreal :: Prelude.Integer -> AERN2.CReal
nreal = AERN2.creal

prec :: Prelude.Integer -> AERN2.CReal
prec = ((0.5 :: AERN2.CReal) P.^)

npow2 :: Prelude.Integer -> Prelude.Integer
npow2 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.succ 0)
    (\n0 -> (Prelude.*) (npow2 n0) (Prelude.succ (Prelude.succ 0)))
    n

data Euclidean =
   Nil
 | Cons Prelude.Integer AERN2.CReal Euclidean

make_euclidean2 :: AERN2.CReal -> AERN2.CReal -> Euclidean
make_euclidean2 x y =
  Cons (Prelude.succ 0) x (Cons 0 y Nil)

type Ball = (,) Euclidean AERN2.CReal

make_ball2 :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal -> Ball
make_ball2 x y r =
  (,) (make_euclidean2 x y) r

tn_ball :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer -> Ball
tn_ball n k j =
  make_ball2
    ((P.*)
      (nreal
        ((Prelude.+) ((Prelude.*) (Prelude.succ (Prelude.succ 0)) k)
          (Prelude.succ 0))) (prec (Prelude.succ n)))
    ((P.*)
      (nreal
        ((Prelude.+) ((Prelude.*) (Prelude.succ (Prelude.succ 0)) j)
          (Prelude.succ 0))) (prec (Prelude.succ n))) (prec (Prelude.succ n))

tn_col :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer -> (([])
          Ball) -> ([]) Ball
tn_col n k j l =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (:) (tn_ball n k 0) l)
    (\j' -> tn_col n k j' ((:) (tn_ball n k j) l))
    j

tn_row :: Prelude.Integer -> Prelude.Integer -> (([]) Ball) -> ([]) Ball
tn_row n k l =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> tn_col n 0 (sub (npow2 n) (Prelude.succ 0)) l)
    (\k' ->
    tn_row n k' (tn_col n k (sub (sub (npow2 n) k) (Prelude.succ 0)) l))
    k

tn :: Prelude.Integer -> ([]) Ball
tn n =
  tn_row n (sub (npow2 n) (Prelude.succ 0)) ([])

