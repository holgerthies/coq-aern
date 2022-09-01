{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module STn where

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

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
concat :: (([]) (([]) a1)) -> ([]) a1
concat l =
  case l of {
   ([]) -> ([]);
   (:) x l0 -> app x (concat l0)}

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f a) (map f t)}

data Euclidean =
   Nil
 | Cons Prelude.Integer AERN2.CReal Euclidean

caseS' :: Prelude.Integer -> Euclidean -> (AERN2.CReal -> Euclidean -> a1) ->
          a1
caseS' _ v h =
  case v of {
   Nil -> __;
   Cons _ h0 t -> h h0 t}

dim_succ_destruct :: Prelude.Integer -> Euclidean -> (,) AERN2.CReal
                     Euclidean
dim_succ_destruct n x =
  caseS' n x (\h t -> (,) h t)

type Ball = (,) Euclidean AERN2.CReal

split_euclidean2 :: Euclidean -> (,) AERN2.CReal AERN2.CReal
split_euclidean2 p =
  let {x = dim_succ_destruct (Prelude.succ 0) p} in
  case x of {
   (,) x0 p0 ->
    let {x1 = dim_succ_destruct 0 p0} in case x1 of {
                                          (,) x2 _ -> (,) x0 x2}}

make_euclidean2 :: AERN2.CReal -> AERN2.CReal -> Euclidean
make_euclidean2 x y =
  Cons (Prelude.succ 0) x (Cons 0 y Nil)

make_ball :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal -> Ball
make_ball x y r =
  (,) (make_euclidean2 x y) r

one_half :: AERN2.CReal
one_half =
  P.recip (2 :: AERN2.CReal)

sT_v1 :: Euclidean
sT_v1 =
  make_euclidean2 (P.negate (1 :: AERN2.CReal)) (1 :: AERN2.CReal)

sT_v2 :: Euclidean
sT_v2 =
  make_euclidean2 (P.negate (1 :: AERN2.CReal)) (P.negate (1 :: AERN2.CReal))

sT_v3 :: Euclidean
sT_v3 =
  make_euclidean2 (1 :: AERN2.CReal) (P.negate (1 :: AERN2.CReal))

point_point_mid :: Euclidean -> Euclidean -> Euclidean
point_point_mid p1 p2 =
  let {s = split_euclidean2 p1} in
  case s of {
   (,) x p ->
    let {s0 = split_euclidean2 p2} in
    case s0 of {
     (,) x0 p0 ->
      make_euclidean2 ((P.*) ((+) x x0) one_half) ((P.*) ((+) p p0) one_half)}}

point_ball_mid :: Euclidean -> Ball -> Ball
point_ball_mid p b =
  case b of {
   (,) a b0 -> (,) (point_point_mid p a) ((P.*) b0 one_half)}

sT_split_ball :: Ball -> ([]) Ball
sT_split_ball b =
  (:) (point_ball_mid sT_v1 b) ((:) (point_ball_mid sT_v2 b) ((:)
    (point_ball_mid sT_v3 b) ([])))

sTn :: Prelude.Integer -> ([]) Ball
sTn n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (:)
    (make_ball (0 :: AERN2.CReal) (0 :: AERN2.CReal) (1 :: AERN2.CReal))
    ([]))
    (\n' -> concat (map sT_split_ball (sTn n')))
    n

