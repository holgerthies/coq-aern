{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module STRn where

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

type Sig a =
  a
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

data T a =
   Nil
 | Cons a Prelude.Integer (T a)

map0 :: (a1 -> a2) -> Prelude.Integer -> (T a1) -> T a2
map0 f _ v =
  case v of {
   Nil -> Nil;
   Cons a n0 v' -> Cons (f a) n0 (map0 f n0 v')}

to_list :: Prelude.Integer -> (T a1) -> ([]) a1
to_list n v =
  let {
   fold_right_fix _ v0 b =
     case v0 of {
      Nil -> b;
      Cons a n0 w -> (:) a (fold_right_fix n0 w b)}}
  in fold_right_fix n v ([])

n2 :: Prelude.Integer
n2 = 2

real_0 :: AERN2.CReal
real_0 = 0

real_1 :: AERN2.CReal
real_1 = 1

real_2 :: AERN2.CReal
real_2 = 2

data Euclidean =
   Nil0
 | Cons0 Prelude.Integer AERN2.CReal Euclidean

caseS' :: Prelude.Integer -> Euclidean -> (AERN2.CReal
          -> Euclidean -> a1) -> a1
caseS' _ v h =
  case v of {
   Nil0 -> __;
   Cons0 _ h0 t -> h h0 t}

dim_succ_destruct :: Prelude.Integer -> Euclidean ->
                     (,) AERN2.CReal Euclidean
dim_succ_destruct n x =
  caseS' n x (\h t -> (,) h t)

split_euclidean2 :: Euclidean -> (,) AERN2.CReal
                    AERN2.CReal
split_euclidean2 p =
  let {x = dim_succ_destruct (Prelude.succ 0) p} in
  case x of {
   (,) x0 p0 ->
    let {x1 = dim_succ_destruct 0 p0} in
    case x1 of {
     (,) x2 _ -> (,) x0 x2}}

make_euclidean2 :: AERN2.CReal -> AERN2.CReal ->
                   Euclidean
make_euclidean2 x y =
  Cons0 (Prelude.succ 0) x (Cons0 0 y Nil0)

type Ball = (,) Euclidean AERN2.CReal

type Is_covert = Prelude.Integer -> (([]) Ball)

make_ball2 :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal
              -> Ball
make_ball2 x y r =
  (,) (make_euclidean2 x y) r

one_half :: AERN2.CReal
one_half =
  P.recip real_2

point_point_mid :: Euclidean -> Euclidean -> Euclidean
point_point_mid p1 p2 =
  let {s = split_euclidean2 p1} in
  case s of {
   (,) x p ->
    let {s0 = split_euclidean2 p2} in
    case s0 of {
     (,) x0 p0 ->
      make_euclidean2 ((P.*) ((+) x x0) one_half)
        ((P.*) ((+) p p0) one_half)}}

point_ball_mid :: Euclidean -> Ball -> Ball
point_ball_mid p b =
  case b of {
   (,) a b0 -> (,) (point_point_mid p a)
    ((P.*) b0 one_half)}

sT_split_ball :: Prelude.Integer -> (T Euclidean) ->
                 Ball -> ([]) Ball
sT_split_ball sT_vs_size_pred sT_vs b =
  to_list (Prelude.succ sT_vs_size_pred)
    (map0 (\v -> point_ball_mid v b) (Prelude.succ
      sT_vs_size_pred) sT_vs)

sTn :: Prelude.Integer -> (T Euclidean) -> Ball ->
       Prelude.Integer -> ([]) Ball
sTn sT_vs_size_pred sT_vs sT_initial_ball n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (:) sT_initial_ball ([]))
    (\n' ->
    concat
      (map (sT_split_ball sT_vs_size_pred sT_vs)
        (sTn sT_vs_size_pred sT_vs sT_initial_ball n')))
    n

sT_is_covert :: Prelude.Integer -> (T Euclidean) ->
                Ball -> Is_covert
sT_is_covert =
  sTn

t3_new :: a1 -> a1 -> a1 -> T a1
t3_new a b c =
  Cons a (Prelude.succ (Prelude.succ 0)) (Cons b
    (Prelude.succ 0) (Cons c 0 Nil))

sTR_initial_ball :: Ball
sTR_initial_ball =
  make_ball2 one_half one_half one_half

sTR_v1 :: Euclidean
sTR_v1 =
  make_euclidean2 real_0 real_1

sTR_v2 :: Euclidean
sTR_v2 =
  make_euclidean2 real_0 real_0

sTR_v3 :: Euclidean
sTR_v3 =
  make_euclidean2 real_1 real_0

sTR_vs :: T Euclidean
sTR_vs =
  t3_new sTR_v1 sTR_v2 sTR_v3

sTR_is_covert :: Is_covert
sTR_is_covert n =
  sT_is_covert n2 sTR_vs sTR_initial_ball n

