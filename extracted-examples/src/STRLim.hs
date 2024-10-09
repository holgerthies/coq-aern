{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module STRLim where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

import Prelude ((+),(-),(/))
import qualified Prelude as P
import MixedTypesNumPrelude (ifThenElse)
import Numeric.CollectErrors (unCNfn2)
import qualified Numeric.OrdGenericBool as OGB
import qualified Unsafe.Coerce as UC
import qualified Control.Monad
import qualified Data.Functor
import qualified MixedTypesNumPrelude as MNP
import qualified Math.NumberTheory.Logarithms as Logs
import qualified AERN2.Real as AERN2
import qualified AERN2.Continuity.Principles as AERN2Principles

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
pred :: Prelude.Integer -> Prelude.Integer
pred = (\n -> Prelude.max 0 (Prelude.pred n))

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

n1 :: Prelude.Integer
n1 = 1

n2 :: Prelude.Integer
n2 = 2

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f a) (map f t)}

real_0 :: AERN2.CReal
real_0 = 0

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

case0 :: a1 -> Euclidean -> a1
case0 h v =
  case v of {
   Nil -> h;
   Cons _ _ _ -> __}

caseS' :: Prelude.Integer -> Euclidean -> (AERN2.CReal -> Euclidean -> a1) ->
          a1
caseS' _ v h =
  case v of {
   Nil -> __;
   Cons _ h0 t -> h h0 t}

rect2 :: a1 -> (Prelude.Integer -> Euclidean -> Euclidean -> a1 ->
         AERN2.CReal -> AERN2.CReal -> a1) -> Prelude.Integer -> Euclidean ->
         Euclidean -> a1
rect2 bas rect _ v1 v2 =
  case v1 of {
   Nil -> case0 bas v2;
   Cons n' h1 t1 ->
    caseS' n' v2 (\h2 t2 -> rect n' t1 t2 (rect2 bas rect n' t1 t2) h1 h2)}

dim_succ_destruct :: Prelude.Integer -> Euclidean -> (,) AERN2.CReal
                     Euclidean
dim_succ_destruct n x =
  caseS' n x (\h t -> (,) h t)

euclidean_plus :: Prelude.Integer -> Euclidean -> Euclidean -> Euclidean
euclidean_plus n x y =
  rect2 Nil (\n0 _ _ x0 a b -> Cons n0 ((+) a b) x0) n x y

euclidean_scalar_mult :: Prelude.Integer -> AERN2.CReal -> Euclidean ->
                         Euclidean
euclidean_scalar_mult n l x =
  nat_rect (\_ -> Nil) (\n0 iHn x0 ->
    let {x1 = dim_succ_destruct n0 x0} in
    case x1 of {
     (,) x2 s -> Cons n0 ((P.*) l x2) (iHn s)}) n x

make_euclidean2 :: AERN2.CReal -> AERN2.CReal -> Euclidean
make_euclidean2 x y =
  Cons (Prelude.succ 0) x (Cons 0 y Nil)

type Csubset x = ()

type Euclidean_subset = Csubset Euclidean

type Ball = (,) Euclidean AERN2.CReal

change_rad :: Prelude.Integer -> (([]) Ball) -> Prelude.Integer -> ([])
              ((,) Euclidean AERN2.CReal)
change_rad d l p =
  case l of {
   ([]) -> ([]);
   (:) a l' -> (:) ((,) (fst a) (prec p)) (change_rad d l' p)}

scale_list :: Prelude.Integer -> (([]) Ball) -> AERN2.CReal -> ([])
              ((,) Euclidean AERN2.CReal)
scale_list d l l0 =
  case l of {
   ([]) -> ([]);
   (:) b l' -> (:) ((,) (euclidean_scalar_mult d l0 (fst b))
    ((P.*) l0 (snd b))) (scale_list d l' l0)}

type Totally_bounded = Prelude.Integer -> (([]) Ball)

tbounded_union :: Prelude.Integer -> Totally_bounded -> Totally_bounded ->
                  Totally_bounded
tbounded_union _ h1 h2 n =
  let {s = h1 n} in let {s0 = h2 n} in app s s0

tbounded_translation :: Prelude.Integer -> Euclidean -> Totally_bounded ->
                        Totally_bounded
tbounded_translation d a h n =
  let {s = h n} in map (\b -> (,) (euclidean_plus d (fst b) a) (snd b)) s

tbounded_scale_down :: Prelude.Integer -> Prelude.Integer -> Totally_bounded
                       -> Totally_bounded
tbounded_scale_down d k mc n =
  let {s = mc (sub n k)} in scale_list d s (prec k)

located_lim :: Prelude.Integer -> (Prelude.Integer -> (,) Euclidean_subset
               ((,) Totally_bounded ())) -> Totally_bounded
located_lim d x p =
  let {s = x (Prelude.succ p)} in
  case s of {
   (,) _ p0 ->
    case p0 of {
     (,) t _ -> let {s0 = t (Prelude.succ p)} in change_rad d s0 p}}

make_ball2 :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal -> Ball
make_ball2 x y r =
  (,) (make_euclidean2 x y) r

tn_ball :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer -> Ball
tn_ball n k j =
  make_ball2
    ((P.*) (nreal ((Prelude.+) ((Prelude.*) n2 k) n1))
      (prec (Prelude.succ n)))
    ((P.*) (nreal ((Prelude.+) ((Prelude.*) n2 j) n1))
      (prec (Prelude.succ n))) (prec (Prelude.succ n))

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
    (\_ -> tn_col n 0 (sub (npow2 n) n1) l)
    (\k' -> tn_row n k' (tn_col n k (sub (sub (npow2 n) k) n1) l))
    k

tn :: Prelude.Integer -> ([]) Ball
tn n =
  tn_row n (sub (npow2 n) n1) ([])

t_tbounded :: Totally_bounded
t_tbounded n =
  tn (pred n)

sierpinski_approx_tbounded :: Prelude.Integer -> Totally_bounded
sierpinski_approx_tbounded n =
  nat_rect t_tbounded (\_ iHn ->
    tbounded_union n2
      (tbounded_union n2 (tbounded_scale_down n2 n1 iHn)
        (tbounded_translation n2 (make_euclidean2 (prec n1) real_0)
          (tbounded_scale_down n2 n1 iHn)))
      (tbounded_translation n2 (make_euclidean2 real_0 (prec n1))
        (tbounded_scale_down n2 n1 iHn))) n

tbounded_sierpinski :: Totally_bounded
tbounded_sierpinski =
  located_lim (Prelude.succ (Prelude.succ 0)) (\n -> (,) __ ((,)
    (sierpinski_approx_tbounded (pred n)) __))

