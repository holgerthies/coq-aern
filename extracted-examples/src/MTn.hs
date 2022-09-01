{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module MTn where

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
  
sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f a) (map f t)}

data RealTypes =
   MkRealTypes

type M a = a

type Is_equiv a b = (b -> a)

data LazyBool_K =
   Build_LazyBool_K AERN2.CKleenean AERN2.CKleenean (AERN2.CKleenean ->
                                                    AERN2.CKleenean) 
 (AERN2.CKleenean -> AERN2.CKleenean -> AERN2.CKleenean) (AERN2.CKleenean ->
                                                         AERN2.CKleenean ->
                                                         AERN2.CKleenean) 
 (AERN2.CKleenean -> () -> P.Bool)

data Monad m =
   Build_Monad (() -> () -> (Any -> Any) -> m -> m) (() -> Any -> m) 
 (() -> m -> m)

type Monoid_hom f g =
  () -> f -> g
  -- singleton inductive, whose constructor was Build_Monoid_hom
  
type NPset x = ()

type Lifts_lifted_trace =
  () -> () -> (M Any) -> (Prelude.Integer -> Any -> M Any) ->
  (M (Prelude.Integer -> Any))

data MultivalueMonad_M =
   Build_MultivalueMonad_M LazyBool_K (Monad (M Any)) (Monoid_hom (M Any)
                                                      (NPset Any)) (() -> ()
                                                                   ->
                                                                   Is_equiv
                                                                   Any
                                                                   (M Any)) 
 Lifts_lifted_trace (AERN2.CKleenean -> AERN2.CKleenean -> () -> M P.Bool) 
 (() -> Is_equiv (M (M Any)) (M (NPset Any))) (() -> (M Any) -> M Any)

type Semidec = AERN2.CKleenean

data SemiDecOrderedField_Real =
   Build_SemiDecOrderedField_Real MultivalueMonad_M AERN2.CReal AERN2.CReal 
 (AERN2.CReal -> AERN2.CReal -> AERN2.CReal) (AERN2.CReal -> AERN2.CReal ->
                                             AERN2.CReal) (AERN2.CReal ->
                                                          AERN2.CReal) 
 (AERN2.CReal -> () -> AERN2.CReal) (AERN2.CReal -> AERN2.CReal -> Semidec)

nreal :: Prelude.Integer -> AERN2.CReal
nreal = AERN2.creal

prec :: Prelude.Integer -> AERN2.CReal
prec = ((0.5 :: AERN2.CReal) P.^)

data ComplArchiSemiDecOrderedField_Real =
   Build_ComplArchiSemiDecOrderedField_Real SemiDecOrderedField_Real 
 ((Prelude.Integer -> AERN2.CReal) -> () -> AERN2.CReal)

npow2 :: Prelude.Integer -> Prelude.Integer
npow2 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.succ 0)
    (\n0 -> (Prelude.*) (npow2 n0) (Prelude.succ (Prelude.succ 0)))
    n

data Euclidean =
   Nil
 | Cons Prelude.Integer AERN2.CReal Euclidean

case0 :: RealTypes -> a1 -> Euclidean -> a1
case0 _ h v =
  case v of {
   Nil -> h;
   Cons _ _ _ -> __}

caseS' :: RealTypes -> Prelude.Integer -> Euclidean -> (AERN2.CReal ->
          Euclidean -> a1) -> a1
caseS' _ _ v h =
  case v of {
   Nil -> __;
   Cons _ h0 t -> h h0 t}

rect2 :: RealTypes -> a1 -> (Prelude.Integer -> Euclidean -> Euclidean -> a1
         -> AERN2.CReal -> AERN2.CReal -> a1) -> Prelude.Integer -> Euclidean
         -> Euclidean -> a1
rect2 types bas rect _ v1 v2 =
  case v1 of {
   Nil -> case0 types bas v2;
   Cons n' h1 t1 ->
    caseS' types n' v2 (\h2 t2 ->
      rect n' t1 t2 (rect2 types bas rect n' t1 t2) h1 h2)}

euclidean_plus :: Prelude.Integer -> Euclidean -> Euclidean -> Euclidean
euclidean_plus n x y =
  rect2 __ {- 1st argument (types) of euclidean_plus -} Nil
    (\n0 _ _ x0 a b -> Cons n0 ((+) a b) x0) n x y

make_euclidean2 :: RealTypes -> AERN2.CReal -> AERN2.CReal -> Euclidean
make_euclidean2 _ x y =
  Cons (Prelude.succ 0) x (Cons 0 y Nil)

type Ball = (,) Euclidean AERN2.CReal

type Is_compact = Prelude.Integer -> (([]) Ball)

is_compact_union :: RealTypes -> ComplArchiSemiDecOrderedField_Real ->
                    Prelude.Integer -> Is_compact -> Is_compact -> Is_compact
is_compact_union _ _ _ h1 h2 n =
  let {s = h1 n} in let {s0 = h2 n} in app s s0

is_compact_translation :: RealTypes -> ComplArchiSemiDecOrderedField_Real ->
                          Prelude.Integer -> Euclidean -> Is_compact ->
                          Is_compact
is_compact_translation _ _ d a h n =
  let {s = h n} in map (\b -> (,) (euclidean_plus d (fst b) a) (snd b)) s

make_ball :: RealTypes -> AERN2.CReal -> AERN2.CReal -> AERN2.CReal -> Ball
make_ball types x y r =
  (,) (make_euclidean2 types x y) r

tn_ball :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer -> Ball
tn_ball n k j =
  make_ball __ {- 1st argument (types) of Tn_ball -}
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

t_is_compact :: RealTypes -> ComplArchiSemiDecOrderedField_Real -> Is_compact
t_is_compact _ _ =
  tn

empty_set_is_compact :: RealTypes -> ComplArchiSemiDecOrderedField_Real ->
                        Is_compact
empty_set_is_compact _ _ _ =
  ([])

multi_triangles_compact :: Prelude.Integer -> Is_compact
multi_triangles_compact n =
  nat_rect
    (empty_set_is_compact __
      {- 1st argument (types) of multi_triangles_compact -} __
      {- 2nd argument (casofReal) of multi_triangles_compact -}) (\_ iHn ->
    is_compact_union __ {- 1st argument (types) of multi_triangles_compact -}
      __ {- 2nd argument (casofReal) of multi_triangles_compact -}
      (Prelude.succ (Prelude.succ 0))
      (t_is_compact __ {- 1st argument (types) of multi_triangles_compact -}
        __ {- 2nd argument (casofReal) of multi_triangles_compact -})
      (is_compact_translation __
        {- 1st argument (types) of multi_triangles_compact -} __
        {- 2nd argument (casofReal) of multi_triangles_compact -}
        (Prelude.succ (Prelude.succ 0))
        (make_euclidean2 __
          {- 1st argument (types) of multi_triangles_compact -}
          (P.negate (P.recip (2 :: AERN2.CReal)))
          (P.negate (P.recip (2 :: AERN2.CReal)))) iHn)) n

