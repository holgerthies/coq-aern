{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module STEn where

import qualified Prelude

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

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rect_r :: a1 -> a2 -> a1 -> a2
eq_rect_r =
  eq_rect

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
pred :: Prelude.Integer -> Prelude.Integer
pred = (\n -> Prelude.max 0 (Prelude.pred n))

log2_iter :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
             Prelude.Integer -> Prelude.Integer
log2_iter k p q r =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> p)
    (\k' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> log2_iter k' (Prelude.succ p) (Prelude.succ q) q)
      (\r' -> log2_iter k' p (Prelude.succ q) r')
      r)
    k

log2 :: Prelude.Integer -> Prelude.Integer
log2 = (MNP.integer P.. Logs.integerLog2)

succ :: Prelude.Integer -> Prelude.Integer
succ x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x) (succ p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) p)
    (\_ -> (\x -> 2 Prelude.* x) 1)
    x

add :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add p q))
      (\q -> (\x -> 2 Prelude.* x) (add p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) p)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (succ q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) q)
      (\_ -> (\x -> 2 Prelude.* x) 1)
      y)
    x

add_carry :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (succ q))
      (\q -> (\x -> 2 Prelude.* x) (succ q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) 1)
      y)
    x

pred_double :: Prelude.Integer -> Prelude.Integer
pred_double x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) (pred_double p))
    (\_ -> 1)
    x

mul :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> add y ((\x -> 2 Prelude.* x) (mul p y)))
    (\p -> (\x -> 2 Prelude.* x) (mul p y))
    (\_ -> y)
    x

compare_cont :: Comparison -> Prelude.Integer -> Prelude.Integer ->
                Comparison
compare_cont r x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> compare_cont r p q)
      (\q -> compare_cont Gt p q)
      (\_ -> Gt)
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> compare_cont Lt p q)
      (\q -> compare_cont r p q)
      (\_ -> Gt)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> Lt)
      (\_ -> Lt)
      (\_ -> r)
      y)
    x

compare :: Prelude.Integer -> Prelude.Integer -> Comparison
compare =
  compare_cont Eq

iter_op :: (a1 -> a1 -> a1) -> Prelude.Integer -> a1 -> a1
iter_op op p a =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> op a (iter_op op p0 (op a a)))
    (\p0 -> iter_op op p0 (op a a))
    (\_ -> a)
    p

to_nat :: Prelude.Integer -> Prelude.Integer
to_nat x =
  iter_op (Prelude.+) x (Prelude.succ 0)

of_succ_nat :: Prelude.Integer -> Prelude.Integer
of_succ_nat n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 1)
    (\x -> succ (of_succ_nat x))
    n

double :: Prelude.Integer -> Prelude.Integer
double x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x) p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x) p))
    x

succ_double :: Prelude.Integer -> Prelude.Integer
succ_double x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (\x -> x) 1)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) p))
    (\p -> Prelude.negate (pred_double p))
    x

pred_double0 :: Prelude.Integer -> Prelude.Integer
pred_double0 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Prelude.negate 1)
    (\p -> (\x -> x) (pred_double p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x Prelude.+ 1) p))
    x

pos_sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pos_sub x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> double (pos_sub p q))
      (\q -> succ_double (pos_sub p q))
      (\_ -> (\x -> x) ((\x -> 2 Prelude.* x) p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> pred_double0 (pos_sub p q))
      (\q -> double (pos_sub p q))
      (\_ -> (\x -> x) (pred_double p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> Prelude.negate ((\x -> 2 Prelude.* x) q))
      (\q -> Prelude.negate (pred_double q))
      (\_ -> 0)
      y)
    x

compare0 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare0 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Eq)
      (\_ -> Lt)
      (\_ -> Gt)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Gt)
      (\y' -> compare x' y')
      (\_ -> Gt)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Lt)
      (\_ -> Lt)
      (\y' -> compOpp (compare x' y'))
      y)
    x

leb :: Prelude.Integer -> Prelude.Integer -> P.Bool
leb x y =
  case compare0 x y of {
   Gt -> P.False;
   _ -> P.True}

ltb :: Prelude.Integer -> Prelude.Integer -> P.Bool
ltb x y =
  case compare0 x y of {
   Lt -> P.True;
   _ -> P.False}

pos_div_eucl :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
                Prelude.Integer
pos_div_eucl a b =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {
       r' = (P.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r)
              ((\x -> x) 1)}
      in
      case ltb r' b of {
       P.True -> (,) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q) r';
       P.False -> (,)
        ((P.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((P.-) r' b)}})
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = (Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r} in
      case ltb r' b of {
       P.True -> (,) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q) r';
       P.False -> (,)
        ((P.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((P.-) r' b)}})
    (\_ ->
    case leb ((\x -> x) ((\x -> 2 Prelude.* x) 1)) b of {
     P.True -> (,) 0 ((\x -> x) 1);
     P.False -> (,) ((\x -> x) 1) 0})
    a

div_eucl :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
            Prelude.Integer
div_eucl a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (,) 0 0)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) 0 a)
      (\_ -> pos_div_eucl a' b)
      (\b' ->
      case pos_div_eucl a' ((\x -> x) b') of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
          (\_ -> (,) (P.negate q) 0)
          (\_ -> (,) (P.negate ((P.+) q ((\x -> x) 1))) ((P.+) b r))
          (\_ -> (,) (P.negate ((P.+) q ((\x -> x) 1))) ((P.+) b r))
          r})
      b)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) 0 a)
      (\_ ->
      case pos_div_eucl a' b of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
          (\_ -> (,) (P.negate q) 0)
          (\_ -> (,) (P.negate ((P.+) q ((\x -> x) 1))) ((P.-) b r))
          (\_ -> (,) (P.negate ((P.+) q ((\x -> x) 1))) ((P.-) b r))
          r})
      (\b' ->
      case pos_div_eucl a' ((\x -> x) b') of {
       (,) q r -> (,) q (P.negate r)})
      b)
    a

div :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div = (\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)

type M a = a

z2 :: Prelude.Integer
z2 = 2

z3 :: Prelude.Integer
z3 = 3

z4 :: Prelude.Integer
z4 = 4

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

m_lift :: (a1 -> a2) -> (M a1) -> M a2
m_lift = P.id

m_lift_dom :: (a1 -> M a2) -> (M a1) -> M a2
m_lift_dom = P.id

m_hprop_elim_f :: (M a1) -> a1
m_hprop_elim_f = P.id

m_countable_lift :: (Prelude.Integer -> M a1) -> M (Prelude.Integer -> a1)
m_countable_lift = P.id

mjoin :: (P.Bool -> a1) -> (M P.Bool) -> M a1
mjoin = P.id

type Semidec = AERN2.CKleenean

choose :: Semidec -> Semidec -> M P.Bool
choose = (unCNfn2 AERN2.select)

real_0 :: AERN2.CReal
real_0 = 0

real_1 :: AERN2.CReal
real_1 = 1

iZreal :: Prelude.Integer -> AERN2.CReal
iZreal = AERN2.creal

real_2 :: AERN2.CReal
real_2 = 2

prec :: Prelude.Integer -> AERN2.CReal
prec = ((0.5 :: AERN2.CReal) P.^)

pow :: AERN2.CReal -> Prelude.Integer -> AERN2.CReal
pow r n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> real_1)
    (\m -> (P.*) r (pow r m))
    n

linear_search_conform :: (Prelude.Integer -> P.Bool) -> Prelude.Integer ->
                         Prelude.Integer
linear_search_conform p_dec start =
  case p_dec start of {
   P.True -> start;
   P.False -> linear_search_conform p_dec (Prelude.succ start)}

linear_search_from_0_conform :: (Prelude.Integer -> P.Bool) ->
                                Prelude.Integer
linear_search_from_0_conform p_dec =
  linear_search_conform p_dec 0

epsilon_smallest :: (Prelude.Integer -> P.Bool) -> Prelude.Integer
epsilon_smallest =
  linear_search_from_0_conform

m_split :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal -> M P.Bool
m_split x y _UU03b5_ =
  choose ((OGB.<) ((-) y _UU03b5_) x) ((OGB.<) ((-) x _UU03b5_) y)

epsilon_smallest_PQ :: (Prelude.Integer -> P.Bool) -> Prelude.Integer
epsilon_smallest_PQ =
  epsilon_smallest

epsilon_smallest_PQ_M :: (Prelude.Integer -> M P.Bool) -> M Prelude.Integer
epsilon_smallest_PQ_M x =
  let {x0 = m_countable_lift x} in m_lift epsilon_smallest_PQ x0

epsilon_smallest_choose_M :: (Prelude.Integer -> M P.Bool) -> M
                             Prelude.Integer
epsilon_smallest_choose_M =
  epsilon_smallest_PQ_M

weaken_orM_r :: (M P.Bool) -> M P.Bool
weaken_orM_r =
  m_lift (\h -> h)

addn_rec :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
addn_rec =
  (Prelude.+)

addn :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
addn =
  addn_rec

muln_rec :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
muln_rec =
  (Prelude.*)

muln :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
muln =
  muln_rec

magnitude1 :: AERN2.CReal -> M Prelude.Integer
magnitude1 x =
  let {
   g1M = epsilon_smallest_choose_M (\n ->
           weaken_orM_r
             (choose ((OGB.<) (prec (Prelude.succ (Prelude.succ n))) x)
               ((OGB.<) x (prec (Prelude.succ n)))))}
  in
  m_lift (\g1 -> g1) g1M

zpow :: AERN2.CReal -> Prelude.Integer -> AERN2.CReal
zpow x z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> real_1)
    (\p -> pow x (to_nat p))
    (\p -> pow (P.recip x) (to_nat p))
    z

dec_x_lt_2 :: AERN2.CReal -> M P.Bool
dec_x_lt_2 x =
  let {h = m_split x ((/) (iZreal z3) real_2) (P.recip real_2)} in
  mjoin (\h0 -> case h0 of {
                 P.True -> P.False;
                 P.False -> P.True}) h

magnitude2 :: AERN2.CReal -> M Prelude.Integer
magnitude2 x =
  let {y = (/) x (iZreal z4)} in
  m_lift (\_top_assumption_ -> (P.+) _top_assumption_ z2)
    (m_lift (\_top_assumption_ -> P.negate (P.id _top_assumption_))
      (magnitude1 y))

magnitude :: AERN2.CReal -> M Prelude.Integer
magnitude x =
  m_lift_dom (\_top_assumption_ ->
    let {_evar_0_ = \_ -> magnitude2 x} in
    let {
     _evar_0_0 = \_ ->
      m_lift (\_top_assumption_0 -> (P.+) (P.negate _top_assumption_0) z2)
        (magnitude2 (P.recip x))}
    in
    case _top_assumption_ of {
     P.True -> _evar_0_ __;
     P.False -> _evar_0_0 __}) (dec_x_lt_2 x)

data Euclidean =
   Nil0
 | Cons0 Prelude.Integer AERN2.CReal Euclidean

caseS' :: Prelude.Integer -> Euclidean -> (AERN2.CReal -> Euclidean -> a1) ->
          a1
caseS' _ v h =
  case v of {
   Nil0 -> __;
   Cons0 _ h0 t -> h h0 t}

dim_succ_destruct :: Prelude.Integer -> Euclidean -> (,) AERN2.CReal
                     Euclidean
dim_succ_destruct n x =
  caseS' n x (\h t -> (,) h t)

split_euclidean2 :: Euclidean -> (,) AERN2.CReal AERN2.CReal
split_euclidean2 p =
  let {x = dim_succ_destruct (Prelude.succ 0) p} in
  case x of {
   (,) x0 s ->
    let {x1 = dim_succ_destruct 0 s} in case x1 of {
                                         (,) x2 _ -> (,) x0 x2}}

make_euclidean2 :: AERN2.CReal -> AERN2.CReal -> Euclidean
make_euclidean2 x y =
  Cons0 (Prelude.succ 0) x (Cons0 0 y Nil0)

sqrt_approx :: AERN2.CReal -> Prelude.Integer -> AERN2.CReal
sqrt_approx x n =
  nat_rect real_1 (\_ __top_assumption_ ->
    (P.*) (P.recip real_2) ((+) __top_assumption_ ((/) x __top_assumption_)))
    n

sqrt_approx_fast :: AERN2.CReal -> Prelude.Integer -> AERN2.CReal
sqrt_approx_fast x n =
  sqrt_approx x (Prelude.succ (log2 (Prelude.succ n)))

restr_sqrt :: AERN2.CReal -> AERN2.CReal
restr_sqrt x =
  AERN2.limit (\n -> sqrt_approx_fast x n)

scale :: AERN2.CReal -> M ((,) Prelude.Integer AERN2.CReal)
scale x =
  let {x0 = magnitude x} in
  m_lift (\_top_assumption_ ->
    let {
     _top_assumption_0 = div _top_assumption_ ((\x -> x)
                           ((\x -> 2 Prelude.* x) 1))}
    in
    (,) _top_assumption_0
    ((P.*)
      (zpow real_2
        ((Prelude.*) (Prelude.negate ((\x -> 2 Prelude.* x) 1))
          _top_assumption_0)) x)) x0

sqrt_pos :: AERN2.CReal -> AERN2.CReal
sqrt_pos x =
  m_hprop_elim_f
    (m_lift (\_top_assumption_ ->
      let {_evar_0_ = \z y -> (P.*) (zpow real_2 z) (restr_sqrt y)} in
      case _top_assumption_ of {
       (,) a b -> _evar_0_ a b}) (scale x))

sqrt :: AERN2.CReal -> AERN2.CReal
sqrt x =
  AERN2.limit (\n ->
    let {
     x0 = m_split x
            (prec
              (addn (muln (Prelude.succ (Prelude.succ 0)) n) (Prelude.succ
                0)))
            (prec
              (addn (muln (Prelude.succ (Prelude.succ 0)) n) (Prelude.succ
                0)))}
    in
    let {
     _evar_0_ = m_lift (\_top_assumption_ ->
                  let {_evar_0_ = \_ -> sqrt_pos x} in
                  let {_evar_0_0 = \_ -> real_0} in
                  case _top_assumption_ of {
                   P.True -> _evar_0_ __;
                   P.False -> _evar_0_0 __})}
    in
    eq_rect_r real_0 _evar_0_
      ((+)
        (prec
          (addn (muln (Prelude.succ (Prelude.succ 0)) n) (Prelude.succ 0)))
        (P.negate
          (prec
            (addn (muln (Prelude.succ (Prelude.succ 0)) n) (Prelude.succ 0)))))
      x0)

type Ball = (,) Euclidean AERN2.CReal

type Totally_bounded = Prelude.Integer -> (([]) Ball)

make_ball2 :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal -> Ball
make_ball2 x y r =
  (,) (make_euclidean2 x y) r

one_half :: AERN2.CReal
one_half =
  P.recip real_2

point_point_mid :: Euclidean -> Euclidean -> Euclidean
point_point_mid p1 p2 =
  let {s = split_euclidean2 p1} in
  case s of {
   (,) x s0 ->
    let {s1 = split_euclidean2 p2} in
    case s1 of {
     (,) x0 s2 ->
      make_euclidean2 ((P.*) ((+) x x0) one_half)
        ((P.*) ((+) s0 s2) one_half)}}

point_ball_mid :: Euclidean -> Ball -> Ball
point_ball_mid p b =
  case b of {
   (,) e r -> (,) (point_point_mid p e) ((P.*) r one_half)}

sT_split_ball :: Prelude.Integer -> (T Euclidean) -> Ball -> ([]) Ball
sT_split_ball sT_vs_size_pred sT_vs b =
  to_list (Prelude.succ sT_vs_size_pred)
    (map0 (\v -> point_ball_mid v b) (Prelude.succ sT_vs_size_pred) sT_vs)

sTn :: Prelude.Integer -> (T Euclidean) -> Ball -> Prelude.Integer -> ([])
       Ball
sTn sT_vs_size_pred sT_vs sT_initial_ball n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (:) sT_initial_ball ([]))
    (\n' ->
    concat
      (map (sT_split_ball sT_vs_size_pred sT_vs)
        (sTn sT_vs_size_pred sT_vs sT_initial_ball n')))
    n

sT_tbounded :: Prelude.Integer -> (T Euclidean) -> Ball -> Totally_bounded
sT_tbounded =
  sTn

t3_new :: a1 -> a1 -> a1 -> T a1
t3_new a b c =
  Cons a (Prelude.succ (Prelude.succ 0)) (Cons b (Prelude.succ 0) (Cons c 0
    Nil))

sTE_initial_ball :: Ball
sTE_initial_ball =
  make_ball2 real_0 real_0 real_1

sqrt_3_exists :: AERN2.CReal
sqrt_3_exists =
  sqrt (iZreal ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))

sqrt_3 :: AERN2.CReal
sqrt_3 =
  sqrt_3_exists

sTE_v1 :: Euclidean
sTE_v1 =
  make_euclidean2 (P.negate real_1) (P.negate real_1)

sTE_v2 :: Euclidean
sTE_v2 =
  make_euclidean2 real_1 (P.negate real_1)

sTE_v3 :: Euclidean
sTE_v3 =
  make_euclidean2 real_0 ((-) sqrt_3 real_1)

sTE_vs :: T Euclidean
sTE_vs =
  t3_new sTE_v1 sTE_v2 sTE_v3

sTE_tbounded :: Totally_bounded
sTE_tbounded n =
  sT_tbounded (Prelude.succ (Prelude.succ 0)) sTE_vs sTE_initial_ball n

