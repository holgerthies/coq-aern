{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module CSqrt where

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
unsafeCoerce :: a -> b
#if __GLASGOW_HASKELL__ >= 900
unsafeCoerce = GHC.Exts.unsafeCoerce#
#else
unsafeCoerce = GHC.Base.unsafeCoerce#
#endif
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
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
  
projT1 :: ((,) a1 a2) -> a1
projT1 x =
  case x of {
   (,) a _ -> a}

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

data RealTypes =
   MkRealTypes

type M a = a

lazy_bool_or :: AERN2.CKleenean -> AERN2.CKleenean -> AERN2.CKleenean
lazy_bool_or = (OGB.||)

m_base_monad_traces_lift :: (M a1) -> (Prelude.Integer -> a1 -> M a1) ->
                            (M (Prelude.Integer -> a1))
m_base_monad_traces_lift = (\ x0 f -> (\n -> P.foldl (P.flip f) (x0) [0 .. ((n :: P.Integer) P.- 1)]))

multivalued_choice :: AERN2.CKleenean -> AERN2.CKleenean -> M P.Bool
multivalued_choice = AERN2.select

m_lift :: (a1 -> a2) -> (M a1) -> M a2
m_lift = P.id

m_unit :: a1 -> M a1
m_unit = P.id

m_lift_dom :: (a1 -> M a2) -> (M a1) -> M a2
m_lift_dom = P.id

m_hprop_elim_f :: (M a1) -> a1
m_hprop_elim_f = P.id

m_paths :: (M a1) -> (Prelude.Integer -> a1 -> M a1) -> M
           (Prelude.Integer -> a1)
m_paths x x0 =
   (m_base_monad_traces_lift x x0)

m_countable_lift :: (Prelude.Integer -> M a1) -> M (Prelude.Integer -> a1)
m_countable_lift = P.id

select :: AERN2.CKleenean -> AERN2.CKleenean -> M P.Bool
select =
  multivalued_choice

mjoin :: (P.Bool -> a1) -> (M P.Bool) -> M a1
mjoin = P.id

type Semidec = AERN2.CKleenean

choose :: Semidec -> Semidec -> M P.Bool
choose x x0 =
  m_lift (\h4 -> h4) (select x x0)

semidec_or :: Semidec -> Semidec -> Semidec
semidec_or =
  lazy_bool_or

iZreal :: Prelude.Integer -> AERN2.CReal
iZreal = AERN2.creal

prec :: Prelude.Integer -> AERN2.CReal
prec = ((0.5 :: AERN2.CReal) P.^)

real_limit_p :: (Prelude.Integer -> AERN2.CReal) -> AERN2.CReal
real_limit_p = AERN2.limit

pow :: AERN2.CReal -> Prelude.Integer -> AERN2.CReal
pow r n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (1 :: AERN2.CReal))
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

real_limit_P_lt_p :: (Prelude.Integer -> AERN2.CReal) -> AERN2.CReal
real_limit_P_lt_p p =
   (real_limit_p (\n ->  (p n)))

real_limit_P_p :: (Prelude.Integer -> AERN2.CReal) -> AERN2.CReal
real_limit_P_p p =
   (real_limit_p (\n ->  (p n)))

real_mslimit_P_p :: (Prelude.Integer -> M AERN2.CReal) -> AERN2.CReal
real_mslimit_P_p x =
  let {x0 = m_countable_lift x} in m_hprop_elim_f (m_lift real_limit_P_p x0)

real_mslimit_P_lt_p :: (Prelude.Integer -> M AERN2.CReal) -> AERN2.CReal
real_mslimit_P_lt_p x =
  let {x0 = m_countable_lift x} in
  m_hprop_elim_f (m_lift real_limit_P_lt_p x0)

abs_prop :: AERN2.CReal -> AERN2.CReal
abs_prop x =
  real_mslimit_P_lt_p (\n ->
    let {x0 = \order -> case order of {
                         P.True -> x;
                         P.False -> P.negate x}}
    in
    m_lift x0
      (m_split x (0 :: AERN2.CReal)
        (prec ((Prelude.+) n (Prelude.succ (Prelude.succ 0))))))

abs :: AERN2.CReal -> AERN2.CReal
abs =
  abs_prop

real_limit :: (Prelude.Integer -> AERN2.CReal) -> AERN2.CReal
real_limit =
  real_limit_p

real_limit_P_lt :: (Prelude.Integer -> AERN2.CReal) -> AERN2.CReal
real_limit_P_lt =
  real_limit_P_lt_p

real_mslimit_P_lt :: (Prelude.Integer -> M AERN2.CReal) -> AERN2.CReal
real_mslimit_P_lt x =
  let {x0 = m_countable_lift x} in m_hprop_elim_f (m_lift real_limit_P_lt x0)

real_max_prop :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal
real_max_prop x y =
  real_mslimit_P_lt (\n ->
    mjoin (\h -> case h of {
                  P.True -> x;
                  P.False -> y}) (m_split x y (prec n)))

real_max :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal
real_max x y =
   (real_max_prop x y)

ssr_have :: a1 -> (a1 -> a2) -> a2
ssr_have step rest =
  rest step

ssr_suff :: (a1 -> a2) -> a1 -> a2
ssr_suff step =
  step

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
  m_lift (\__top_assumption_ ->
    let {_evar_0_ = \_ -> P.True} in
    let {_evar_0_0 = \_ -> P.False} in
    case __top_assumption_ of {
     P.True -> _evar_0_ __;
     P.False -> _evar_0_0 __})

magnitude1 :: AERN2.CReal -> M Prelude.Integer
magnitude1 x =
  ssr_have __ (\_ ->
    ssr_suff (\g1M -> m_lift (\g1 -> g1) g1M)
      (epsilon_smallest_choose_M (\n ->
        weaken_orM_r
          (choose ((OGB.<) (prec (Prelude.succ (Prelude.succ n))) x)
            ((OGB.<) x (prec (Prelude.succ n)))))))

zpow :: AERN2.CReal -> Prelude.Integer -> AERN2.CReal
zpow x z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (1 :: AERN2.CReal))
    (\p -> pow x (to_nat p))
    (\p -> pow (P.recip x) (to_nat p))
    z

dec_x_lt_2 :: AERN2.CReal -> M P.Bool
dec_x_lt_2 x =
  let {
   h = m_split x
         ((/) (iZreal ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))
           (2 :: AERN2.CReal)) (P.recip (2 :: AERN2.CReal))}
  in
  mjoin (\h0 -> case h0 of {
                 P.True -> P.False;
                 P.False -> P.True}) h

magnitude2 :: AERN2.CReal -> M Prelude.Integer
magnitude2 x =
  let {
   y = (/) x
         (iZreal ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
           1))))}
  in
  ssr_have __ (\_ ->
    ssr_have __ (\_ ->
      ssr_suff
        (m_lift (\_top_assumption_ ->
          (P.+) _top_assumption_ ((\x -> x) ((\x -> 2 Prelude.* x) 1))))
        (ssr_have (magnitude1 y)
          (m_lift (\_top_assumption_ -> P.negate (P.id _top_assumption_))))))

magnitude :: AERN2.CReal -> M Prelude.Integer
magnitude x =
  ssr_have (dec_x_lt_2 x)
    (m_lift_dom (\_top_assumption_ ->
      let {_evar_0_ = \_ -> magnitude2 x} in
      let {
       _evar_0_0 = \_ ->
        ssr_have __ (\_ ->
          ssr_have (magnitude2 (P.recip x))
            (m_lift (\_top_assumption_0 ->
              (P.+) (P.negate _top_assumption_0) ((\x -> x)
                ((\x -> 2 Prelude.* x) 1)))))}
      in
      case _top_assumption_ of {
       P.True -> _evar_0_ __;
       P.False -> _evar_0_0 __}))

data Euclidean =
   Nil
 | Cons Prelude.Integer AERN2.CReal Euclidean

euclidean_rect :: RealTypes -> a1 -> (Prelude.Integer -> AERN2.CReal ->
                  Euclidean -> a1 -> a1) -> Prelude.Integer -> Euclidean ->
                  a1
euclidean_rect types f f0 _ e =
  case e of {
   Nil -> f;
   Cons n r e0 -> f0 n r e0 (euclidean_rect types f f0 n e0)}

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

dim_succ_destruct :: RealTypes -> Prelude.Integer -> Euclidean -> (,)
                     AERN2.CReal Euclidean
dim_succ_destruct types n x =
  caseS' types n x (\h t -> (,) h t)

euclidean_zero :: Prelude.Integer -> Euclidean
euclidean_zero n =
  nat_rect Nil (\n0 iHn -> Cons n0 (0 :: AERN2.CReal) iHn) n

euclidean_plus :: Prelude.Integer -> Euclidean -> Euclidean -> Euclidean
euclidean_plus n x y =
  rect2 __ {- 1st argument (types) of euclidean_plus -} Nil
    (\n0 _ _ x0 a b -> Cons n0 ((+) a b) x0) n x y

euclidean_opp :: Prelude.Integer -> Euclidean -> Euclidean
euclidean_opp n x =
  nat_rect (\_ -> Nil) (\n0 iHn x0 ->
    let {
     x1 = dim_succ_destruct __ {- 1st argument (types) of euclidean_opp -} n0
            x0}
    in
    case x1 of {
     (,) x2 p -> Cons n0 (P.negate x2) (iHn p)}) n x

euclidean_minus :: Prelude.Integer -> Euclidean -> Euclidean -> Euclidean
euclidean_minus n x y =
  euclidean_plus n x (euclidean_opp n y)

euclidean_max_norm :: Prelude.Integer -> Euclidean -> AERN2.CReal
euclidean_max_norm n x =
  euclidean_rect __ {- 1st argument (types) of euclidean_max_norm -}
    (0 :: AERN2.CReal) (\_ r _ iHx -> real_max (abs r) iHx) n x

euclidean_max_dist :: Prelude.Integer -> Euclidean -> Euclidean ->
                      AERN2.CReal
euclidean_max_dist n x y =
  euclidean_max_norm n (euclidean_minus n x y)

euclidean_head_sequence :: RealTypes -> Prelude.Integer -> (Prelude.Integer
                           -> Euclidean) -> Prelude.Integer -> AERN2.CReal
euclidean_head_sequence types n f h =
  let {x = f h} in
  let {s = dim_succ_destruct types n x} in case s of {
                                            (,) x0 _ -> x0}

euclidean_tail_sequence :: RealTypes -> Prelude.Integer -> (Prelude.Integer
                           -> Euclidean) -> Prelude.Integer -> Euclidean
euclidean_tail_sequence types n f h =
  let {x = f h} in
  let {s = dim_succ_destruct types n x} in case s of {
                                            (,) _ p -> p}

euclidean_limit :: Prelude.Integer -> (Prelude.Integer -> Euclidean) ->
                   Euclidean
euclidean_limit n f =
  nat_rect (\_ _ -> Nil) (\n0 iHn f0 _ -> Cons n0
    (
      (real_limit
        (euclidean_head_sequence __
          {- 1st argument (types) of euclidean_limit -} n0 f0)))
    (
      (iHn
        (euclidean_tail_sequence __
          {- 1st argument (types) of euclidean_limit -} n0 f0) __))) n f __

euclidean_mlimit_PQ :: Prelude.Integer -> (M ((,) Euclidean a1)) ->
                       (Prelude.Integer -> Euclidean -> () -> a1 -> M
                       ((,) Euclidean a1)) -> M Euclidean
euclidean_mlimit_PQ d x f =
  let {
   x0 = \n x0 ->
    case x0 of {
     (,) x1 p ->
      let {x2 = f n x1 __ p} in
      m_lift (\x3 -> case x3 of {
                      (,) x4 p0 -> (,) x4 p0}) x2}}
  in
  let {x1 = m_paths x x0} in
  m_lift_dom (\_ ->
    m_lift (\x3 -> euclidean_limit d (\n -> projT1 (x3 n))) x1) x

type Complex = Euclidean

complex :: RealTypes -> AERN2.CReal -> AERN2.CReal -> Complex
complex _ r i =
  Cons (Prelude.succ 0) r (Cons 0 i Nil)

complex_destruct :: RealTypes -> Complex -> (,) AERN2.CReal AERN2.CReal
complex_destruct types x =
  let {s = dim_succ_destruct types (Prelude.succ 0) x} in
  case s of {
   (,) x0 p -> (,) x0
    (let {s0 = dim_succ_destruct types 0 p} in case s0 of {
                                                (,) x1 _ -> x1})}

complex0 :: Euclidean
complex0 =
  euclidean_zero (Prelude.succ (Prelude.succ 0))

sqrt_approx :: AERN2.CReal -> Prelude.Integer -> AERN2.CReal
sqrt_approx x n =
  nat_rect (1 :: AERN2.CReal) (\_ __top_assumption_ ->
    ssr_have __ (\_ ->
      (P.*) (P.recip (2 :: AERN2.CReal))
        ((+) __top_assumption_ ((/) x __top_assumption_)))) n

sqrt_approx_fast :: AERN2.CReal -> Prelude.Integer -> AERN2.CReal
sqrt_approx_fast x n =
  ssr_have (sqrt_approx x (Prelude.succ (log2 (Prelude.succ n))))
    (\__top_assumption_ -> __top_assumption_)

restr_sqrt :: AERN2.CReal -> AERN2.CReal
restr_sqrt x =
  ssr_have __ (\_ ->
    real_limit_P_lt_p (\n ->
      ssr_have (sqrt_approx_fast x n) (\__top_assumption_ ->
        __top_assumption_)))

scale :: AERN2.CReal -> M ((,) Prelude.Integer AERN2.CReal)
scale x =
  let {x0 = magnitude x} in
  m_lift (\_top_assumption_ ->
    ssr_have (div _top_assumption_ ((\x -> x) ((\x -> 2 Prelude.* x) 1)))
      (\_top_assumption_0 -> (,) _top_assumption_0
      ((P.*)
        (zpow (2 :: AERN2.CReal)
          ((Prelude.*) (Prelude.negate ((\x -> 2 Prelude.* x) 1))
            _top_assumption_0)) x))) x0

sqrt_pos :: AERN2.CReal -> AERN2.CReal
sqrt_pos x =
  m_hprop_elim_f
    (ssr_have (scale x)
      (m_lift (\_top_assumption_ ->
        let {
         _evar_0_ = \z y -> (P.*) (zpow (2 :: AERN2.CReal) z) (restr_sqrt y)}
        in
        case _top_assumption_ of {
         (,) a b -> _evar_0_ a b})))

sqrt :: AERN2.CReal -> AERN2.CReal
sqrt x =
  real_mslimit_P_p (\n ->
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
                  let {_evar_0_0 = \_ -> (0 :: AERN2.CReal)} in
                  case _top_assumption_ of {
                   P.True -> _evar_0_ __;
                   P.False -> _evar_0_0 __})}
    in
    eq_rect_r (0 :: AERN2.CReal) _evar_0_
      ((+)
        (prec
          (addn (muln (Prelude.succ (Prelude.succ 0)) n) (Prelude.succ 0)))
        (P.negate
          (prec
            (addn (muln (Prelude.succ (Prelude.succ 0)) n) (Prelude.succ 0)))))
      x0)

complex_nonzero_cases :: AERN2.CReal -> AERN2.CReal -> M
                         (Prelude.Maybe (Prelude.Maybe P.Bool))
complex_nonzero_cases a b =
  ssr_have __ (\_ ->
    ssr_have __ (\_ ->
      m_lift_dom (\_top_assumption_ ->
        let {_evar_0_ = \_ -> m_unit (Prelude.Just (Prelude.Just P.True))} in
        let {
         _evar_0_0 = \_ ->
          m_lift_dom (\_top_assumption_0 ->
            let {
             _evar_0_0 = \_ -> m_unit (Prelude.Just (Prelude.Just P.False))}
            in
            let {
             _evar_0_1 = \_ ->
              m_lift_dom (\_top_assumption_1 ->
                let {_evar_0_1 = \_ -> m_unit (Prelude.Just Prelude.Nothing)}
                in
                let {_evar_0_2 = \_ -> m_unit Prelude.Nothing} in
                case _top_assumption_1 of {
                 P.True -> _evar_0_1 __;
                 P.False -> _evar_0_2 __})
                (choose ((OGB.<) (0 :: AERN2.CReal) b)
                  ((OGB.<) b (0 :: AERN2.CReal)))}
            in
            case _top_assumption_0 of {
             P.True -> _evar_0_0 __;
             P.False -> _evar_0_1 __})
            (choose ((OGB.<) a (0 :: AERN2.CReal))
              (semidec_or ((OGB.<) (0 :: AERN2.CReal) b)
                ((OGB.<) b (0 :: AERN2.CReal))))}
        in
        case _top_assumption_ of {
         P.True -> _evar_0_ __;
         P.False -> _evar_0_0 __})
        (choose ((OGB.<) (0 :: AERN2.CReal) a)
          (semidec_or ((OGB.<) a (0 :: AERN2.CReal))
            (semidec_or ((OGB.<) (0 :: AERN2.CReal) b)
              ((OGB.<) b (0 :: AERN2.CReal)))))))

csqrt_neq0 :: Complex -> M Complex
csqrt_neq0 z =
  let {s = complex_destruct __ {- 1st argument (types) of csqrt_neq0 -} z} in
  case s of {
   (,) x p ->
    eq_rect_r (complex __ {- 1st argument (types) of csqrt_neq0 -} x p)
      (\_ ->
      ssr_have (complex_nonzero_cases x p)
        (ssr_have __ (\_ ->
          let {x0 = sqrt ((+) ((P.*) x x) ((P.*) p p))} in
          ssr_have __ (\_ ->
            ssr_have __ (\_ ->
              ssr_have __ (\_ ->
                let {x1 = sqrt ((/) ((+) x0 x) (2 :: AERN2.CReal))} in
                let {x2 = sqrt ((/) ((-) x0 x) (2 :: AERN2.CReal))} in
                ssr_have __ (\_ ->
                  ssr_have __ (\_ ->
                    ssr_have __ (\_ ->
                      ssr_have __ (\_ ->
                        m_lift (\__top_assumption_ ->
                          let {
                           _evar_0_ = \__top_assumption_0 ->
                            let {
                             _evar_0_ = \__top_assumption_1 ->
                              let {
                               _evar_0_ = \_ ->
                                ssr_have __ (\_ ->
                                  complex __
                                    {- 1st argument (types) of csqrt_neq0 -}
                                    x1 ((/) p ((P.*) (2 :: AERN2.CReal) x1)))}
                              in
                              let {
                               _evar_0_0 = \_ ->
                                ssr_have __ (\_ ->
                                  complex __
                                    {- 1st argument (types) of csqrt_neq0 -}
                                    ((/) p ((P.*) (2 :: AERN2.CReal) x2)) x2)}
                              in
                              case __top_assumption_1 of {
                               P.True -> _evar_0_ __;
                               P.False -> _evar_0_0 __}}
                            in
                            let {
                             _evar_0_0 = \_ ->
                              ssr_have __ (\_ ->
                                complex __
                                  {- 1st argument (types) of csqrt_neq0 -} x1
                                  ((/) p ((P.*) (2 :: AERN2.CReal) x1)))}
                            in
                            case __top_assumption_0 of {
                             Prelude.Just a -> _evar_0_ a;
                             Prelude.Nothing -> _evar_0_0 __}}
                          in
                          let {
                           _evar_0_0 = \_ ->
                            complex __
                              {- 1st argument (types) of csqrt_neq0 -} x1
                              (P.negate x2)}
                          in
                          case __top_assumption_ of {
                           Prelude.Just a -> _evar_0_ a;
                           Prelude.Nothing -> _evar_0_0 __}))))))))))) z __}

csqrt :: Complex -> M Complex
csqrt z =
  euclidean_mlimit_PQ (Prelude.succ (Prelude.succ 0))
    (let {
      x = m_split
            (euclidean_max_dist (Prelude.succ (Prelude.succ 0)) complex0 z)
            (prec
              ((Prelude.+)
                (addn
                  (muln (Prelude.succ (Prelude.succ 0))
                    (addn 0 (Prelude.succ 0))) (Prelude.succ 0))
                (Prelude.succ 0)))
            (prec
              ((Prelude.+)
                (addn
                  (muln (Prelude.succ (Prelude.succ 0))
                    (addn 0 (Prelude.succ 0))) (Prelude.succ 0))
                (Prelude.succ 0)))}
     in
     let {
      _evar_0_ = m_lift_dom (\_top_assumption_ ->
                   let {
                    _evar_0_ = \_ ->
                     ssr_have (csqrt_neq0 z)
                       (m_lift (\_top_assumption_0 -> (,) _top_assumption_0
                         P.False))}
                   in
                   let {
                    _evar_0_0 = \_ ->
                     let {
                      _evar_0_0 = \_ ->
                       let {
                        _evar_0_0 = \_ ->
                         let {
                          _evar_0_0 = \_ ->
                           let {
                            _evar_0_0 = \_ ->
                             let {
                              _evar_0_0 = \_ ->
                               let {
                                _evar_0_0 = \_ ->
                                 m_unit ((,) complex0
                                   (ssr_have __ (\_ -> P.True)))}
                               in
                               eq_rect_r
                                 (prec
                                   (addn
                                     (muln (Prelude.succ (Prelude.succ 0))
                                       (addn 0 (Prelude.succ 0)))
                                     (Prelude.succ 0))) _evar_0_0
                                 ((+)
                                   (prec
                                     ((Prelude.+)
                                       (addn
                                         (muln (Prelude.succ (Prelude.succ
                                           0)) (addn 0 (Prelude.succ 0)))
                                         (Prelude.succ 0)) (Prelude.succ 0)))
                                   (prec
                                     ((Prelude.+)
                                       (addn
                                         (muln (Prelude.succ (Prelude.succ
                                           0)) (addn 0 (Prelude.succ 0)))
                                         (Prelude.succ 0)) (Prelude.succ 0))))
                                 __}
                             in
                             eq_rect_r
                               (euclidean_max_dist (Prelude.succ
                                 (Prelude.succ 0)) complex0 z) _evar_0_0
                               ((+) (0 :: AERN2.CReal)
                                 (euclidean_max_dist (Prelude.succ
                                   (Prelude.succ 0)) complex0 z)) __}
                           in
                           eq_rect_r
                             ((+) (0 :: AERN2.CReal)
                               (euclidean_max_dist (Prelude.succ
                                 (Prelude.succ 0)) complex0 z)) _evar_0_0
                             ((+)
                               (euclidean_max_dist (Prelude.succ
                                 (Prelude.succ 0)) complex0 z)
                               (0 :: AERN2.CReal)) __}
                         in
                         eq_rect_r (0 :: AERN2.CReal) _evar_0_0
                           ((+)
                             (prec
                               ((Prelude.+)
                                 (addn
                                   (muln (Prelude.succ (Prelude.succ 0))
                                     (addn 0 (Prelude.succ 0))) (Prelude.succ
                                   0)) (Prelude.succ 0)))
                             (P.negate
                               (prec
                                 ((Prelude.+)
                                   (addn
                                     (muln (Prelude.succ (Prelude.succ 0))
                                       (addn 0 (Prelude.succ 0)))
                                     (Prelude.succ 0)) (Prelude.succ 0)))))
                           __}
                       in
                       eq_rect_r
                         ((+)
                           (prec
                             ((Prelude.+)
                               (addn
                                 (muln (Prelude.succ (Prelude.succ 0))
                                   (addn 0 (Prelude.succ 0))) (Prelude.succ
                                 0)) (Prelude.succ 0)))
                           (P.negate
                             (prec
                               ((Prelude.+)
                                 (addn
                                   (muln (Prelude.succ (Prelude.succ 0))
                                     (addn 0 (Prelude.succ 0))) (Prelude.succ
                                   0)) (Prelude.succ 0))))) _evar_0_0
                         ((+)
                           (P.negate
                             (prec
                               ((Prelude.+)
                                 (addn
                                   (muln (Prelude.succ (Prelude.succ 0))
                                     (addn 0 (Prelude.succ 0))) (Prelude.succ
                                   0)) (Prelude.succ 0))))
                           (prec
                             ((Prelude.+)
                               (addn
                                 (muln (Prelude.succ (Prelude.succ 0))
                                   (addn 0 (Prelude.succ 0))) (Prelude.succ
                                 0)) (Prelude.succ 0)))) __}
                     in
                     eq_rect_r
                       ((+)
                         (euclidean_max_dist (Prelude.succ (Prelude.succ 0))
                           complex0 z)
                         ((+)
                           (P.negate
                             (prec
                               ((Prelude.+)
                                 (addn
                                   (muln (Prelude.succ (Prelude.succ 0))
                                     (addn 0 (Prelude.succ 0))) (Prelude.succ
                                   0)) (Prelude.succ 0))))
                           (prec
                             ((Prelude.+)
                               (addn
                                 (muln (Prelude.succ (Prelude.succ 0))
                                   (addn 0 (Prelude.succ 0))) (Prelude.succ
                                 0)) (Prelude.succ 0))))) _evar_0_0
                       ((+)
                         ((+)
                           (euclidean_max_dist (Prelude.succ (Prelude.succ
                             0)) complex0 z)
                           (P.negate
                             (prec
                               ((Prelude.+)
                                 (addn
                                   (muln (Prelude.succ (Prelude.succ 0))
                                     (addn 0 (Prelude.succ 0))) (Prelude.succ
                                   0)) (Prelude.succ 0)))))
                         (prec
                           ((Prelude.+)
                             (addn
                               (muln (Prelude.succ (Prelude.succ 0))
                                 (addn 0 (Prelude.succ 0))) (Prelude.succ 0))
                             (Prelude.succ 0)))) __}
                   in
                   case _top_assumption_ of {
                    P.True -> _evar_0_ __;
                    P.False -> _evar_0_0 __})}
     in
     eq_rect_r (0 :: AERN2.CReal) _evar_0_
       ((+)
         (prec
           ((Prelude.+)
             (addn
               (muln (Prelude.succ (Prelude.succ 0))
                 (addn 0 (Prelude.succ 0))) (Prelude.succ 0)) (Prelude.succ
             0)))
         (P.negate
           (prec
             ((Prelude.+)
               (addn
                 (muln (Prelude.succ (Prelude.succ 0))
                   (addn 0 (Prelude.succ 0))) (Prelude.succ 0)) (Prelude.succ
               0))))) x) (\n x _ p2 ->
    case p2 of {
     P.True ->
      let {
       x0 = m_split
              (euclidean_max_dist (Prelude.succ (Prelude.succ 0)) complex0 z)
              (prec
                ((Prelude.+)
                  (addn
                    (muln (Prelude.succ (Prelude.succ 0)) (Prelude.succ
                      (Prelude.succ n))) (Prelude.succ 0)) (Prelude.succ 0)))
              (prec
                ((Prelude.+)
                  (addn
                    (muln (Prelude.succ (Prelude.succ 0)) (Prelude.succ
                      (Prelude.succ n))) (Prelude.succ 0)) (Prelude.succ 0)))}
      in
      let {
       _evar_0_ = m_lift_dom (\_top_assumption_ ->
                    let {
                     _evar_0_ = \_ ->
                      ssr_have (csqrt_neq0 z)
                        (m_lift (\_top_assumption_0 -> (,) _top_assumption_0
                          P.False))}
                    in
                    let {
                     _evar_0_0 = \_ ->
                      let {
                       _evar_0_0 = let {
                                    _evar_0_0 = let {
                                                 _evar_0_0 = let {
                                                              _evar_0_0 = 
                                                               let {
                                                                _evar_0_0 = 
                                                                 let {
                                                                  _evar_0_0 = \_ ->
                                                                   m_unit
                                                                    ((,)
                                                                    complex0
                                                                    (ssr_have
                                                                    __ (\_ ->
                                                                    P.True)))}
                                                                 in
                                                                 eq_rect_r
                                                                   (prec
                                                                    (addn
                                                                    (muln
                                                                    (Prelude.succ
                                                                    (Prelude.succ
                                                                    0))
                                                                    (Prelude.succ
                                                                    (Prelude.succ
                                                                    n)))
                                                                    (Prelude.succ
                                                                    0)))
                                                                   _evar_0_0
                                                                   ((+)
                                                                    (prec
                                                                    ((Prelude.+)
                                                                    (addn
                                                                    (muln
                                                                    (Prelude.succ
                                                                    (Prelude.succ
                                                                    0))
                                                                    (Prelude.succ
                                                                    (Prelude.succ
                                                                    n)))
                                                                    (Prelude.succ
                                                                    0))
                                                                    (Prelude.succ
                                                                    0)))
                                                                    (prec
                                                                    ((Prelude.+)
                                                                    (addn
                                                                    (muln
                                                                    (Prelude.succ
                                                                    (Prelude.succ
                                                                    0))
                                                                    (Prelude.succ
                                                                    (Prelude.succ
                                                                    n)))
                                                                    (Prelude.succ
                                                                    0))
                                                                    (Prelude.succ
                                                                    0))))}
                                                               in
                                                               eq_rect_r
                                                                 (euclidean_max_dist
                                                                   (Prelude.succ
                                                                   (Prelude.succ
                                                                   0))
                                                                   complex0
                                                                   z)
                                                                 _evar_0_0
                                                                 ((+)
                                                                   (0 :: AERN2.CReal)
                                                                   (euclidean_max_dist
                                                                    (Prelude.succ
                                                                    (Prelude.succ
                                                                    0))
                                                                    complex0
                                                                    z))}
                                                             in
                                                             eq_rect_r
                                                               ((+)
                                                                 (0 :: AERN2.CReal)
                                                                 (euclidean_max_dist
                                                                   (Prelude.succ
                                                                   (Prelude.succ
                                                                   0))
                                                                   complex0
                                                                   z))
                                                               _evar_0_0
                                                               ((+)
                                                                 (euclidean_max_dist
                                                                   (Prelude.succ
                                                                   (Prelude.succ
                                                                   0))
                                                                   complex0
                                                                   z)
                                                                 (0 :: AERN2.CReal))}
                                                in
                                                eq_rect_r (0 :: AERN2.CReal)
                                                  _evar_0_0
                                                  ((+)
                                                    (prec
                                                      ((Prelude.+)
                                                        (addn
                                                          (muln (Prelude.succ
                                                            (Prelude.succ 0))
                                                            (Prelude.succ
                                                            (Prelude.succ
                                                            n)))
                                                          (Prelude.succ 0))
                                                        (Prelude.succ 0)))
                                                    (P.negate
                                                      (prec
                                                        ((Prelude.+)
                                                          (addn
                                                            (muln
                                                              (Prelude.succ
                                                              (Prelude.succ
                                                              0))
                                                              (Prelude.succ
                                                              (Prelude.succ
                                                              n)))
                                                            (Prelude.succ 0))
                                                          (Prelude.succ 0)))))}
                                   in
                                   eq_rect_r
                                     ((+)
                                       (prec
                                         ((Prelude.+)
                                           (addn
                                             (muln (Prelude.succ
                                               (Prelude.succ 0))
                                               (Prelude.succ (Prelude.succ
                                               n))) (Prelude.succ 0))
                                           (Prelude.succ 0)))
                                       (P.negate
                                         (prec
                                           ((Prelude.+)
                                             (addn
                                               (muln (Prelude.succ
                                                 (Prelude.succ 0))
                                                 (Prelude.succ (Prelude.succ
                                                 n))) (Prelude.succ 0))
                                             (Prelude.succ 0))))) _evar_0_0
                                     ((+)
                                       (P.negate
                                         (prec
                                           ((Prelude.+)
                                             (addn
                                               (muln (Prelude.succ
                                                 (Prelude.succ 0))
                                                 (Prelude.succ (Prelude.succ
                                                 n))) (Prelude.succ 0))
                                             (Prelude.succ 0))))
                                       (prec
                                         ((Prelude.+)
                                           (addn
                                             (muln (Prelude.succ
                                               (Prelude.succ 0))
                                               (Prelude.succ (Prelude.succ
                                               n))) (Prelude.succ 0))
                                           (Prelude.succ 0))))}
                      in
                      eq_rect_r
                        ((+)
                          (euclidean_max_dist (Prelude.succ (Prelude.succ 0))
                            complex0 z)
                          ((+)
                            (P.negate
                              (prec
                                ((Prelude.+)
                                  (addn
                                    (muln (Prelude.succ (Prelude.succ 0))
                                      (Prelude.succ (Prelude.succ n)))
                                    (Prelude.succ 0)) (Prelude.succ 0))))
                            (prec
                              ((Prelude.+)
                                (addn
                                  (muln (Prelude.succ (Prelude.succ 0))
                                    (Prelude.succ (Prelude.succ n)))
                                  (Prelude.succ 0)) (Prelude.succ 0)))))
                        _evar_0_0
                        ((+)
                          ((+)
                            (euclidean_max_dist (Prelude.succ (Prelude.succ
                              0)) complex0 z)
                            (P.negate
                              (prec
                                ((Prelude.+)
                                  (addn
                                    (muln (Prelude.succ (Prelude.succ 0))
                                      (Prelude.succ (Prelude.succ n)))
                                    (Prelude.succ 0)) (Prelude.succ 0)))))
                          (prec
                            ((Prelude.+)
                              (addn
                                (muln (Prelude.succ (Prelude.succ 0))
                                  (Prelude.succ (Prelude.succ n)))
                                (Prelude.succ 0)) (Prelude.succ 0)))) __}
                    in
                    case _top_assumption_ of {
                     P.True -> _evar_0_ __;
                     P.False -> _evar_0_0 __})}
      in
      eq_rect_r (0 :: AERN2.CReal) _evar_0_
        ((+)
          (prec
            ((Prelude.+)
              (addn
                (muln (Prelude.succ (Prelude.succ 0)) (Prelude.succ
                  (Prelude.succ n))) (Prelude.succ 0)) (Prelude.succ 0)))
          (P.negate
            (prec
              ((Prelude.+)
                (addn
                  (muln (Prelude.succ (Prelude.succ 0)) (Prelude.succ
                    (Prelude.succ n))) (Prelude.succ 0)) (Prelude.succ 0)))))
        x0;
     P.False -> m_unit ((,) x P.False)})

