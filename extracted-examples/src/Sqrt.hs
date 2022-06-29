{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Sqrt where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

import MixedTypesNumPrelude (ifThenElse)
import qualified Numeric.OrdGenericBool as OGB
import qualified Unsafe.Coerce as UC
import qualified Control.Monad
import qualified Data.Functor
import qualified MixedTypesNumPrelude as MNP
import qualified Math.NumberTheory.Logarithms as Logs
import qualified AERN2.Real as AERN2

__uc :: a -> b
__uc = UC.unsafeCoerce
__K :: a -> AERN2.CKleenean
__K = UC.unsafeCoerce
__R :: a -> AERN2.CReal
__R = UC.unsafeCoerce
__seqR :: a -> (Prelude.Integer -> AERN2.CReal)
__seqR = UC.unsafeCoerce

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = __uc
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
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

leb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb x y =
  case compare0 x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

ltb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb x y =
  case compare0 x y of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

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
       r' = (Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r)
              ((\x -> x) 1)}
      in
      case ltb r' b of {
       Prelude.True -> (,)
        ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q) r';
       Prelude.False -> (,)
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = (Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r} in
      case ltb r' b of {
       Prelude.True -> (,)
        ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q) r';
       Prelude.False -> (,)
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\_ ->
    case leb ((\x -> x) ((\x -> 2 Prelude.* x) 1)) b of {
     Prelude.True -> (,) 0 ((\x -> x) 1);
     Prelude.False -> (,) ((\x -> x) 1) 0})
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
      (\_ -> (,) 0 0)
      (\_ -> pos_div_eucl a' b)
      (\b' ->
      case pos_div_eucl a' ((\x -> x) b') of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
          (\_ -> (,) (Prelude.negate q) 0)
          (\_ -> (,) (Prelude.negate ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.+) b r))
          (\_ -> (,) (Prelude.negate ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.+) b r))
          r})
      b)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) 0 0)
      (\_ ->
      case pos_div_eucl a' b of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
          (\_ -> (,) (Prelude.negate q) 0)
          (\_ -> (,) (Prelude.negate ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.-) b r))
          (\_ -> (,) (Prelude.negate ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.-) b r))
          r})
      (\b' ->
      case pos_div_eucl a' ((\x -> x) b') of {
       (,) q r -> (,) q (Prelude.negate r)})
      b)
    a

div :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div = (\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)

multivalued_choice :: a1 -> a1 -> a2
multivalued_choice = (\k1 k2 -> __uc (AERN2.select (__K k1) (__K k2)))

select :: a1 -> a1 -> a2
select =
  multivalued_choice

type Semidec k = k

choose :: (Semidec a1) -> (Semidec a1) -> a2
choose x x0 =
  __uc (\h4 -> h4) (select x x0)

real_0 :: a2
real_0 = (__uc (0 :: AERN2.CReal))

real_1 :: a2
real_1 = (__uc (1 :: AERN2.CReal))

real_plus :: a2 -> a2 -> a2
real_plus = (\x y -> __uc (((__R x) Prelude.+ (__R y))))

real_mult :: a2 -> a2 -> a2
real_mult = (\x y -> __uc (((__R x) Prelude.* (__R y))))

real_opp :: a2 -> a2
real_opp = (\x -> __uc (Prelude.negate (__R x)))

real_inv :: a2 -> a2
real_inv = (\x -> __uc (Prelude.recip (__R x)))

real_lt_semidec :: a2 -> a2 -> Semidec a1
real_lt_semidec = (\ x y -> __uc ((__R x) OGB.< (__R y)))

real_minus :: a2 -> a2 -> a2
real_minus = (\x y -> __uc (((__R x) Prelude.- (__R y))))

real_div :: a2 -> a2 -> a2
real_div = (\x y -> __uc (((__R x) Prelude./ (__R y))))

iZreal :: Prelude.Integer -> a2
iZreal = (\z -> __uc (AERN2.creal z))

real_2 :: a2
real_2 = (__uc (2 :: AERN2.CReal))

prec :: Prelude.Integer -> a2
prec = (\n -> __uc ((0.5 :: AERN2.CReal) Prelude.^ n))

real_limit_p :: (Prelude.Integer -> a2) -> a2
real_limit_p = (\ f -> __uc (AERN2.limit (__seqR f)))

pow :: a2 -> Prelude.Integer -> a2
pow r n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> real_1)
    (\m -> real_mult r (pow r m))
    n

linear_search :: (Prelude.Integer -> Prelude.Bool) -> Prelude.Integer ->
                 Prelude.Integer
linear_search p_dec m =
  case p_dec m of {
   Prelude.True -> m;
   Prelude.False -> linear_search p_dec (Prelude.succ m)}

epsilon_smallest :: (Prelude.Integer -> Prelude.Bool) -> Prelude.Integer
epsilon_smallest p_dec =
  linear_search p_dec 0

m_split :: a3 -> a3 -> a3 -> a2
m_split x y _UU03b5_ =
  choose (real_lt_semidec (real_minus y _UU03b5_) x)
    (real_lt_semidec (real_minus x _UU03b5_) y)

real_limit_P_lt_p :: (Prelude.Integer -> a2) -> a2
real_limit_P_lt_p p =
   (real_limit_p (\n ->  (p n)))

real_limit_P_p :: (Prelude.Integer -> a2) -> a2
real_limit_P_p p =
   (real_limit_p (\n ->  (p n)))

real_mslimit_P_p :: (Prelude.Integer -> a2) -> a3
real_mslimit_P_p x =
  let {x0 = __uc x} in __uc (__uc real_limit_P_p x0)

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

epsilon_smallest_PQ :: (Prelude.Integer -> Prelude.Bool) -> Prelude.Integer
epsilon_smallest_PQ =
  epsilon_smallest

epsilon_smallest_PQ_M :: (Prelude.Integer -> a2) -> a2
epsilon_smallest_PQ_M x =
  let {x0 = __uc x} in __uc epsilon_smallest_PQ x0

epsilon_smallest_choose_M :: (Prelude.Integer -> a2) -> a2
epsilon_smallest_choose_M =
  epsilon_smallest_PQ_M

weaken_orM_r :: a1 -> a1
weaken_orM_r =
  __uc (\__top_assumption_ ->
    let {_evar_0_ = \_ -> Prelude.True} in
    let {_evar_0_0 = \_ -> Prelude.False} in
    case __top_assumption_ of {
     Prelude.True -> _evar_0_ __;
     Prelude.False -> _evar_0_0 __})

magnitude1 :: a3 -> a2
magnitude1 x =
  ssr_have __ (\_ ->
    ssr_suff (\g1M -> __uc (\g1 -> g1) g1M)
      (epsilon_smallest_choose_M (\n ->
        weaken_orM_r
          (choose (real_lt_semidec (prec (Prelude.succ (Prelude.succ n))) x)
            (real_lt_semidec x (prec (Prelude.succ n)))))))

zpow :: a2 -> Prelude.Integer -> a2
zpow x z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> real_1)
    (\p -> pow x (to_nat p))
    (\p -> pow (real_inv x) (to_nat p))
    z

dec_x_lt_2 :: a3 -> a2
dec_x_lt_2 x =
  let {
   h = m_split x
         (real_div (iZreal ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))
           real_2) (real_inv real_2)}
  in
  __uc (\h0 ->
    case h0 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}) h

magnitude2 :: a3 -> a2
magnitude2 x =
  let {
   y = real_div x
         (iZreal ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
           1))))}
  in
  ssr_have __ (\_ ->
    ssr_have __ (\_ ->
      ssr_suff
        (__uc (\_top_assumption_ ->
          (Prelude.+) _top_assumption_ ((\x -> x) ((\x -> 2 Prelude.* x) 1))))
        (ssr_have (magnitude1 y)
          (__uc (\_top_assumption_ -> Prelude.negate ( _top_assumption_))))))

magnitude :: a3 -> a2
magnitude x =
  ssr_have (dec_x_lt_2 x)
    (__uc (\_top_assumption_ ->
      let {_evar_0_ = \_ -> magnitude2 x} in
      let {
       _evar_0_0 = \_ ->
        ssr_have __ (\_ ->
          ssr_have (magnitude2 (real_inv x))
            (__uc (\_top_assumption_0 ->
              (Prelude.+) (Prelude.negate _top_assumption_0) ((\x -> x)
                ((\x -> 2 Prelude.* x) 1)))))}
      in
      case _top_assumption_ of {
       Prelude.True -> _evar_0_ __;
       Prelude.False -> _evar_0_0 __}))

sqrt_approx :: a2 -> Prelude.Integer -> a2
sqrt_approx x n =
  nat_rect real_1 (\_ __top_assumption_ ->
    ssr_have __ (\_ ->
      real_mult (real_inv real_2)
        (real_plus __top_assumption_ (real_div x __top_assumption_)))) n

sqrt_approx_fast :: a2 -> Prelude.Integer -> a2
sqrt_approx_fast x n =
  ssr_have
    (sqrt_approx x (Prelude.succ
      ((MNP.integer Prelude.. Logs.integerLog2) (Prelude.succ n))))
    (\__top_assumption_ -> __top_assumption_)

restr_sqrt :: a2 -> a2
restr_sqrt x =
  ssr_have __ (\_ ->
    real_limit_P_lt_p (\n ->
      ssr_have (sqrt_approx_fast x n) (\__top_assumption_ ->
        __top_assumption_)))

scale :: a3 -> a2
scale x =
  let {x0 = magnitude x} in
  __uc (\_top_assumption_ ->
    ssr_have (div _top_assumption_ ((\x -> x) ((\x -> 2 Prelude.* x) 1)))
      (\_top_assumption_0 -> (,) _top_assumption_0
      (real_mult
        (zpow real_2
          ((Prelude.*) (Prelude.negate ((\x -> 2 Prelude.* x) 1))
            _top_assumption_0)) x))) x0

sqrt_pos :: a3 -> a3
sqrt_pos x =
  __uc
    (ssr_have (scale x)
      (__uc (\_top_assumption_ ->
        let {_evar_0_ = \z y -> real_mult (zpow real_2 z) (restr_sqrt y)} in
        case _top_assumption_ of {
         (,) x0 x1 -> _evar_0_ x0 x1})))

sqrt :: a3 -> a3
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
     _evar_0_ = __uc (\_top_assumption_ ->
                  let {_evar_0_ = \_ -> sqrt_pos x} in
                  let {_evar_0_0 = \_ -> real_0} in
                  case _top_assumption_ of {
                   Prelude.True -> _evar_0_ __;
                   Prelude.False -> _evar_0_0 __})}
    in
    eq_rect_r real_0 _evar_0_
      (real_plus
        (prec
          (addn (muln (Prelude.succ (Prelude.succ 0)) n) (Prelude.succ 0)))
        (real_opp
          (prec
            (addn (muln (Prelude.succ (Prelude.succ 0)) n) (Prelude.succ 0)))))
      x0)

r_sqrt2 :: AERN2.CReal -> AERN2.CReal
r_sqrt2 =
  sqrt

