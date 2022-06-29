{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module IVT where

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

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
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

real_lt_semidec :: a2 -> a2 -> Semidec a1
real_lt_semidec = (\ x y -> __uc ((__R x) OGB.< (__R y)))

real_div :: a2 -> a2 -> a2
real_div = (\x y -> __uc (((__R x) Prelude./ (__R y))))

real_2 :: a2
real_2 = (__uc (2 :: AERN2.CReal))

real_limit_p :: (Prelude.Integer -> a2) -> a2
real_limit_p = (\ f -> __uc (AERN2.limit (__seqR f)))

real_limit_P_p :: (Prelude.Integer -> a2) -> a2
real_limit_P_p p =
   (real_limit_p (\n ->  (p n)))

real_limit_P :: (Prelude.Integer -> a3) -> a3
real_limit_P =
  real_limit_P_p

real_mslimit_P :: (Prelude.Integer -> a2) -> a3
real_mslimit_P x =
  let {x0 = __uc x} in __uc (__uc real_limit_P x0)

m_uniq_pick :: (a3 -> a3) -> a3 -> a3 -> a3 -> a3 -> a2
m_uniq_pick f _ b c _ =
  choose (real_lt_semidec (f b) real_0) (real_lt_semidec real_0 (f c))

real_3 :: a2
real_3 = (__uc (3 :: AERN2.CReal))

trisect :: (a3 -> a3) -> a3 -> a3 -> a2
trisect f a b =
  __uc (\h0 ->
    case h0 of {
     Prelude.True -> (,) (real_div (real_plus (real_mult real_2 a) b) real_3)
      b;
     Prelude.False -> (,) a
      (real_div (real_plus a (real_mult real_2 b)) real_3)})
    (m_uniq_pick f a (real_div (real_plus (real_mult real_2 a) b) real_3)
      (real_div (real_plus a (real_mult real_2 b)) real_3) b)

halving :: (a3 -> a3) -> a3 -> a3 -> a2
halving f a b =
  let {one = trisect f a b} in
  __uc (\q ->
    case q of {
     (,) x s ->
      let {x0 = trisect f x s} in
      __uc (\x1 -> case x1 of {
                    (,) x' s0 -> (,) x' s0}) x0}) one

root_approx :: (a3 -> a3) -> Prelude.Integer -> a2
root_approx f n =
  nat_rect (__uc ((,) real_0 real_1)) (\_ iHn ->
    __uc (\x ->
      case x of {
       (,) x0 s ->
        let {x1 = halving f x0 s} in
        __uc (\x2 -> case x2 of {
                      (,) x' s0 -> (,) x' s0}) x1}) iHn) n

cIVT :: (a3 -> a3) -> a3
cIVT f =
  real_mslimit_P (\n ->
    let {x = root_approx f (Prelude.succ n)} in
    __uc (\x0 -> case x0 of {
                  (,) x1 _ -> x1}) x)

r_CIVT :: (AERN2.CReal -> AERN2.CReal) -> AERN2.CReal
r_CIVT =
  cIVT

