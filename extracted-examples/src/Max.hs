{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Max where

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

real_lt_semidec :: a2 -> a2 -> Semidec a1
real_lt_semidec = (\ x y -> __uc ((__R x) OGB.< (__R y)))

real_minus :: a2 -> a2 -> a2
real_minus = (\x y -> __uc (((__R x) Prelude.- (__R y))))

prec :: Prelude.Integer -> a2
prec = (\n -> __uc ((0.5 :: AERN2.CReal) Prelude.^ n))

real_limit_p :: (Prelude.Integer -> a2) -> a2
real_limit_p = (\ f -> __uc (AERN2.limit (__seqR f)))

m_split :: a3 -> a3 -> a3 -> a2
m_split x y _UU03b5_ =
  choose (real_lt_semidec (real_minus y _UU03b5_) x)
    (real_lt_semidec (real_minus x _UU03b5_) y)

real_limit_P_lt_p :: (Prelude.Integer -> a2) -> a2
real_limit_P_lt_p p =
   (real_limit_p (\n ->  (p n)))

real_limit_P_lt :: (Prelude.Integer -> a3) -> a3
real_limit_P_lt =
  real_limit_P_lt_p

real_mslimit_P_lt :: (Prelude.Integer -> a2) -> a3
real_mslimit_P_lt x =
  let {x0 = __uc x} in __uc (__uc real_limit_P_lt x0)

real_max_prop :: a3 -> a3 -> a3
real_max_prop x y =
  real_mslimit_P_lt (\n ->
    __uc (\h -> case h of {
                 Prelude.True -> x;
                 Prelude.False -> y}) (m_split x y (prec n)))

real_max :: a3 -> a3 -> a3
real_max x y =
   (real_max_prop x y)

r_real_max :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal
r_real_max =
  real_max

