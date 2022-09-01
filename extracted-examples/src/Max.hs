{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Max where

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

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
type M a = a

multivalued_choice :: AERN2.CKleenean -> AERN2.CKleenean -> M P.Bool
multivalued_choice = AERN2.select

m_lift :: (a1 -> a2) -> (M a1) -> M a2
m_lift = P.id

m_hprop_elim_f :: (M a1) -> a1
m_hprop_elim_f = P.id

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

prec :: Prelude.Integer -> AERN2.CReal
prec = ((0.5 :: AERN2.CReal) P.^)

real_limit_p :: (Prelude.Integer -> AERN2.CReal) -> AERN2.CReal
real_limit_p = AERN2.limit

m_split :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal -> M P.Bool
m_split x y _UU03b5_ =
  choose ((OGB.<) ((-) y _UU03b5_) x) ((OGB.<) ((-) x _UU03b5_) y)

real_limit_P_lt_p :: (Prelude.Integer -> AERN2.CReal) -> AERN2.CReal
real_limit_P_lt_p p =
   (real_limit_p (\n ->  (p n)))

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

