{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module IVT where

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

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) ->
            Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
type M a = a

m_lift :: (a1 -> a2) -> (M a1) -> M a2
m_lift = P.id

m_unit :: a1 -> M a1
m_unit = P.id

m_lift_dom :: (a1 -> M a2) -> (M a1) -> M a2
m_lift_dom = P.id

m_hprop_elim_f :: (M a1) -> a1
m_hprop_elim_f = P.id

m_countable_lift :: (Prelude.Integer -> M a1) -> M
                    (Prelude.Integer -> a1)
m_countable_lift = P.id

mjoin :: (P.Bool -> a1) -> (M P.Bool) -> M a1
mjoin = P.id

type Semidec = AERN2.CKleenean

choose :: Semidec -> Semidec -> M P.Bool
choose = AERN2.select

real_0 :: AERN2.CReal
real_0 = 0

real_1 :: AERN2.CReal
real_1 = 1

real_2 :: AERN2.CReal
real_2 = 2

real_limit_p :: (Prelude.Integer -> AERN2.CReal) ->
                AERN2.CReal
real_limit_p = AERN2.limit

real_limit_P_p :: (Prelude.Integer -> AERN2.CReal) ->
                  AERN2.CReal
real_limit_P_p p =
   (real_limit_p (\n ->  (p n)))

real_limit_P :: (Prelude.Integer -> AERN2.CReal) ->
                AERN2.CReal
real_limit_P =
  real_limit_P_p

real_mslimit_P :: (Prelude.Integer -> M AERN2.CReal) ->
                  AERN2.CReal
real_mslimit_P x =
  let {x0 = m_countable_lift x} in
  m_hprop_elim_f (m_lift real_limit_P x0)

m_uniq_pick :: (AERN2.CReal -> AERN2.CReal) ->
               AERN2.CReal -> AERN2.CReal ->
               AERN2.CReal -> AERN2.CReal -> M 
               P.Bool
m_uniq_pick f _ b c _ =
  choose ((OGB.<) (f b) real_0) ((OGB.<) real_0 (f c))

real_3 :: AERN2.CReal
real_3 = (3 :: AERN2.CReal)

trisect :: (AERN2.CReal -> AERN2.CReal) -> AERN2.CReal
           -> AERN2.CReal -> M
           ((,) AERN2.CReal AERN2.CReal)
trisect f a b =
  mjoin (\h0 ->
    case h0 of {
     P.True -> (,)
      ((/) ((+) ((P.*) real_2 a) b) real_3) b;
     P.False -> (,) a
      ((/) ((+) a ((P.*) real_2 b)) real_3)})
    (m_uniq_pick f a
      ((/) ((+) ((P.*) real_2 a) b) real_3)
      ((/) ((+) a ((P.*) real_2 b)) real_3) b)

halving :: (AERN2.CReal -> AERN2.CReal) -> AERN2.CReal
           -> AERN2.CReal -> M
           ((,) AERN2.CReal AERN2.CReal)
halving f a b =
  let {one = trisect f a b} in
  m_lift_dom (\q ->
    case q of {
     (,) x p ->
      let {x0 = trisect f x p} in
      m_lift (\x1 ->
        case x1 of {
         (,) x2 p0 -> (,) x2 p0}) x0}) one

root_approx :: (AERN2.CReal -> AERN2.CReal) ->
               Prelude.Integer -> M
               ((,) AERN2.CReal AERN2.CReal)
root_approx f n =
  nat_rect (m_unit ((,) real_0 real_1)) (\_ iHn ->
    m_lift_dom (\x ->
      case x of {
       (,) x0 p ->
        let {x1 = halving f x0 p} in
        m_lift (\x2 ->
          case x2 of {
           (,) x3 p0 -> (,) x3 p0}) x1}) iHn) n

cIVT :: (AERN2.CReal -> AERN2.CReal) -> AERN2.CReal
cIVT f =
  real_mslimit_P (\n ->
    let {x = root_approx f (Prelude.succ n)} in
    m_lift (\x0 -> case x0 of {
                    (,) x1 _ -> x1}) x)

