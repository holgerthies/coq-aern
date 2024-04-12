{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module IVT where

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

__uc :: a -> b
__uc = UC.unsafeCoerce
__K :: a -> AERN2.CKleenean
__K = UC.unsafeCoerce
__R :: a -> AERN2.CReal
__R = UC.unsafeCoerce

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

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
type M a = a

m_lift :: (a1 -> a2) -> (M a1) -> M a2
m_lift = P.id

m_unit :: a1 -> M a1
m_unit = P.id

m_lift_dom :: (a1 -> M a2) -> (M a1) -> M a2
m_lift_dom = P.id

mjoin :: (P.Bool -> a1) -> (M P.Bool) -> M a1
mjoin = P.id

type Semidec = AERN2.CKleenean

choose :: Semidec -> Semidec -> M P.Bool
choose = (unCNfn2 AERN2.select)

real_0 :: AERN2.CReal
real_0 = 0

real_1 :: AERN2.CReal
real_1 = 1

real_2 :: AERN2.CReal
real_2 = 2

m_uniq_pick :: (AERN2.CReal -> AERN2.CReal) -> AERN2.CReal -> AERN2.CReal ->
               AERN2.CReal -> AERN2.CReal -> M P.Bool
m_uniq_pick f _ b c _ =
  choose ((OGB.<) (f b) real_0) ((OGB.<) real_0 (f c))

real_3 :: AERN2.CReal
real_3 = (3 :: AERN2.CReal)

trisect :: (AERN2.CReal -> AERN2.CReal) -> AERN2.CReal -> AERN2.CReal -> M
           ((,) AERN2.CReal AERN2.CReal)
trisect f a b =
  mjoin (\h0 ->
    case h0 of {
     P.True -> (,) ((/) ((+) ((P.*) real_2 a) b) real_3) b;
     P.False -> (,) a ((/) ((+) a ((P.*) real_2 b)) real_3)})
    (m_uniq_pick f a ((/) ((+) ((P.*) real_2 a) b) real_3)
      ((/) ((+) a ((P.*) real_2 b)) real_3) b)

halving :: (AERN2.CReal -> AERN2.CReal) -> AERN2.CReal -> AERN2.CReal -> M
           ((,) AERN2.CReal AERN2.CReal)
halving f a b =
  let {one = trisect f a b} in
  m_lift_dom (\q ->
    case q of {
     (,) x s ->
      let {x0 = trisect f x s} in
      m_lift (\x1 -> case x1 of {
                      (,) x2 s0 -> (,) x2 s0}) x0}) one

root_approx :: (AERN2.CReal -> AERN2.CReal) -> Prelude.Integer -> M
               ((,) AERN2.CReal AERN2.CReal)
root_approx f n =
  nat_rect (m_unit ((,) real_0 real_1)) (\_ iHn ->
    m_lift_dom (\x ->
      case x of {
       (,) x0 s ->
        let {x1 = halving f x0 s} in
        m_lift (\x2 -> case x2 of {
                        (,) x3 s0 -> (,) x3 s0}) x1}) iHn) n

cIVT :: (AERN2.CReal -> AERN2.CReal) -> AERN2.CReal
cIVT f =
  AERN2.limit (\n ->
    let {x = root_approx f (Prelude.succ n)} in
    m_lift (\x0 -> case x0 of {
                    (,) x1 _ -> x1}) x)

