{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
module IVTMB where

import qualified Prelude
import Prelude hiding (pred, succ, (==),(/=),(<),(<=),(>),(>=),not,(&&),(||))
import Numeric.OrdGenericBool
import MixedTypesNumPrelude (ifThenElse, integer, Kleenean(..), kleenean)
import Math.NumberTheory.Logarithms (integerLog2)
import Numeric.CollectErrors (CN,cn,liftTakeErrors)
import AERN2.MP
import AERN2.MP.Dyadic ()
import AERN2.MP.WithCurrentPrec
import AERN2.Limit
import AERN2.Real(select)
import AERN2.Real.Type

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
type M a =  a 

lift_domM :: (a1 -> M a2) -> (M a1) -> M a2
lift_domM f x =
  id (id f x)

type Semidec = (CN Kleenean)

slimit :: (HasCurrentPrecision p) => (Prelude.Integer -> (WithCurrentPrec (CN MPBall) p)) ->
          (WithCurrentPrec (CN MPBall) p)
slimit =
  limit

mslimit :: (HasCurrentPrecision p) => (Prelude.Integer -> M (WithCurrentPrec (CN MPBall) p)) ->
           (WithCurrentPrec (CN MPBall) p)
mslimit x =
  let {x0 = id x} in id (id slimit x0)

m_uniq_pick :: (HasCurrentPrecision p) => ((WithCurrentPrec (CN MPBall) p) ->
               (WithCurrentPrec (CN MPBall) p)) ->
               (WithCurrentPrec (CN MPBall) p) ->
               (WithCurrentPrec (CN MPBall) p) ->
               (WithCurrentPrec (CN MPBall) p) ->
               (WithCurrentPrec (CN MPBall) p) -> M (CN Bool)
m_uniq_pick f _ b c _ =
  select ((<) (f b) 0) ((<) 0 (f c))

trisect :: (HasCurrentPrecision p) => ((WithCurrentPrec (CN MPBall) p) ->
           (WithCurrentPrec (CN MPBall) p)) ->
           (WithCurrentPrec (CN MPBall) p) -> (WithCurrentPrec (CN MPBall) p)
           -> M
           ((,) (WithCurrentPrec (CN MPBall) p)
           (WithCurrentPrec (CN MPBall) p))
trisect f a b =
  liftTakeErrors (\h0 ->
    case h0 of {
     True -> (,) ((/) ((+) ((*) 2 a) b) 3) b;
     False -> (,) a ((/) ((+) a ((*) 2 b)) 3)})
    (m_uniq_pick f a ((/) ((+) ((*) 2 a) b) 3) ((/) ((+) a ((*) 2 b)) 3) b)

halving :: (HasCurrentPrecision p) => ((WithCurrentPrec (CN MPBall) p) ->
           (WithCurrentPrec (CN MPBall) p)) ->
           (WithCurrentPrec (CN MPBall) p) -> (WithCurrentPrec (CN MPBall) p)
           -> M
           ((,) (WithCurrentPrec (CN MPBall) p)
           (WithCurrentPrec (CN MPBall) p))
halving f a b =
  let {one = trisect f a b} in
  lift_domM (\q ->
    case q of {
     (,) x s -> let {x0 = trisect f x s} in id (\h1 -> h1) x0}) one

root_approx :: (HasCurrentPrecision p) => ((WithCurrentPrec (CN MPBall) p) ->
               (WithCurrentPrec (CN MPBall) p)) -> Prelude.Integer -> M
               ((,) (WithCurrentPrec (CN MPBall) p)
               (WithCurrentPrec (CN MPBall) p))
root_approx f n =
  nat_rect (id ((,) 0 1)) (\_ iHn ->
    lift_domM (\x ->
      case x of {
       (,) x0 s -> let {x1 = halving f x0 s} in id (\h -> h) x1}) iHn) n

cIVT :: (HasCurrentPrecision p) => ((WithCurrentPrec (CN MPBall) p) -> (WithCurrentPrec (CN MPBall) p))
        -> (WithCurrentPrec (CN MPBall) p)
cIVT f =
  mslimit (\n ->
    let {x = root_approx f (Prelude.succ n)} in
    id (\h -> case h of {
               (,) x0 _ -> x0}) x)

