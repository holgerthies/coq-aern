module IVT where

import qualified Prelude
import Prelude hiding (pred, succ, (==),(/=),(<),(<=),(>),(>=),not,(&&),(||))
import Numeric.OrdGenericBool
import MixedTypesNumPrelude (ifThenElse, integer)
import Math.NumberTheory.Logarithms (integerLog2)
import AERN2.Real

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

mjoin :: (Bool -> a1) -> (M Bool) -> M a1
mjoin =
  id

type Semidec = CKleenean

slimit :: (Prelude.Integer -> CReal) -> CReal
slimit =
  limit

mslimit :: (Prelude.Integer -> M CReal) -> CReal
mslimit x =
  let {x0 = id x} in id (id slimit x0)

m_uniq_pick :: (CReal -> CReal) -> CReal -> CReal -> CReal -> CReal -> M Bool
m_uniq_pick f _ b c _ =
  select ((<) (f b) 0) ((<) 0 (f c))

trisect :: (CReal -> CReal) -> CReal -> CReal -> M ((,) CReal CReal)
trisect f a b =
  mjoin (\h0 ->
    case h0 of {
     True -> (,) ((/) ((+) ((*) 2 a) b) 3) b;
     False -> (,) a ((/) ((+) a ((*) 2 b)) 3)})
    (m_uniq_pick f a ((/) ((+) ((*) 2 a) b) 3) ((/) ((+) a ((*) 2 b)) 3) b)

halving :: (CReal -> CReal) -> CReal -> CReal -> M ((,) CReal CReal)
halving f a b =
  let {one = trisect f a b} in
  lift_domM (\q ->
    case q of {
     (,) x s -> let {x0 = trisect f x s} in id (\h1 -> h1) x0}) one

root_approx :: (CReal -> CReal) -> Prelude.Integer -> M ((,) CReal CReal)
root_approx f n =
  nat_rect (id ((,) 0 1)) (\_ iHn ->
    lift_domM (\x ->
      case x of {
       (,) x0 s -> let {x1 = halving f x0 s} in id (\h -> h) x1}) iHn) n

cIVT :: (CReal -> CReal) -> CReal
cIVT f =
  mslimit (\n ->
    let {x = root_approx f (Prelude.succ n)} in
    id (\h -> case h of {
               (,) x0 _ -> x0}) x)

