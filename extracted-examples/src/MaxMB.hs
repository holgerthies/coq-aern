{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
module MaxMB where

import qualified Prelude
import Prelude hiding (pred, succ, (==),(/=),(<),(<=),(>),(>=),not,(&&),(||))
import Numeric.OrdGenericBool
import MixedTypesNumPrelude (ifThenElse, integer, Kleenean(..), kleenean)
import Math.NumberTheory.Logarithms (integerLog2)
import Numeric.CollectErrors (CN,cn,liftTakeErrors)
import AERN2.MP
import AERN2.MP.Dyadic ()
import AERN2.MP.WithCurrentPrec
import AERN2.Real hiding (pi)

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
type M a =  a 

type Semidec = (CN Kleenean)

m_split :: (HasCurrentPrecision p) => (WithCurrentPrec (CN MPBall) p) -> (WithCurrentPrec (CN MPBall) p)
           -> (WithCurrentPrec (CN MPBall) p) -> M (CN Bool)
m_split x y _UU03b5_ =
  select ((>) x ((-) y _UU03b5_)) ((>) y ((-) x _UU03b5_))

slimit :: (HasCurrentPrecision p) => (Prelude.Integer -> (WithCurrentPrec (CN MPBall) p)) ->
          (WithCurrentPrec (CN MPBall) p)
slimit =
  limit

mslimit :: (HasCurrentPrecision p) => (Prelude.Integer -> M (WithCurrentPrec (CN MPBall) p)) ->
           (WithCurrentPrec (CN MPBall) p)
mslimit x =
  let {x0 = id x} in id (id slimit x0)

realmax :: (HasCurrentPrecision p) => (WithCurrentPrec (CN MPBall) p) -> (WithCurrentPrec (CN MPBall) p)
           -> (WithCurrentPrec (CN MPBall) p)
realmax x y =
  mslimit (\n ->
    liftTakeErrors (\h -> case h of {
                           True -> x;
                           False -> y}) (m_split x y ((0.5^) n)))
