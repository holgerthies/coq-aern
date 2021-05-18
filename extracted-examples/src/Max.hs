module Max where

import qualified Prelude
import Prelude hiding (pi, pred, succ, (==),(/=),(<),(<=),(>),(>=),not,(&&),(||))
import Numeric.OrdGenericBool
import MixedTypesNumPrelude (ifThenElse, integer)
import Math.NumberTheory.Logarithms (integerLog2)
import AERN2.Real

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
type M a =  a 

mjoin :: (Bool -> a1) -> (M Bool) -> M a1
mjoin =
  id

type Semidec = CKleenean

m_split :: CReal -> CReal -> CReal -> M Bool
m_split x y _UU03b5_ =
  select ((>) x ((-) y _UU03b5_)) ((>) y ((-) x _UU03b5_))

slimit :: (Prelude.Integer -> CReal) -> CReal
slimit =
  limit

mslimit :: (Prelude.Integer -> M CReal) -> CReal
mslimit x =
  let {x0 = id x} in id (id slimit x0)

realmax :: CReal -> CReal -> CReal
realmax x y =
  mslimit (\n ->
    mjoin (\h -> case h of {
                  True -> x;
                  False -> y}) (m_split x y ((0.5^) n)))

