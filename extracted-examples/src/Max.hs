module Max where

import qualified Prelude
import qualified Numeric.OrdGenericBool as OGB
import MixedTypesNumPrelude (ifThenElse)
import qualified MixedTypesNumPrelude as MNP
import qualified Math.NumberTheory.Logarithms as Logs
import qualified AERN2.Real as AERN2

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
type M a =  a 

type Semidec = AERN2.CKleenean

choose :: Semidec -> Semidec -> M Prelude.Bool
choose h h0 =
  Prelude.id (\h4 -> h4) (AERN2.select h h0)

m_split :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal -> M Prelude.Bool
m_split x y _UU03b5_ =
  choose ((OGB.>) x ((Prelude.-) y _UU03b5_))
    ((OGB.>) y ((Prelude.-) x _UU03b5_))

slimit :: (Prelude.Integer -> AERN2.CReal) -> AERN2.CReal
slimit =
  AERN2.limit

mslimit :: (Prelude.Integer -> M AERN2.CReal) -> AERN2.CReal
mslimit x =
  let {x0 = Prelude.id x} in Prelude.id (Prelude.id slimit x0)

realmax :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal
realmax x y =
  mslimit (\n ->
    Prelude.id (\h -> case h of {
                       Prelude.True -> x;
                       Prelude.False -> y}) (m_split x y ((0.5 Prelude.^) n)))

