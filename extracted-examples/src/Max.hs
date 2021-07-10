module Max where

import qualified Prelude
import qualified Numeric.OrdGenericBool as OGB
import MixedTypesNumPrelude (ifThenElse)
import qualified MixedTypesNumPrelude as MNP
import qualified Math.NumberTheory.Logarithms as Logs
import qualified AERN2.Real as AERN2

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
projP1 :: a1 -> a1
projP1 x =
  x

type M a =  a 

mjoin :: (Prelude.Bool -> a1) -> (M Prelude.Bool) -> M a1
mjoin =
  Prelude.id

type Semidec = AERN2.CKleenean

m_split :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal -> M Prelude.Bool
m_split x y _UU03b5_ =
  AERN2.select ((OGB.>) x ((Prelude.-) y _UU03b5_))
    ((OGB.>) y ((Prelude.-) x _UU03b5_))

limit :: (Prelude.Integer -> AERN2.CReal) -> AERN2.CReal
limit p =
  projP1 (AERN2.limit (\n -> projP1 (p n)))

slimit :: (Prelude.Integer -> AERN2.CReal) -> AERN2.CReal
slimit =
  limit

mslimit :: (Prelude.Integer -> M AERN2.CReal) -> AERN2.CReal
mslimit x =
  let {x0 = Prelude.id x} in Prelude.id (Prelude.id slimit x0)

realmax :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal
realmax x y =
  mslimit (\n ->
    mjoin (\h -> case h of {
                  Prelude.True -> x;
                  Prelude.False -> y}) (m_split x y ((0.5 Prelude.^) n)))

