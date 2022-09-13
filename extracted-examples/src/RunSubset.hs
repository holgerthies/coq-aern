module RunSubset where
import MixedTypesNumPrelude (double)
import Numeric.CollectErrors ( unCN )

import Data.List (intercalate)
import Text.Printf (printf)

import AERN2.Real (CReal, bits, (?))
import AERN2.MP (IsBall(centre))

-- import qualified Tn as EXTR
-- import qualified MTn as EXTR
-- import qualified STARn as EXTR
-- import qualified STRn as EXTR
-- import qualified STEn as EXTR
-- import qualified STE4n as EXTR
import qualified STRLim as EXTR

{-
toJSON :: [Ball AERN2.CReal] -> Prelude.String
toJSON = ballsToJSON Prelude.. Prelude.map (\(Cons _ x (Cons _ y _), r) -> ((x,y),r))
-}

ballsToJSON :: [EXTR.Ball] -> String
ballsToJSON balls =
  printf "balls = [%s]" $ intercalate ",\n" $ map b balls
  where
    b (c, r) =
      printf "{ \"c\": %s, \"r\": %s }" (p c) (show $ d r)
    p :: EXTR.Euclidean -> String
    p (EXTR.Cons _ x (EXTR.Cons _ y EXTR.Nil)) =
    -- p (EXTR.Cons0 _ x (EXTR.Cons0 _ y EXTR.Nil0)) =
      printf "{ \"x\": %s, \"y\": %s }" (show $ d x) (show $ d y)
    p _ = error "ballsToJSON: an Euclidean value does not have dimension 2"
    d :: CReal -> Double
    d = double . centre . unCN . (\r -> r ? (bits (53 :: Integer)))
