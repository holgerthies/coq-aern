module JSON where
import MixedTypesNumPrelude (double)
import Numeric.CollectErrors ( unCN )

import Data.List (intercalate)
import Text.Printf (printf)

import AERN2.Real (CReal, bits, (?))
import AERN2.MP (IsBall(centre))

{-
toJSON :: [Ball AERN2.CReal] -> Prelude.String
toJSON = ballsToJSON Prelude.. Prelude.map (\(Cons _ x (Cons _ y _), r) -> ((x,y),r))
-}

ballsToJSON :: [((CReal, CReal), CReal)] -> String
ballsToJSON balls =
  printf "balls = [%s]" $ intercalate ",\n" $ map b balls
  where
    b (c, r) =
      printf "{ \"c\": %s, \"r\": %s }" (p c) (show $ d r)
    p :: (CReal, CReal) -> String
    p (x, y) =
      printf "{ \"x\": %s, \"y\": %s }" (show $ d x) (show $ d y)
    d :: CReal -> Double
    d = double . centre . unCN . (\r -> r ? (bits (53 :: Integer)))
