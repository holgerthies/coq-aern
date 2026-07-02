{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports -Wno-type-defaults -Wno-incomplete-patterns #-}
-- Evaluate one extracted fractal-drawing example at accuracy n:
--   `*_tbounded n` returns a finite set of balls (each of radius 2^-(n+1))
--   whose union is within Hausdorff distance 2^-n of the fractal -- so `n`
--   is the accuracy parameter (target error 2^-n), not a recursion depth.
-- We compute the covering balls, force every coordinate/radius to `prec`
-- bits, and report (#balls, wall-clock seconds for the computation).
-- Usage: eval-fractals <example> <n> <precisionBits>
module Main where

import Prelude
import System.Environment (getArgs)
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import Data.List (intercalate)
import Text.Printf (printf)
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Numeric.CollectErrors (unCN)
import MixedTypesNumPrelude (double)
import AERN2.Real (CReal, bits, (?))
import AERN2.MP (IsBall(centre))

import qualified Tn
import qualified STRn
import qualified STEn
import qualified STE4n
import qualified STRLim

-- force a CReal to a concrete Double at precision 2^-p
toD :: Integer -> CReal -> Double
toD p r = double (centre (unCN (r ? (bits p))))

-- (Euclidean point = Cons _ x (Cons _ y Nil)) -> the two coordinates + radius
ballsOf :: String -> Integer -> Integer -> [(Double, Double, Double)]
ballsOf "Tn"     p n = [ (toD p x, toD p y, toD p r) | (Tn.Cons     _ x (Tn.Cons     _ y Tn.Nil),     r) <- Tn.t_tbounded n ]
ballsOf "STRn"   p n = [ (toD p x, toD p y, toD p r) | (STRn.Cons0  _ x (STRn.Cons0  _ y STRn.Nil0),  r) <- STRn.sTR_tbounded n ]
ballsOf "STEn"   p n = [ (toD p x, toD p y, toD p r) | (STEn.Cons0  _ x (STEn.Cons0  _ y STEn.Nil0),  r) <- STEn.sTE_tbounded n ]
ballsOf "STE4n"  p n = [ (toD p x, toD p y, toD p r) | (STE4n.Cons0 _ x (STE4n.Cons0 _ y STE4n.Nil0), r) <- STE4n.sTE4_tbounded n ]
ballsOf "STRLim" p n = [ (toD p x, toD p y, toD p r) | (STRLim.Cons _ x (STRLim.Cons _ y STRLim.Nil), r) <- STRLim.tbounded_sierpinski n ]
ballsOf ex _ _ = error ("unknown example: " ++ ex)

main :: IO ()
main = do
  args <- getArgs
  case args of
    -- emit a JS data line for the gallery renderer (centers @ 53 bits):
    --   DATA["<ex>_<n>"] = {"r":<radius>, "c":[[x,y],...]};
    -- (all balls at a given (ex,n) share one radius, so it is stored once)
    [ex, nS, "js"] -> do
      let n  = read nS :: Integer
          bs = ballsOf ex 53 n
          r  = case bs of ((_,_,rr):_) -> rr; [] -> 0
          pt (x,y,_) = printf "[%.7g,%.7g]" x y :: String
      putStrLn (printf "DATA[\"%s_%s\"] = {\"r\":%.7g,\"c\":[%s]};"
                        ex nS r (intercalate "," (map pt bs)))
    [ex, nS, precS] -> do
      let n    = read nS    :: Integer
          prec = read precS :: Integer
      -- warm-up: force the cheap n=1 cover first, so the timed run excludes
      -- one-time evaluation of shared top-level constants (sqrt_3, one_half,
      -- AERN2 setup). n=1 does one subdivision, which is what forces them;
      -- this makes small-n times comparable to the rest.
      _  <- evaluate (force (ballsOf ex prec 1))
      t0 <- getCurrentTime
      let bs = ballsOf ex prec n
      _  <- evaluate (force bs)
      t1 <- getCurrentTime
      let secs = realToFrac (diffUTCTime t1 t0) :: Double
      putStrLn (ex ++ "," ++ nS ++ "," ++ precS ++ "," ++ show (length bs) ++ "," ++ show secs)
    _ -> putStrLn "usage: eval-fractals <example> <n> <precisionBits>"
