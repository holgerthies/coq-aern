{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
module Main where
  
import Prelude hiding (pred, succ, (==),(/=),(<),(<=),(>),(>=),abs,max,min,not,(&&),(||))
import Numeric.OrdGenericBool
import MixedTypesNumPrelude (ifThenElse, CN, integer)
import qualified Data.List as List
import Data.Maybe (fromJust)

import System.Environment

-- import Criterion.Main

import AERN2.MP
import AERN2.Real hiding (pi)
-- import AERN2.MP.WithCurrentPrec
import Math.NumberTheory.Logarithms (integerLog2)

import qualified Max
import qualified IVT
import qualified Sqrt
import qualified Magnitude

real_max :: _ => t -> t -> t
real_max x y = 
  limit $ \(n :: Integer) -> 
    let e = 0.5^n in
    if select (x > y - e) (y > x - e)
      then x
      else y

cIVT :: _ => (t -> t) -> t
cIVT (f :: t -> t) = 
  limit $ \ n -> fst $ (iterate aux (0, 1)) !! (2*n)
  where
  aux (a, b) =
    let m1 = (2*a + b)/3 in
    let m2 = (a + 2*b)/3 in
    if select ((f m2) > 0) ((f m1) < 0)
      then (a, m2)
      else (m1, b)

restr_sqrt :: _ => t -> t
restr_sqrt x = limit $ sqrt_approx_fast x
    
sqrt_approx_fast :: _ => t -> Integer -> t
sqrt_approx_fast x n =
  sqrt_approx x (1 + (integerLog2 (n+1)))
    
sqrt_approx :: _ => t -> Int -> t
sqrt_approx x n =
  let step y = (y + x/y)/2 in
  (iterate step 1) !! n

magnitude1 :: _ => t -> Integer
magnitude1 x = 
  integer $ fromJust $ List.findIndex id $ map test [0..]
  where
  test n = select (0.5^^(n+2) < x) (x < 0.5^^(n::Int))

magnitude2 :: _ => t -> Integer
magnitude2 x = 2 - (magnitude1 (x/4))

magnitude :: _ => t -> Integer
magnitude x =
  if select (x < 2) (x > 0.25)
    then magnitude2 x
    else 2 - (magnitude2 (1/x))

scale :: _ => t -> (Integer, t)
scale x = (z,y)
  where
  z = (magnitude x) `div` 2
  y = x * 2^^(-2*z)

sqrt_pos :: _ => t -> t
sqrt_pos x = (restr_sqrt y) * 2^^z
  where
  (z,y) = scale x

split :: _ => t -> t -> t -> Bool
split x y eps = 
  select (y-eps < x) (x - eps < y)

sqrt2 :: _ => t -> t
sqrt2 (x :: t) = limit $ \n ->
  let eps = (0.5 :: t)^(n :: Integer) in
  if (split x eps eps)
    then sqrt_pos x 
    else 0

realmax_bench :: (Floating t) => (t -> t -> t) -> t
realmax_bench maxfn =
  maxfn (pi - pi) 0

civt_bench1 :: (Floating t) => ((t -> t) -> t) -> t
civt_bench1 ivtfn =
  ivtfn (\x -> x - 0.5)

civt_bench2 :: (Floating t) => ((t -> t) -> t) -> t
civt_bench2 ivtfn =
  ivtfn (\x -> x*(2-x) - 0.5)

civt_bench3 :: (Floating t) => ((t -> t) -> t) -> (t -> t) -> t
civt_bench3 ivtfn sqrtfn =
  ivtfn (\x -> sqrtfn (x+0.5) - 1)

sqrt_bench1 :: (Floating t) => (t -> t) -> t
sqrt_bench1 sqrtfn = sqrtfn 2

sqrt_bench2 :: (Floating t) => (t -> t) -> t
sqrt_bench2 sqrtfn = sqrtfn $ sqrtfn 2

magnitude_bench1 :: (Fractional t) => (t -> Integer) -> Integer
magnitude_bench1 magFn = magFn (0.5^(10000 :: Int))

main :: IO ()
main =
  do
  [benchName, pS] <- getArgs
  putStrLn $ bench benchName (read pS)
  where
  bench "realmaxE" p =
    showR $ (realmax_bench Max.r_real_max :: CReal) ? (prec p)
  bench "realmaxH" p =
    showR $ (realmax_bench real_max :: CReal) ? (prec p)
  bench "realmaxN" p =
    showR $ (realmax_bench max :: CReal) ? (prec p)
  -- bench "realmaxMBE" p =
  --   showR $ (runWithPrec (prec p) $ realmax_bench MaxMB.realmax)
  -- bench "realmaxMBH" p =
  --   showR $ (runWithPrec (prec p) $ realmax_bench realmax)
  -- bench "realmaxMBN" p =
  --   showR $ ((runWithPrec (prec p) $ realmax_bench max) :: CN MPBall)

  bench "magnitude1E" _p =
    show $ (magnitude_bench1 (Magnitude.r_magnitude :: CReal -> Integer))
  bench "magnitude1H" _p =
    show $ (magnitude_bench1 (magnitude :: CReal -> Integer))
  -- bench "magnitude1N" p =
  --   showR $ (magnitude_bench1 sqrt :: CReal) ? (prec p)

  bench "sqrt1E" p =
    showR $ (sqrt_bench1 Sqrt.r_sqrt2 :: CReal) ? (prec p)
  bench "sqrt1H" p =
    showR $ (sqrt_bench1 sqrt2 :: CReal) ? (prec p)
  bench "sqrt1N" p =
    showR $ (sqrt_bench1 sqrt :: CReal) ? (prec p)
  -- bench "sqrt1MBE" p =
  --   showR $ (runWithPrec (prec p) $ sqrt_bench1 SqrtMB.restr_sqrt)
  -- bench "sqrt1MBH" p =
  --   showR $ (runWithPrec (prec p) $ sqrt_bench1 restr_sqrt)
  -- bench "sqrt1MBN" p =
  --   showR $ ((runWithPrec (prec p) $ sqrt_bench1 sqrt) :: CN MPBall)

  bench "sqrt2E" p =
    showR $ (sqrt_bench2 Sqrt.r_sqrt2 :: CReal) ? (prec p)
  bench "sqrt2H" p =
    showR $ (sqrt_bench2 sqrt2 :: CReal) ? (prec p)
  bench "sqrt2N" p =
    showR $ (sqrt_bench2 sqrt :: CReal) ? (prec p)
  -- bench "sqrt2MBE" p =
  --   showR $ (runWithPrec (prec p) $ sqrt_bench2 SqrtMB.restr_sqrt)
  -- bench "sqrt2MBH" p =
  --   showR $ (runWithPrec (prec p) $ sqrt_bench2 restr_sqrt)
  -- bench "sqrt2MBN" p =
  --   showR $ ((runWithPrec (prec p) $ sqrt_bench2 sqrt) :: CN MPBall)

  bench "civt1E" p =
    showR $ (civt_bench1 IVT.r_CIVT :: CReal) ? (prec p)
  bench "civt2E" p =
    showR $ (civt_bench2 IVT.r_CIVT :: CReal) ? (prec p)
  bench "civt3E" p =
    showR $ (civt_bench3 IVT.r_CIVT Sqrt.r_sqrt2 :: CReal) ? (prec p)
  bench "civt1H" p =
    showR $ (civt_bench1 cIVT :: CReal) ? (prec p)
  bench "civt2H" p =
    showR $ (civt_bench2 cIVT :: CReal) ? (prec p)
  bench "civt3H" p =
    showR $ (civt_bench3 cIVT sqrt2 :: CReal) ? (prec p)
  -- bench "civt1MBE" p =
  --   showR $ (runWithPrec (prec p) $ civt_bench1 IVTMB.cIVT)
  -- bench "civt2MBE" p =
  --   showR $ (runWithPrec (prec p) $ civt_bench2 IVTMB.cIVT)
  -- bench "civt3MBE" p =
  --   showR $ (runWithPrec (prec p) $ civt_bench3 IVTMB.cIVT SqrtMB.restr_sqrt)
  -- bench "civt1MBH" p =
  --   showR $ (runWithPrec (prec p) $ civt_bench1 cIVT)
  -- bench "civt2MBH" p =
  --   showR $ (runWithPrec (prec p) $ civt_bench2 cIVT)
  -- bench "civt3MBH" p =
  --   showR $ (runWithPrec (prec p) $ civt_bench3 cIVT restr_sqrt)

  bench name _p = 
    error $ "unrecognised benchmark name: " <> name
  showR :: CN MPBall -> String
  showR b =
    show b <> "\naccuracy: " <> show (getAccuracy b)

-- suite :: [Benchmark]
-- suite = [
--     bgroup "Max" [
--       bench "CReal (extracted)" $ nf (? (prec 1100000)) (realmax_bench Max.realmax :: CReal)
--     , bench "CReal (by hand)" $ nf (? (prec 1100000)) (realmax_bench realmax :: CReal)
--     , bench "CReal (native)" $ nf (? (prec 1100000)) (realmax_bench MxP.max :: CReal) 
--     ]
--   ]

-- main :: IO ()
-- main = defaultMain $ suite
