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
import MixedTypesNumPrelude (ifThenElse, CN, integer, CanTestCertainly (isCertainlyTrue))
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
import qualified CSqrt
import qualified Magnitude
import CSqrt (Complex, complex, complex_destruct)

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
  integer $ fromJust $ List.findIndex isCertainlyTrue $ map test [0..]
  where
  test n = select (0.5^^(n+2) < x) (x < 0.5^^(n+1::Int))

magnitude2 :: _ => t -> Integer
magnitude2 x = 2 - (magnitude1 (x/4))

magnitude :: _ => t -> Integer
magnitude x =
  if isCertainlyTrue (select (x < 2) (x > 0.25))
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
  isCertainlyTrue $ select (y-eps < x) (x - eps < y)

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

sqrt_bench0 :: (Floating t) => (t -> t) -> t
sqrt_bench0 sqrtfn = sqrtfn 0

sqrt_bench1 :: (Floating t) => (t -> t) -> t
sqrt_bench1 sqrtfn = sqrtfn 2

sqrt_bench2 :: (Floating t) => (t -> t) -> t
sqrt_bench2 sqrtfn = sqrtfn $ sqrtfn 2

-- complex_i :: Complex c -> c
-- complex_i = snd . complex_destruct

-- complex_r :: Complex c -> c
-- complex_r = fst . complex_destruct

-- csqrt_bench0 :: (Floating t) => (Complex t -> Complex t) -> Complex t
-- csqrt_bench0 csqrtfn = csqrtfn (complex 0 0)

-- csqrt_bench0i :: (Floating t) => (Complex t -> Complex t) -> t
-- csqrt_bench0i csqrtfn = 
--    complex_i $ csqrt_bench0 csqrtfn

-- csqrt_bench0r :: (Floating t) => (Complex t -> Complex t) -> t
-- csqrt_bench0r csqrtfn = 
--    complex_r $ csqrt_bench0 csqrtfn

-- csqrt_bench1 :: (Floating t) => (Complex t -> Complex t) -> Complex t
-- csqrt_bench1 csqrtfn = csqrtfn (complex (-2) 0)

-- csqrt_bench1i :: (Floating t) => (Complex t -> Complex t) -> t
-- csqrt_bench1i csqrtfn = 
--    complex_i $ csqrt_bench1 csqrtfn

-- csqrt_bench1r :: (Floating t) => (Complex t -> Complex t) -> t
-- csqrt_bench1r csqrtfn = 
--    complex_r $ csqrt_bench1 csqrtfn

-- csqrt_bench2 :: (Floating t) => (Complex t -> Complex t) -> Complex t
-- csqrt_bench2 csqrtfn = csqrtfn (complex 0 (2))

-- csqrt_bench2i :: (Floating t) => (Complex t -> Complex t) -> t
-- csqrt_bench2i csqrtfn = 
--    complex_i $ csqrt_bench2 csqrtfn

-- csqrt_bench2r :: (Floating t) => (Complex t -> Complex t) -> t
-- csqrt_bench2r csqrtfn = 
--    complex_r $ csqrt_bench2 csqrtfn

-- csqrt_bench3 :: (Floating t) => (Complex t -> Complex t) -> Complex t
-- csqrt_bench3 csqrtfn = csqrtfn (complex 0 (2^^(-1000 :: Int)))

-- csqrt_bench3i :: (Floating t) => (Complex t -> Complex t) -> t
-- csqrt_bench3i csqrtfn = 
--    complex_i $ csqrt_bench3 csqrtfn

-- csqrt_bench3r :: (Floating t) => (Complex t -> Complex t) -> t
-- csqrt_bench3r csqrtfn = 
--    complex_r $ csqrt_bench3 csqrtfn

-- csqrt_bench4 :: (Floating t) => (Complex t -> Complex t) -> Complex t
-- csqrt_bench4 csqrtfn = csqrtfn (complex 0 (2^^(-10000 :: Int)))

-- csqrt_bench4i :: (Floating t) => (Complex t -> Complex t) -> t
-- csqrt_bench4i csqrtfn = 
--    complex_i $ csqrt_bench4 csqrtfn

-- csqrt_bench4r :: (Floating t) => (Complex t -> Complex t) -> t
-- csqrt_bench4r csqrtfn = 
--    complex_r $ csqrt_bench4 csqrtfn

-- csqrt_bench5 :: (Floating t) => (Complex t -> Complex t) -> Complex t
-- csqrt_bench5 csqrtfn = csqrtfn (complex 0 (2^^(1000 :: Int)))

-- csqrt_bench5i :: (Floating t) => (Complex t -> Complex t) -> t
-- csqrt_bench5i csqrtfn = 
--    complex_i $ csqrt_bench5 csqrtfn

-- csqrt_bench5r :: (Floating t) => (Complex t -> Complex t) -> t
-- csqrt_bench5r csqrtfn = 
--    complex_r $ csqrt_bench5 csqrtfn

magnitude_bench1 :: (CReal -> Integer) -> Integer
magnitude_bench1 magFn = magFn (0.5^(10000 :: Int))

main :: IO ()
main =
  do
  [benchName, pS] <- getArgs
  putStrLn $ bench benchName (read pS)
  where
  bench "realmaxE" p =
    showR $ (realmax_bench Max.real_max :: CReal) ? (prec p)
  bench "realmaxH" p =
    showR $ (realmax_bench real_max :: CReal) ? (prec p)
  bench "realmaxN" p =
    showR $ (realmax_bench max :: CReal) ? (prec p)

  bench "magnitude1E" _p =
    show $ (magnitude_bench1 (Magnitude.magnitude :: CReal -> Integer))
  bench "magnitude1H" _p =
    show $ (magnitude_bench1 (magnitude :: CReal -> Integer))
  -- bench "magnitude1N" p =
  --   showR $ (magnitude_bench1 sqrt :: CReal) ? (prec p)

  bench "sqrt1E" p =
    showR $ (sqrt_bench1 Sqrt.sqrt :: CReal) ? (prec p)
  bench "sqrt1H" p =
    showR $ (sqrt_bench1 sqrt2 :: CReal) ? (prec p)
  bench "sqrt1N" p =
    showR $ (sqrt_bench1 sqrt :: CReal) ? (prec p)

  bench "sqrt2E" p =
    showR $ (sqrt_bench2 Sqrt.sqrt :: CReal) ? (prec p)
  bench "sqrt2H" p =
    showR $ (sqrt_bench2 sqrt2 :: CReal) ? (prec p)
  bench "sqrt2N" p =
    showR $ (sqrt_bench2 sqrt :: CReal) ? (prec p)

  -- bench "csqrt0rE" p =
  --   showR $ (csqrt_bench0r CSqrt.csqrt :: CReal) ? (prec p)
  -- bench "csqrt0iE" p =
  --   showR $ (csqrt_bench0i CSqrt.csqrt :: CReal) ? (prec p)
  -- bench "csqrt1rE" p =
  --   showR $ (csqrt_bench1r CSqrt.csqrt :: CReal) ? (prec p)
  -- bench "csqrt1iE" p =
  --   showR $ (csqrt_bench1i CSqrt.csqrt :: CReal) ? (prec p)
  -- bench "csqrt2rE" p =
  --   showR $ (csqrt_bench2r CSqrt.csqrt :: CReal) ? (prec p)
  -- bench "csqrt2iE" p =
  --   showR $ (csqrt_bench2i CSqrt.csqrt :: CReal) ? (prec p)
  -- bench "csqrt3rE" p =
  --   showR $ (csqrt_bench3r CSqrt.csqrt :: CReal) ? (prec p)
  -- bench "csqrt3iE" p =
  --   showR $ (csqrt_bench3i CSqrt.csqrt :: CReal) ? (prec p)
  -- bench "csqrt4rE" p =
  --   showR $ (csqrt_bench4r CSqrt.csqrt :: CReal) ? (prec p)
  -- bench "csqrt4iE" p =
  --   showR $ (csqrt_bench4i CSqrt.csqrt :: CReal) ? (prec p)
  -- bench "csqrt5rE" p =
  --   showR $ (csqrt_bench5r CSqrt.csqrt :: CReal) ? (prec p)
  -- bench "csqrt5iE" p =
  --   showR $ (csqrt_bench5i CSqrt.csqrt :: CReal) ? (prec p)

  bench "civt1E" p =
    showR $ (civt_bench1 IVT.cIVT :: CReal) ? (prec p)
  bench "civt2E" p =
    showR $ (civt_bench2 IVT.cIVT :: CReal) ? (prec p)
  bench "civt3E" p =
    showR $ (civt_bench3 IVT.cIVT Sqrt.sqrt :: CReal) ? (prec p)
  bench "civt1H" p =
    showR $ (civt_bench1 cIVT :: CReal) ? (prec p)
  bench "civt2H" p =
    showR $ (civt_bench2 cIVT :: CReal) ? (prec p)
  bench "civt3H" p =
    showR $ (civt_bench3 cIVT sqrt2 :: CReal) ? (prec p)

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
