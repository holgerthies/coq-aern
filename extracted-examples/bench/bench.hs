{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
module Main where
  
import Prelude hiding (pred, succ, (==),(/=),(<),(<=),(>),(>=),abs,max,min,not,(&&),(||))
import Numeric.OrdGenericBool
import MixedTypesNumPrelude (ifThenElse, CN)

import System.Environment

-- import Criterion.Main

import AERN2.MP
import AERN2.Real hiding (pi)
import AERN2.MP.WithCurrentPrec
import Math.NumberTheory.Logarithms (integerLog2)

import qualified Max
import qualified MaxMB 
import qualified IVT
import qualified IVTMB 
import qualified Sqrt
import qualified SqrtMB 

maxH :: _ => t -> t -> t
maxH x y = 
  limit $ \(n :: Integer) -> 
    let e = 0.5^n in
    if select (x > y - e) (y > x - e)
      then x
      else y

civtH :: _ => (t -> t) -> t
civtH (f :: t -> t) = 
  limit $ \ n -> fst $ (iterate aux (0, 1)) !! (2*n)
  where
  aux (a, b) =
    let m1 = (2*a + b)/3 in
    let m2 = (a + 2*b)/3 in
    if select ((f m2) > 0) ((f m1) < 0)
      then (a, m2)
      else (m1, b)

rsqrtH :: _ => t -> t
rsqrtH x =
  limit $ \n -> 
    let step y = (y + x/y)/2 in
    (iterate step 1) !! (integerLog2 n)
    

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


main :: IO ()
main =
  do
  [benchName, pS] <- getArgs
  putStrLn $ bench benchName (read pS)
  where
  bench "realmaxE" p =
    showR $ (realmax_bench Max.realmax :: CReal) ? (prec p)
  bench "realmaxH" p =
    showR $ (realmax_bench maxH :: CReal) ? (prec p)
  bench "realmaxN" p =
    showR $ (realmax_bench max :: CReal) ? (prec p)
  bench "realmaxMBE" p =
    showR $ (runWithPrec (prec p) $ realmax_bench MaxMB.realmax)
  bench "realmaxMBH" p =
    showR $ (runWithPrec (prec p) $ realmax_bench maxH)
  bench "realmaxMBN" p =
    showR $ ((runWithPrec (prec p) $ realmax_bench max) :: CN MPBall)

  bench "sqrt1E" p =
    showR $ (sqrt_bench1 Sqrt.restr_sqrt :: CReal) ? (prec p)
  bench "sqrt1H" p =
    showR $ (sqrt_bench1 rsqrtH :: CReal) ? (prec p)
  bench "sqrt1N" p =
    showR $ (sqrt_bench1 sqrt :: CReal) ? (prec p)
  bench "sqrt1MBE" p =
    showR $ (runWithPrec (prec p) $ sqrt_bench1 SqrtMB.restr_sqrt)
  bench "sqrt1MBH" p =
    showR $ (runWithPrec (prec p) $ sqrt_bench1 rsqrtH)
  bench "sqrt1MBN" p =
    showR $ ((runWithPrec (prec p) $ sqrt_bench1 sqrt) :: CN MPBall)

  bench "sqrt2E" p =
    showR $ (sqrt_bench2 Sqrt.restr_sqrt :: CReal) ? (prec p)
  bench "sqrt2H" p =
    showR $ (sqrt_bench2 rsqrtH :: CReal) ? (prec p)
  bench "sqrt2N" p =
    showR $ (sqrt_bench2 sqrt :: CReal) ? (prec p)
  bench "sqrt2MBE" p =
    showR $ (runWithPrec (prec p) $ sqrt_bench2 SqrtMB.restr_sqrt)
  bench "sqrt2MBH" p =
    showR $ (runWithPrec (prec p) $ sqrt_bench2 rsqrtH)
  bench "sqrt2MBN" p =
    showR $ ((runWithPrec (prec p) $ sqrt_bench2 sqrt) :: CN MPBall)

  bench "civt1E" p =
    showR $ (civt_bench1 IVT.cIVT :: CReal) ? (prec p)
  bench "civt2E" p =
    showR $ (civt_bench2 IVT.cIVT :: CReal) ? (prec p)
  bench "civt3E" p =
    showR $ (civt_bench3 IVT.cIVT Sqrt.restr_sqrt :: CReal) ? (prec p)
  bench "civt1H" p =
    showR $ (civt_bench1 civtH :: CReal) ? (prec p)
  bench "civt2H" p =
    showR $ (civt_bench2 civtH :: CReal) ? (prec p)
  bench "civt3H" p =
    showR $ (civt_bench3 civtH Sqrt.restr_sqrt :: CReal) ? (prec p)
  bench "civt1MBE" p =
    showR $ (runWithPrec (prec p) $ civt_bench1 IVTMB.cIVT)
  bench "civt2MBE" p =
    showR $ (runWithPrec (prec p) $ civt_bench2 IVTMB.cIVT)
  bench "civt3MBE" p =
    showR $ (runWithPrec (prec p) $ civt_bench3 IVTMB.cIVT SqrtMB.restr_sqrt)
  bench "civt1MBH" p =
    showR $ (runWithPrec (prec p) $ civt_bench1 civtH)
  bench "civt2MBH" p =
    showR $ (runWithPrec (prec p) $ civt_bench2 civtH)
  bench "civt3MBH" p =
    showR $ (runWithPrec (prec p) $ civt_bench3 civtH rsqrtH)

  bench name _p = 
    error $ "unrecognised benchmark name: " <> name
  showR :: CN MPBall -> String
  showR b =
    show b <> "\naccuracy: " <> show (getAccuracy b)

-- suite :: [Benchmark]
-- suite = [
--     bgroup "Max" [
--       bench "CReal (extracted)" $ nf (? (prec 1100000)) (realmax_bench Max.realmax :: CReal)
--     , bench "CReal (by hand)" $ nf (? (prec 1100000)) (realmax_bench maxH :: CReal)
--     , bench "CReal (native)" $ nf (? (prec 1100000)) (realmax_bench MxP.max :: CReal) 
--     ]
--   ]

-- main :: IO ()
-- main = defaultMain $ suite
