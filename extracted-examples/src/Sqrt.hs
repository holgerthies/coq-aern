module Sqrt where

import qualified Prelude
import Prelude hiding (pred, succ, (==),(/=),(<),(<=),(>),(>=),not,(&&),(||))
import Numeric.OrdGenericBool
import MixedTypesNumPrelude (ifThenElse, integer)
import Math.NumberTheory.Logarithms (integerLog2)
import AERN2.Real

__ :: any
__ = Prelude.error "Logical or arity value used"

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

nat_rec :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rec =
  nat_rect

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
pred :: Prelude.Integer -> Prelude.Integer
pred = (\n -> Prelude.max 0 (Prelude.pred n))

log2_iter :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
             Prelude.Integer -> Prelude.Integer
log2_iter k p q r =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> p)
    (\k' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> log2_iter k' (Prelude.succ p) (Prelude.succ q) q)
      (\r' -> log2_iter k' p (Prelude.succ q) r')
      r)
    k

ssr_have :: a1 -> (a1 -> a2) -> a2
ssr_have step rest =
  rest step

ssr_suff :: (a1 -> a2) -> a1 -> a2
ssr_suff step =
  step

sqrt_approx :: CReal -> Prelude.Integer -> CReal
sqrt_approx x n =
  ssr_suff (\__top_assumption_ -> __top_assumption_)
    (nat_rec 1 (\_ __top_assumption_ ->
      ssr_have __ (\_ ->
        (*) (recip 2) ((+) __top_assumption_ ((/) x __top_assumption_)))) n)

sqrt_approx_fast :: CReal -> Prelude.Integer -> CReal
sqrt_approx_fast x n =
  ssr_have
    (sqrt_approx x (Prelude.succ ((integer . integerLog2) (Prelude.succ n))))
    (\__top_assumption_ -> __top_assumption_)

restr_sqrt :: CReal -> CReal
restr_sqrt x =
  ssr_have __ (\_ ->
    limit (\n ->
      ssr_have (sqrt_approx_fast x n) (\__top_assumption_ ->
        __top_assumption_)))

