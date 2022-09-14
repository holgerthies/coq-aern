{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Magnitude where

import qualified Prelude
import Prelude ((+),(-),(/))
import qualified Prelude as P
import MixedTypesNumPrelude (ifThenElse)
import qualified Numeric.OrdGenericBool as OGB
import qualified Unsafe.Coerce as UC
import qualified Control.Monad
import qualified Data.Functor
import qualified MixedTypesNumPrelude as MNP
import qualified Math.NumberTheory.Logarithms as Logs
import qualified AERN2.Real as AERN2

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
succ :: Prelude.Integer -> Prelude.Integer
succ x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x) (succ p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) p)
    (\_ -> (\x -> 2 Prelude.* x) 1)
    x

add :: Prelude.Integer -> Prelude.Integer ->
       Prelude.Integer
add x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add p q))
      (\q -> (\x -> 2 Prelude.* x) (add p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) p)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (succ q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) q)
      (\_ -> (\x -> 2 Prelude.* x) 1)
      y)
    x

add_carry :: Prelude.Integer -> Prelude.Integer ->
             Prelude.Integer
add_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (succ q))
      (\q -> (\x -> 2 Prelude.* x) (succ q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) 1)
      y)
    x

pred_double :: Prelude.Integer -> Prelude.Integer
pred_double x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1)
    ((\x -> 2 Prelude.* x) p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1)
    (pred_double p))
    (\_ -> 1)
    x

of_succ_nat :: Prelude.Integer -> Prelude.Integer
of_succ_nat n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 1)
    (\x -> succ (of_succ_nat x))
    n

double :: Prelude.Integer -> Prelude.Integer
double x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x) p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x) p))
    x

succ_double :: Prelude.Integer -> Prelude.Integer
succ_double x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (\x -> x) 1)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
    p))
    (\p -> Prelude.negate (pred_double p))
    x

pred_double0 :: Prelude.Integer -> Prelude.Integer
pred_double0 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Prelude.negate 1)
    (\p -> (\x -> x) (pred_double p))
    (\p -> Prelude.negate
    ((\x -> 2 Prelude.* x Prelude.+ 1) p))
    x

pos_sub :: Prelude.Integer -> Prelude.Integer ->
           Prelude.Integer
pos_sub x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> double (pos_sub p q))
      (\q -> succ_double (pos_sub p q))
      (\_ -> (\x -> x) ((\x -> 2 Prelude.* x) p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> pred_double0 (pos_sub p q))
      (\q -> double (pos_sub p q))
      (\_ -> (\x -> x) (pred_double p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> Prelude.negate ((\x -> 2 Prelude.* x)
      q))
      (\q -> Prelude.negate (pred_double q))
      (\_ -> 0)
      y)
    x

type M a = a

z2 :: Prelude.Integer
z2 = 2

z3 :: Prelude.Integer
z3 = 3

z4 :: Prelude.Integer
z4 = 4

m_lift :: (a1 -> a2) -> (M a1) -> M a2
m_lift = P.id

m_lift_dom :: (a1 -> M a2) -> (M a1) -> M a2
m_lift_dom = P.id

m_countable_lift :: (Prelude.Integer -> M a1) -> M
                    (Prelude.Integer -> a1)
m_countable_lift = P.id

mjoin :: (P.Bool -> a1) -> (M P.Bool) -> M a1
mjoin = P.id

type Semidec = AERN2.CKleenean

choose :: Semidec -> Semidec -> M P.Bool
choose = AERN2.select

iZreal :: Prelude.Integer -> AERN2.CReal
iZreal = AERN2.creal

real_2 :: AERN2.CReal
real_2 = 2

prec :: Prelude.Integer -> AERN2.CReal
prec = ((0.5 :: AERN2.CReal) P.^)

linear_search_conform :: (Prelude.Integer -> P.Bool) ->
                         Prelude.Integer ->
                         Prelude.Integer
linear_search_conform p_dec start =
  case p_dec start of {
   P.True -> start;
   P.False ->
    linear_search_conform p_dec (Prelude.succ start)}

linear_search_from_0_conform :: (Prelude.Integer ->
                                P.Bool) ->
                                Prelude.Integer
linear_search_from_0_conform p_dec =
  linear_search_conform p_dec 0

epsilon_smallest :: (Prelude.Integer -> P.Bool) ->
                    Prelude.Integer
epsilon_smallest =
  linear_search_from_0_conform

m_split :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal ->
           M P.Bool
m_split x y _UU03b5_ =
  choose ((OGB.<) ((-) y _UU03b5_) x)
    ((OGB.<) ((-) x _UU03b5_) y)

ssr_have :: a1 -> (a1 -> a2) -> a2
ssr_have step rest =
  rest step

ssr_suff :: (a1 -> a2) -> a1 -> a2
ssr_suff step =
  step

epsilon_smallest_PQ :: (Prelude.Integer -> P.Bool) ->
                       Prelude.Integer
epsilon_smallest_PQ =
  epsilon_smallest

epsilon_smallest_PQ_M :: (Prelude.Integer -> M 
                         P.Bool) -> M Prelude.Integer
epsilon_smallest_PQ_M x =
  let {x0 = m_countable_lift x} in
  m_lift epsilon_smallest_PQ x0

epsilon_smallest_choose_M :: (Prelude.Integer -> M
                             P.Bool) -> M
                             Prelude.Integer
epsilon_smallest_choose_M =
  epsilon_smallest_PQ_M

weaken_orM_r :: (M P.Bool) -> M P.Bool
weaken_orM_r =
  m_lift (\__top_assumption_ ->
    let {_evar_0_ = \_ -> P.True} in
    let {_evar_0_0 = \_ -> P.False} in
    case __top_assumption_ of {
     P.True -> _evar_0_ __;
     P.False -> _evar_0_0 __})

magnitude1 :: AERN2.CReal -> M Prelude.Integer
magnitude1 x =
  ssr_have __ (\_ ->
    ssr_suff (\g1M -> m_lift (\g1 -> g1) g1M)
      (epsilon_smallest_choose_M (\n ->
        weaken_orM_r
          (choose
            ((OGB.<)
              (prec (Prelude.succ (Prelude.succ n))) x)
            ((OGB.<) x (prec (Prelude.succ n)))))))

dec_x_lt_2 :: AERN2.CReal -> M P.Bool
dec_x_lt_2 x =
  let {
   h = m_split x ((/) (iZreal z3) real_2)
         (P.recip real_2)}
  in
  mjoin (\h0 ->
    case h0 of {
     P.True -> P.False;
     P.False -> P.True}) h

magnitude2 :: AERN2.CReal -> M Prelude.Integer
magnitude2 x =
  let {y = (/) x (iZreal z4)} in
  ssr_have __ (\_ ->
    ssr_have __ (\_ ->
      ssr_suff
        (m_lift (\_top_assumption_ ->
          (P.+) _top_assumption_ z2))
        (ssr_have (magnitude1 y)
          (m_lift (\_top_assumption_ ->
            P.negate (P.id _top_assumption_))))))

magnitude :: AERN2.CReal -> M Prelude.Integer
magnitude x =
  ssr_have (dec_x_lt_2 x)
    (m_lift_dom (\_top_assumption_ ->
      let {_evar_0_ = \_ -> magnitude2 x} in
      let {
       _evar_0_0 = \_ ->
        ssr_have __ (\_ ->
          ssr_have (magnitude2 (P.recip x))
            (m_lift (\_top_assumption_0 ->
              (P.+) (P.negate _top_assumption_0) z2)))}
      in
      case _top_assumption_ of {
       P.True -> _evar_0_ __;
       P.False -> _evar_0_0 __}))

