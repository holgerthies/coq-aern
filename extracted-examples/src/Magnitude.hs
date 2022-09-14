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

type Sig a = a
  -- singleton inductive, whose constructor was exist

type M a = a

multivalued_choice :: AERN2.CKleenean -> AERN2.CKleenean -> M P.Bool
multivalued_choice = AERN2.select

m_lift :: (a1 -> a2) -> (M a1) -> M a2
m_lift = P.id

m_lift_dom :: (a1 -> M a2) -> (M a1) -> M a2
m_lift_dom = P.id

m_countable_lift :: (Prelude.Integer -> M a1) -> M (Prelude.Integer -> a1)
m_countable_lift = P.id

select :: AERN2.CKleenean -> AERN2.CKleenean -> M P.Bool
select =
  multivalued_choice

mjoin :: (P.Bool -> a1) -> (M P.Bool) -> M a1
mjoin = P.id

type Semidec = AERN2.CKleenean

choose :: Semidec -> Semidec -> M P.Bool
choose x x0 =
  m_lift (\h4 -> h4) (select x x0)

iZreal :: Prelude.Integer -> AERN2.CReal
iZreal = AERN2.creal

prec :: Prelude.Integer -> AERN2.CReal
prec = ((0.5 :: AERN2.CReal) P.^)

linear_search_conform :: (Prelude.Integer -> P.Bool) -> Prelude.Integer ->
                         Prelude.Integer
linear_search_conform p_dec start =
  case p_dec start of {
   P.True -> start;
   P.False -> linear_search_conform p_dec (Prelude.succ start)}

linear_search_from_0_conform :: (Prelude.Integer -> P.Bool) ->
                                Prelude.Integer
linear_search_from_0_conform p_dec =
  linear_search_conform p_dec 0

epsilon_smallest :: (Prelude.Integer -> P.Bool) -> Prelude.Integer
epsilon_smallest =
  linear_search_from_0_conform

m_split :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal -> M P.Bool
m_split x y _UU03b5_ =
  choose ((OGB.<) ((-) y _UU03b5_) x) ((OGB.<) ((-) x _UU03b5_) y)

ssr_have :: a1 -> (a1 -> a2) -> a2
ssr_have step rest =
  rest step

ssr_suff :: (a1 -> a2) -> a1 -> a2
ssr_suff step =
  step

epsilon_smallest_PQ :: (Prelude.Integer -> P.Bool) -> Prelude.Integer
epsilon_smallest_PQ =
  epsilon_smallest

epsilon_smallest_PQ_M :: (Prelude.Integer -> M P.Bool) -> M Prelude.Integer
epsilon_smallest_PQ_M x =
  let {x0 = m_countable_lift x} in m_lift epsilon_smallest_PQ x0

epsilon_smallest_choose_M :: (Prelude.Integer -> M P.Bool) -> M
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
          (choose ((OGB.<) (prec (Prelude.succ (Prelude.succ n))) x)
            ((OGB.<) x (prec (Prelude.succ n)))))))

dec_x_lt_2 :: AERN2.CReal -> M P.Bool
dec_x_lt_2 x =
  let {
   h = m_split x ((/) (iZreal 3) (2 :: AERN2.CReal))
         (P.recip (2 :: AERN2.CReal))}
  in
  mjoin (\h0 -> case h0 of {
                 P.True -> P.False;
                 P.False -> P.True}) h

magnitude2 :: AERN2.CReal -> M Prelude.Integer
magnitude2 x =
  let {y = (/) x (iZreal 4)} in
  ssr_have __ (\_ ->
    ssr_have __ (\_ ->
      ssr_suff (m_lift (\_top_assumption_ -> (P.+) _top_assumption_ 2))
        (ssr_have (magnitude1 y)
          (m_lift (\_top_assumption_ -> P.negate (P.id _top_assumption_))))))

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
              (P.+) (P.negate _top_assumption_0) 2)))}
      in
      case _top_assumption_ of {
       P.True -> _evar_0_ __;
       P.False -> _evar_0_0 __}))

