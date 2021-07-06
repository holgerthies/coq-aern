{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
module MagnitudeMB where

import qualified Prelude
import Prelude hiding (pred, succ, (==),(/=),(<),(<=),(>),(>=),not,(&&),(||))
import Control.Monad (join)
import Numeric.OrdGenericBool
import MixedTypesNumPrelude (ifThenElse, integer, Kleenean(..), kleenean)
import Math.NumberTheory.Logarithms (integerLog2)
import Numeric.CollectErrors (CN,cn,liftTakeErrors)
import AERN2.MP
import AERN2.MP.Dyadic ()
import AERN2.MP.WithCurrentPrec
import AERN2.Real hiding (pi)

__ :: any
__ = Prelude.error "Logical or arity value used"

type Sig a = a
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

add :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
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
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add p q))
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

add_carry :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
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
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (succ q))
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
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) (pred_double p))
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
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) p))
    (\p -> Prelude.negate (pred_double p))
    x

pred_double0 :: Prelude.Integer -> Prelude.Integer
pred_double0 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Prelude.negate 1)
    (\p -> (\x -> x) (pred_double p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x Prelude.+ 1) p))
    x

pos_sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
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
      (\q -> Prelude.negate ((\x -> 2 Prelude.* x) q))
      (\q -> Prelude.negate (pred_double q))
      (\_ -> 0)
      y)
    x

opp :: Prelude.Integer -> Prelude.Integer
opp x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\x0 -> Prelude.negate x0)
    (\x0 -> (\x -> x) x0)
    x

of_nat :: Prelude.Integer -> Prelude.Integer
of_nat n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n0 -> (\x -> x) (of_succ_nat n0))
    n

type M a =  CN a 

lift_domM :: (a1 -> M a2) -> (M a1) -> M a2
lift_domM f x =
  join (Prelude.fmap f x)

type Semidec = Kleenean

iPReal_2 :: (HasCurrentPrecision p) => Prelude.Integer -> (WithCurrentPrec (CN MPBall) p)
iPReal_2 p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> (*) ((+) 1 1) ((+) 1 (iPReal_2 p0)))
    (\p0 -> (*) ((+) 1 1) (iPReal_2 p0))
    (\_ -> (+) 1 1)
    p

iPReal :: (HasCurrentPrecision p) => Prelude.Integer -> (WithCurrentPrec (CN MPBall) p)
iPReal p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> (+) 1 (iPReal_2 p0))
    (\p0 -> iPReal_2 p0)
    (\_ -> 1)
    p

iZReal :: (HasCurrentPrecision p) => Prelude.Integer -> (WithCurrentPrec (CN MPBall) p)
iZReal z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\n -> iPReal n)
    (\n -> negate (iPReal n))
    z

m_split :: (HasCurrentPrecision p) => (WithCurrentPrec (CN MPBall) p) -> (WithCurrentPrec (CN MPBall) p)
           -> (WithCurrentPrec (CN MPBall) p) -> M Bool
m_split x y _UU03b5_ =
  select ((>) x ((-) y _UU03b5_)) ((>) y ((-) x _UU03b5_))

ssr_have :: a1 -> (a1 -> a2) -> a2
ssr_have step rest =
  rest step

ssr_suff :: (a1 -> a2) -> a1 -> a2
ssr_suff step =
  step

mjoinM :: (Bool -> M a1) -> (M Bool) -> M a1
mjoinM =
  lift_domM

linear_search_min_choose :: (Prelude.Integer -> M Bool) -> Prelude.Integer ->
                            M Prelude.Integer
linear_search_min_choose p_decM m =
  mjoinM (\p_dec ->
    case p_dec of {
     True -> cn (Prelude.succ m);
     False -> linear_search_min_choose p_decM (Prelude.succ m)})
    (p_decM (Prelude.succ (Prelude.succ m)))

constructive_search_min_choose_nat :: (Prelude.Integer -> M Bool) -> M
                                      Prelude.Integer
constructive_search_min_choose_nat p_decM =
  linear_search_min_choose p_decM 0

weaken_orM_r :: (M Bool) -> M Bool
weaken_orM_r =
  Prelude.fmap (\__top_assumption_ ->
    let {_evar_0_ = \_ -> True} in
    let {_evar_0_0 = \_ -> False} in
    case __top_assumption_ of {
     True -> _evar_0_ __;
     False -> _evar_0_0 __})

magnitude1 :: (HasCurrentPrecision p) => (WithCurrentPrec (CN MPBall) p) -> M Prelude.Integer
magnitude1 x =
  constructive_search_min_choose_nat (\n ->
    weaken_orM_r
      (select ((<) ((0.5^) (Prelude.succ n)) x) ((<) x ((0.5^) n))))

dec_x_lt_2 :: (HasCurrentPrecision p) => (WithCurrentPrec (CN MPBall) p) -> M Bool
dec_x_lt_2 x =
  ssr_have
    (m_split x
      ((/) (iZReal ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))) 2)
      (recip 2))
    (Prelude.fmap (\_top_assumption_ ->
      let {_evar_0_ = \_ -> False} in
      let {_evar_0_0 = \_ -> True} in
      case _top_assumption_ of {
       True -> _evar_0_ __;
       False -> _evar_0_0 __}))

magnitude2 :: (HasCurrentPrecision p) => (WithCurrentPrec (CN MPBall) p) -> M Prelude.Integer
magnitude2 x =
  let {
   y = (/) x
         (iZReal ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
           1))))}
  in
  ssr_have __ (\_ ->
    ssr_have __ (\_ ->
      ssr_suff
        (Prelude.fmap (\_top_assumption_ ->
          (Prelude.+) _top_assumption_ ((\x -> x) ((\x -> 2 Prelude.* x) 1))))
        (ssr_have (magnitude1 y)
          (Prelude.fmap (\_top_assumption_ -> opp (of_nat _top_assumption_))))))

magnitude :: (HasCurrentPrecision p) => (WithCurrentPrec (CN MPBall) p) -> M Prelude.Integer
magnitude x =
  ssr_have (dec_x_lt_2 x)
    (mjoinM (\_top_assumption_ ->
      let {_evar_0_ = \_ -> magnitude2 x} in
      let {
       _evar_0_0 = \_ ->
        ssr_have __ (\_ ->
          ssr_suff (\_ ->
            ssr_have (magnitude2 (recip x))
              (Prelude.fmap (\_top_assumption_0 ->
                (Prelude.+) (opp _top_assumption_0) ((\x -> x)
                  ((\x -> 2 Prelude.* x) 1))))) __)}
      in
      case _top_assumption_ of {
       True -> _evar_0_ __;
       False -> _evar_0_0 __}))

