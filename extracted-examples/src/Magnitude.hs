{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Magnitude where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

import MixedTypesNumPrelude (ifThenElse)
import qualified Numeric.OrdGenericBool as OGB
import qualified Unsafe.Coerce as UC
import qualified Control.Monad
import qualified Data.Functor
import qualified MixedTypesNumPrelude as MNP
import qualified Math.NumberTheory.Logarithms as Logs
import qualified AERN2.Real as AERN2

__uc :: a -> b
__uc = UC.unsafeCoerce
__K :: a -> AERN2.CKleenean
__K = UC.unsafeCoerce
__R :: a -> AERN2.CReal
__R = UC.unsafeCoerce

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
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

type Is_equiv a b = (b -> a)

data LazyBool lB =
   Build_LazyBool lB lB (lB -> lB) (lB -> lB -> lB) (lB -> lB -> lB) 
 (lB -> () -> Prelude.Bool)

data Monad m =
   Build_Monad (() -> () -> (Any -> Any) -> m -> m) (() -> Any -> m) 
 (() -> m -> m)

monad_fun_map :: (Monad a1) -> (a2 -> a3) -> a1 -> a1
monad_fun_map monad x x0 =
  case monad of {
   Build_Monad monad_fun_map0 _ _ -> unsafeCoerce monad_fun_map0 __ __ x x0}

monad_mult :: (Monad a1) -> a1 -> a1
monad_mult monad x =
  case monad of {
   Build_Monad _ _ monad_mult0 -> monad_mult0 __ x}

type Monoid_hom f g =
  () -> f -> g
  -- singleton inductive, whose constructor was Build_Monoid_hom
  
type NPset x = ()

type Lifts_lifted_trace m =
  () -> () -> m -> (Prelude.Integer -> Any -> m) -> m

data MultivalueMonad k m =
   Build_MultivalueMonad (() -> () -> Is_equiv Any m) (Lifts_lifted_trace m) 
 (k -> k -> () -> m) (() -> Is_equiv m m) (() -> m -> m)

multivalued_choice :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2
                      (NPset Any)) -> (MultivalueMonad a1 a2) -> a1 -> a1 ->
                      a2
multivalued_choice _ _ _ multivalueMonad x y =
  case multivalueMonad of {
   Build_MultivalueMonad _ _ multivalued_choice0 _ _ ->
    multivalued_choice0 x y __}

m_lift :: (Monad a1) -> (a2 -> a3) -> a1 -> a1
m_lift =
  monad_fun_map

m_mult :: (Monad a1) -> a1 -> a1
m_mult =
  monad_mult

m_lift_dom :: (Monad a1) -> (a2 -> a1) -> a1 -> a1
m_lift_dom m_Monad0 f x =
  m_mult m_Monad0 (m_lift m_Monad0 f x)

m_countable_lift :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2
                    (NPset Any)) -> (MultivalueMonad a1 a2) ->
                    (Prelude.Integer -> a2) -> a2
m_countable_lift = (\_ _ _ _ f -> (__uc f))

select :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
          (MultivalueMonad a1 a2) -> a1 -> a1 -> a2
select =
  multivalued_choice

mjoin :: (Monad a1) -> (Prelude.Bool -> a2) -> a1 -> a1
mjoin =
  monad_fun_map

type Semidec k = k

choose :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
          (MultivalueMonad a1 a2) -> (Semidec a1) -> (Semidec a1) -> a2
choose klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 x x0 =
  monad_fun_map m_Monad0 (\h4 -> h4)
    (select klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 x
      x0)

data SemiDecOrderedField k real =
   Build_SemiDecOrderedField real real (real -> real -> real) (real -> real
                                                              -> real) 
 (real -> real) (real -> () -> real) (real -> real -> Semidec k)

real_inv :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2
real_inv _ semiDecOrderedField z =
  case semiDecOrderedField of {
   Build_SemiDecOrderedField _ _ _ _ _ real_inv0 _ -> real_inv0 z __}

real_lt_semidec :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2
                   -> Semidec a1
real_lt_semidec _ semiDecOrderedField =
  case semiDecOrderedField of {
   Build_SemiDecOrderedField _ _ _ _ _ _ real_lt_semidec0 -> real_lt_semidec0}

real_minus :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2 -> a2
real_minus = (\_ _ x y -> __uc (((__R x) Prelude.- (__R y))))

real_div :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2 -> a2
real_div = (\_ _ x y -> __uc (((__R x) Prelude./ (__R y))))

iZreal :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> Prelude.Integer ->
          a2
iZreal = (\_ _ z -> __uc (AERN2.creal z))

real_2 :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2
real_2 klb semiDecOrderedField_Real =
  iZreal klb semiDecOrderedField_Real ((\x -> x) ((\x -> 2 Prelude.* x) 1))

prec :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> Prelude.Integer -> a2
prec = (\_ _ n -> __uc ((0.5 :: AERN2.CReal) Prelude.^ n))

linear_search :: (Prelude.Integer -> Prelude.Bool) -> Prelude.Integer ->
                 Prelude.Integer
linear_search p_dec m =
  case p_dec m of {
   Prelude.True -> m;
   Prelude.False -> linear_search p_dec (Prelude.succ m)}

epsilon_smallest :: (Prelude.Integer -> Prelude.Bool) -> Prelude.Integer
epsilon_smallest p_dec =
  linear_search p_dec 0

m_split :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
           (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) -> a3 -> a3
           -> a3 -> a2
m_split klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real x y _UU03b5_ =
  choose klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
    (real_lt_semidec klb semiDecOrderedField_Real
      (real_minus klb semiDecOrderedField_Real y _UU03b5_) x)
    (real_lt_semidec klb semiDecOrderedField_Real
      (real_minus klb semiDecOrderedField_Real x _UU03b5_) y)

ssr_have :: a1 -> (a1 -> a2) -> a2
ssr_have step rest =
  rest step

ssr_suff :: (a1 -> a2) -> a1 -> a2
ssr_suff step =
  step

epsilon_smallest_PQ :: (Prelude.Integer -> Prelude.Bool) -> Prelude.Integer
epsilon_smallest_PQ =
  epsilon_smallest

epsilon_smallest_PQ_M :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2
                         (NPset Any)) -> (MultivalueMonad a1 a2) ->
                         (Prelude.Integer -> a2) -> a2
epsilon_smallest_PQ_M klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 x =
  let {
   x0 = m_countable_lift klb m_Monad0 multivalueMonad_description0
          m_MultivalueMonad0 x}
  in
  m_lift m_Monad0 epsilon_smallest_PQ x0

epsilon_smallest_choose_M :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom 
                             a2 (NPset Any)) -> (MultivalueMonad a1 a2) ->
                             (Prelude.Integer -> a2) -> a2
epsilon_smallest_choose_M =
  epsilon_smallest_PQ_M

weaken_orM_r :: (Monad a1) -> a1 -> a1
weaken_orM_r m_Monad0 =
  m_lift m_Monad0 (\__top_assumption_ ->
    let {_evar_0_ = \_ -> Prelude.True} in
    let {_evar_0_0 = \_ -> Prelude.False} in
    case __top_assumption_ of {
     Prelude.True -> _evar_0_ __;
     Prelude.False -> _evar_0_0 __})

magnitude1 :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
              (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) -> a3 ->
              a2
magnitude1 klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real x =
  ssr_have __ (\_ ->
    ssr_suff (\g1M -> m_lift m_Monad0 (\g1 -> g1) g1M)
      (epsilon_smallest_choose_M klb m_Monad0 multivalueMonad_description0
        m_MultivalueMonad0 (\n ->
        weaken_orM_r m_Monad0
          (choose klb m_Monad0 multivalueMonad_description0
            m_MultivalueMonad0
            (real_lt_semidec klb semiDecOrderedField_Real
              (prec klb semiDecOrderedField_Real (Prelude.succ (Prelude.succ
                n))) x)
            (real_lt_semidec klb semiDecOrderedField_Real x
              (prec klb semiDecOrderedField_Real (Prelude.succ n)))))))

dec_x_lt_2 :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
              (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) -> a3 ->
              a2
dec_x_lt_2 klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real x =
  let {
   h = m_split klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
         semiDecOrderedField_Real x
         (real_div klb semiDecOrderedField_Real
           (iZreal klb semiDecOrderedField_Real ((\x -> x)
             ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))
           (real_2 klb semiDecOrderedField_Real))
         (real_inv klb semiDecOrderedField_Real
           (real_2 klb semiDecOrderedField_Real))}
  in
  mjoin m_Monad0 (\h0 ->
    case h0 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}) h

magnitude2 :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
              (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) -> a3 ->
              a2
magnitude2 klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real x =
  let {
   y = real_div klb semiDecOrderedField_Real x
         (iZreal klb semiDecOrderedField_Real ((\x -> x)
           ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))}
  in
  ssr_have __ (\_ ->
    ssr_have __ (\_ ->
      ssr_suff
        (m_lift m_Monad0 (\_top_assumption_ ->
          (Prelude.+) _top_assumption_ ((\x -> x) ((\x -> 2 Prelude.* x) 1))))
        (ssr_have
          (magnitude1 klb m_Monad0 multivalueMonad_description0
            m_MultivalueMonad0 semiDecOrderedField_Real y)
          (m_lift m_Monad0 (\_top_assumption_ ->
            opp (of_nat _top_assumption_))))))

magnitude :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
             (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) -> a3 ->
             a2
magnitude klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real x =
  ssr_have
    (dec_x_lt_2 klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
      semiDecOrderedField_Real x)
    (m_lift_dom m_Monad0 (\_top_assumption_ ->
      let {
       _evar_0_ = \_ ->
        magnitude2 klb m_Monad0 multivalueMonad_description0
          m_MultivalueMonad0 semiDecOrderedField_Real x}
      in
      let {
       _evar_0_0 = \_ ->
        ssr_have __ (\_ ->
          ssr_have
            (magnitude2 klb m_Monad0 multivalueMonad_description0
              m_MultivalueMonad0 semiDecOrderedField_Real
              (real_inv klb semiDecOrderedField_Real x))
            (m_lift m_Monad0 (\_top_assumption_0 ->
              (Prelude.+) (opp _top_assumption_0) ((\x -> x)
                ((\x -> 2 Prelude.* x) 1)))))}
      in
      case _top_assumption_ of {
       Prelude.True -> _evar_0_ __;
       Prelude.False -> _evar_0_0 __}))

k_LazyBool :: LazyBool AERN2.CKleenean
k_LazyBool = Build_LazyBool (AERN2.ckleenean Prelude.True) (AERN2.ckleenean Prelude.False) OGB.not (OGB.||) (OGB.&&) (\k _ -> Prelude.error "UNREALIZED lazy_bool_defined_is_bool")

type M a = a

m_Monad :: Monad (M Any)
m_Monad = Build_Monad (\ _ _ f -> __uc f) (\_ a -> __uc a) (\ _ m -> m)

multivalueMonad_description :: Monoid_hom (M Any) (NPset Any)
multivalueMonad_description = (Prelude.error "UNREALIZED MultivalueMonad_description")

m_MultivalueMonad :: MultivalueMonad AERN2.CKleenean (M Any)
m_MultivalueMonad = Build_MultivalueMonad (\ _ _ x -> __uc x) (\ _ _ x0 f -> __uc (\n -> Prelude.foldl (Prelude.flip (__uc f)) (x0) [0 .. ((n :: Prelude.Integer) Prelude.- 1)])) (\k1 k2 _ -> __uc (AERN2.select k1 k2)) (\ _ m -> m) (\ _ m -> m)

r_SemiDecOrderedField :: SemiDecOrderedField AERN2.CKleenean AERN2.CReal
r_SemiDecOrderedField = Build_SemiDecOrderedField 0 1 (Prelude.+) (Prelude.*) Prelude.negate (\ x _ -> Prelude.recip x) (OGB.<)

r_magnitude :: AERN2.CReal -> M Prelude.Integer
r_magnitude x =
  magnitude k_LazyBool (unsafeCoerce m_Monad)
    (unsafeCoerce multivalueMonad_description)
    (unsafeCoerce m_MultivalueMonad) r_SemiDecOrderedField x

