{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module IVT where

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

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
type Is_equiv a b = (b -> a)

projP1 :: a1 -> a1
projP1 x =
  x

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

monad_unit :: (Monad a1) -> a2 -> a1
monad_unit monad x =
  case monad of {
   Build_Monad _ monad_unit0 _ -> unsafeCoerce monad_unit0 __ x}

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

multivalueMonad_base_monad_hprop_elim :: (LazyBool a1) -> (Monad a2) ->
                                         (Monoid_hom a2 (NPset Any)) ->
                                         (MultivalueMonad a1 a2) -> Is_equiv
                                         a3 a2
multivalueMonad_base_monad_hprop_elim _ _ _ multivalueMonad =
  case multivalueMonad of {
   Build_MultivalueMonad multivalueMonad_base_monad_hprop_elim0 _ _ _ _ ->
    unsafeCoerce multivalueMonad_base_monad_hprop_elim0 __ __}

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

m_unit :: (Monad a1) -> a2 -> a1
m_unit =
  monad_unit

m_mult :: (Monad a1) -> a1 -> a1
m_mult =
  monad_mult

m_lift_dom :: (Monad a1) -> (a2 -> a1) -> a1 -> a1
m_lift_dom m_Monad0 f x =
  m_mult m_Monad0 (m_lift m_Monad0 f x)

m_hprop_elim_f :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any))
                  -> (MultivalueMonad a1 a2) -> a2 -> a3
m_hprop_elim_f klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 x =
  projP1
    (multivalueMonad_base_monad_hprop_elim klb m_Monad0
      multivalueMonad_description0 m_MultivalueMonad0) x

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

real_0 :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2
real_0 _ semiDecOrderedField =
  case semiDecOrderedField of {
   Build_SemiDecOrderedField real_4 _ _ _ _ _ _ -> real_4}

real_1 :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2
real_1 _ semiDecOrderedField =
  case semiDecOrderedField of {
   Build_SemiDecOrderedField _ real_4 _ _ _ _ _ -> real_4}

real_plus :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2 -> a2
real_plus _ semiDecOrderedField =
  case semiDecOrderedField of {
   Build_SemiDecOrderedField _ _ real_plus0 _ _ _ _ -> real_plus0}

real_mult :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2 -> a2
real_mult _ semiDecOrderedField =
  case semiDecOrderedField of {
   Build_SemiDecOrderedField _ _ _ real_mult0 _ _ _ -> real_mult0}

real_lt_semidec :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2
                   -> Semidec a1
real_lt_semidec _ semiDecOrderedField =
  case semiDecOrderedField of {
   Build_SemiDecOrderedField _ _ _ _ _ _ real_lt_semidec0 -> real_lt_semidec0}

real_div :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2 -> a2
real_div = (\_ _ x y -> __uc (((__R x) Prelude./ (__R y))))

iZreal :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> Prelude.Integer ->
          a2
iZreal = (\_ _ z -> __uc (AERN2.creal z))

real_2 :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2
real_2 klb semiDecOrderedField_Real =
  iZreal klb semiDecOrderedField_Real ((\x -> x) ((\x -> 2 Prelude.* x) 1))

type ComplArchiSemiDecOrderedField k real =
  (Prelude.Integer -> real) -> () -> real
  -- singleton inductive, whose constructor was Build_ComplArchiSemiDecOrderedField
  
real_limit_p :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) ->
                (ComplArchiSemiDecOrderedField a1 a2) -> (Prelude.Integer ->
                a2) -> a2
real_limit_p _ _ complArchiSemiDecOrderedField f =
  complArchiSemiDecOrderedField f __

real_limit_P_p :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) ->
                  (ComplArchiSemiDecOrderedField a1 a2) -> (Prelude.Integer
                  -> a2) -> a2
real_limit_P_p klb semiDecOrderedField_Real complArchiSemiDecOrderedField_Real p =
  projP1
    (real_limit_p klb semiDecOrderedField_Real
      complArchiSemiDecOrderedField_Real (\n -> projP1 (p n)))

real_limit_P :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
                (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
                (ComplArchiSemiDecOrderedField a1 a3) -> (Prelude.Integer ->
                a3) -> a3
real_limit_P klb _ _ _ semiDecOrderedField_Real complArchiSemiDecOrderedField_Real x =
  real_limit_P_p klb semiDecOrderedField_Real
    complArchiSemiDecOrderedField_Real x

real_mslimit_P :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any))
                  -> (MultivalueMonad a1 a2) -> (SemiDecOrderedField 
                  a1 a3) -> (ComplArchiSemiDecOrderedField a1 a3) ->
                  (Prelude.Integer -> a2) -> a3
real_mslimit_P klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real x =
  let {
   x0 = m_countable_lift klb m_Monad0 multivalueMonad_description0
          m_MultivalueMonad0 x}
  in
  m_hprop_elim_f klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
    (let {
      x1 = \h1 ->
       real_limit_P klb m_Monad0 multivalueMonad_description0
         m_MultivalueMonad0 semiDecOrderedField_Real
         complArchiSemiDecOrderedField_Real h1}
     in
     m_lift m_Monad0 x1 x0)

m_uniq_pick :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
               (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
               (ComplArchiSemiDecOrderedField a1 a3) -> (a3 -> a3) -> a3 ->
               a3 -> a3 -> a3 -> a2
m_uniq_pick klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real _ f _ b c _ =
  choose klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
    (real_lt_semidec klb semiDecOrderedField_Real (f b)
      (real_0 klb semiDecOrderedField_Real))
    (real_lt_semidec klb semiDecOrderedField_Real
      (real_0 klb semiDecOrderedField_Real) (f c))

real_3 :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2
real_3 klb semiDecOrderedField_Real =
  iZreal klb semiDecOrderedField_Real ((\x -> x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) 1))

trisect :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
           (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
           (ComplArchiSemiDecOrderedField a1 a3) -> (a3 -> a3) -> a3 -> a3 ->
           a2
trisect klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real f a b =
  mjoin m_Monad0 (\h0 ->
    case h0 of {
     Prelude.True -> (,)
      (real_div klb semiDecOrderedField_Real
        (real_plus klb semiDecOrderedField_Real
          (real_mult klb semiDecOrderedField_Real
            (real_2 klb semiDecOrderedField_Real) a) b)
        (real_3 klb semiDecOrderedField_Real)) b;
     Prelude.False -> (,) a
      (real_div klb semiDecOrderedField_Real
        (real_plus klb semiDecOrderedField_Real a
          (real_mult klb semiDecOrderedField_Real
            (real_2 klb semiDecOrderedField_Real) b))
        (real_3 klb semiDecOrderedField_Real))})
    (m_uniq_pick klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
      semiDecOrderedField_Real complArchiSemiDecOrderedField_Real f a
      (real_div klb semiDecOrderedField_Real
        (real_plus klb semiDecOrderedField_Real
          (real_mult klb semiDecOrderedField_Real
            (real_2 klb semiDecOrderedField_Real) a) b)
        (real_3 klb semiDecOrderedField_Real))
      (real_div klb semiDecOrderedField_Real
        (real_plus klb semiDecOrderedField_Real a
          (real_mult klb semiDecOrderedField_Real
            (real_2 klb semiDecOrderedField_Real) b))
        (real_3 klb semiDecOrderedField_Real)) b)

halving :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
           (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
           (ComplArchiSemiDecOrderedField a1 a3) -> (a3 -> a3) -> a3 -> a3 ->
           a2
halving klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real f a b =
  let {
   one = trisect klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
           semiDecOrderedField_Real complArchiSemiDecOrderedField_Real f a b}
  in
  m_lift_dom m_Monad0 (\q ->
    case q of {
     (,) x s ->
      let {
       x0 = trisect klb m_Monad0 multivalueMonad_description0
              m_MultivalueMonad0 semiDecOrderedField_Real
              complArchiSemiDecOrderedField_Real f x s}
      in
      m_lift m_Monad0 (\x1 -> case x1 of {
                               (,) x' s0 -> (,) x' s0}) x0}) one

root_approx :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
               (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
               (ComplArchiSemiDecOrderedField a1 a3) -> (a3 -> a3) ->
               Prelude.Integer -> a2
root_approx klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real f n =
  nat_rect
    (m_unit m_Monad0 ((,) (real_0 klb semiDecOrderedField_Real)
      (real_1 klb semiDecOrderedField_Real))) (\_ iHn ->
    m_lift_dom m_Monad0 (\x ->
      case x of {
       (,) x0 s ->
        let {
         x1 = halving klb m_Monad0 multivalueMonad_description0
                m_MultivalueMonad0 semiDecOrderedField_Real
                complArchiSemiDecOrderedField_Real f x0 s}
        in
        m_lift m_Monad0 (\x2 -> case x2 of {
                                 (,) x' s0 -> (,) x' s0}) x1}) iHn) n

cIVT :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
        (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
        (ComplArchiSemiDecOrderedField a1 a3) -> (a3 -> a3) -> a3
cIVT klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real f =
  real_mslimit_P klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
    semiDecOrderedField_Real complArchiSemiDecOrderedField_Real (\n ->
    let {
     x = root_approx klb m_Monad0 multivalueMonad_description0
           m_MultivalueMonad0 semiDecOrderedField_Real
           complArchiSemiDecOrderedField_Real f (Prelude.succ n)}
    in
    m_lift m_Monad0 (\x0 -> case x0 of {
                             (,) x1 _ -> x1}) x)

k_LazyBool :: LazyBool AERN2.CKleenean
k_LazyBool = Build_LazyBool (AERN2.ckleenean Prelude.True) (AERN2.ckleenean Prelude.False) OGB.not (OGB.||) (OGB.&&) (\k _ -> Prelude.error "UNREALIZED lazy_bool_defined_is_bool")

type M a = a

m_Monad :: Monad (M Any)
m_Monad = Build_Monad (\ _ _ f -> __uc f) (\_ a -> __uc a) (\ _ m -> m)

multivalueMonad_description :: Monoid_hom (M Any) (NPset Any)
multivalueMonad_description = (Prelude.error "UNREALIZED MultivalueMonad_description")

m_MultivalueMonad :: MultivalueMonad AERN2.CKleenean (M Any)
m_MultivalueMonad = Build_MultivalueMonad (\ _ _ x -> __uc x) (\ _ _ x0 f -> __uc (\n -> Prelude.foldl (Prelude.flip (__uc f)) (x0) [0 .. ((n :: Prelude.Integer) Prelude.- 1)])) (\k1 k2 _ -> __uc (AERN2.select k1 k2)) (\ _ m -> m) (\ _ m -> m)

real_SemiDecOrderedField :: SemiDecOrderedField AERN2.CKleenean AERN2.CReal
real_SemiDecOrderedField = Build_SemiDecOrderedField 0 1 (Prelude.+) (Prelude.*) Prelude.negate (\ x _ -> Prelude.recip x) (OGB.<)

real_ComplArchiSemiDecOrderedField :: ComplArchiSemiDecOrderedField
                                      AERN2.CKleenean AERN2.CReal
real_ComplArchiSemiDecOrderedField = (\ f _ -> AERN2.limit f)

run_CIVT :: (AERN2.CReal -> AERN2.CReal) -> AERN2.CReal
run_CIVT f =
  cIVT k_LazyBool m_Monad multivalueMonad_description m_MultivalueMonad
    real_SemiDecOrderedField real_ComplArchiSemiDecOrderedField f

