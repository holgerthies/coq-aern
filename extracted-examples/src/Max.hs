{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Max where

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

real_lt_semidec :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2
                   -> Semidec a1
real_lt_semidec _ semiDecOrderedField =
  case semiDecOrderedField of {
   Build_SemiDecOrderedField _ _ _ _ _ _ real_lt_semidec0 -> real_lt_semidec0}

real_minus :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2 -> a2
real_minus = (\_ _ x y -> __uc (((__R x) Prelude.- (__R y))))

prec :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> Prelude.Integer -> a2
prec = (\_ _ n -> __uc ((0.5 :: AERN2.CReal) Prelude.^ n))

type ComplArchiSemiDecOrderedField k real =
  (Prelude.Integer -> real) -> () -> real
  -- singleton inductive, whose constructor was Build_ComplArchiSemiDecOrderedField
  
real_limit_p :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) ->
                (ComplArchiSemiDecOrderedField a1 a2) -> (Prelude.Integer ->
                a2) -> a2
real_limit_p _ _ complArchiSemiDecOrderedField f =
  complArchiSemiDecOrderedField f __

m_split :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
           (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) -> a3 -> a3
           -> a3 -> a2
m_split klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real x y _UU03b5_ =
  choose klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
    (real_lt_semidec klb semiDecOrderedField_Real
      (real_minus klb semiDecOrderedField_Real y _UU03b5_) x)
    (real_lt_semidec klb semiDecOrderedField_Real
      (real_minus klb semiDecOrderedField_Real x _UU03b5_) y)

real_limit_P_lt_p :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) ->
                     (ComplArchiSemiDecOrderedField a1 a2) ->
                     (Prelude.Integer -> a2) -> a2
real_limit_P_lt_p klb semiDecOrderedField_Real complArchiSemiDecOrderedField_Real p =
  projP1
    (real_limit_p klb semiDecOrderedField_Real
      complArchiSemiDecOrderedField_Real (\n -> projP1 (p n)))

real_limit_P_lt :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any))
                   -> (MultivalueMonad a1 a2) -> (SemiDecOrderedField 
                   a1 a3) -> (ComplArchiSemiDecOrderedField a1 a3) ->
                   (Prelude.Integer -> a3) -> a3
real_limit_P_lt klb _ _ _ semiDecOrderedField_Real complArchiSemiDecOrderedField_Real x =
  real_limit_P_lt_p klb semiDecOrderedField_Real
    complArchiSemiDecOrderedField_Real x

real_mslimit_P_lt :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2
                     (NPset Any)) -> (MultivalueMonad a1 a2) ->
                     (SemiDecOrderedField a1 a3) ->
                     (ComplArchiSemiDecOrderedField a1 a3) ->
                     (Prelude.Integer -> a2) -> a3
real_mslimit_P_lt klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real x =
  let {
   x0 = m_countable_lift klb m_Monad0 multivalueMonad_description0
          m_MultivalueMonad0 x}
  in
  m_hprop_elim_f klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
    (let {
      x1 = \x1 ->
       real_limit_P_lt klb m_Monad0 multivalueMonad_description0
         m_MultivalueMonad0 semiDecOrderedField_Real
         complArchiSemiDecOrderedField_Real x1}
     in
     m_lift m_Monad0 x1 x0)

real_max_prop :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any))
                 -> (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 
                 a3) -> (ComplArchiSemiDecOrderedField a1 a3) -> a3 -> a3 ->
                 a3
real_max_prop klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real x y =
  real_mslimit_P_lt klb m_Monad0 multivalueMonad_description0
    m_MultivalueMonad0 semiDecOrderedField_Real
    complArchiSemiDecOrderedField_Real (\n ->
    mjoin m_Monad0 (\h -> case h of {
                           Prelude.True -> x;
                           Prelude.False -> y})
      (m_split klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
        semiDecOrderedField_Real x y (prec klb semiDecOrderedField_Real n)))

real_max :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
            (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
            (ComplArchiSemiDecOrderedField a1 a3) -> a3 -> a3 -> a3
real_max klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real x y =
  projP1
    (real_max_prop klb m_Monad0 multivalueMonad_description0
      m_MultivalueMonad0 semiDecOrderedField_Real
      complArchiSemiDecOrderedField_Real x y)

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

r_ComplArchiSemiDecOrderedField :: ComplArchiSemiDecOrderedField
                                   AERN2.CKleenean AERN2.CReal
r_ComplArchiSemiDecOrderedField = (\ f _ -> AERN2.limit f)

r_real_max :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal
r_real_max =
  real_max k_LazyBool m_Monad multivalueMonad_description m_MultivalueMonad
    r_SemiDecOrderedField r_ComplArchiSemiDecOrderedField

