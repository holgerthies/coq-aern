{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Ode_exp where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

import Prelude ((+),(-),(/))
import qualified Prelude as P
import MixedTypesNumPrelude (ifThenElse)
import Numeric.CollectErrors (unCNfn2)
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
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

list_rect :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rect f f0 l =
  case l of {
   ([]) -> f;
   (:) y l0 -> f0 y l0 (list_rect f f0 l0)}

length :: (([]) a1) -> Prelude.Integer
length l =
  case l of {
   ([]) -> 0;
   (:) _ l' -> Prelude.succ (length l')}

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

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

log2 :: Prelude.Integer -> Prelude.Integer
log2 = (MNP.integer P.. Logs.integerLog2)

data RealTypes =
   MkRealTypes

type M a = a

type Is_equiv a b = (b -> a)

pr1 :: a1 -> a1
pr1 a =
  a

nth :: Prelude.Integer -> (([]) a1) -> a1 -> a1
nth n l default0 =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> case l of {
            ([]) -> default0;
            (:) x _ -> x})
    (\m -> case l of {
            ([]) -> default0;
            (:) _ t -> nth m t default0})
    n

rev :: (([]) a1) -> ([]) a1
rev l =
  case l of {
   ([]) -> ([]);
   (:) x l' -> app (rev l') ((:) x ([]))}

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f a) (map f t)}

seq :: Prelude.Integer -> Prelude.Integer -> ([]) Prelude.Integer
seq start len =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> ([]))
    (\len0 -> (:) start (seq (Prelude.succ start) len0))
    len

data LazyBool_K =
   Build_LazyBool_K AERN2.CKleenean AERN2.CKleenean (AERN2.CKleenean ->
                                                    AERN2.CKleenean) 
 (AERN2.CKleenean -> AERN2.CKleenean -> AERN2.CKleenean) (AERN2.CKleenean ->
                                                         AERN2.CKleenean ->
                                                         AERN2.CKleenean) 
 (AERN2.CKleenean -> () -> P.Bool)

data Monad m =
   Build_Monad (() -> () -> (Any -> Any) -> m -> m) (() -> Any -> m) 
 (() -> m -> m)

type Monoid_hom f g =
  () -> f -> g
  -- singleton inductive, whose constructor was Build_Monoid_hom
  
type NPset x = ()

type Lifts_lifted_trace =
  () -> () -> (M Any) -> (Prelude.Integer -> Any -> M Any) ->
  (M (Prelude.Integer -> Any))

data MultivalueMonad_M =
   Build_MultivalueMonad_M LazyBool_K (Monad (M Any)) (Monoid_hom (M Any)
                                                      (NPset Any)) (() -> ()
                                                                   ->
                                                                   Is_equiv
                                                                   Any
                                                                   (M Any)) 
 Lifts_lifted_trace (AERN2.CKleenean -> AERN2.CKleenean -> () -> M P.Bool) 
 (() -> Is_equiv (M (M Any)) (M (NPset Any))) (() -> (M Any) -> M Any) 
 ((Prelude.Integer -> AERN2.CKleenean) -> () -> M Prelude.Integer)

m_lift :: (a1 -> a2) -> (M a1) -> M a2
m_lift = P.id

mjoin :: (P.Bool -> a1) -> (M P.Bool) -> M a1
mjoin = P.id

type Semidec = AERN2.CKleenean

choose :: Semidec -> Semidec -> M P.Bool
choose = (unCNfn2 AERN2.select)

data SemiDecOrderedField_Real =
   Build_SemiDecOrderedField_Real MultivalueMonad_M AERN2.CReal AERN2.CReal 
 (AERN2.CReal -> AERN2.CReal -> AERN2.CReal) (AERN2.CReal -> AERN2.CReal ->
                                             AERN2.CReal) (AERN2.CReal ->
                                                          AERN2.CReal) 
 (AERN2.CReal -> () -> AERN2.CReal) (AERN2.CReal -> AERN2.CReal -> Semidec)

real_0 :: AERN2.CReal
real_0 = 0

real_1 :: AERN2.CReal
real_1 = 1

nreal :: Prelude.Integer -> AERN2.CReal
nreal = AERN2.creal

real_2 :: AERN2.CReal
real_2 = 2

prec :: Prelude.Integer -> AERN2.CReal
prec = ((0.5 :: AERN2.CReal) P.^)

data ComplArchiSemiDecOrderedField_Real =
   Build_ComplArchiSemiDecOrderedField_Real SemiDecOrderedField_Real 
 ((Prelude.Integer -> AERN2.CReal) -> () -> AERN2.CReal)

m_split :: AERN2.CReal -> AERN2.CReal -> AERN2.CReal -> M P.Bool
m_split x y _UU03b5_ =
  choose ((OGB.<) ((-) y _UU03b5_) x) ((OGB.<) ((-) x _UU03b5_) y)

abs_prop :: AERN2.CReal -> AERN2.CReal
abs_prop x =
  AERN2.limit (\n ->
    let {x0 = \order -> case order of {
                         P.True -> x;
                         P.False -> P.negate x}}
    in
    m_lift x0
      (m_split x real_0
        (prec ((Prelude.+) n (Prelude.succ (Prelude.succ 0))))))

abs :: AERN2.CReal -> AERN2.CReal
abs =
  abs_prop

types :: RealTypes
types =
  Prelude.error "AXIOM TO BE REALIZED"

casofReal :: ComplArchiSemiDecOrderedField_Real
casofReal =
  Prelude.error "AXIOM TO BE REALIZED"

real_add1 :: AERN2.CReal -> AERN2.CReal
real_add1 x =
  (+) x real_1

_real_0 :: AERN2.CReal
_real_0 =
  real_0

real_max_prop :: RealTypes -> ComplArchiSemiDecOrderedField_Real ->
                 AERN2.CReal -> AERN2.CReal -> AERN2.CReal
real_max_prop _ _ x y =
  AERN2.limit (\n ->
    mjoin (\h -> case h of {
                  P.True -> x;
                  P.False -> y}) (m_split x y (prec n)))

real_max :: RealTypes -> ComplArchiSemiDecOrderedField_Real -> AERN2.CReal ->
            AERN2.CReal -> AERN2.CReal
real_max types0 casofReal0 x y =
   (real_max_prop types0 casofReal0 x y)

type Poly = ([]) AERN2.CReal

eval_poly :: Poly -> AERN2.CReal -> AERN2.CReal
eval_poly a x =
  case a of {
   ([]) -> real_0;
   (:) h t -> (+) h ((P.*) x (eval_poly t x))}

smul_poly :: AERN2.CReal -> Poly -> Poly
smul_poly lambda p1 =
  list_rect ([]) (\a0 _ iH -> (:) ((P.*) lambda a0) iH) p1

sum_polyf :: Poly -> Poly -> Poly
sum_polyf p1 =
  list_rect (\p2 -> p2) (\a0 p1' s p2 ->
    case p2 of {
     ([]) -> (:) a0 p1';
     (:) r l -> (:) ((+) a0 r) (s l)}) p1

sum_poly :: Poly -> Poly -> Poly
sum_poly =
  sum_polyf

convolution_coeff_rec :: (([]) AERN2.CReal) -> (([]) AERN2.CReal) ->
                         Prelude.Integer -> Prelude.Integer -> AERN2.CReal
convolution_coeff_rec a b n i =
  (+) ((P.*) (nth (sub n i) a real_0) (nth i b real_0))
    ((\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
       (\_ -> real_0)
       (\i' -> convolution_coeff_rec a b n i')
       i)

convolution_coeff :: (([]) AERN2.CReal) -> (([]) AERN2.CReal) ->
                     Prelude.Integer -> AERN2.CReal
convolution_coeff a b n =
  convolution_coeff_rec a b n n

mult_coefficients_rec :: (([]) AERN2.CReal) -> (([]) AERN2.CReal) ->
                         Prelude.Integer -> ([]) AERN2.CReal
mult_coefficients_rec a b n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> ([]))
    (\n' -> (:)
    (convolution_coeff a b
      (sub (sub ((Prelude.+) (length a) (length b)) (Prelude.succ 0)) n))
    (mult_coefficients_rec a b n'))
    n

mult_coefficients :: (([]) AERN2.CReal) -> (([]) AERN2.CReal) -> ([])
                     AERN2.CReal
mult_coefficients a b =
  mult_coefficients_rec a b
    (sub ((Prelude.+) (length a) (length b)) (Prelude.succ 0))

mult_poly :: Poly -> Poly -> Poly
mult_poly =
  mult_coefficients

shift_poly :: Poly -> AERN2.CReal -> Poly
shift_poly p1 c =
  list_rect ([]) (\a0 _ iH ->
    let {s = mult_poly ((:) (P.negate c) ((:) real_1 ([]))) iH} in
    sum_poly ((:) a0 ([])) s) p1

poly_rev_ind :: a1 -> (AERN2.CReal -> Poly -> a1 -> a1) -> Poly -> a1
poly_rev_ind x x0 l =
  eq_rect (rev (rev l))
    (let {l0 = rev l} in list_rect x (\a l1 iHl0 -> x0 a (rev l1) iHl0) l0) l

poly_deriv_exists :: Poly -> Poly
poly_deriv_exists p =
  poly_rev_ind ([]) (\x p0 iHp ->
    case p0 of {
     ([]) -> ([]);
     (:) _ l ->
      app iHp ((:) ((P.*) (nreal (Prelude.succ (length l))) x) ([]))}) p

derive_poly :: Poly -> Poly
derive_poly p =
  pr1 (poly_deriv_exists p)

to_poly :: (Prelude.Integer -> AERN2.CReal) -> Prelude.Integer -> ([])
           AERN2.CReal
to_poly a n =
  map a (seq 0 (Prelude.succ n))

data Bounded_ps =
   Mk_bounded_ps (Prelude.Integer -> AERN2.CReal) Prelude.Integer AERN2.CReal

series :: Bounded_ps -> Prelude.Integer -> AERN2.CReal
series b =
  case b of {
   Mk_bounded_ps series0 _ _ -> series0}

bounded_ps_M :: Bounded_ps -> Prelude.Integer
bounded_ps_M b =
  case b of {
   Mk_bounded_ps _ bounded_ps_M0 _ -> bounded_ps_M0}

bounded_ps_r :: Bounded_ps -> AERN2.CReal
bounded_ps_r b =
  case b of {
   Mk_bounded_ps _ _ bounded_ps_r0 -> bounded_ps_r0}

eval_radius :: Bounded_ps -> AERN2.CReal
eval_radius a =
  (/) (bounded_ps_r a) real_2

eval_seq :: Bounded_ps -> AERN2.CReal -> Prelude.Integer -> AERN2.CReal
eval_seq a x n =
  eval_poly
    (to_poly (series a)
      ((Prelude.+) n (Prelude.succ (log2 (bounded_ps_M a))))) x

eval_val :: Bounded_ps -> AERN2.CReal -> AERN2.CReal
eval_val a x =
  AERN2.limit (eval_seq a x)

pivp_to_pivp0 :: Poly -> AERN2.CReal -> Poly
pivp_to_pivp0 p y0 =
  shift_poly p (P.negate y0)

scalar_mult_poly :: AERN2.CReal -> Poly -> Poly
scalar_mult_poly m p =
  pr1 (smul_poly m p)

pn :: (([]) AERN2.CReal) -> Prelude.Integer -> ([]) AERN2.CReal
pn p n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> p)
    (\n' ->
    scalar_mult_poly (P.recip (nreal (Prelude.succ n)))
      (mult_coefficients p (derive_poly (pn p n'))))
    n

pn0 :: (([]) AERN2.CReal) -> Prelude.Integer -> AERN2.CReal
pn0 p n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> _real_0)
    (\n' -> eval_poly (pn p n') real_0)
    n

poly_norm :: Poly -> AERN2.CReal
poly_norm p =
  list_rect real_0 (\a _ iHp -> real_max types casofReal (abs a) iHp) p

pivp_ps_exists :: Poly -> AERN2.CReal -> Bounded_ps
pivp_ps_exists q y0 =
  let {s = pivp_to_pivp0 q y0} in
  let {
   r = (+)
         (abs
           ((P.*) (nreal ((Prelude.*) (length s) (length s))) (poly_norm s)))
         real_1}
  in
  Mk_bounded_ps (pn0 s) (Prelude.succ 0) (P.recip r)

local_solution :: Poly -> AERN2.CReal -> ((,) AERN2.CReal AERN2.CReal)
local_solution p y0 =
  let {s = pivp_ps_exists p y0} in
  let {s0 = eval_val s (eval_radius s)} in (,) (eval_radius s) ((+) s0 y0)

solve_ivp :: Poly -> AERN2.CReal -> Prelude.Integer ->
             (([]) ((,) AERN2.CReal AERN2.CReal))
solve_ivp p y0 n =
  nat_rect ((:) ((,) _real_0 y0) ([])) (\n0 iHn ->
    let {s = local_solution p (snd (nth n0 iHn ((,) _real_0 _real_0)))} in
    case s of {
     (,) r r0 ->
      app iHn ((:) ((,) ((+) (fst (nth n0 iHn ((,) _real_0 _real_0))) r) r0)
        ([]))}) n

exp_example :: Prelude.Integer -> ([]) ((,) AERN2.CReal AERN2.CReal)
exp_example steps =
  pr1
    (solve_ivp ((:) _real_0 ((:) (real_add1 _real_0) ([])))
      (real_add1 _real_0) steps)

