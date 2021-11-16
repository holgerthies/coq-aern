{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module CSqrt where

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

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rect_r :: a1 -> a2 -> a1 -> a2
eq_rect_r =
  eq_rect

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
projT1 :: ((,) a1 a2) -> a1
projT1 x =
  case x of {
   (,) a _ -> a}

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

mul :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> add y ((\x -> 2 Prelude.* x) (mul p y)))
    (\p -> (\x -> 2 Prelude.* x) (mul p y))
    (\_ -> y)
    x

compare_cont :: Comparison -> Prelude.Integer -> Prelude.Integer -> Comparison
compare_cont r x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> compare_cont r p q)
      (\q -> compare_cont Gt p q)
      (\_ -> Gt)
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> compare_cont Lt p q)
      (\q -> compare_cont r p q)
      (\_ -> Gt)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> Lt)
      (\_ -> Lt)
      (\_ -> r)
      y)
    x

compare :: Prelude.Integer -> Prelude.Integer -> Comparison
compare =
  compare_cont Eq

iter_op :: (a1 -> a1 -> a1) -> Prelude.Integer -> a1 -> a1
iter_op op p a =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> op a (iter_op op p0 (op a a)))
    (\p0 -> iter_op op p0 (op a a))
    (\_ -> a)
    p

to_nat :: Prelude.Integer -> Prelude.Integer
to_nat x =
  iter_op (Prelude.+) x (Prelude.succ 0)

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

compare0 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare0 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Eq)
      (\_ -> Lt)
      (\_ -> Gt)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Gt)
      (\y' -> compare x' y')
      (\_ -> Gt)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Lt)
      (\_ -> Lt)
      (\y' -> compOpp (compare x' y'))
      y)
    x

leb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb x y =
  case compare0 x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

ltb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb x y =
  case compare0 x y of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

of_nat :: Prelude.Integer -> Prelude.Integer
of_nat n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n0 -> (\x -> x) (of_succ_nat n0))
    n

pos_div_eucl :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
                Prelude.Integer
pos_div_eucl a b =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {
       r' = (Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r)
              ((\x -> x) 1)}
      in
      case ltb r' b of {
       Prelude.True -> (,) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
        r';
       Prelude.False -> (,)
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = (Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r} in
      case ltb r' b of {
       Prelude.True -> (,) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
        r';
       Prelude.False -> (,)
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\_ ->
    case leb ((\x -> x) ((\x -> 2 Prelude.* x) 1)) b of {
     Prelude.True -> (,) 0 ((\x -> x) 1);
     Prelude.False -> (,) ((\x -> x) 1) 0})
    a

div_eucl :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
            Prelude.Integer
div_eucl a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (,) 0 0)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) 0 0)
      (\_ -> pos_div_eucl a' b)
      (\b' ->
      case pos_div_eucl a' ((\x -> x) b') of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
          (\_ -> (,) (opp q) 0)
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.+) b r))
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1))) ((Prelude.+) b r))
          r})
      b)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) 0 0)
      (\_ ->
      case pos_div_eucl a' b of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
          (\_ -> (,) (opp q) 0)
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.-) b r))
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1))) ((Prelude.-) b r))
          r})
      (\b' ->
      case pos_div_eucl a' ((\x -> x) b') of {
       (,) q r -> (,) q (opp r)})
      b)
    a

div :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div = (\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)

type Is_equiv a b = (b -> a)

projP1 :: a1 -> a1
projP1 x =
  x

data LazyBool lB =
   Build_LazyBool lB lB (lB -> lB) (lB -> lB -> lB) (lB -> lB -> lB) (lB -> ()
                                                                     ->
                                                                     Prelude.Bool)

lazy_bool_or :: (LazyBool a1) -> a1 -> a1 -> a1
lazy_bool_or lazyBool =
  case lazyBool of {
   Build_LazyBool _ _ _ lazy_bool_or0 _ _ -> lazy_bool_or0}

data Monad m =
   Build_Monad (() -> () -> (Any -> Any) -> m -> m) (() -> Any -> m) (() -> m ->
                                                                     m)

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

type Lifts_lifted_trace m = () -> () -> m -> (Prelude.Integer -> Any -> m) -> m

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

multivalueMonad_base_monad_traces_lift :: (LazyBool a1) -> (Monad a2) ->
                                          (Monoid_hom a2 (NPset Any)) ->
                                          (MultivalueMonad a1 a2) -> a2 ->
                                          (Prelude.Integer -> a3 -> a2) -> 
                                          a2
multivalueMonad_base_monad_traces_lift _ _ _ multivalueMonad x f =
  case multivalueMonad of {
   Build_MultivalueMonad _ multivalueMonad_base_monad_traces_lift0 _ _ _ ->
    unsafeCoerce multivalueMonad_base_monad_traces_lift0 __ __ x f}

multivalued_choice :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any))
                      -> (MultivalueMonad a1 a2) -> a1 -> a1 -> a2
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

m_hprop_elim_f :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
                  (MultivalueMonad a1 a2) -> a2 -> a3
m_hprop_elim_f klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 x =
  projP1
    (multivalueMonad_base_monad_hprop_elim klb m_Monad0
      multivalueMonad_description0 m_MultivalueMonad0) x

m_paths :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
           (MultivalueMonad a1 a2) -> a2 -> (Prelude.Integer -> a3 -> a2) -> a2
m_paths klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 x x0 =
  projP1
    (multivalueMonad_base_monad_traces_lift klb m_Monad0
      multivalueMonad_description0 m_MultivalueMonad0 x x0)

m_countable_lift :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any))
                    -> (MultivalueMonad a1 a2) -> (Prelude.Integer -> a2) -> a2
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
    (select klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 x x0)

semidec_or :: (LazyBool a1) -> (Semidec a1) -> (Semidec a1) -> Semidec a1
semidec_or =
  lazy_bool_or

data SemiDecOrderedField k real =
   Build_SemiDecOrderedField real real (real -> real -> real) (real -> real ->
                                                              real) (real ->
                                                                    real) 
 (real -> () -> real) (real -> real -> Semidec k)

real_0 :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2
real_0 _ semiDecOrderedField =
  case semiDecOrderedField of {
   Build_SemiDecOrderedField real_3 _ _ _ _ _ _ -> real_3}

real_1 :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2
real_1 _ semiDecOrderedField =
  case semiDecOrderedField of {
   Build_SemiDecOrderedField _ real_3 _ _ _ _ _ -> real_3}

real_plus :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2 -> a2
real_plus _ semiDecOrderedField =
  case semiDecOrderedField of {
   Build_SemiDecOrderedField _ _ real_plus0 _ _ _ _ -> real_plus0}

real_mult :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2 -> a2
real_mult _ semiDecOrderedField =
  case semiDecOrderedField of {
   Build_SemiDecOrderedField _ _ _ real_mult0 _ _ _ -> real_mult0}

real_opp :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2
real_opp _ semiDecOrderedField =
  case semiDecOrderedField of {
   Build_SemiDecOrderedField _ _ _ _ real_opp0 _ _ -> real_opp0}

real_inv :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2
real_inv _ semiDecOrderedField z =
  case semiDecOrderedField of {
   Build_SemiDecOrderedField _ _ _ _ _ real_inv0 _ -> real_inv0 z __}

real_lt_semidec :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2 ->
                   Semidec a1
real_lt_semidec _ semiDecOrderedField =
  case semiDecOrderedField of {
   Build_SemiDecOrderedField _ _ _ _ _ _ real_lt_semidec0 -> real_lt_semidec0}

real_minus :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2 -> a2
real_minus = (\_ _ x y -> __uc (((__R x) Prelude.- (__R y))))

real_div :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> a2 -> a2
real_div = (\_ _ x y -> __uc (((__R x) Prelude./ (__R y))))

iZreal :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> Prelude.Integer -> a2
iZreal = (\_ _ z -> __uc (AERN2.creal z))

real_2 :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2
real_2 klb semiDecOrderedField_Real =
  iZreal klb semiDecOrderedField_Real ((\x -> x) ((\x -> 2 Prelude.* x) 1))

prec :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> Prelude.Integer -> a2
prec = (\_ _ n -> __uc ((0.5 :: AERN2.CReal) Prelude.^ n))

type ComplArchiSemiDecOrderedField k real =
  (Prelude.Integer -> real) -> () -> real
  -- singleton inductive, whose constructor was Build_ComplArchiSemiDecOrderedField
  
real_limit_p :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) ->
                (ComplArchiSemiDecOrderedField a1 a2) -> (Prelude.Integer -> a2)
                -> a2
real_limit_p _ _ complArchiSemiDecOrderedField f =
  complArchiSemiDecOrderedField f __

pow :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> Prelude.Integer ->
       a2
pow klb semiDecOrderedField_Real r n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> real_1 klb semiDecOrderedField_Real)
    (\m ->
    real_mult klb semiDecOrderedField_Real r
      (pow klb semiDecOrderedField_Real r m))
    n

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
           (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) -> a3 -> a3 ->
           a3 -> a2
m_split klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real x y _UU03b5_ =
  choose klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
    (real_lt_semidec klb semiDecOrderedField_Real
      (real_minus klb semiDecOrderedField_Real y _UU03b5_) x)
    (real_lt_semidec klb semiDecOrderedField_Real
      (real_minus klb semiDecOrderedField_Real x _UU03b5_) y)

real_limit_P_lt_p :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) ->
                     (ComplArchiSemiDecOrderedField a1 a2) -> (Prelude.Integer
                     -> a2) -> a2
real_limit_P_lt_p klb semiDecOrderedField_Real complArchiSemiDecOrderedField_Real p =
  projP1
    (real_limit_p klb semiDecOrderedField_Real
      complArchiSemiDecOrderedField_Real (\n -> projP1 (p n)))

real_limit_P_p :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) ->
                  (ComplArchiSemiDecOrderedField a1 a2) -> (Prelude.Integer ->
                  a2) -> a2
real_limit_P_p klb semiDecOrderedField_Real complArchiSemiDecOrderedField_Real p =
  projP1
    (real_limit_p klb semiDecOrderedField_Real
      complArchiSemiDecOrderedField_Real (\n -> projP1 (p n)))

real_mslimit_P_p :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any))
                    -> (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 
                    a3) -> (ComplArchiSemiDecOrderedField a1 a3) ->
                    (Prelude.Integer -> a2) -> a3
real_mslimit_P_p klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real x =
  let {
   x0 = m_countable_lift klb m_Monad0 multivalueMonad_description0
          m_MultivalueMonad0 x}
  in
  m_hprop_elim_f klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
    (let {
      x1 = \x1 ->
       real_limit_P_p klb semiDecOrderedField_Real
         complArchiSemiDecOrderedField_Real x1}
     in
     m_lift m_Monad0 x1 x0)

real_mslimit_P_lt_p :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2
                       (NPset Any)) -> (MultivalueMonad a1 a2) ->
                       (SemiDecOrderedField a1 a3) ->
                       (ComplArchiSemiDecOrderedField a1 a3) -> (Prelude.Integer
                       -> a2) -> a3
real_mslimit_P_lt_p klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real x =
  let {
   x0 = m_countable_lift klb m_Monad0 multivalueMonad_description0
          m_MultivalueMonad0 x}
  in
  m_hprop_elim_f klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
    (let {
      x1 = \x1 ->
       real_limit_P_lt_p klb semiDecOrderedField_Real
         complArchiSemiDecOrderedField_Real x1}
     in
     m_lift m_Monad0 x1 x0)

abs_prop :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
            (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
            (ComplArchiSemiDecOrderedField a1 a3) -> a3 -> a3
abs_prop klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real x =
  real_mslimit_P_lt_p klb m_Monad0 multivalueMonad_description0
    m_MultivalueMonad0 semiDecOrderedField_Real
    complArchiSemiDecOrderedField_Real (\n ->
    let {
     x0 = \order ->
      case order of {
       Prelude.True -> x;
       Prelude.False -> real_opp klb semiDecOrderedField_Real x}}
    in
    m_lift m_Monad0 x0
      (m_split klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
        semiDecOrderedField_Real x (real_0 klb semiDecOrderedField_Real)
        (prec klb semiDecOrderedField_Real
          ((Prelude.+) n (Prelude.succ (Prelude.succ 0))))))

abs :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
       (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
       (ComplArchiSemiDecOrderedField a1 a3) -> a3 -> a3
abs =
  abs_prop

real_limit :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
              (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
              (ComplArchiSemiDecOrderedField a1 a3) -> (Prelude.Integer -> a3)
              -> a3
real_limit klb _ _ _ semiDecOrderedField_Real complArchiSemiDecOrderedField_Real f =
  real_limit_p klb semiDecOrderedField_Real complArchiSemiDecOrderedField_Real f

real_limit_P_lt :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
                   (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
                   (ComplArchiSemiDecOrderedField a1 a3) -> (Prelude.Integer ->
                   a3) -> a3
real_limit_P_lt klb _ _ _ semiDecOrderedField_Real complArchiSemiDecOrderedField_Real x =
  real_limit_P_lt_p klb semiDecOrderedField_Real
    complArchiSemiDecOrderedField_Real x

real_mslimit_P_lt :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any))
                     -> (MultivalueMonad a1 a2) -> (SemiDecOrderedField 
                     a1 a3) -> (ComplArchiSemiDecOrderedField a1 a3) ->
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

real_max_prop :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
                 (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
                 (ComplArchiSemiDecOrderedField a1 a3) -> a3 -> a3 -> a3
real_max_prop klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real x y =
  real_mslimit_P_lt klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
    semiDecOrderedField_Real complArchiSemiDecOrderedField_Real (\n ->
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
    (real_max_prop klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
      semiDecOrderedField_Real complArchiSemiDecOrderedField_Real x y)

ssr_have :: a1 -> (a1 -> a2) -> a2
ssr_have step rest =
  rest step

ssr_suff :: (a1 -> a2) -> a1 -> a2
ssr_suff step =
  step

addn_rec :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
addn_rec =
  (Prelude.+)

addn :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
addn =
  addn_rec

muln_rec :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
muln_rec =
  (Prelude.*)

muln :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
muln =
  muln_rec

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
              (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) -> a3 -> a2
magnitude1 klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real x =
  ssr_have __ (\_ ->
    ssr_suff (\g1M -> m_lift m_Monad0 (\g1 -> g1) g1M)
      (epsilon_smallest_choose_M klb m_Monad0 multivalueMonad_description0
        m_MultivalueMonad0 (\n ->
        weaken_orM_r m_Monad0
          (choose klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
            (real_lt_semidec klb semiDecOrderedField_Real
              (prec klb semiDecOrderedField_Real (Prelude.succ (Prelude.succ
                n))) x)
            (real_lt_semidec klb semiDecOrderedField_Real x
              (prec klb semiDecOrderedField_Real (Prelude.succ n)))))))

zpow :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 -> Prelude.Integer ->
        a2
zpow klb semiDecOrderedField_Real x z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> real_1 klb semiDecOrderedField_Real)
    (\p -> pow klb semiDecOrderedField_Real x (to_nat p))
    (\p ->
    pow klb semiDecOrderedField_Real (real_inv klb semiDecOrderedField_Real x)
      (to_nat p))
    z

dec_x_lt_2 :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
              (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) -> a3 -> a2
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
              (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) -> a3 -> a2
magnitude2 klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real x =
  let {
   y = real_div klb semiDecOrderedField_Real x
         (iZreal klb semiDecOrderedField_Real ((\x -> x) ((\x -> 2 Prelude.* x)
           ((\x -> 2 Prelude.* x) 1))))}
  in
  ssr_have __ (\_ ->
    ssr_have __ (\_ ->
      ssr_suff
        (m_lift m_Monad0 (\_top_assumption_ ->
          (Prelude.+) _top_assumption_ ((\x -> x) ((\x -> 2 Prelude.* x) 1))))
        (ssr_have
          (magnitude1 klb m_Monad0 multivalueMonad_description0
            m_MultivalueMonad0 semiDecOrderedField_Real y)
          (m_lift m_Monad0 (\_top_assumption_ -> opp (of_nat _top_assumption_))))))

magnitude :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
             (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) -> a3 -> a2
magnitude klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real x =
  ssr_have
    (dec_x_lt_2 klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
      semiDecOrderedField_Real x)
    (m_lift_dom m_Monad0 (\_top_assumption_ ->
      let {
       _evar_0_ = \_ ->
        magnitude2 klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
          semiDecOrderedField_Real x}
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

data Euclidean real =
   Nil
 | Cons Prelude.Integer real (Euclidean real)

euclidean_rect :: a2 -> (Prelude.Integer -> a1 -> (Euclidean a1) -> a2 -> a2) ->
                  Prelude.Integer -> (Euclidean a1) -> a2
euclidean_rect f f0 _ e =
  case e of {
   Nil -> f;
   Cons n r e0 -> f0 n r e0 (euclidean_rect f f0 n e0)}

case0 :: a2 -> (Euclidean a1) -> a2
case0 h v =
  case v of {
   Nil -> h;
   Cons _ _ _ -> __}

caseS' :: Prelude.Integer -> (Euclidean a1) -> (a1 -> (Euclidean a1) -> a2) ->
          a2
caseS' _ v h =
  case v of {
   Nil -> __;
   Cons _ h0 t -> h h0 t}

rect2 :: a2 -> (Prelude.Integer -> (Euclidean a1) -> (Euclidean a1) -> a2 -> a1
         -> a1 -> a2) -> Prelude.Integer -> (Euclidean a1) -> (Euclidean 
         a1) -> a2
rect2 bas rect _ v1 v2 =
  case v1 of {
   Nil -> case0 bas v2;
   Cons n' h1 t1 ->
    caseS' n' v2 (\h2 t2 -> rect n' t1 t2 (rect2 bas rect n' t1 t2) h1 h2)}

dim_succ_destruct :: Prelude.Integer -> (Euclidean a1) -> (,) a1 (Euclidean a1)
dim_succ_destruct n x =
  caseS' n x (\h t -> (,) h t)

euclidean_zero :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) ->
                  Prelude.Integer -> Euclidean a2
euclidean_zero klb semiDecOrderedField_Real n =
  nat_rect Nil (\n0 iHn -> Cons n0 (real_0 klb semiDecOrderedField_Real) iHn) n

euclidean_plus :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) ->
                  Prelude.Integer -> (Euclidean a2) -> (Euclidean a2) ->
                  Euclidean a2
euclidean_plus klb semiDecOrderedField_Real n x y =
  rect2 Nil (\n0 _ _ x0 a b -> Cons n0
    (real_plus klb semiDecOrderedField_Real a b) x0) n x y

euclidean_opp :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> Prelude.Integer
                 -> (Euclidean a2) -> Euclidean a2
euclidean_opp klb semiDecOrderedField_Real n x =
  nat_rect (\_ -> Nil) (\n0 iHn x0 ->
    let {x1 = dim_succ_destruct n0 x0} in
    case x1 of {
     (,) x2 s -> Cons n0 (real_opp klb semiDecOrderedField_Real x2) (iHn s)}) n
    x

euclidean_minus :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) ->
                   Prelude.Integer -> (Euclidean a2) -> (Euclidean a2) ->
                   Euclidean a2
euclidean_minus klb semiDecOrderedField_Real n x y =
  euclidean_plus klb semiDecOrderedField_Real n x
    (euclidean_opp klb semiDecOrderedField_Real n y)

euclidean_max_norm :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any))
                      -> (MultivalueMonad a1 a2) -> (SemiDecOrderedField 
                      a1 a3) -> (ComplArchiSemiDecOrderedField a1 a3) ->
                      Prelude.Integer -> (Euclidean a3) -> a3
euclidean_max_norm klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real n x =
  euclidean_rect (real_0 klb semiDecOrderedField_Real) (\_ r _ iHx ->
    real_max klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
      semiDecOrderedField_Real complArchiSemiDecOrderedField_Real
      (abs klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
        semiDecOrderedField_Real complArchiSemiDecOrderedField_Real r) iHx) n x

euclidean_max_dist :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any))
                      -> (MultivalueMonad a1 a2) -> (SemiDecOrderedField 
                      a1 a3) -> (ComplArchiSemiDecOrderedField a1 a3) ->
                      Prelude.Integer -> (Euclidean a3) -> (Euclidean a3) -> a3
euclidean_max_dist klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real n x y =
  euclidean_max_norm klb m_Monad0 multivalueMonad_description0
    m_MultivalueMonad0 semiDecOrderedField_Real
    complArchiSemiDecOrderedField_Real n
    (euclidean_minus klb semiDecOrderedField_Real n x y)

euclidean_head_sequence :: Prelude.Integer -> (Prelude.Integer -> Euclidean 
                           a1) -> Prelude.Integer -> a1
euclidean_head_sequence n f h =
  let {x = f h} in
  let {s = dim_succ_destruct n x} in case s of {
                                      (,) x0 _ -> x0}

euclidean_tail_sequence :: Prelude.Integer -> (Prelude.Integer -> Euclidean 
                           a1) -> Prelude.Integer -> Euclidean a1
euclidean_tail_sequence n f h =
  let {x = f h} in
  let {s = dim_succ_destruct n x} in case s of {
                                      (,) _ s0 -> s0}

euclidean_limit :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
                   (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
                   (ComplArchiSemiDecOrderedField a1 a3) -> Prelude.Integer ->
                   (Prelude.Integer -> Euclidean a3) -> (Euclidean a3)
euclidean_limit klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real n f =
  nat_rect (\_ _ -> Nil) (\n0 iHn f0 _ -> Cons n0
    (projP1
      (real_limit klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
        semiDecOrderedField_Real complArchiSemiDecOrderedField_Real
        (euclidean_head_sequence n0 f0)))
    (projP1 (iHn (euclidean_tail_sequence n0 f0) __))) n f __

euclidean_mlimit_PQ :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2
                       (NPset Any)) -> (MultivalueMonad a1 a2) ->
                       (SemiDecOrderedField a1 a3) ->
                       (ComplArchiSemiDecOrderedField a1 a3) -> Prelude.Integer
                       -> a2 -> (Prelude.Integer -> (Euclidean a3) -> () -> a4
                       -> a2) -> a2
euclidean_mlimit_PQ klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real d x f =
  let {
   x0 = \n x0 ->
    case x0 of {
     (,) x1 s ->
      let {x2 = f n x1 __ s} in
      m_lift m_Monad0 (\x3 -> case x3 of {
                               (,) x4 s0 -> (,) x4 s0}) x2}}
  in
  let {
   x1 = m_paths klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 x
          x0}
  in
  m_lift_dom m_Monad0 (\_ ->
    m_lift m_Monad0 (\x3 ->
      euclidean_limit klb m_Monad0 multivalueMonad_description0
        m_MultivalueMonad0 semiDecOrderedField_Real
        complArchiSemiDecOrderedField_Real d (\n -> projT1 (x3 n))) x1) x

type Complex real = Euclidean real

complex :: a1 -> a1 -> Complex a1
complex r i =
  Cons (Prelude.succ 0) r (Cons 0 i Nil)

complex_destruct :: (Complex a1) -> (,) a1 a1
complex_destruct x =
  let {s = dim_succ_destruct (Prelude.succ 0) x} in
  case s of {
   (,) x0 s0 -> (,) x0
    (let {s1 = dim_succ_destruct 0 s0} in case s1 of {
                                           (,) x2 _ -> x2})}

complex0 :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> Euclidean a2
complex0 klb semiDecOrderedField_Real =
  euclidean_zero klb semiDecOrderedField_Real (Prelude.succ (Prelude.succ 0))

sqrt_approx :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 ->
               Prelude.Integer -> a2
sqrt_approx klb semiDecOrderedField_Real x n =
  nat_rect (real_1 klb semiDecOrderedField_Real) (\_ __top_assumption_ ->
    ssr_have __ (\_ ->
      real_mult klb semiDecOrderedField_Real
        (real_inv klb semiDecOrderedField_Real
          (real_2 klb semiDecOrderedField_Real))
        (real_plus klb semiDecOrderedField_Real __top_assumption_
          (real_div klb semiDecOrderedField_Real x __top_assumption_)))) n

sqrt_approx_fast :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> a2 ->
                    Prelude.Integer -> a2
sqrt_approx_fast klb semiDecOrderedField_Real x n =
  ssr_have
    (sqrt_approx klb semiDecOrderedField_Real x (Prelude.succ
      ((MNP.integer Prelude.. Logs.integerLog2) (Prelude.succ n))))
    (\__top_assumption_ -> __top_assumption_)

restr_sqrt :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) ->
              (ComplArchiSemiDecOrderedField a1 a2) -> a2 -> a2
restr_sqrt klb semiDecOrderedField_Real complArchiSemiDecOrderedField_Real x =
  ssr_have __ (\_ ->
    real_limit_P_lt_p klb semiDecOrderedField_Real
      complArchiSemiDecOrderedField_Real (\n ->
      ssr_have (sqrt_approx_fast klb semiDecOrderedField_Real x n)
        (\__top_assumption_ -> __top_assumption_)))

scale :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
         (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) -> a3 -> a2
scale klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real x =
  let {
   x0 = magnitude klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
          semiDecOrderedField_Real x}
  in
  m_lift m_Monad0 (\_top_assumption_ ->
    ssr_have (div _top_assumption_ ((\x -> x) ((\x -> 2 Prelude.* x) 1)))
      (\_top_assumption_0 -> (,) _top_assumption_0
      (real_mult klb semiDecOrderedField_Real
        (zpow klb semiDecOrderedField_Real (real_2 klb semiDecOrderedField_Real)
          ((Prelude.*) (Prelude.negate ((\x -> 2 Prelude.* x) 1))
            _top_assumption_0)) x))) x0

sqrt_pos :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
            (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
            (ComplArchiSemiDecOrderedField a1 a3) -> a3 -> a3
sqrt_pos klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real x =
  m_hprop_elim_f klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
    (ssr_have
      (scale klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
        semiDecOrderedField_Real x)
      (m_lift m_Monad0 (\_top_assumption_ ->
        let {
         _evar_0_ = \z y ->
          real_mult klb semiDecOrderedField_Real
            (zpow klb semiDecOrderedField_Real
              (real_2 klb semiDecOrderedField_Real) z)
            (restr_sqrt klb semiDecOrderedField_Real
              complArchiSemiDecOrderedField_Real y)}
        in
        case _top_assumption_ of {
         (,) x0 x1 -> _evar_0_ x0 x1})))

sqrt :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
        (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
        (ComplArchiSemiDecOrderedField a1 a3) -> a3 -> a3
sqrt klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real x =
  real_mslimit_P_p klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
    semiDecOrderedField_Real complArchiSemiDecOrderedField_Real (\n ->
    let {
     x0 = m_split klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
            semiDecOrderedField_Real x
            (prec klb semiDecOrderedField_Real
              (addn (muln (Prelude.succ (Prelude.succ 0)) n) (Prelude.succ 0)))
            (prec klb semiDecOrderedField_Real
              (addn (muln (Prelude.succ (Prelude.succ 0)) n) (Prelude.succ 0)))}
    in
    let {
     _evar_0_ = m_lift m_Monad0 (\_top_assumption_ ->
                  let {
                   _evar_0_ = \_ ->
                    sqrt_pos klb m_Monad0 multivalueMonad_description0
                      m_MultivalueMonad0 semiDecOrderedField_Real
                      complArchiSemiDecOrderedField_Real x}
                  in
                  let {_evar_0_0 = \_ -> real_0 klb semiDecOrderedField_Real} in
                  case _top_assumption_ of {
                   Prelude.True -> _evar_0_ __;
                   Prelude.False -> _evar_0_0 __})}
    in
    eq_rect_r (real_0 klb semiDecOrderedField_Real) _evar_0_
      (real_plus klb semiDecOrderedField_Real
        (prec klb semiDecOrderedField_Real
          (addn (muln (Prelude.succ (Prelude.succ 0)) n) (Prelude.succ 0)))
        (real_opp klb semiDecOrderedField_Real
          (prec klb semiDecOrderedField_Real
            (addn (muln (Prelude.succ (Prelude.succ 0)) n) (Prelude.succ 0)))))
      x0)

complex_nonzero_cases :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2
                         (NPset Any)) -> (MultivalueMonad a1 a2) ->
                         (SemiDecOrderedField a1 a3) -> a3 -> a3 -> a2
complex_nonzero_cases klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real a b =
  ssr_have __ (\_ ->
    ssr_have __ (\_ ->
      m_lift_dom m_Monad0 (\_top_assumption_ ->
        let {
         _evar_0_ = \_ ->
          m_unit m_Monad0 (Prelude.Just (Prelude.Just Prelude.True))}
        in
        let {
         _evar_0_0 = \_ ->
          m_lift_dom m_Monad0 (\_top_assumption_0 ->
            let {
             _evar_0_0 = \_ ->
              m_unit m_Monad0 (Prelude.Just (Prelude.Just Prelude.False))}
            in
            let {
             _evar_0_1 = \_ ->
              m_lift_dom m_Monad0 (\_top_assumption_1 ->
                let {
                 _evar_0_1 = \_ ->
                  m_unit m_Monad0 (Prelude.Just Prelude.Nothing)}
                in
                let {_evar_0_2 = \_ -> m_unit m_Monad0 Prelude.Nothing} in
                case _top_assumption_1 of {
                 Prelude.True -> _evar_0_1 __;
                 Prelude.False -> _evar_0_2 __})
                (choose klb m_Monad0 multivalueMonad_description0
                  m_MultivalueMonad0
                  (real_lt_semidec klb semiDecOrderedField_Real
                    (real_0 klb semiDecOrderedField_Real) b)
                  (real_lt_semidec klb semiDecOrderedField_Real b
                    (real_0 klb semiDecOrderedField_Real)))}
            in
            case _top_assumption_0 of {
             Prelude.True -> _evar_0_0 __;
             Prelude.False -> _evar_0_1 __})
            (choose klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
              (real_lt_semidec klb semiDecOrderedField_Real a
                (real_0 klb semiDecOrderedField_Real))
              (semidec_or klb
                (real_lt_semidec klb semiDecOrderedField_Real
                  (real_0 klb semiDecOrderedField_Real) b)
                (real_lt_semidec klb semiDecOrderedField_Real b
                  (real_0 klb semiDecOrderedField_Real))))}
        in
        case _top_assumption_ of {
         Prelude.True -> _evar_0_ __;
         Prelude.False -> _evar_0_0 __})
        (choose klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
          (real_lt_semidec klb semiDecOrderedField_Real
            (real_0 klb semiDecOrderedField_Real) a)
          (semidec_or klb
            (real_lt_semidec klb semiDecOrderedField_Real a
              (real_0 klb semiDecOrderedField_Real))
            (semidec_or klb
              (real_lt_semidec klb semiDecOrderedField_Real
                (real_0 klb semiDecOrderedField_Real) b)
              (real_lt_semidec klb semiDecOrderedField_Real b
                (real_0 klb semiDecOrderedField_Real)))))))

csqrt_neq0 :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
              (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
              (ComplArchiSemiDecOrderedField a1 a3) -> (Complex a3) -> a2
csqrt_neq0 klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real z =
  let {s = complex_destruct z} in
  case s of {
   (,) a s0 ->
    eq_rect_r (complex a s0) (\_ ->
      ssr_have
        (complex_nonzero_cases klb m_Monad0 multivalueMonad_description0
          m_MultivalueMonad0 semiDecOrderedField_Real a s0)
        (ssr_have __ (\_ ->
          let {
           absz = sqrt klb m_Monad0 multivalueMonad_description0
                    m_MultivalueMonad0 semiDecOrderedField_Real
                    complArchiSemiDecOrderedField_Real
                    (real_plus klb semiDecOrderedField_Real
                      (real_mult klb semiDecOrderedField_Real a a)
                      (real_mult klb semiDecOrderedField_Real s0 s0))}
          in
          ssr_have __ (\_ ->
            ssr_have __ (\_ ->
              ssr_have __ (\_ ->
                let {
                 c = sqrt klb m_Monad0 multivalueMonad_description0
                       m_MultivalueMonad0 semiDecOrderedField_Real
                       complArchiSemiDecOrderedField_Real
                       (real_div klb semiDecOrderedField_Real
                         (real_plus klb semiDecOrderedField_Real absz a)
                         (real_2 klb semiDecOrderedField_Real))}
                in
                let {
                 d = sqrt klb m_Monad0 multivalueMonad_description0
                       m_MultivalueMonad0 semiDecOrderedField_Real
                       complArchiSemiDecOrderedField_Real
                       (real_div klb semiDecOrderedField_Real
                         (real_minus klb semiDecOrderedField_Real absz a)
                         (real_2 klb semiDecOrderedField_Real))}
                in
                ssr_have __ (\_ ->
                  ssr_have __ (\_ ->
                    ssr_have __ (\_ ->
                      ssr_have __ (\_ ->
                        m_lift m_Monad0 (\__top_assumption_ ->
                          let {
                           _evar_0_ = \__top_assumption_0 ->
                            let {
                             _evar_0_ = \__top_assumption_1 ->
                              let {
                               _evar_0_ = \_ ->
                                ssr_have __ (\_ ->
                                  complex c
                                    (real_div klb semiDecOrderedField_Real s0
                                      (real_mult klb semiDecOrderedField_Real
                                        (real_2 klb semiDecOrderedField_Real) c)))}
                              in
                              let {
                               _evar_0_0 = \_ ->
                                ssr_have __ (\_ ->
                                  complex
                                    (real_div klb semiDecOrderedField_Real s0
                                      (real_mult klb semiDecOrderedField_Real
                                        (real_2 klb semiDecOrderedField_Real) d))
                                    d)}
                              in
                              case __top_assumption_1 of {
                               Prelude.True -> _evar_0_ __;
                               Prelude.False -> _evar_0_0 __}}
                            in
                            let {
                             _evar_0_0 = \_ ->
                              ssr_have __ (\_ ->
                                complex c
                                  (real_div klb semiDecOrderedField_Real s0
                                    (real_mult klb semiDecOrderedField_Real
                                      (real_2 klb semiDecOrderedField_Real) c)))}
                            in
                            case __top_assumption_0 of {
                             Prelude.Just x -> _evar_0_ x;
                             Prelude.Nothing -> _evar_0_0 __}}
                          in
                          let {
                           _evar_0_0 = \_ ->
                            complex c (real_opp klb semiDecOrderedField_Real d)}
                          in
                          case __top_assumption_ of {
                           Prelude.Just x -> _evar_0_ x;
                           Prelude.Nothing -> _evar_0_0 __}))))))))))) z __}

csqrt :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
         (MultivalueMonad a1 a2) -> (SemiDecOrderedField a1 a3) ->
         (ComplArchiSemiDecOrderedField a1 a3) -> (Complex a3) -> a2
csqrt klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 semiDecOrderedField_Real complArchiSemiDecOrderedField_Real z =
  euclidean_mlimit_PQ klb m_Monad0 multivalueMonad_description0
    m_MultivalueMonad0 semiDecOrderedField_Real
    complArchiSemiDecOrderedField_Real (Prelude.succ (Prelude.succ 0))
    (let {
      x = m_split klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
            semiDecOrderedField_Real
            (euclidean_max_dist klb m_Monad0 multivalueMonad_description0
              m_MultivalueMonad0 semiDecOrderedField_Real
              complArchiSemiDecOrderedField_Real (Prelude.succ (Prelude.succ 0))
              (complex0 klb semiDecOrderedField_Real) z)
            (prec klb semiDecOrderedField_Real
              ((Prelude.+)
                (addn
                  (muln (Prelude.succ (Prelude.succ 0))
                    (addn 0 (Prelude.succ 0))) (Prelude.succ 0)) (Prelude.succ
                0)))
            (prec klb semiDecOrderedField_Real
              ((Prelude.+)
                (addn
                  (muln (Prelude.succ (Prelude.succ 0))
                    (addn 0 (Prelude.succ 0))) (Prelude.succ 0)) (Prelude.succ
                0)))}
     in
     let {
      _evar_0_ = m_lift_dom m_Monad0 (\_top_assumption_ ->
                   let {
                    _evar_0_ = \_ ->
                     ssr_have
                       (csqrt_neq0 klb m_Monad0 multivalueMonad_description0
                         m_MultivalueMonad0 semiDecOrderedField_Real
                         complArchiSemiDecOrderedField_Real z)
                       (m_lift m_Monad0 (\_top_assumption_0 -> (,)
                         _top_assumption_0 Prelude.False))}
                   in
                   let {
                    _evar_0_0 = \_ ->
                     let {
                      _evar_0_0 = \_ ->
                       let {
                        _evar_0_0 = \_ ->
                         let {
                          _evar_0_0 = \_ ->
                           let {
                            _evar_0_0 = \_ ->
                             let {
                              _evar_0_0 = \_ ->
                               let {
                                _evar_0_0 = \_ ->
                                 m_unit m_Monad0 ((,)
                                   (complex0 klb semiDecOrderedField_Real)
                                   (ssr_have __ (\_ -> Prelude.True)))}
                               in
                               eq_rect_r
                                 (prec klb semiDecOrderedField_Real
                                   (addn
                                     (muln (Prelude.succ (Prelude.succ 0))
                                       (addn 0 (Prelude.succ 0))) (Prelude.succ
                                     0))) _evar_0_0
                                 (real_plus klb semiDecOrderedField_Real
                                   (prec klb semiDecOrderedField_Real
                                     ((Prelude.+)
                                       (addn
                                         (muln (Prelude.succ (Prelude.succ 0))
                                           (addn 0 (Prelude.succ 0)))
                                         (Prelude.succ 0)) (Prelude.succ 0)))
                                   (prec klb semiDecOrderedField_Real
                                     ((Prelude.+)
                                       (addn
                                         (muln (Prelude.succ (Prelude.succ 0))
                                           (addn 0 (Prelude.succ 0)))
                                         (Prelude.succ 0)) (Prelude.succ 0))))
                                 __}
                             in
                             eq_rect_r
                               (euclidean_max_dist klb m_Monad0
                                 multivalueMonad_description0 m_MultivalueMonad0
                                 semiDecOrderedField_Real
                                 complArchiSemiDecOrderedField_Real
                                 (Prelude.succ (Prelude.succ 0))
                                 (complex0 klb semiDecOrderedField_Real) z)
                               _evar_0_0
                               (real_plus klb semiDecOrderedField_Real
                                 (real_0 klb semiDecOrderedField_Real)
                                 (euclidean_max_dist klb m_Monad0
                                   multivalueMonad_description0
                                   m_MultivalueMonad0 semiDecOrderedField_Real
                                   complArchiSemiDecOrderedField_Real
                                   (Prelude.succ (Prelude.succ 0))
                                   (complex0 klb semiDecOrderedField_Real) z))
                               __}
                           in
                           eq_rect_r
                             (real_plus klb semiDecOrderedField_Real
                               (real_0 klb semiDecOrderedField_Real)
                               (euclidean_max_dist klb m_Monad0
                                 multivalueMonad_description0 m_MultivalueMonad0
                                 semiDecOrderedField_Real
                                 complArchiSemiDecOrderedField_Real
                                 (Prelude.succ (Prelude.succ 0))
                                 (complex0 klb semiDecOrderedField_Real) z))
                             _evar_0_0
                             (real_plus klb semiDecOrderedField_Real
                               (euclidean_max_dist klb m_Monad0
                                 multivalueMonad_description0 m_MultivalueMonad0
                                 semiDecOrderedField_Real
                                 complArchiSemiDecOrderedField_Real
                                 (Prelude.succ (Prelude.succ 0))
                                 (complex0 klb semiDecOrderedField_Real) z)
                               (real_0 klb semiDecOrderedField_Real)) __}
                         in
                         eq_rect_r (real_0 klb semiDecOrderedField_Real)
                           _evar_0_0
                           (real_plus klb semiDecOrderedField_Real
                             (prec klb semiDecOrderedField_Real
                               ((Prelude.+)
                                 (addn
                                   (muln (Prelude.succ (Prelude.succ 0))
                                     (addn 0 (Prelude.succ 0))) (Prelude.succ
                                   0)) (Prelude.succ 0)))
                             (real_opp klb semiDecOrderedField_Real
                               (prec klb semiDecOrderedField_Real
                                 ((Prelude.+)
                                   (addn
                                     (muln (Prelude.succ (Prelude.succ 0))
                                       (addn 0 (Prelude.succ 0))) (Prelude.succ
                                     0)) (Prelude.succ 0))))) __}
                       in
                       eq_rect_r
                         (real_plus klb semiDecOrderedField_Real
                           (prec klb semiDecOrderedField_Real
                             ((Prelude.+)
                               (addn
                                 (muln (Prelude.succ (Prelude.succ 0))
                                   (addn 0 (Prelude.succ 0))) (Prelude.succ 0))
                               (Prelude.succ 0)))
                           (real_opp klb semiDecOrderedField_Real
                             (prec klb semiDecOrderedField_Real
                               ((Prelude.+)
                                 (addn
                                   (muln (Prelude.succ (Prelude.succ 0))
                                     (addn 0 (Prelude.succ 0))) (Prelude.succ
                                   0)) (Prelude.succ 0))))) _evar_0_0
                         (real_plus klb semiDecOrderedField_Real
                           (real_opp klb semiDecOrderedField_Real
                             (prec klb semiDecOrderedField_Real
                               ((Prelude.+)
                                 (addn
                                   (muln (Prelude.succ (Prelude.succ 0))
                                     (addn 0 (Prelude.succ 0))) (Prelude.succ
                                   0)) (Prelude.succ 0))))
                           (prec klb semiDecOrderedField_Real
                             ((Prelude.+)
                               (addn
                                 (muln (Prelude.succ (Prelude.succ 0))
                                   (addn 0 (Prelude.succ 0))) (Prelude.succ 0))
                               (Prelude.succ 0)))) __}
                     in
                     eq_rect_r
                       (real_plus klb semiDecOrderedField_Real
                         (euclidean_max_dist klb m_Monad0
                           multivalueMonad_description0 m_MultivalueMonad0
                           semiDecOrderedField_Real
                           complArchiSemiDecOrderedField_Real (Prelude.succ
                           (Prelude.succ 0))
                           (complex0 klb semiDecOrderedField_Real) z)
                         (real_plus klb semiDecOrderedField_Real
                           (real_opp klb semiDecOrderedField_Real
                             (prec klb semiDecOrderedField_Real
                               ((Prelude.+)
                                 (addn
                                   (muln (Prelude.succ (Prelude.succ 0))
                                     (addn 0 (Prelude.succ 0))) (Prelude.succ
                                   0)) (Prelude.succ 0))))
                           (prec klb semiDecOrderedField_Real
                             ((Prelude.+)
                               (addn
                                 (muln (Prelude.succ (Prelude.succ 0))
                                   (addn 0 (Prelude.succ 0))) (Prelude.succ 0))
                               (Prelude.succ 0))))) _evar_0_0
                       (real_plus klb semiDecOrderedField_Real
                         (real_plus klb semiDecOrderedField_Real
                           (euclidean_max_dist klb m_Monad0
                             multivalueMonad_description0 m_MultivalueMonad0
                             semiDecOrderedField_Real
                             complArchiSemiDecOrderedField_Real (Prelude.succ
                             (Prelude.succ 0))
                             (complex0 klb semiDecOrderedField_Real) z)
                           (real_opp klb semiDecOrderedField_Real
                             (prec klb semiDecOrderedField_Real
                               ((Prelude.+)
                                 (addn
                                   (muln (Prelude.succ (Prelude.succ 0))
                                     (addn 0 (Prelude.succ 0))) (Prelude.succ
                                   0)) (Prelude.succ 0)))))
                         (prec klb semiDecOrderedField_Real
                           ((Prelude.+)
                             (addn
                               (muln (Prelude.succ (Prelude.succ 0))
                                 (addn 0 (Prelude.succ 0))) (Prelude.succ 0))
                             (Prelude.succ 0)))) __}
                   in
                   case _top_assumption_ of {
                    Prelude.True -> _evar_0_ __;
                    Prelude.False -> _evar_0_0 __})}
     in
     eq_rect_r (real_0 klb semiDecOrderedField_Real) _evar_0_
       (real_plus klb semiDecOrderedField_Real
         (prec klb semiDecOrderedField_Real
           ((Prelude.+)
             (addn
               (muln (Prelude.succ (Prelude.succ 0)) (addn 0 (Prelude.succ 0)))
               (Prelude.succ 0)) (Prelude.succ 0)))
         (real_opp klb semiDecOrderedField_Real
           (prec klb semiDecOrderedField_Real
             ((Prelude.+)
               (addn
                 (muln (Prelude.succ (Prelude.succ 0))
                   (addn 0 (Prelude.succ 0))) (Prelude.succ 0)) (Prelude.succ
               0))))) x) (\n x _ p2 ->
    case p2 of {
     Prelude.True ->
      let {
       x0 = m_split klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0
              semiDecOrderedField_Real
              (euclidean_max_dist klb m_Monad0 multivalueMonad_description0
                m_MultivalueMonad0 semiDecOrderedField_Real
                complArchiSemiDecOrderedField_Real (Prelude.succ (Prelude.succ
                0)) (complex0 klb semiDecOrderedField_Real) z)
              (prec klb semiDecOrderedField_Real
                ((Prelude.+)
                  (addn
                    (muln (Prelude.succ (Prelude.succ 0)) (Prelude.succ
                      (Prelude.succ n))) (Prelude.succ 0)) (Prelude.succ 0)))
              (prec klb semiDecOrderedField_Real
                ((Prelude.+)
                  (addn
                    (muln (Prelude.succ (Prelude.succ 0)) (Prelude.succ
                      (Prelude.succ n))) (Prelude.succ 0)) (Prelude.succ 0)))}
      in
      let {
       _evar_0_ = m_lift_dom m_Monad0 (\_top_assumption_ ->
                    let {
                     _evar_0_ = \_ ->
                      ssr_have
                        (csqrt_neq0 klb m_Monad0 multivalueMonad_description0
                          m_MultivalueMonad0 semiDecOrderedField_Real
                          complArchiSemiDecOrderedField_Real z)
                        (m_lift m_Monad0 (\_top_assumption_0 -> (,)
                          _top_assumption_0 Prelude.False))}
                    in
                    let {
                     _evar_0_0 = \_ ->
                      let {
                       _evar_0_0 = let {
                                    _evar_0_0 = let {
                                                 _evar_0_0 = let {
                                                              _evar_0_0 = 
                                                               let {
                                                                _evar_0_0 = 
                                                                 let {
                                                                  _evar_0_0 = \_ ->
                                                                   m_unit
                                                                     m_Monad0
                                                                     ((,)
                                                                     (complex0
                                                                       klb
                                                                       semiDecOrderedField_Real)
                                                                     (ssr_have
                                                                       __ (\_ ->
                                                                       Prelude.True)))}
                                                                 in
                                                                 eq_rect_r
                                                                   (prec klb
                                                                     semiDecOrderedField_Real
                                                                     (addn
                                                                       (muln
                                                                       (Prelude.succ
                                                                       (Prelude.succ
                                                                       0))
                                                                       (Prelude.succ
                                                                       (Prelude.succ
                                                                       n)))
                                                                       (Prelude.succ
                                                                       0)))
                                                                   _evar_0_0
                                                                   (real_plus
                                                                     klb
                                                                     semiDecOrderedField_Real
                                                                     (prec klb
                                                                       semiDecOrderedField_Real
                                                                       ((Prelude.+)
                                                                       (addn
                                                                       (muln
                                                                       (Prelude.succ
                                                                       (Prelude.succ
                                                                       0))
                                                                       (Prelude.succ
                                                                       (Prelude.succ
                                                                       n)))
                                                                       (Prelude.succ
                                                                       0))
                                                                       (Prelude.succ
                                                                       0)))
                                                                     (prec klb
                                                                       semiDecOrderedField_Real
                                                                       ((Prelude.+)
                                                                       (addn
                                                                       (muln
                                                                       (Prelude.succ
                                                                       (Prelude.succ
                                                                       0))
                                                                       (Prelude.succ
                                                                       (Prelude.succ
                                                                       n)))
                                                                       (Prelude.succ
                                                                       0))
                                                                       (Prelude.succ
                                                                       0))))}
                                                               in
                                                               eq_rect_r
                                                                 (euclidean_max_dist
                                                                   klb m_Monad0
                                                                   multivalueMonad_description0
                                                                   m_MultivalueMonad0
                                                                   semiDecOrderedField_Real
                                                                   complArchiSemiDecOrderedField_Real
                                                                   (Prelude.succ
                                                                   (Prelude.succ
                                                                   0))
                                                                   (complex0 klb
                                                                     semiDecOrderedField_Real)
                                                                   z) _evar_0_0
                                                                 (real_plus klb
                                                                   semiDecOrderedField_Real
                                                                   (real_0 klb
                                                                     semiDecOrderedField_Real)
                                                                   (euclidean_max_dist
                                                                     klb
                                                                     m_Monad0
                                                                     multivalueMonad_description0
                                                                     m_MultivalueMonad0
                                                                     semiDecOrderedField_Real
                                                                     complArchiSemiDecOrderedField_Real
                                                                     (Prelude.succ
                                                                     (Prelude.succ
                                                                     0))
                                                                     (complex0
                                                                       klb
                                                                       semiDecOrderedField_Real)
                                                                     z))}
                                                             in
                                                             eq_rect_r
                                                               (real_plus klb
                                                                 semiDecOrderedField_Real
                                                                 (real_0 klb
                                                                   semiDecOrderedField_Real)
                                                                 (euclidean_max_dist
                                                                   klb m_Monad0
                                                                   multivalueMonad_description0
                                                                   m_MultivalueMonad0
                                                                   semiDecOrderedField_Real
                                                                   complArchiSemiDecOrderedField_Real
                                                                   (Prelude.succ
                                                                   (Prelude.succ
                                                                   0))
                                                                   (complex0 klb
                                                                     semiDecOrderedField_Real)
                                                                   z)) _evar_0_0
                                                               (real_plus klb
                                                                 semiDecOrderedField_Real
                                                                 (euclidean_max_dist
                                                                   klb m_Monad0
                                                                   multivalueMonad_description0
                                                                   m_MultivalueMonad0
                                                                   semiDecOrderedField_Real
                                                                   complArchiSemiDecOrderedField_Real
                                                                   (Prelude.succ
                                                                   (Prelude.succ
                                                                   0))
                                                                   (complex0 klb
                                                                     semiDecOrderedField_Real)
                                                                   z)
                                                                 (real_0 klb
                                                                   semiDecOrderedField_Real))}
                                                in
                                                eq_rect_r
                                                  (real_0 klb
                                                    semiDecOrderedField_Real)
                                                  _evar_0_0
                                                  (real_plus klb
                                                    semiDecOrderedField_Real
                                                    (prec klb
                                                      semiDecOrderedField_Real
                                                      ((Prelude.+)
                                                        (addn
                                                          (muln (Prelude.succ
                                                            (Prelude.succ 0))
                                                            (Prelude.succ
                                                            (Prelude.succ n)))
                                                          (Prelude.succ 0))
                                                        (Prelude.succ 0)))
                                                    (real_opp klb
                                                      semiDecOrderedField_Real
                                                      (prec klb
                                                        semiDecOrderedField_Real
                                                        ((Prelude.+)
                                                          (addn
                                                            (muln (Prelude.succ
                                                              (Prelude.succ 0))
                                                              (Prelude.succ
                                                              (Prelude.succ n)))
                                                            (Prelude.succ 0))
                                                          (Prelude.succ 0)))))}
                                   in
                                   eq_rect_r
                                     (real_plus klb semiDecOrderedField_Real
                                       (prec klb semiDecOrderedField_Real
                                         ((Prelude.+)
                                           (addn
                                             (muln (Prelude.succ (Prelude.succ
                                               0)) (Prelude.succ (Prelude.succ
                                               n))) (Prelude.succ 0))
                                           (Prelude.succ 0)))
                                       (real_opp klb semiDecOrderedField_Real
                                         (prec klb semiDecOrderedField_Real
                                           ((Prelude.+)
                                             (addn
                                               (muln (Prelude.succ (Prelude.succ
                                                 0)) (Prelude.succ (Prelude.succ
                                                 n))) (Prelude.succ 0))
                                             (Prelude.succ 0))))) _evar_0_0
                                     (real_plus klb semiDecOrderedField_Real
                                       (real_opp klb semiDecOrderedField_Real
                                         (prec klb semiDecOrderedField_Real
                                           ((Prelude.+)
                                             (addn
                                               (muln (Prelude.succ (Prelude.succ
                                                 0)) (Prelude.succ (Prelude.succ
                                                 n))) (Prelude.succ 0))
                                             (Prelude.succ 0))))
                                       (prec klb semiDecOrderedField_Real
                                         ((Prelude.+)
                                           (addn
                                             (muln (Prelude.succ (Prelude.succ
                                               0)) (Prelude.succ (Prelude.succ
                                               n))) (Prelude.succ 0))
                                           (Prelude.succ 0))))}
                      in
                      eq_rect_r
                        (real_plus klb semiDecOrderedField_Real
                          (euclidean_max_dist klb m_Monad0
                            multivalueMonad_description0 m_MultivalueMonad0
                            semiDecOrderedField_Real
                            complArchiSemiDecOrderedField_Real (Prelude.succ
                            (Prelude.succ 0))
                            (complex0 klb semiDecOrderedField_Real) z)
                          (real_plus klb semiDecOrderedField_Real
                            (real_opp klb semiDecOrderedField_Real
                              (prec klb semiDecOrderedField_Real
                                ((Prelude.+)
                                  (addn
                                    (muln (Prelude.succ (Prelude.succ 0))
                                      (Prelude.succ (Prelude.succ n)))
                                    (Prelude.succ 0)) (Prelude.succ 0))))
                            (prec klb semiDecOrderedField_Real
                              ((Prelude.+)
                                (addn
                                  (muln (Prelude.succ (Prelude.succ 0))
                                    (Prelude.succ (Prelude.succ n)))
                                  (Prelude.succ 0)) (Prelude.succ 0)))))
                        _evar_0_0
                        (real_plus klb semiDecOrderedField_Real
                          (real_plus klb semiDecOrderedField_Real
                            (euclidean_max_dist klb m_Monad0
                              multivalueMonad_description0 m_MultivalueMonad0
                              semiDecOrderedField_Real
                              complArchiSemiDecOrderedField_Real (Prelude.succ
                              (Prelude.succ 0))
                              (complex0 klb semiDecOrderedField_Real) z)
                            (real_opp klb semiDecOrderedField_Real
                              (prec klb semiDecOrderedField_Real
                                ((Prelude.+)
                                  (addn
                                    (muln (Prelude.succ (Prelude.succ 0))
                                      (Prelude.succ (Prelude.succ n)))
                                    (Prelude.succ 0)) (Prelude.succ 0)))))
                          (prec klb semiDecOrderedField_Real
                            ((Prelude.+)
                              (addn
                                (muln (Prelude.succ (Prelude.succ 0))
                                  (Prelude.succ (Prelude.succ n))) (Prelude.succ
                                0)) (Prelude.succ 0)))) __}
                    in
                    case _top_assumption_ of {
                     Prelude.True -> _evar_0_ __;
                     Prelude.False -> _evar_0_0 __})}
      in
      eq_rect_r (real_0 klb semiDecOrderedField_Real) _evar_0_
        (real_plus klb semiDecOrderedField_Real
          (prec klb semiDecOrderedField_Real
            ((Prelude.+)
              (addn
                (muln (Prelude.succ (Prelude.succ 0)) (Prelude.succ
                  (Prelude.succ n))) (Prelude.succ 0)) (Prelude.succ 0)))
          (real_opp klb semiDecOrderedField_Real
            (prec klb semiDecOrderedField_Real
              ((Prelude.+)
                (addn
                  (muln (Prelude.succ (Prelude.succ 0)) (Prelude.succ
                    (Prelude.succ n))) (Prelude.succ 0)) (Prelude.succ 0))))) x0;
     Prelude.False -> m_unit m_Monad0 ((,) x Prelude.False)})

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

r_ComplArchiSemiDecOrderedField :: ComplArchiSemiDecOrderedField AERN2.CKleenean
                                   AERN2.CReal
r_ComplArchiSemiDecOrderedField = (\ f _ -> AERN2.limit f)

c_sqrt2 :: (Complex AERN2.CReal) -> M (Complex AERN2.CReal)
c_sqrt2 =
  csqrt k_LazyBool (unsafeCoerce m_Monad)
    (unsafeCoerce multivalueMonad_description) (unsafeCoerce m_MultivalueMonad)
    r_SemiDecOrderedField r_ComplArchiSemiDecOrderedField

