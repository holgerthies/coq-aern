module Tn where

import qualified Prelude

import JSON

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
__seqR :: a -> (Prelude.Integer -> AERN2.CReal)
__seqR = UC.unsafeCoerce

__ :: any
__ = Prelude.error "Logical or arity value used"

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

data LazyBool lB =
   Build_LazyBool lB lB (lB -> lB) (lB -> lB -> lB) (lB -> lB -> lB) 
 (lB -> () -> Prelude.Bool)

type Semidec k = k

data SemiDecOrderedField k real =
   Build_SemiDecOrderedField real real (real -> real -> real) (real -> real
                                                              -> real) 
 (real -> real) (real -> () -> real) (real -> real -> Semidec k)

real_0 :: a2
real_0 = (__uc (0 :: AERN2.CReal))

real_1 :: a2
real_1 = (__uc (1 :: AERN2.CReal))

real_plus :: a2 -> a2 -> a2
real_plus = (\x y -> __uc (((__R x) Prelude.+ (__R y))))

real_mult :: a2 -> a2 -> a2
real_mult = (\x y -> __uc (((__R x) Prelude.* (__R y))))

nreal :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> Prelude.Integer ->
         a2
nreal klb semiDecOrderedField_Real n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> real_0)
    (\n0 -> real_plus real_1 (nreal klb semiDecOrderedField_Real n0))
    n

prec :: Prelude.Integer -> a2
prec = (\n -> __uc ((0.5 :: AERN2.CReal) Prelude.^ n))

npow2 :: Prelude.Integer -> Prelude.Integer
npow2 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.succ 0)
    (\n0 -> (Prelude.*) (npow2 n0) (Prelude.succ (Prelude.succ 0)))
    n

data Euclidean real =
   Nil
 | Cons Prelude.Integer real (Euclidean real)
  deriving Prelude.Show


type Ball real = (,) (Euclidean real) real

make_euclidean2 :: a1 -> a1 -> Euclidean a1
make_euclidean2 x y =
  Cons (Prelude.succ 0) x (Cons 0 y Nil)

make_ball :: a1 -> a1 -> a1 -> Ball a1
make_ball x y r =
  (,) (make_euclidean2 x y) r

tn_ball :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> Prelude.Integer ->
           Prelude.Integer -> Prelude.Integer -> Ball a2
tn_ball klb semiDecOrderedField_Real n k j =
  make_ball
    (real_mult
      (nreal klb semiDecOrderedField_Real
        ((Prelude.+) ((Prelude.*) (Prelude.succ (Prelude.succ 0)) k)
          (Prelude.succ 0))) (prec (Prelude.succ n)))
    (real_mult
      (nreal klb semiDecOrderedField_Real
        ((Prelude.+) ((Prelude.*) (Prelude.succ (Prelude.succ 0)) j)
          (Prelude.succ 0))) (prec (Prelude.succ n))) (prec (Prelude.succ n))

tn_col :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> Prelude.Integer ->
          Prelude.Integer -> Prelude.Integer -> (([]) (Ball a2)) -> ([])
          (Ball a2)
tn_col klb semiDecOrderedField_Real n k j l =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (:) (tn_ball klb semiDecOrderedField_Real n k 0) l)
    (\j' ->
    tn_col klb semiDecOrderedField_Real n k j' ((:)
      (tn_ball klb semiDecOrderedField_Real n k j) l))
    j

tn_row :: (LazyBool a1) -> (SemiDecOrderedField a1 a2) -> Prelude.Integer ->
          Prelude.Integer -> (([]) (Ball a2)) -> ([]) (Ball a2)
tn_row klb semiDecOrderedField_Real n k l =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    tn_col klb semiDecOrderedField_Real n 0 (sub (npow2 n) (Prelude.succ 0))
      l)
    (\k' ->
    tn_row klb semiDecOrderedField_Real n k'
      (tn_col klb semiDecOrderedField_Real n k
        (sub (sub (npow2 n) k) (Prelude.succ 0)) l))
    k

tn :: Prelude.Integer -> ([]) (Ball a2)
tn n =
  tn_row __ {- 2nd argument (klb) of Tn -} __
    {- 4th argument (SemiDecOrderedField_Real) of Tn -} n
    (sub (npow2 n) (Prelude.succ 0)) ([])

r_Tn :: Prelude.Integer -> ([]) (Ball AERN2.CReal)
r_Tn =
  tn

toJSON :: [Ball AERN2.CReal] -> Prelude.String
toJSON = ballsToJSON Prelude.. Prelude.map (\(Cons _ x (Cons _ y _), r) -> ((x,y),r))

