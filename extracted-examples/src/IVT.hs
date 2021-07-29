module IVT where

import qualified Prelude
import qualified Numeric.OrdGenericBool as OGB
import MixedTypesNumPrelude (ifThenElse)
import qualified MixedTypesNumPrelude as MNP
import qualified Math.NumberTheory.Logarithms as Logs
import qualified AERN2.Real as AERN2

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
type M a =  a 

lift_domM :: (a1 -> M a2) -> (M a1) -> M a2
lift_domM f x =
  Prelude.id (Prelude.id f x)

type Semidec = AERN2.CKleenean

choose :: Semidec -> Semidec -> M Prelude.Bool
choose h h0 =
  Prelude.id (\h4 -> h4) (AERN2.select h h0)

iPReal_2 :: Prelude.Integer -> AERN2.CReal
iPReal_2 p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (Prelude.*) ((Prelude.+) 1 1) ((Prelude.+) 1 (iPReal_2 p0)))
    (\p0 -> (Prelude.*) ((Prelude.+) 1 1) (iPReal_2 p0))
    (\_ -> (Prelude.+) 1 1)
    p

iPReal :: Prelude.Integer -> AERN2.CReal
iPReal p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> (Prelude.+) 1 (iPReal_2 p0))
    (\p0 -> iPReal_2 p0)
    (\_ -> 1)
    p

iZReal :: Prelude.Integer -> AERN2.CReal
iZReal z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\n -> iPReal n)
    (\n -> Prelude.negate (iPReal n))
    z

slimit :: (Prelude.Integer -> AERN2.CReal) -> AERN2.CReal
slimit =
  AERN2.limit

mslimit :: (Prelude.Integer -> M AERN2.CReal) -> AERN2.CReal
mslimit x =
  let {x0 = Prelude.id x} in Prelude.id (Prelude.id slimit x0)

m_uniq_pick :: (AERN2.CReal -> AERN2.CReal) -> AERN2.CReal -> AERN2.CReal ->
               AERN2.CReal -> AERN2.CReal -> M Prelude.Bool
m_uniq_pick f _ b c _ =
  choose ((OGB.<) (f b) 0) ((OGB.<) 0 (f c))

real3 :: AERN2.CReal
real3 =
  iZReal ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))

trisect :: (AERN2.CReal -> AERN2.CReal) -> AERN2.CReal -> AERN2.CReal -> M
           ((,) AERN2.CReal AERN2.CReal)
trisect f a b =
  Prelude.id (\h0 ->
    case h0 of {
     Prelude.True -> (,)
      ((Prelude./) ((Prelude.+) ((Prelude.*) 2 a) b) real3) b;
     Prelude.False -> (,) a
      ((Prelude./) ((Prelude.+) a ((Prelude.*) 2 b)) real3)})
    (m_uniq_pick f a ((Prelude./) ((Prelude.+) ((Prelude.*) 2 a) b) real3)
      ((Prelude./) ((Prelude.+) a ((Prelude.*) 2 b)) real3) b)

halving :: (AERN2.CReal -> AERN2.CReal) -> AERN2.CReal -> AERN2.CReal -> M
           ((,) AERN2.CReal AERN2.CReal)
halving f a b =
  let {one = trisect f a b} in
  lift_domM (\q ->
    case q of {
     (,) x s -> let {x0 = trisect f x s} in Prelude.id (\h1 -> h1) x0}) one

root_approx :: (AERN2.CReal -> AERN2.CReal) -> Prelude.Integer -> M
               ((,) AERN2.CReal AERN2.CReal)
root_approx f n =
  nat_rect (Prelude.id ((,) 0 1)) (\_ iHn ->
    lift_domM (\x ->
      case x of {
       (,) x0 s -> let {x1 = halving f x0 s} in Prelude.id (\h -> h) x1}) iHn)
    n

cIVT :: (AERN2.CReal -> AERN2.CReal) -> AERN2.CReal
cIVT f =
  mslimit (\n ->
    let {x = root_approx f (Prelude.succ n)} in
    Prelude.id (\h -> case h of {
                       (,) x0 _ -> x0}) x)

