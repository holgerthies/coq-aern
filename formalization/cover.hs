module Cover where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) ->
            Prelude.Integer -> a1
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

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
real_1 :: a2
real_1 = (__uc (1 :: AERN2.CReal))

real_plus :: a2 -> a2 -> a2
real_plus = (\x y -> __uc (((__R x) Prelude.+ (__R y))))

real_minus :: a2 -> a2 -> a2
real_minus = (\x y -> __uc (((__R x) Prelude.- (__R y))))

real_div :: a2 -> a2 -> a2
real_div = (\x y -> __uc (((__R x) Prelude./ (__R y))))

real_2 :: a2
real_2 = (__uc (2 :: AERN2.CReal))

data Euclidean real =
   Nil
 | Cons Prelude.Integer real (Euclidean real)

caseS' :: Prelude.Integer -> (Euclidean a1) -> (a1
          -> (Euclidean a1) -> a2) -> a2
caseS' _ v h =
  case v of {
   Nil -> __;
   Cons _ h0 t -> h h0 t}

dim_succ_destruct :: Prelude.Integer -> (Euclidean
                     a1) -> (,) a1 (Euclidean a1)
dim_succ_destruct n x =
  caseS' n x (\h t -> (,) h t)

type Real = () -- AXIOM TO BE REALIZED
  

type Ball = (,) (Euclidean Real) Real

split_euclidean2 :: (Euclidean Real) -> (,) 
                    Real Real
split_euclidean2 p =
  let {x = dim_succ_destruct (Prelude.succ 0) p}
  in
  case x of {
   (,) x0 p0 ->
    let {x1 = dim_succ_destruct 0 p0} in
    case x1 of {
     (,) x2 _ -> (,) x0 x2}}

make_euclidean2 :: Real -> Real -> Euclidean Real
make_euclidean2 x y =
  Cons (Prelude.succ 0) x (Cons 0 y Nil)

make_ball :: Real -> Real -> Real -> Ball
make_ball x y r =
  (,) (make_euclidean2 x y) r

process :: Ball -> (,) ((,) Ball Ball) Ball
process b =
  let {r' = real_div (snd b) real_2} in
  let {s = split_euclidean2 (fst b)} in
  case s of {
   (,) x p -> (,) ((,) ((,)
    (make_euclidean2 (real_minus x r')
      (real_minus p r')) r') ((,)
    (make_euclidean2 (real_minus x r')
      (real_plus p r')) r')) ((,)
    (make_euclidean2 (real_plus x r')
      (real_minus p r')) r')}

coverIter :: Prelude.Integer -> Ball -> ([]) Ball
coverIter n b =
  nat_rect ((:) b ([])) (\n' _ ->
    let {p = process b} in
    case p of {
     (,) a b0 ->
      case a of {
       (,) a0 b1 ->
        let {l2 = coverIter n' b1} in
        let {l3 = coverIter n' b0} in
        (:) a0 (app l2 l3)}}) n

coverT :: Prelude.Integer -> ([]) Ball
coverT n =
  coverIter n
    (make_ball (real_div real_1 real_2)
      (real_div real_1 real_2)
      (real_div real_1 real_2))

