Require Import Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellNatInteger.
Require ExtrHaskellZInteger.
Extraction Language Haskell.

Require Import ZArith_base.


(* Require Import R. *)
Require Import Kleene.

(* Declare the existence of Kleeneans *)
Parameter K : Set.
Axiom K_LazyBool : LazyBool K.

(* interpreting Kleeneans *)
Extract Inlined Constant K => "AERN2.CKleenean".
Extract Constant K_LazyBool => "Build_LazyBool (AERN2.ckleenean Prelude.True) (AERN2.ckleenean Prelude.False) OGB.not (OGB.||) (OGB.&&) (\k _ -> Prelude.error ""UNREALIZED lazy_bool_defined_is_bool"")".

(* Test extraction of Kleeneans *)

Section K_Dummy_Defs.
  Generalizable Variable K.
  Context `(klb : LazyBool K).
  Definition lb_test := lazy_bool_and lazy_bool_true lazy_bool_false.
End K_Dummy_Defs.
Definition k_test := @lb_test K_LazyBool.
(* Extraction "K_Test" k_test.  *)

Require Import Monad.
Require Import ClassicalMonads.
Require Import MultivalueMonad.

(* Declare the existence of multivaluemonad *)
Parameter M : Type -> Type.
Axiom M_Monad : Monad M.
Axiom MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad.
Axiom M_MultivalueMonad : @MultivalueMonad _ K_LazyBool _ _ MultivalueMonad_description.

(* interpreting multivaluemonad *)
Extract Constant M "a" => "a".
Extract Constant M_Monad => "Build_Monad (\ _ _ f -> __uc f) (\_ a -> __uc a) (\ _ m -> m)".
Extract Constant MultivalueMonad_description => "(Prelude.error ""UNREALIZED MultivalueMonad_description"")".
Extract Constant M_MultivalueMonad => "Build_MultivalueMonad (\ _ _ x -> __uc x) (\ _ _ x0 f -> __uc (\n -> Prelude.foldl (Prelude.flip (__uc f)) (x0) [0 .. ((n :: Prelude.Integer) Prelude.- 1)])) (\k1 k2 _ -> __uc (AERN2.select k1 k2)) (\ _ m -> m) (\ _ m -> m)".

(* The following text provides some explanation of the above rule, in particular the second argument of
 Build_MultivalueMonad.

* Copied from MultivalueMonad.v:

Class MultivalueMonad :=
  {
    MultivalueMonad_base_monad_hprop_elim : forall A, is_hprop A -> is_equiv (Monad_unit A);
    MultivalueMonad_base_monad_traces_lift : lifts_lifted_trace M_Monad;
    multivalued_choice : forall x y : K, x = lazy_bool_true \/ y = lazy_bool_true -> M ({ x = lazy_bool_true } + { (y = lazy_bool_true) });

    MultivalueMonad_description_is_mono : Monoid_hom_is_mono _ _ MultivalueMonad_description;
    MultivalueMonad_description_is_equiv : forall A, is_equiv (Monad_fun_map _ _ (M_description A));

    MultivalueMonad_destruct : forall A (X : M A), M  {x : A | projP1 _ _ (M_description A X) x};
  }.

Definition lifts_lifted_trace := 
  forall P : nat -> Type,
  forall R : (forall n, P n -> P (S n) -> Prop),
  forall X : M (P O),
  forall f : (forall n (x : P n), M {y : P (S n) | R n x y}),
    {F : M {f : forall n, (P n) | forall m, R m (f m) (f (S m))} |
     sections_to_fibers _ (lifted_projP1 _ _ F) = trace_lifts_to_fiber P R X f}.

* A simplified version of the above Haskell implementation of a lifts_lifted_trace:

multivalueMonad_base_monad_traces_lift _ _ x0 f n 
  = foldl (flip f) x0 [0 .. (n - 1)]

which can be informally written as:

  = f(n-1, f(n-2, ... f(1, f(0, x0))))

* Example of use within extracted code:

m_paths :: (LazyBool a1) -> (Monad a2) -> (Monoid_hom a2 (NPset Any)) ->
           (MultivalueMonad a1 a2) -> a2 -> (Prelude.Integer -> a3 -> a2) -> a2
m_paths klb m_Monad0 multivalueMonad_description0 m_MultivalueMonad0 x x0 =
  projP1
    (multivalueMonad_base_monad_traces_lift klb m_Monad0
      multivalueMonad_description0 m_MultivalueMonad0 x x0)

*)

(* Some shortcuts for efficiency. Not necessary. *)
Extract Constant M_countable_lift => "(\_ _ _ _ f -> (__uc f))". 

(* Test extraction of multivaluemonad *)
(* Definition m_test := @select _ _ _ _ _ M_MultivalueMonad.
Extraction "M_Test" m_test. *)

Require Import RealAxioms.

(* Assume that there is R*)
Parameter R : Set.
Axiom R_SemiDecOrderedField : @SemiDecOrderedField  _ K_LazyBool R.
Axiom R_ComplArchiSemiDecOrderedField : @ComplArchiSemiDecOrderedField _ _ _ R_SemiDecOrderedField.

Extract Inlined Constant R => "AERN2.CReal".

Extract Constant R_SemiDecOrderedField => "Build_SemiDecOrderedField 0 1 (Prelude.+) (Prelude.*) Prelude.negate (\ x _ -> Prelude.recip x) (OGB.<)".

Extract Constant R_ComplArchiSemiDecOrderedField => "(\ f _ -> AERN2.limit f)".

(* Some shortcuts for efficiency. Not necessary. *)
Extract Constant IZreal => "(\_ _ z -> __uc (AERN2.creal z))".
Extract Constant real_minus => "(\_ _ x y -> __uc (((__R x) Prelude.- (__R y))))".
Extract Constant real_div => "(\_ _ x y -> __uc (((__R x) Prelude./ (__R y))))".
Extract Constant prec => "(\_ _ n -> __uc ((0.5 :: AERN2.CReal) Prelude.^ n))".

(* Test extraction of R *)
Section Real_tests.
  Local Open Scope Real_scope.

  Generalizable Variables K M R.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
    {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
    {M_MultivalueMonad : MultivalueMonad}
    {R : Type}
    {SemiDecOrderedField_Real : SemiDecOrderedField R}.
  
  Definition real_test1 := (IZreal 2) - (prec 2).
End Real_tests.

Definition R_test1 := @real_test1 _ _ R_SemiDecOrderedField.
(* Extraction "R_Test1" R_test1. *)

Definition R_test2 := @real_limit_p _ _ _ _ R_ComplArchiSemiDecOrderedField.
(* Extraction "R_Test2" R_test2. *)

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extract Inductive sigT => "(,)" ["(,)"].
Extract Inductive prod => "(,)"  [ "(,)" ].

Extract Inlined Constant Nat.log2 => "(MNP.integer Prelude.. Logs.integerLog2)".

(* Sewon's lab seminar talk material*)
(* Maximum *)

(* root finding function *)
Require Import IVT.
Definition R_CIVT := @CIVT _ _ _ _ _ M_MultivalueMonad _ _ R_ComplArchiSemiDecOrderedField.
Extraction "IVT" R_CIVT.

(* maximum *)
Require Import Minmax.
Definition R_real_max := @real_max _ _ _ _ _ M_MultivalueMonad _ _ R_ComplArchiSemiDecOrderedField.
Extraction "Max" R_real_max.

(* magnitude *)
Require Import magnitude.
Definition R_magnitude := @magnitude _ _ _ _ _ M_MultivalueMonad _ R_SemiDecOrderedField.
Extraction "Magnitude" R_magnitude.

(* sqrt *)
Require Import sqrt.
Definition R_sqrt2 := @sqrt _ _ _ _ _ M_MultivalueMonad _ _ R_ComplArchiSemiDecOrderedField.
Extraction "Sqrt" R_sqrt2.
Definition C_sqrt2 := @csqrt _ _ _ _ _ M_MultivalueMonad _ _ R_ComplArchiSemiDecOrderedField.
Extraction "CSqrt" C_sqrt2.

(* Require Import Nabla. *)

(* Require Import Coq.Reals.Abstract.ConstructiveMinMax. *)

(* Recursive Extraction CRmin. *)

(*

The Haskell module will require the following packages:
- cdar-mBound >= 0.1.0.1
- collect-errors >= 0.1.4
- mixed-types-num >= 0.5.3
- aern2-mp >= 0.2.1
- aern2-real >= 0.2.1
- integer-logarithms

In the generated Haskell files, add the following imports and definitions:

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

*)
