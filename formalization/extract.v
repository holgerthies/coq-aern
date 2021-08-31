Require Import Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellNatInteger.
Require ExtrHaskellZInteger.
Extraction Language Haskell.

Require Import ZArith_base.


(* Require Import Real. *)
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
Extract Constant M_Monad => "Build_Monad (\ _ _ _ m -> m) (\_ a -> unsafeCoerce a) (\ _ m -> m)".
Extract Constant M_MultivalueMonad => "Build_MultivalueMonad (Prelude.error ""UNREALIZED MultivalueMonad_base_monad_hprop_elim"") (Prelude.error ""UNREALIZED MultivalueMonad_base_monad_traces_lift"") (\k1 k2 _ -> unsafeCoerce (AERN2.select k1 k2)) (Prelude.error ""UNREALIZED MultivalueMonad_description_is_equiv"") (\ _ m -> m)".
(* Extract Inlined Constant M_paths => "(\ x0 f n -> Prelude.foldl (Prelude.flip f) x0 [0 .. (n Prelude.- 1)])".
Extract Inlined Constant M_countable_lift => "Prelude.id".  *)

(* Test extraction of multivaluemonad *)
(* Definition m_test := @select _ _ _ _ _ M_MultivalueMonad.
Extraction "M_Test" m_test. *)

Require Import RealAxioms.

(* Assume that there is Real*)
Parameter Real : Set.
Axiom Real_SemiDecOrderedField : @SemiDecOrderedField  _ K_LazyBool Real.
Axiom Real_ComplArchiSemiDecOrderedField : @ComplArchiSemiDecOrderedField _ _ _ Real_SemiDecOrderedField.

Extract Inlined Constant Real => "AERN2.CReal".

Extract Constant Real_SemiDecOrderedField => "Build_SemiDecOrderedField 0 1 (Prelude.+) (Prelude.*) Prelude.negate (\ x _ -> Prelude.recip x) (OGB.<)".

Extract Constant Real_ComplArchiSemiDecOrderedField => "(\ f _ -> AERN2.limit f)".

(* Some shortcuts for efficiency. Not necessary. *)
Extract Constant IZreal => "(\_ _ z -> __uc (AERN2.creal z))".
Extract Constant real_minus => "(\_ _ x y -> __uc (((__R x) Prelude.- (__R y))))".
Extract Constant real_div => "(\_ _ x y -> __uc (((__R x) Prelude./ (__R y))))".
Extract Constant prec => "(\_ _ n -> __uc ((0.5 :: AERN2.CReal) Prelude.^ n))".

(* Test extraction of Real *)
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

Definition R_test1 := @real_test1 _ _ Real_SemiDecOrderedField.
(* Extraction "R_Test1" R_test1. *)

Definition R_test2 := @real_limit_p _ _ _ _ Real_ComplArchiSemiDecOrderedField.
(* Extraction "R_Test2" R_test2. *)

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extract Inductive sigT => "(,)" ["(,)"].
Extract Inductive prod => "(,)"  [ "(,)" ].

Extract Inlined Constant Nat.log2 => "(MNP.integer Prelude.<<< Logs.integerLog2)".

(* Sewon's lab seminar talk material*)
(* Maximum *)

(* TODO: update the rest of the file *)

(* root finding function *)
Require Import IVT.
Extraction "IVT" CIVT.

(* maximum *)
Require Import Minmax.
Extraction "Max" Realmax.

(* magnitude *)
Require Import magnitude.
Extraction "Magnitude" magnitude.magnitude.

(* sqrt *)
Require Import sqrt.
Extraction "Sqrt" restr_sqrt.

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
