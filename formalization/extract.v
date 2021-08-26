Require Import Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellNatInteger.
Require ExtrHaskellZInteger.
Extraction Language Haskell.

(* Require Import Real. *)
Require Import Kleene.

(* Declare the existence of Kleeneans *)
Parameter K : Set.
Axiom K_LazyBool : LazyBool K.

(* interpreting Kleeneans *)
Extract Inlined Constant K => "AERN2.CKleenean".

Extract Inlined Constant lazy_bool_true => "(\ _ -> (AERN2.ckleenean Prelude.True))".
Extract Inlined Constant lazy_bool_false => "(\ _ -> (AERN2.ckleenean Prelude.False))".
Extract Inlined Constant lazy_bool_neg => "(\ _ -> OGB.not)".
Extract Inlined Constant lazy_bool_and => "(\ _ -> (OGB.&&))".
Extract Inlined Constant lazy_bool_or => "(\ _ -> (OGB.||))".

(* Test extraction of Kleeneans *)
Section K_Dummy_Defs.
  Generalizable Variable K.
  Context `(klb : LazyBool K).
  Definition lb_test := lazy_bool_and lazy_bool_true lazy_bool_false.
End K_Dummy_Defs.
Definition k_test := @lb_test K_LazyBool.
(* Extraction "K_Test" k_test. *)

Require Import Monad.
Require Import ClassicalMonads.
Require Import MultivalueMonad.

(* Declare the existence of multivaluemonad *)
Parameter M : Type -> Type.
Axiom M_Monad : Monad M.
Axiom MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad.
Axiom M_MultivalueMonad : @MultivalueMonad _ K_LazyBool _ _ MultivalueMonad_description.

(* interpreting multivaluemonad *)
Extract Constant M "a" => " a ".
Extract Inlined Constant M_unit => "Prelude.id".
Extract Inlined Constant M_mult => "Prelude.id".
Extract Inlined Constant M_lift => "Prelude.id".
Extract Inlined Constant M_hprop_elim_f => "Prelude.id".
Extract Inlined Constant M_paths => "(\ x0 f n -> Prelude.foldl (Prelude.flip f) x0 [0 .. (n Prelude.- 1)])".
Extract Inlined Constant M_countable_lift => "Prelude.id". 

(* Test extraction of multivaluemonad *)
Definition m_test := @select _ _ _ _ _ M_MultivalueMonad.
Extraction "M_Test" m_test.

(* TODO: update the rest of the file *)

(* Assume that there is Real*)
Axiom R : ComplArchiSemiDecOrderedField.

Require Import Minmax.
Definition extract_max := @real_max R.
Extraction "Max" R.

(* Real is Real, K is LazyBoolean, and M T is T *)
Extract Inlined Constant Real => "AERN2.CReal".
Extract Inlined Constant K => "AERN2.CKleenean".

(* Axioms for Kleenean *)
Extract Inlined Constant trueK => "(AERN2.ckleenean Prelude.True)".
Extract Inlined Constant falseK => "(AERN2.ckleenean Prelude.False)".
                                   
Extract Inlined Constant kneg => "OGB.not".
Extract Inlined Constant kland => "(OGB.&&)".
Extract Inlined Constant klor => "(OGB.||)".

Extract Inlined Constant select => "AERN2.select".

(* Axioms for Multivalueness *)
Extract Constant M "a" => " a ".
Extract Inlined Constant unitM => "Prelude.id".
Extract Inlined Constant multM => "Prelude.id".
Extract Inlined Constant liftM => "Prelude.id".

Extract Inlined Constant elimM => "Prelude.id".
Extract Inlined Constant pathsM => "(\ x0 f n -> Prelude.foldl (Prelude.flip f) x0 [0 .. (n Prelude.- 1)])".
(* Extracted countableLiftM is too slow. *)
Extract Inlined Constant countableLiftM => "Prelude.id". 

(* Exact Real Number Operations *)
Extract Inlined Constant Real0 => "0".
Extract Inlined Constant Real1 => "1".

Extract Inlined Constant Realplus => "(Prelude.+)".
Extract Inlined Constant Realmult => "(Prelude.*)".
Extract Inlined Constant Realopp => "Prelude.negate".
Extract Inlined Constant Realinv => "Prelude.recip".
Extract Inlined Constant Reallt_semidec => "(OGB.<)".
Extract Inlined Constant Realgt_semidec => "(OGB.>)".
Extract Inlined Constant Real_limit_p => "AERN2.limit".

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

(* some shortcuts for efficiency. Not necessary *)
Extract Inlined Constant  Real2 => "2".
Extract Inlined Constant Realminus => "(Prelude.-)".
Extract Inlined Constant Realdiv => "(Prelude./)".
Extract Inlined Constant prec => "(0.5 Prelude.^)".

Extract Inductive sigT => "(,)" ["(,)"].
Extract Inductive prod => "(,)"  [ "(,)" ].

Extract Inlined Constant Nat.log2 => "(MNP.integer Prelude.<<< Logs.integerLog2)".

(* Sewon's lab seminar talk material*)
(* Maximum *)

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

In the generated Haskell files, add the following imports:

import qualified Numeric.OrdGenericBool as OGB
import MixedTypesNumPrelude (ifThenElse)
import qualified MixedTypesNumPrelude as MNP
import qualified Math.NumberTheory.Logarithms as Logs
import qualified AERN2.Real as AERN2

*)
