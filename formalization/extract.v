Require Import Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellNatInteger.
Require ExtrHaskellZInteger.
Extraction Language Haskell.
Unset Extraction SafeImplicits.

Require Import ZArith_base.

Extract Inlined Constant Z.of_nat => "P.id".
Extract Inlined Constant Z.add => "(P.+)".
Extract Inlined Constant Z.sub => "(P.-)".
Extract Inlined Constant Z.succ => "(P.+ 1)".
Extract Inlined Constant Z.opp => "P.negate".

Require Import Base.

Extract Inlined Constant projP1 => "".

Require Import Kleene.

(* Declare the existence of Kleeneans *)
Parameter types : RealTypes.
Axiom klb : LazyBool_K types.

(* interpreting Kleeneans *)
Extraction Implicit K [ r ].
Extract Inlined Constant K => "AERN2.CKleenean".

(* Erase the type class parameter and map to concrete types in Haskell. *)
Extraction Implicit lazy_bool_true [ types LazyBool_K ].
Extract Constant lazy_bool_true => "(AERN2.ckleenean P.True)".

Extraction Implicit lazy_bool_false [ types LazyBool_K ].
Extract Constant lazy_bool_false => "(AERN2.ckleenean P.False)".

Extraction Implicit lazy_bool_neg [ types LazyBool_K ].
Extract Constant lazy_bool_neg => "OGB.not".

Extraction Implicit lazy_bool_or [ types LazyBool_K ].
Extract Constant lazy_bool_or => "(OGB.||)".

Extraction Implicit lazy_bool_and [ types LazyBool_K ].
Extract Constant lazy_bool_and => "(OGB.&&)".

Extraction Implicit lazy_bool_defined_is_bool [ types LazyBool_K ].
Extract Inlined Constant lazy_bool_defined_is_bool => "(P.error ""UNREALIZED lazy_bool_defined_is_bool"")".

(* Test extraction of Kleeneans *)

Section K_Dummy_Defs.

Context {types : RealTypes} { klb : LazyBool_K types }.

#[local] Notation "^K" := (@K types) (at level 0).

  Definition k_test := lazy_bool_and lazy_bool_true lazy_bool_false.
End K_Dummy_Defs.

(* Extraction Implicit k_test [ types klb ]. *)
(* Extraction "K_Test" k_test. *)

Require Import Monad.
Require Import ClassicalMonads.
Require Import MultivalueMonad.

(* Declare the existence of multivaluemonad *)

Axiom mvmM : MultivalueMonad_M types.

(* interpreting the Multivalue Monad as the identity monad in Haskell *)
Extraction Implicit M [ r ].
Extract Constant M "a" => "a".

(* interpreting multivaluemonad *)

Extraction Implicit M_Monad [ types MultivalueMonad_M ].

Extraction Implicit M_lift [ types mvmM ].
Extract Constant M_lift => "P.id".

Extraction Implicit M_unit [ types mvmM ].
Extract Constant M_unit => "P.id".

Extraction Implicit M_mult [ types mvmM ].
Extract Constant M_mult => "P.id".

(* Shortcut extractions for improved readability. *)
Extraction Implicit M_lift_dom [ types mvmM ].
Extract Constant M_lift_dom => "P.id".
Extraction Implicit mjoin [ types mvmM ].
Extract Constant mjoin => "P.id".

Extraction Implicit M_base_monad_traces_lift [ types MultivalueMonad_M ].
Extract Constant M_base_monad_traces_lift => "(\ x0 f -> (\n -> P.foldl (P.flip f) (x0) [0 .. ((n :: P.Integer) P.- 1)]))".

(* Extraction Implicit M_base_monad_hprop_elim [ types MultivalueMonad_M ]. *)
(* Extract Inlined Constant M_base_monad_hprop_elim => "__uc". *)

Extraction Implicit multivalued_choice [ types MultivalueMonad_M ].
Extract Constant multivalued_choice => "AERN2.select".

Extraction Implicit M_hprop_elim_f [ types mvmM ].
Extract Constant M_hprop_elim_f => "P.id".

Extraction Implicit choose [ types mvmM ].

Extraction Implicit M_paths  [ types mvmM ].

Extraction Implicit semidec_or [ types mvmM ].
Extraction Implicit semidec_and [ types mvmM ].


(* (\ _ m -> m)  *)

(* MultivalueMonad_destruct *)
(* (\ _ m -> m) *)

Extraction Implicit select  [ types mvmM ].

(* Some shortcuts for efficiency. *)
Extraction Implicit M_countable_lift [ types mvmM ].
Extract Constant M_countable_lift => "P.id". 

(* Test extraction of multivaluemonad *)
Definition m_test := @select _ mvmM.
(* Extraction "M_Test" m_test. *)

Require Import Real.

Axiom sofReal : @SemiDecOrderedField_Real types.
Axiom casofReal : @ComplArchiSemiDecOrderedField_Real types.

Extraction Implicit Real [ r ].
Extract Inlined Constant Real => "AERN2.CReal".

Extraction Implicit real_0 [ types SemiDecOrderedField_Real ].
Extract Inlined Constant real_0 => "(0 :: AERN2.CReal)".

Extraction Implicit real_1 [ types SemiDecOrderedField_Real ].
Extract Inlined Constant real_1 => "(1 :: AERN2.CReal)".

Extraction Implicit real_2 [ types sofReal ].
Extract Inlined Constant real_2 => "(2 :: AERN2.CReal)".

(* Extraction Implicit real_3 [ klb SemiDecOrderedField_Real ]. *)
(* Extract Inlined Constant real_3 => "(3 :: AERN2.CReal)". *)

Extraction Implicit real_plus [ types SemiDecOrderedField_Real ].
Extract Inlined Constant real_plus => "(+)".

Extraction Implicit real_mult [ types SemiDecOrderedField_Real ].
Extract Inlined Constant real_mult => "(P.*)".

Extraction Implicit real_opp [ types SemiDecOrderedField_Real ].
Extract Inlined Constant real_opp => "P.negate".

Extraction Implicit real_inv [ types SemiDecOrderedField_Real ].
Extract Inlined Constant real_inv => "P.recip".

Extraction Implicit real_lt_semidec [ types SemiDecOrderedField_Real ].
Extract Inlined Constant real_lt_semidec => "(OGB.<)".

Extraction Implicit real_limit_p [ types ComplArchiSemiDecOrderedField_Real ].
Extract Constant real_limit_p => "AERN2.limit".

Extraction Implicit real_limit  [ types casofReal ].
Extraction Implicit real_limit_P  [ types casofReal ].
Extraction Implicit real_limit_P_p  [ types casofReal ].
Extraction Implicit real_limit_P_lt  [ types casofReal ].
Extraction Implicit real_limit_P_lt_p  [ types casofReal ].
Extraction Implicit real_mslimit_P  [ types casofReal ].
Extraction Implicit real_mslimit_P_p  [ types casofReal ].
Extraction Implicit real_mslimit_P_lt  [ types casofReal ].
Extraction Implicit real_mslimit_P_lt_p  [ types casofReal ].

Extraction Implicit M_split  [ types casofReal ].

(* Some optional shortcuts for increased efficiency. *)
Extraction Implicit IZreal [ types sofReal ].
Extract Constant IZreal => "AERN2.creal".
Extraction Implicit Nreal [ types sofReal ].
Extract Constant Nreal => "AERN2.creal".
Extraction Implicit real_minus [ types sofReal ].
Extract Inlined Constant real_minus => "(-)".
Extraction Implicit real_div [ types sofReal ].
Extract Inlined Constant real_div => "(/)".
Extraction Implicit prec [ types sofReal ].
Extract Constant prec => "((0.5 :: AERN2.CReal) P.^)".

Extraction Implicit abs [ types casofReal ].

Extraction Implicit abs_prop [ types casofReal ].

(* Test extraction of R *)
Section Real_tests.
  Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

  #[local] Notation "^K" := (@K types) (at level 0).
  #[local] Notation "^M" := (@M types) (at level 0).
  #[local] Notation "^Real" := (@Real types) (at level 0).

  Definition real_test1 := (- real_1) + (IZreal 2) - (prec 2).
End Real_tests.

Extraction Implicit real_test1 [ types casofReal ].
(* Extraction "R_Test1" real_test1. *)

Definition R_test2 := @real_limit_p _ casofReal.
(* Extraction "R_Test2" R_test2. *)

Extract Inductive bool => "P.Bool" [ "P.True" "P.False" ].
Extract Inductive sumbool => "P.Bool" [ "P.True" "P.False" ].

Extract Inductive sigT => "(,)" ["(,)"].
Extract Inductive prod => "(,)"  [ "(,)" ].

Extract Constant Nat.log2 => "(MNP.integer P.. Logs.integerLog2)".

(* Sewon's lab seminar talk material*)
(* Maximum *)

(* root finding function *)
Require Import IVT.

Extraction Implicit real_3 [ types casofReal ].
Extract Constant real_3 => "(3 :: AERN2.CReal)".

Extraction Implicit CIVT [ types casofReal ].
Extraction Implicit root_approx [ types casofReal ].
Extraction Implicit halving [ types casofReal ].
Extraction Implicit trisect [ types casofReal ].
Extraction Implicit M_uniq_pick [ types casofReal ].

(* Extraction "IVT" CIVT. *)

(* maximum *)
Require Import Minmax.

Extraction Implicit real_max_prop [ types casofReal ].
Extraction Implicit real_max [ types casofReal ].

(* Extraction "Max" real_max. *)

(* magnitude *)
Require Import testsearch.

Extraction Implicit weaken_orM_r [ types casofReal ].

Extraction Implicit epsilon_smallest_choose_M  [ types casofReal ].

Extraction Implicit epsilon_smallest_PQ_M [ types casofReal ].

Require Import magnitude.

Extraction Implicit magnitude [ types casofReal ].
Extraction Implicit magnitude1 [ types casofReal ].
Extraction Implicit magnitude2 [ types casofReal ].
Extraction Implicit dec_x_lt_2 [ types casofReal ].

Extraction Implicit Zpow [ types casofReal ].

(* Extraction "Magnitude" magnitude.magnitude. *)

Require Import RealRing.

Extraction Implicit pow [ types sofReal ].

Require Import Complex.

Extraction Implicit complex0  [ types casofReal ].

Require Import Euclidean.

Extraction Implicit euclidean_max_dist [ types casofReal ].
Extraction Implicit euclidean_mlimit_PQ [ types casofReal ].
Extraction Implicit euclidean_max_norm [ types casofReal ].
Extraction Implicit euclidean_limit [ types casofReal ].
Extraction Implicit euclidean_zero [ types casofReal ].
Extraction Implicit euclidean_opp [ types casofReal ].
Extraction Implicit euclidean_plus [ types casofReal ].
Extraction Implicit euclidean_minus [ types casofReal ].
Extraction Implicit caseS' [ types ].
Extraction Implicit dim_succ_destruct [ types ].

(* sqrt *)
Require Import sqrt.

Extraction Implicit sqrt [ types casofReal ].
Extraction Implicit sqrt_pos [ types casofReal ].

Extraction Implicit scale [ types casofReal ].

Extraction Implicit restr_sqrt [ types casofReal ].
Extraction Implicit sqrt_approx_fast [ types casofReal ].
Extraction Implicit sqrt_approx [ types casofReal ].

(* Extraction "Sqrt" sqrt.sqrt. *)

Extraction Implicit csqrt [ types casofReal ].
Extraction Implicit csqrt_neq0 [ types casofReal ].
Extraction Implicit complex_nonzero_cases [ types casofReal ].

(* Extraction "CSqrt" csqrt. *)

Require Import Subsets.

Extraction Implicit split_euclidean2 [ types ].
Extraction Implicit make_euclidean2 [ types ].
Extraction Implicit make_ball2 [ types ].

Require Import simpletriangle.
Extraction Implicit Tn_ball [ types casofReal ].
Extraction Implicit Tn_col [ types casofReal ].
Extraction Implicit Tn_row [ types casofReal ].
Extraction Implicit Tn [ types casofReal ].
(* Extraction "Tn" Tn. *)

Extraction Implicit multi_triangles_compact [ types casofReal ].
(* Extraction "MTn" multi_triangles_compact. *)

Require Import SierpinskiTriangle.
Extraction Implicit one_half [ types casofReal ].
Extraction Implicit point_point_mid [ types casofReal ].
Extraction Implicit point_ball_mid [ types casofReal ].
Extraction Implicit ST_split_ball [ types casofReal ].
Extraction Implicit STn [ types casofReal ].

Extraction Implicit STR_initial_ball [ types casofReal ].
Extraction Implicit STR_v1 [ types casofReal ].
Extraction Implicit STR_v2 [ types casofReal ].
Extraction Implicit STR_v3 [ types casofReal ].
Extraction Implicit STRn [ types casofReal ].
(* Extraction "STRn" STRn. *)

Extraction Implicit real_sqrt_3 [ types casofReal ].
Extraction Implicit STE_initial_ball [ types casofReal ].
Extraction Implicit STE_v1 [ types casofReal ].
Extraction Implicit STE_v2 [ types casofReal ].
Extraction Implicit STE_v3 [ types casofReal ].
Extraction Implicit STEn [ types casofReal ].
Extraction "STEn" STEn.
               
(* Require Import Nabla. *)

(* Require Import Coq.Reals.Abstract.ConstructiveMinMax. *)

(* Recursive Extraction CRmin. *)
(*

The Haskell module will require the packages specified in stack.yaml in folder extracted-examples.
 
In the generated Haskell files, add the following imports:

import Prelude ((+),(-),(/))
import qualified Prelude as P
import MixedTypesNumPrelude (ifThenElse)
import qualified Numeric.OrdGenericBool as OGB
import qualified Unsafe.Coerce as UC
import qualified Control.Monad
import qualified Data.Functor
import qualified MixedTypesNumPrelude as MNP
import qualified Math.NumberTheory.Logarithms as Logs
import qualified AERN2.Real as AERN2

*)
