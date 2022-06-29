Require Import Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellNatInteger.
Require ExtrHaskellZInteger.
Extraction Language Haskell.
Unset Extraction SafeImplicits.

Require Import ZArith_base.

Extract Inlined Constant Z.of_nat => "".
Extract Inlined Constant Z.add => "(Prelude.+)".
Extract Inlined Constant Z.sub => "(Prelude.-)".
Extract Inlined Constant Z.succ => "(Prelude.+ 1)".
Extract Inlined Constant Z.opp => "Prelude.negate".

Require Import Base.

Extract Inlined Constant projP1 => "".

Require Import Kleene.

(* Declare the existence of Kleeneans *)
Parameter K : Set.
Axiom K_LazyBool : LazyBool K.

(* interpreting Kleeneans *)
Extract Inlined Constant K => "AERN2.CKleenean".

(* Erase the type class parameter and map to concrete types in Haskell. *)
Extraction Implicit lazy_bool_true [ LB ].
Extract Constant lazy_bool_true => "AERN2.ckleenean Prelude.True".

Extraction Implicit lazy_bool_false [ LB ].
Extract Constant lazy_bool_false => "AERN2.ckleenean Prelude.False".

Extraction Implicit lazy_bool_neg [ LB ].
Extract Constant lazy_bool_neg => "\x -> __uc (OGB.not (__K x))".

Extraction Implicit lazy_bool_or [ LB ].
Extract Constant lazy_bool_or => "\x y -> __uc ((__K x) OGB.|| (__K y))".

Extraction Implicit lazy_bool_and [ LB ].
Extract Constant lazy_bool_and => "\x y -> __uc ((__K x) OGB.&& (__K y))".

Extraction Implicit lazy_bool_defined_is_bool [ LB ].
Extract Inlined Constant lazy_bool_defined_is_bool => "Prelude.error ""UNREALIZED lazy_bool_defined_is_bool"" ".

(* Test extraction of Kleeneans *)

Section K_Dummy_Defs.
  Generalizable Variable K.
  Context `(klb : LazyBool K).
  Definition k_test := lazy_bool_and lazy_bool_true lazy_bool_false.
End K_Dummy_Defs.

(* Extraction Implicit k_test [ 1 ]. *)
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
Extract Constant M "a" => "a".

Extraction Implicit Monad_fun_map [ Monad ].
Extract Inlined Constant Monad_fun_map => "__uc".

Extraction Implicit Monad_unit [ Monad ].
Extract Inlined Constant Monad_unit => "__uc".

Extraction Implicit Monad_mult [ Monad ].
Extract Inlined Constant Monad_mult => "__uc".

Extract Constant MultivalueMonad_description => "(Prelude.error ""UNREALIZED MultivalueMonad_description"")".


(* Shortcut extractions for improved readability. *)
Extraction Implicit M_unit [ M_Monad ].
Extract Inlined Constant M_unit => "__uc".
Extraction Implicit M_mult [ M_Monad ].
Extract Inlined Constant M_mult => "__uc".
Extraction Implicit M_lift [ M_Monad ].
Extract Inlined Constant M_lift => "__uc".
Extraction Implicit M_lift_dom [ M_Monad ].
Extract Inlined Constant M_lift_dom => "__uc".
Extraction Implicit mjoin [ M_Monad ].
Extract Inlined Constant mjoin => "__uc".

Extraction Implicit MultivalueMonad_base_monad_traces_lift [ klb M_Monad MultivalueMonad_description MultivalueMonad ].
Extract Constant MultivalueMonad_base_monad_traces_lift => "(\ x0 f -> __uc (\n -> Prelude.foldl (Prelude.flip (__uc f)) (x0) [0 .. ((n :: Prelude.Integer) Prelude.- 1)]))".

Extraction Implicit MultivalueMonad_base_monad_hprop_elim [ klb M_Monad MultivalueMonad_description MultivalueMonad ].
Extract Inlined Constant MultivalueMonad_base_monad_hprop_elim => "__uc".

Extraction Implicit multivalued_choice [ klb M_Monad MultivalueMonad_description MultivalueMonad ].
Extract Constant multivalued_choice => "(\k1 k2 -> __uc (AERN2.select (__K k1) (__K k2)))".

Extraction Implicit M_hprop_elim_f [ klb M_Monad MultivalueMonad_description M_MultivalueMonad ].
Extract Inlined Constant M_hprop_elim_f => "__uc".

Extraction Implicit choose [ klb M_Monad MultivalueMonad_description M_MultivalueMonad ].

Extraction Implicit M_paths [ klb M_Monad MultivalueMonad_description M_MultivalueMonad ].

Extraction Implicit semidec_or [ klb ].
Extraction Implicit semidec_and [ klb ].


(* (\ _ m -> m)  *)

(* MultivalueMonad_destruct *)
(* (\ _ m -> m) *)

Extraction Implicit select [ klb M_Monad MultivalueMonad_description M_MultivalueMonad ].

(* Some shortcuts for efficiency. *)
Extraction Implicit M_countable_lift [ klb M_Monad MultivalueMonad_description M_MultivalueMonad ].
Extract Inlined Constant M_countable_lift => "__uc". 

(* Test extraction of multivaluemonad *)
Definition m_test := @select _ _ _ _ _ M_MultivalueMonad.
(* Extraction "M_Test" m_test. *)

Require Import Real.

(* Assume that there is R*)
Parameter R : Set.
Axiom R_SemiDecOrderedField : @SemiDecOrderedField  _ K_LazyBool R.
Axiom R_ComplArchiSemiDecOrderedField : @ComplArchiSemiDecOrderedField _ _ _ R_SemiDecOrderedField.

Extract Inlined Constant R => "AERN2.CReal".

Extraction Implicit real_0 [ klb SemiDecOrderedField ].
Extract Constant real_0 => "(__uc (0 :: AERN2.CReal))".

Extraction Implicit real_1 [ klb SemiDecOrderedField ].
Extract Constant real_1 => "(__uc (1 :: AERN2.CReal))".

Extraction Implicit real_2 [ klb SemiDecOrderedField_Real ].
Extract Constant real_2 => "(__uc (2 :: AERN2.CReal))".

(* Extraction Implicit real_3 [ klb SemiDecOrderedField_Real ]. *)
(* Extract Constant real_3 => "(__uc (3 :: AERN2.CReal))". *)

Extraction Implicit real_plus [ klb SemiDecOrderedField ].
Extract Constant real_plus => "(\x y -> __uc (((__R x) Prelude.+ (__R y))))".

Extraction Implicit real_mult [ klb SemiDecOrderedField ].
Extract Constant real_mult => "(\x y -> __uc (((__R x) Prelude.* (__R y))))".

Extraction Implicit real_opp [ klb SemiDecOrderedField ].
Extract Constant real_opp => "(\x -> __uc (Prelude.negate (__R x)))".

Extraction Implicit real_inv [ klb SemiDecOrderedField ].
Extract Constant real_inv => "(\x -> __uc (Prelude.recip (__R x)))".

Extraction Implicit real_lt_semidec [ klb SemiDecOrderedField ].
Extract Constant real_lt_semidec => "(\ x y -> __uc ((__R x) OGB.< (__R y)))".

Extraction Implicit real_limit_p [ klb SemiDecOrderedField_Real ComplArchiSemiDecOrderedField ].
Extract Constant real_limit_p => "(\ f -> __uc (AERN2.limit (__seqR f)))".

Extraction Implicit real_limit [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].
Extraction Implicit real_limit_P [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].
Extraction Implicit real_limit_P_p [ klb SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].
Extraction Implicit real_limit_P_lt [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].
Extraction Implicit real_limit_P_lt_p [ klb SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].
Extraction Implicit real_mslimit_P [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].
Extraction Implicit real_mslimit_P_p [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].
Extraction Implicit real_mslimit_P_lt [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].
Extraction Implicit real_mslimit_P_lt_p [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].

Extraction Implicit M_split [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ].

(* Some optional shortcuts for increased efficiency. *)
Extraction Implicit IZreal [ klb SemiDecOrderedField_Real ].
Extract Constant IZreal => "(\z -> __uc (AERN2.creal z))".
Extraction Implicit real_minus [ klb SemiDecOrderedField_Real ].
Extract Constant real_minus => "(\x y -> __uc (((__R x) Prelude.- (__R y))))".
Extraction Implicit real_div [ klb SemiDecOrderedField_Real ].
Extract Constant real_div => "(\x y -> __uc (((__R x) Prelude./ (__R y))))".
Extraction Implicit prec [ klb SemiDecOrderedField_Real ].
Extract Constant prec => "(\n -> __uc ((0.5 :: AERN2.CReal) Prelude.^ n))".

Extraction Implicit abs [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].

Extraction Implicit abs_prop [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].

(* Test extraction of R *)
Section Real_tests.
  Local Open Scope Real_scope.

  Generalizable Variables K M R.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
    {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
    {M_MultivalueMonad : MultivalueMonad}
    {R : Type}
    {R_OF : SemiDecOrderedField R}.
  
  Definition real_test1 := (- real_1) + (IZreal 2) - (prec 2).
End Real_tests.

Extraction Implicit real_test1 [ klb R_OF ].
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

Extraction Implicit real_3 [ klb SemiDecOrderedField_Real ].
Extract Constant real_3 => "(__uc (3 :: AERN2.CReal))".

Extraction Implicit CIVT [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].
Extraction Implicit root_approx [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].
Extraction Implicit halving [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].
Extraction Implicit trisect [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].
Extraction Implicit M_uniq_pick [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].

Definition R_CIVT := @CIVT _ _ _ _ _ M_MultivalueMonad _ _ R_ComplArchiSemiDecOrderedField.

Extraction "IVT" R_CIVT.

(* maximum *)
Require Import Minmax.

Extraction Implicit real_max_prop [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].
Extraction Implicit real_max [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].

Definition R_real_max := @real_max _ _ _ _ _ M_MultivalueMonad _ _ R_ComplArchiSemiDecOrderedField.
Extraction "Max" R_real_max.

(* magnitude *)
Require Import testsearch.

Extraction Implicit weaken_orM_r [ M_Monad ].

Extraction Implicit epsilon_smallest_choose_M [ klb M_Monad MultivalueMonad_description M_MultivalueMonad ].

Extraction Implicit epsilon_smallest_PQ_M [ klb M_Monad MultivalueMonad_description M_MultivalueMonad ].

Require Import magnitude.

Extraction Implicit magnitude [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ].
Extraction Implicit magnitude1 [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ].
Extraction Implicit magnitude2 [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ].
Extraction Implicit dec_x_lt_2 [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ].

Extraction Implicit Zpow [ klb SemiDecOrderedField_Real ].

Definition R_magnitude := @magnitude _ _ _ _ _ M_MultivalueMonad _ R_SemiDecOrderedField.
Extraction "Magnitude" R_magnitude.

Require Import RealRing.

Extraction Implicit pow [ klb SemiDecOrderedField_Real ].

Require Import Complex.

Extraction Implicit complex0 [ klb SemiDecOrderedField_Real ].

Require Import Euclidean.

Extraction Implicit euclidean_max_dist [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real].

Extraction Implicit euclidean_mlimit_PQ [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real].

Extraction Implicit euclidean_max_norm [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real].

Extraction Implicit euclidean_limit [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real].

Extraction Implicit euclidean_zero [ klb SemiDecOrderedField_Real].

Extraction Implicit euclidean_opp [ klb SemiDecOrderedField_Real].

Extraction Implicit euclidean_plus [ klb SemiDecOrderedField_Real].

Extraction Implicit euclidean_minus [ klb SemiDecOrderedField_Real].

(* sqrt *)
Require Import sqrt.

Extraction Implicit sqrt [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].

Extraction Implicit sqrt_pos [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].

Extraction Implicit scale [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ].

Extraction Implicit restr_sqrt [ klb SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].

Extraction Implicit sqrt_approx_fast [ klb SemiDecOrderedField_Real ].

Extraction Implicit sqrt_approx [ klb SemiDecOrderedField_Real ].


Definition R_sqrt2 := @sqrt _ _ _ _ _ M_MultivalueMonad _ _ R_ComplArchiSemiDecOrderedField.
Extraction "Sqrt" R_sqrt2.

Extraction Implicit csqrt [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].

Extraction Implicit csqrt_neq0 [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ComplArchiSemiDecOrderedField_Real ].

Extraction Implicit complex_nonzero_cases [ klb M_Monad MultivalueMonad_description M_MultivalueMonad SemiDecOrderedField_Real ].

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
__seqR :: a -> (Prelude.Integer -> AERN2.CReal)
__seqR = UC.unsafeCoerce

*)
