Require Export ZArith_base.
Require Import Base.
Require Import Kleene.

(*********************************************************)
(* A library for abstract real number with constructive  *)
(* reasoning; if you have a Type, it has a computational *)
(* content with meta theory of realizability.            *)
(* In the mere proposition level, decidability and order *)
(* completion axiom is assumed.                          *)
(* We have a naming convention where mere proposition    *)
(* starts its name with W and a contructive but multival *)
(* object starts its name with M                         *)
(*********************************************************)

(* basic axioms for our type theory *)

Parameter Real : Set.

Declare Scope Real_scope.
Delimit Scope Real_scope with Real.
Bind Scope Real_scope with Real.

Local Open Scope Real_scope.

(*********************************************************)
(** **           Symbols of Realype Real                       *)
(*********************************************************)
(*********************************************************)
(** ***          Constants Symbols                       *)
(*********************************************************)
Parameter Real0 : Real.
Parameter Real1 : Real.


(*********************************************************)
(** **           Operator Symbols                        *)
(*********************************************************)
Parameter Realplus : Real -> Real -> Real.
Parameter Realmult : Real -> Real -> Real.
Parameter Realopp : Real -> Real.
Parameter Realinv : forall {z}, z <> Real0 -> Real.


(*********************************************************)
(** **           Boolean Symbols                         *)
(*********************************************************)
Parameter Realltb : Real -> Real -> K.

(*********************************************************)
(** **           Predicate Symbols                       *)
(*********************************************************)
Parameter Reallt : Real -> Real -> Prop.

(*********************************************************)
(** **           Metric of Realype Real                        *)
(*********************************************************)
Parameter dist : Real -> Real -> Real.




Infix "+" := Realplus : Real_scope.
Infix "*" := Realmult : Real_scope.
Notation "- x" := (Realopp x) : Real_scope.
Notation "/ x" := (Realinv x) : Real_scope.

Infix "<" := Reallt : Real_scope.
Infix "<?" := Realltb : Real_scope.


(***********************************************************)

(**********)
Definition Realgt (z1 z2:Real) : Prop := z2 < z1.
Definition Realle (z1 z2:Real) : Prop := z1 < z2 \/ z1 = z2.
Definition Realge (z1 z2:Real) : Prop := Realgt z1 z2 \/ z1 = z2.
Definition Realminus (z1 z2:Real) : Real := z1 + - z2.
Definition Realdiv (z1 :Real) {z2:Real} (p:z2<>Real0) :  Real := z1 * / p.
Definition abs (z:Real) : Real := dist Real0 z.
Definition Realgtb (z1 z2: Real) : K := z2 <? z1.

(**********)
Infix "-" := Realminus : Real_scope.
Infix "/" := Realdiv   : Real_scope.

Infix "<=" := Realle : Real_scope.
Infix ">=" := Realge : Real_scope.
Infix ">"  := Realgt : Real_scope.
Infix ">?" := Realgtb : Real_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : Real_scope.
Notation "x <= y < z"  := (x <= y /\ y <  z) : Real_scope.
Notation "x < y < z"   := (x <  y /\ y <  z) : Real_scope.
Notation "x < y <= z"  := (x <  y /\ y <= z) : Real_scope.



(*********************************************************)
(** **   Injection from Z, nat to Real                      *)
(*********************************************************)

Inductive EZ :=
  Epos : nat -> EZ
| Ezero : EZ
| Eneg : nat -> EZ.

Fixpoint NReal (n : nat) : Real :=
  match n with
  | O => Real0
  | S n => Real1 + NReal n
  end.
Arguments NReal n%nat.

Fixpoint EZReal (z : EZ) : Real :=
  match z with
  | Epos n => NReal n
  | Ezero => Real0
  | Eneg n => - (NReal n)
  end.


(**********)
Fixpoint IPReal_2 (p:positive) : Real :=
  match p with
  | xH => Real1 + Real1
  | xO p => (Real1 + Real1) * IPReal_2 p
  | xI p => (Real1 + Real1) * (Real1 + IPReal_2 p)
  end.

Definition IPReal (p:positive) : Real :=
  match p with
  | xH => Real1
  | xO p => IPReal_2 p
  | xI p => Real1 + IPReal_2 p
  end.
Arguments IPReal p%positive : simpl never.

Definition IZReal (z:Z) : Real :=
  match z with
  | Z0 => Real0
  | Zpos n => IPReal n
  | Zneg n => - IPReal n
  end.
Arguments IZReal z%Z : simpl never.

(**********)
Fixpoint INReal (n:nat) : Real :=
  match n with
  | O => Real0
  | S O => Real1
  | S n => INReal n + Real1
  end.
Arguments INReal n%nat.
  




(*********************************************************)
(** *            Axioms of Realype Real                        *)
(** neq_path is just a general assumption in Prop, as a  *)
(** mere proposition. inv_unif says that equality of an  *)
(** inversion only matters on the denumerator. Need to   *)
(** whether it is derivable...                           *)
(*********************************************************)

Lemma neq_path : forall z1 z2 : Real, forall p1 p2 : (z1 <> z2), p1 = p2.
Proof.
  intros; apply irrl.
Qed.

Hint Resolve neq_path: Realiny.
Lemma inv_unif : forall z1 z2 : Real, forall p1 : z1 <> Real0, forall p2 : z2 <> Real0,
        z1 = z2 -> /p1 = /p2.
Proof.
  intros.
  induction H.
  assert (p1 = p2) by apply irrl.
  induction H; auto.
Qed.
  
Hint Resolve inv_unif: Realiny.
(*********************************************************)
(** *            Field axioms                            *)
(*********************************************************)

Axiom Realplus_comm : forall r1 r2:Real, r1 + r2 = r2 + r1.
Axiom Realplus_assoc : forall r1 r2 r3:Real, r1 + r2 + r3 = r1 + (r2 + r3).
Axiom Realplus_inv : forall r:Real, r + - r = Real0.
Axiom Realplus_unit : forall r:Real, Real0 + r = r.

Hint Resolve Realplus_comm Realplus_assoc Realplus_inv Realplus_unit: Realiny.

Axiom Realmult_comm : forall r1 r2:Real, r1 * r2 = r2 * r1.
Axiom Realmult_assoc : forall r1 r2 r3:Real, r1 * r2 * r3 = r1 * (r2 * r3).
Axiom Realmult_inv : forall (r:Real) (p : r <> Real0), / p * r = Real1.
Axiom Realmult_unit : forall r:Real, Real1 * r = r.

Hint Resolve Realmult_comm Realmult_assoc Realmult_inv Realmult_unit: Realiny.

Axiom Realmult_plus_distr: forall r1 r2 r3:Real, r1 * (r2 + r3) = r1 * r2 + r1 * r3.
Hint Resolve Realmult_plus_distr: Realiny.

Axiom Real1_neq_Real0 : Real1 <> Real0.
Hint Resolve Real1_neq_Real0: Realiny.


(************************************c*********************)
(** *    Order axioms                                    *)
(*********************************************************)
(*********************************************************)
(** **   Realotal Order                                     *)
(*********************************************************)

(**********)
Axiom Real1_gt_Real0 : Real1 > Real0.

(**********)
Axiom Realtotal_order : forall r1 r2 : Real, r1 < r2 \/ r1 = r2 \/ r1 > r2.

(**********)
Axiom Reallt_nlt : forall r1 r2 : Real, r1 < r2 -> ~ r2 < r1.

(**********)
Axiom Reallt_lt_lt : forall r1 r2 r3:Real, r1 < r2 -> r2 < r3 -> r1 < r3.

(**********)
Axiom Reallt_plus_lt : forall r r1 r2:Real, r1 < r2 -> r + r1 < r + r2.

(**********)
Axiom
  Reallt_mult_pos_lt : forall r r1 r2:Real, Real0 < r -> r1 < r2 -> r * r1 < r * r2.

(**********)
Axiom Realltb_lt_t : forall x y : Real, Realltb x y = trueK <-> x < y.
Axiom Realltb_lt_f : forall x y : Real, Realltb x y = falseK <-> y < x.

Lemma Reallt_semidec : forall x y : Real, semidec (x < y).
Proof.
  intros x y. exists (x <? y).
  exact (Realltb_lt_t x y).
Qed.

Lemma Realgt_semidec : forall x y : Real, semidec (x > y).
Proof.
  intros x y.
  exists (x >? y).
  exact (Realltb_lt_t y x).  
Qed.



Hint Resolve Real1_gt_Real0 Realtotal_order Reallt_nlt Reallt_lt_lt Reallt_plus_lt Reallt_mult_pos_lt: Realiny.
Hint Resolve Realltb_lt_t Realltb_lt_f Reallt_semidec Realgt_semidec: Realiny.



(**********************************************************)
(** *    Order Completeness of Real; need to make it derived *)
(**      from the metric completeness of Real                *)
(**      Currently it ways every nonempty bounded above   *)
(**      set has a supremum                               *)
(**********************************************************)
Definition W_nemp (c : Real -> Prop) := exists z, c z.
Definition W_upb (c : Real -> Prop) (u : Real) := forall z : Real, c z -> z <= u.
Definition W_upbd (c : Real -> Prop) := exists u, W_upb c u.
Definition W_sup (c : Real -> Prop) (s : Real)
  := W_upb c s /\ (forall s', W_upb c s' -> s <= s').
Axiom W_complete :
  forall c : Real -> Prop, W_nemp c ->  W_upbd c -> exists z, W_sup c z. 

(**********************************************************)
(** **    Metric Completeness of Real                         *)
(**********************************************************)
(**********************************************************)
(** ***  Realhough there are many facts that are not axioms  *)
(** below, we have to list them here to make the axiom of *)
(** constructive limit which requires precision embedding *)
(** and to define the precision embedding, we need to     *)
(** the fact that Real2 is nonzero...                        *)
(** Realhe above order completion is not computable hence it *)
(** has the endtype exists, ... In contrary, the construc *)
(** tive limit is constructive hence it has its endtype   *)
(** {x | P x }                                            *)
(**********************************************************)



(*** Some utility constants ***)
Definition Real2 : Real := IZReal 2.

Lemma Reallt_n_Sn : forall x, x < x + Real1.
Proof.
intro.
pose proof Real1_gt_Real0.
rewrite <- Realplus_unit at 1.
rewrite Realplus_comm.
apply (Reallt_plus_lt x).
auto with Realiny.
Qed.

Lemma Reallt_0_2 : Real0 < Real2.
Proof.
  unfold Real2.
  unfold IZReal.
  unfold IPReal.
  unfold IPReal_2.  
  apply Reallt_lt_lt with (Real0 + Real1).
  apply Reallt_n_Sn.
  rewrite Realplus_comm.
   apply Reallt_plus_lt.
   replace Real1 with (Real0 + Real1).
   apply Reallt_n_Sn.
   apply Realplus_unit.
Qed.

Lemma Realngt_triv : forall x, ~ x > x.
Proof.
  intro x.
  intuition.
  pose proof (Reallt_nlt x x H) as H1.
  contradict H.
  intuition.
Qed.

Lemma Realgt_neq : forall z1 z2, z1 > z2 -> z1 <> z2.
Proof.
  red.
  intros z1 z2 p q.
  apply (Realngt_triv z1).
  pattern z1 at 2; rewrite q; trivial.
Qed.
Hint Resolve Reallt_n_Sn Reallt_0_2 Realngt_triv Realgt_neq: Realiny.


  
Lemma Real2_neq_Real0 : Real2 <> Real0.
Proof.
  exact (Realgt_neq Real2 Real0 Reallt_0_2).
Qed.
Hint Resolve Real2_neq_Real0: Realiny.

Fixpoint prec (n : nat) : Real :=
  match n with
  | O => Real1
  | S m => (prec m) / Real2_neq_Real0
  end.
Arguments prec n%nat.



(* let us have a strong definition of dist then make other obligations derivable *)
Axiom dist_prop : forall z1 z2 : Real,
    (z1 > z2 -> dist z1 z2 = z1 - z2)  
    /\ (z1 = z2 -> dist z1 z2 = Real0)
    /\ (z1 < z2 -> dist z1 z2 = z2 - z1).
Hint Resolve dist_prop: Realiny.


(* this should be derived from the below
Axiom slimit :
  forall (P : Real -> Prop),
    (exists! z, P z) ->
    ((forall n, {e : Real | (exists a : Real, P a /\ dist e a < prec n)}) ->
    {a : Real | P a}).
*)
(* limit with multivalued *)

Axiom slimit :
  forall (P : Real -> Prop), (exists z, P z) ->
    (forall n, {e | (exists a : Real, P a /\ dist e a < prec n) }) -> {a : Real | P a}.


Definition mslimit :
  forall (P : Real -> Prop),
    (exists! z, P z) ->
    ((forall n, [e  | (exists a : Real, P a /\ dist e a < prec n)]) -> {a : Real | P a}).
Proof.
  intros.
  apply (countableM)  in X.
  apply singletonM.
  intros x y.
  destruct H, x, y.
  destruct H.
  induction (H0 x1 p0).
  induction (H0 x p).
  induction (irrl _ p p0).
  apply eq_refl.
  assert (exists z : Real, P z).
  destruct H.
  exists x.
  destruct H.
  exact H.

  
  assert ((forall n : nat, {e : Real | exists a : Real, P a /\ dist e a < prec n}) -> {a : Real | P a} ).
  intro.

  apply  (slimit P H0 H1).
  apply (liftM _ _ H1 X).
Defined.

  
(* Definition wlim : (nat -> Real) -> Real -> Prop. *)
(* Proof. *)
(*   intros f x. *)
(*   exact (forall n, dist (f n) x < prec n). *)
(* Defined. *)

(* Definition climit : forall (s : nat -> Real),  (forall n : nat, dist (s n) (s (S n)) < prec n) -> Real. *)
(* Proof. *)
(*   intros s H. *)
(*   assert (exists! z, wlim s z). *)
