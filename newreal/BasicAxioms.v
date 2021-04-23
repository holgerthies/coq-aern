(* Require Import Lift. *)
(* Require Export AbBool.           *)
(* Require Export Multival. *)
Require Export ZArith_base.
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

Parameter T : Set.

Delimit Scope T_scope with T.
Bind Scope T_scope with T.

Local Open Scope T_scope.

(*********************************************************)
(** **           Symbols of Type T                       *)
(*********************************************************)
(*********************************************************)
(** ***          Constants Symbols                       *)
(*********************************************************)
Parameter T0 : T.
Parameter T1 : T.


(*********************************************************)
(** **           Operator Symbols                        *)
(*********************************************************)
Parameter Tplus : T -> T -> T.
Parameter Tmult : T -> T -> T.
Parameter Topp : T -> T.
Parameter Tinv : forall {z}, z <> T0 -> T.


(*********************************************************)
(** **           Boolean Symbols                         *)
(*********************************************************)
Parameter Tltb : T -> T -> K.

(*********************************************************)
(** **           Predicate Symbols                       *)
(*********************************************************)
Parameter Tlt : T -> T -> Prop.

(*********************************************************)
(** **           Metric of Type T                        *)
(*********************************************************)
Parameter dist : T -> T -> T.




Infix "+" := Tplus : T_scope.
Infix "*" := Tmult : T_scope.
Notation "- x" := (Topp x) : T_scope.
Notation "/ x" := (Tinv x) : T_scope.

Infix "<" := Tlt : T_scope.
Infix "<?" := Tltb : T_scope.


(***********************************************************)

(**********)
Definition Tgt (z1 z2:T) : Prop := z2 < z1.
Definition Tle (z1 z2:T) : Prop := z1 < z2 \/ z1 = z2.
Definition Tge (z1 z2:T) : Prop := Tgt z1 z2 \/ z1 = z2.
Definition Tminus (z1 z2:T) : T := z1 + - z2.
Definition Tdiv (z1 :T) {z2:T} (p:z2<>T0) :  T := z1 * / p.
Definition abs (z:T) : T := dist T0 z.
Definition Tgtb (z1 z2: T) : K := z2 <? z1.

(**********)
Infix "-" := Tminus : T_scope.
Infix "/" := Tdiv   : T_scope.

Infix "<=" := Tle : T_scope.
Infix ">=" := Tge : T_scope.
Infix ">"  := Tgt : T_scope.
Infix ">?" := Tgtb : T_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : T_scope.
Notation "x <= y < z"  := (x <= y /\ y <  z) : T_scope.
Notation "x < y < z"   := (x <  y /\ y <  z) : T_scope.
Notation "x < y <= z"  := (x <  y /\ y <= z) : T_scope.



(*********************************************************)
(** **   Injection from Z, nat to T                      *)
(*********************************************************)

Inductive EZ :=
  Epos : nat -> EZ
| Ezero : EZ
| Eneg : nat -> EZ.

Fixpoint NT (n : nat) : T :=
  match n with
  | O => T0
  | S n => T1 + NT n
  end.
Arguments NT n%nat.

Fixpoint EZT (z : EZ) : T :=
  match z with
  | Epos n => NT n
  | Ezero => T0
  | Eneg n => - (NT n)
  end.


(**********)
Fixpoint IPT_2 (p:positive) : T :=
  match p with
  | xH => T1 + T1
  | xO p => (T1 + T1) * IPT_2 p
  | xI p => (T1 + T1) * (T1 + IPT_2 p)
  end.

Definition IPT (p:positive) : T :=
  match p with
  | xH => T1
  | xO p => IPT_2 p
  | xI p => T1 + IPT_2 p
  end.
Arguments IPT p%positive : simpl never.

Definition IZT (z:Z) : T :=
  match z with
  | Z0 => T0
  | Zpos n => IPT n
  | Zneg n => - IPT n
  end.
Arguments IZT z%Z : simpl never.

(**********)
Fixpoint INT (n:nat) : T :=
  match n with
  | O => T0
  | S O => T1
  | S n => INT n + T1
  end.
Arguments INT n%nat.
  




(*********************************************************)
(** *            Axioms of Type T                        *)
(** neq_path is just a general assumption in Prop, as a  *)
(** mere proposition. inv_unif says that equality of an  *)
(** inversion only matters on the denumerator. Need to   *)
(** whether it is derivable...                           *)
(*********************************************************)

Axiom neq_path : forall z1 z2 : T, forall p1 p2 : (z1 <> z2), p1 = p2.
Hint Resolve neq_path: Tiny.
Axiom inv_unif : forall z1 z2 : T, forall p1 : z1 <> T0, forall p2 : z2 <> T0,
        z1 = z2 -> /p1 = /p2.
Hint Resolve inv_unif: Tiny.
(*********************************************************)
(** *            Field axioms                            *)
(*********************************************************)

Axiom Tplus_comm : forall r1 r2:T, r1 + r2 = r2 + r1.
Axiom Tplus_assoc : forall r1 r2 r3:T, r1 + r2 + r3 = r1 + (r2 + r3).
Axiom Tplus_inv : forall r:T, r + - r = T0.
Axiom Tplus_unit : forall r:T, T0 + r = r.

Hint Resolve Tplus_comm Tplus_assoc Tplus_inv Tplus_unit: Tiny.

Axiom Tmult_comm : forall r1 r2:T, r1 * r2 = r2 * r1.
Axiom Tmult_assoc : forall r1 r2 r3:T, r1 * r2 * r3 = r1 * (r2 * r3).
Axiom Tmult_inv : forall (r:T) (p : r <> T0), / p * r = T1.
Axiom Tmult_unit : forall r:T, T1 * r = r.

Hint Resolve Tmult_comm Tmult_assoc Tmult_inv Tmult_unit: Tiny.

Axiom Tmult_plus_distr: forall r1 r2 r3:T, r1 * (r2 + r3) = r1 * r2 + r1 * r3.
Hint Resolve Tmult_plus_distr: Tiny.

Axiom T1_neq_T0 : T1 <> T0.
Hint Resolve T1_neq_T0: Tiny.


(************************************c*********************)
(** *    Order axioms                                    *)
(*********************************************************)
(*********************************************************)
(** **   Total Order                                     *)
(*********************************************************)

(**********)
Axiom T1_gt_T0 : T1 > T0.

(**********)
Axiom Ttotal_order : forall r1 r2:T, r1 < r2 \/ r1 = r2 \/ r1 > r2.

(**********)
Axiom Tlt_nlt : forall r1 r2:T, r1 < r2 -> ~ r2 < r1.

(**********)
Axiom Tlt_lt_lt : forall r1 r2 r3:T, r1 < r2 -> r2 < r3 -> r1 < r3.

(**********)
Axiom Tlt_plus_lt : forall r r1 r2:T, r1 < r2 -> r + r1 < r + r2.

(**********)
Axiom
  Tlt_mult_pos_lt : forall r r1 r2:T, T0 < r -> r1 < r2 -> r * r1 < r * r2.

(**********)
Axiom Tltb_lt_t : forall x y : T, Tltb x y = trueK <-> x < y.
Axiom Tltb_lt_f : forall x y : T, Tltb x y = falseK <-> y < x.


Hint Resolve T1_gt_T0 Ttotal_order Tlt_nlt Tlt_lt_lt Tlt_plus_lt Tlt_mult_pos_lt: Tiny.
Hint Resolve Tltb_lt_t Tltb_lt_f: Tiny.

(**********************************************************)
(** *    Order Completeness of T; need to make it derived *)
(**      from the metric completeness of T                *)
(**      Currently it ways every nonempty bounded above   *)
(**      set has a supremum                               *)
(**********************************************************)
Definition W_nemp (c : T -> Prop) := exists z, c z.
Definition W_upb (c : T -> Prop) (u : T) := forall z : T, c z -> z <= u.
Definition W_upbd (c : T -> Prop) := exists u, W_upb c u.
Definition W_sup (c : T -> Prop) (s : T)
  := W_upb c s /\ (forall s', W_upb c s' -> s <= s').
Axiom W_complete :
  forall c : T -> Prop, W_nemp c ->  W_upbd c -> exists z, W_sup c z. 

(**********************************************************)
(** **    Metric Completeness of T                         *)
(**********************************************************)
(**********************************************************)
(** ***  Though there are many facts that are not axioms  *)
(** below, we have to list them here to make the axiom of *)
(** constructive limit which requires precision embedding *)
(** and to define the precision embedding, we need to     *)
(** the fact that T2 is nonzero...                        *)
(** The above order completion is not computable hence it *)
(** has the endtype exists, ... In contrary, the construc *)
(** tive limit is constructive hence it has its endtype   *)
(** {x | P x }                                            *)
(**********************************************************)



(*** Some utility constants ***)
Definition T2 : T := IZT 2.

Lemma Tlt_n_Sn : forall x, x < x + T1.
Proof.
intro.
pose proof T1_gt_T0.
rewrite <- Tplus_unit at 1.
rewrite Tplus_comm.
apply (Tlt_plus_lt x).
auto with Tiny.
Qed.

Lemma Tlt_0_2 : T0 < T2.
Proof.
  unfold T2.
  unfold IZT.
  unfold IPT.
  unfold IPT_2.  
  apply Tlt_lt_lt with (T0 + T1).
  apply Tlt_n_Sn.
  rewrite Tplus_comm.
   apply Tlt_plus_lt.
   replace T1 with (T0 + T1).
   apply Tlt_n_Sn.
   apply Tplus_unit.
Qed.

Lemma Tngt_triv : forall x, ~ x > x.
Proof.
  intro x.
  intuition.
  pose proof (Tlt_nlt x x H) as H1.
  contradict H.
  intuition.
Qed.

Lemma Tgt_neq : forall z1 z2, z1 > z2 -> z1 <> z2.
Proof.
  red.
  intros z1 z2 p q.
  apply (Tngt_triv z1).
  pattern z1 at 2; rewrite q; trivial.
Qed.
Hint Resolve Tlt_n_Sn Tlt_0_2 Tngt_triv Tgt_neq: Tiny.


  
Lemma T2_neq_T0 : T2 <> T0.
Proof.
  exact (Tgt_neq T2 T0 Tlt_0_2).
Qed.
Hint Resolve T2_neq_T0: Tiny.

Fixpoint prec (n : nat) : T :=
  match n with
  | O => T1
  | S m => (prec m) / T2_neq_T0
  end.
Arguments prec n%nat.



(* let us have a strong definition of dist then make other obligations derivable *)
Axiom dist_prop : forall z1 z2 : T,
    (z1 > z2 -> dist z1 z2 = z1 - z2)  
    /\ (z1 = z2 -> dist z1 z2 = T0)
    /\ (z1 < z2 -> dist z1 z2 = z2 - z1).
Hint Resolve dist_prop: Tiny.


(* this should be derived from the below
Axiom slimit :
  forall (P : T -> Prop),
    (exists! z, P z) ->
    ((forall n, {e : T | (exists a : T, P a /\ dist e a < prec n)}) ->
    {a : T | P a}).
*)
(* limit with multivalued *)
Axiom mslimit :
  forall (P : T -> Prop),
    (exists! z, P z) ->
    ((forall n, [e  | (exists a : T, P a /\ dist e a < prec n)]) -> {a : T | P a}).

Axiom slimit :
  forall (P : T -> Prop), (exists z, P z) ->
    (forall n, {e | (exists a : T, P a /\ dist e a < prec n) }) -> {a : T | P a}.

Axiom climit : forall (s : nat -> T),  (forall n : nat, dist (s n) (s (S n)) < prec n) -> T.
