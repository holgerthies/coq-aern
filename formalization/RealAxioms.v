Require Export ZArith_base.
Require Import Base.
Require Import Kleene.


Declare Scope Real_scope.
Delimit Scope Real_scope with Real.
(* Bind Scope Real_scope with Real. *)
Local Open Scope Real_scope.


Structure SemiDecOrderedField : Type :=
  {
    real : Set;
    real_0 : real;
    real_1 : real;
    real_plus : real -> real -> real;
    real_mult : real -> real -> real;
    real_opp : real -> real;
    real_inv : forall {z}, z <> real_0 -> real;
    real_lt : real -> real -> Prop;
    real_lt_semidec : forall x y : real, semidec (real_lt x y);

    real_plus_comm : forall r1 r2 : real, real_plus r1 r2 = real_plus r2 r1;
    real_plus_assoc : forall r1 r2 r3 : real, real_plus (real_plus r1 r2) r3 = real_plus r1 (real_plus r2 r3);
    real_plus_inv : forall r : real, real_plus r (real_opp r) = real_0;
    real_plus_unit : forall r : real, real_plus real_0 r = r;
    real_mult_comm : forall r1 r2 : real, real_mult r1 r2 = real_mult r2 r1;
    real_mult_assoc : forall r1 r2 r3 : real, real_mult (real_mult r1 r2) r3 = real_mult r1 (real_mult r2 r3);
    real_mult_inv : forall (r : real) (p : r <> real_0), real_mult (real_inv p) r = real_1;
    real_mult_unit : forall r : real, real_mult real_1 r = r;
    real_mult_plus_distr: forall r1 r2 r3 : real, real_mult r1 (real_plus r2 r3) = real_plus (real_mult r1 r2) (real_mult r1  r3);

    real_1_neq_0 : real_1 <> real_0;
    real_1_gt_0 : real_lt real_0 real_1;

    real_total_order : forall r1 r2 : real, real_lt r1 r2 \/ r1 = r2 \/ real_lt r2 r1;
    real_lt_nlt : forall r1 r2 : real, real_lt r1 r2 -> ~ real_lt r2 r1;
    real_lt_lt_lt : forall r1 r2 r3 : real, real_lt r1 r2 -> real_lt r2 r3 -> real_lt r1 r3;
    real_lt_plus_lt : forall r r1 r2 : real, real_lt r1 r2 -> real_lt (real_plus r r1) (real_plus r r2);
    real_lt_mult_pos_lt : forall r r1 r2 : real, real_lt real_0 r -> real_lt r1 r2 -> real_lt (real_mult r r1) (real_mult r r2);
  }.

Arguments real_0 {_}.
Arguments real_1 {_}.
Arguments real_plus {_}.
Arguments real_mult {_}.
Arguments real_opp {_}.
Arguments real_inv {_}.
Arguments real_lt {_}.
Arguments real_lt_semidec {_}.

Arguments real_plus_comm {_}.
Arguments real_plus_assoc {_}.
Arguments real_plus_inv {_} {_}.
Arguments real_plus_unit {_}.
Arguments real_mult_comm {_}.
Arguments real_mult_assoc {_}.
Arguments real_mult_inv {_}.
Arguments real_mult_unit {_}.
Arguments real_mult_plus_distr {_}.
Arguments real_1_neq_0 {_}.
Arguments real_1_gt_0 {_}.

Arguments real_total_order {_}.
Arguments real_lt_nlt {_}.
Arguments real_lt_lt_lt {_}.
Arguments real_lt_plus_lt {_}.
Arguments real_lt_mult_pos_lt {_}.

Infix "+" := (real_plus ) : Real_scope.
Infix "*" := (real_mult ) : Real_scope.
Notation "- x" := (real_opp  x) : Real_scope.
Notation "/ p" := (real_inv _ p ) : Real_scope.
Infix "<" := (real_lt ) : Real_scope.
Definition real_gt {T : SemiDecOrderedField} (x y : real T) : Prop := y < x.
Definition real_le {T : SemiDecOrderedField} (x y : real T) : Prop := x < y \/ x = y.
Definition real_ge {T : SemiDecOrderedField} (x y : real T) : Prop := real_gt x y \/ x = y.
Definition real_minus {T : SemiDecOrderedField} (x y : real T) : real T := x + - y.

Definition real_div {T : SemiDecOrderedField} (x : real T) {y : real T} (p:y <> real_0) : real T := x * (/ p).
Definition real_ltb {T : SemiDecOrderedField} : real T -> real T -> K.
Proof.
  intros x y.
  exact (projP1 _ _ (real_lt_semidec x y)).
Defined.

Definition real_gtb {T : SemiDecOrderedField} (x y : real T) : K := real_ltb y x.

Infix "-" := (real_minus) : Real_scope.
Infix "/" := (real_div ): Real_scope.
Infix "<=" := (real_le ): Real_scope.
Infix ">=" := (real_ge): Real_scope.
Infix ">"  := (real_gt): Real_scope.
Infix "<?" := (real_ltb): Real_scope.
Infix ">?" := (real_gtb): Real_scope.
Notation "x <= y <= z" := (x <= y /\ y <= z): Real_scope.
Notation "x <= y < z"  := (x <= y /\ y <  z): Real_scope.
Notation "x < y < z"   := (x <  y /\ y <  z): Real_scope.
Notation "x < y <= z"  := (x <  y /\ y <= z): Real_scope.


(* Definition W_nemp {T : SemiDecOrderedField} (c : real T -> Prop) := exists z, c z. *)
(* Definition W_upb {T : SemiDecOrderedField} (c : real T -> Prop) (u : real T) := forall z : real T, c z -> z <= u. *)
(* Definition W_upbd {T : SemiDecOrderedField} (c : real T-> Prop) := exists u, W_upb c u. *)
(* Definition W_sup {T : SemiDecOrderedField} (c : real T-> Prop) (s : real T) *)
(*   := W_upb c s /\ (forall s', W_upb c s' -> s <= s'). *)
(* Definition is_W_complete (T : SemiDecOrderedField) := *)
(*   forall c : real T -> Prop, W_nemp c ->  W_upbd c -> exists z, W_sup c z.  *)

Inductive EZ :=
  Epos : nat -> EZ
| Ezero : EZ
| Eneg : nat -> EZ.

Fixpoint Nreal {T : SemiDecOrderedField} (n : nat) : real T :=
  match n with
  | O => real_0 | S n => real_1 + Nreal n
  end.

Arguments Nreal _ n%nat.

Definition EZreal {T : SemiDecOrderedField} (z : EZ) : real T:=
  match z with
  | Epos n => Nreal n
  | Ezero => real_0 | Eneg n => - (Nreal n)
  end.

(**********)
Fixpoint IPreal_2 {T : SemiDecOrderedField} (p:positive) : real T :=
  match p with
  | xH => real_1 + real_1
  | xO p => (real_1 + real_1) * IPreal_2 p
  | xI p => (real_1 + real_1) * (real_1 + IPreal_2 p)
  end.

Definition IPreal {T : SemiDecOrderedField} (p:positive) : real T:=
  match p with
  | xH => real_1
  | xO p => IPreal_2 p
  | xI p => real_1 + IPreal_2 p
  end.
Arguments IPreal _ p%positive : simpl never.

Definition IZreal {T : SemiDecOrderedField} (z : Z) : real T :=
  match z with
  | Z0 => real_0
  | Zpos n => IPreal n
  | Zneg n => - IPreal n
  end.
Arguments IZreal _ z%Z : simpl never.

(**********)
Fixpoint INreal {T : SemiDecOrderedField} (n:nat) : real T  :=
  match n with
  | O => real_0
  | S O => real_1 
  | S n => INreal n + real_1
  end.
Arguments INreal _ n%nat.

Definition real_2 {T : SemiDecOrderedField} : real T := IZreal 2.

Lemma real_lt_n_Sn : forall {T : SemiDecOrderedField} (x : real T), x < x + real_1.
Proof.
  intros.
    pose proof (@real_1_gt_0 T).
    rewrite <- (real_plus_unit) at 1.
    rewrite (real_plus_comm (real_0) x).
    apply (real_lt_plus_lt x).
    apply real_1_gt_0.
  Qed.

Lemma real_lt_0_2 : forall {T : SemiDecOrderedField}, @real_0 T < real_2.
Proof.
  intro T.
  unfold real_2.
  unfold IZreal.
  unfold IPreal.
  unfold IPreal_2.  
  apply real_lt_lt_lt with (real_0 + real_1).
  apply real_lt_n_Sn.
  rewrite real_plus_comm.
  apply real_lt_plus_lt.
  replace (real_1 ) with (@real_0 T + real_1).
  apply real_lt_n_Sn.
  apply real_plus_unit.
Qed.

Lemma real_ngt_triv : forall {T : SemiDecOrderedField} (x  : real T), ~ x > x.
Proof.
  intros T x.
  intuition.
  pose proof (real_lt_nlt x x H) as H1.
  contradict H.
  intuition.
Qed.

Lemma real_gt_neq : forall {T : SemiDecOrderedField} (z1 z2 : real T), z1 > z2 -> z1 <> z2.
Proof.
  intro T.
  red.
  intros z1 z2 p q.
  apply (real_ngt_triv z1).
  pattern z1 at 2; rewrite q; trivial.
Qed.

Lemma real_2_neq_0 : forall {T : SemiDecOrderedField}, @real_2 T <> real_0.
Proof.
  intro T; exact (real_gt_neq  (real_2 ) (real_0 ) (real_lt_0_2 )).
Qed.

Fixpoint prec {T : SemiDecOrderedField} (n : nat) : real T :=
  match n with
  | O => real_1
  | S m => (prec m) / (real_2_neq_0)
  end.
Arguments prec _ n%nat.

Definition is_fast_cauchy_p {T : SemiDecOrderedField} (f : nat -> real T) := forall n m, - prec n - prec m <= f n - f m <= prec n + prec m.
Definition is_fast_limit_p {T : SemiDecOrderedField} (x : real T) (f : nat -> real T) := forall n, - prec n <= x - f n <= prec n.

Structure ComplArchiSemiDecOrderedField : Type :=
  {
    CarrierField : SemiDecOrderedField;
    (* W_complete : forall c : real CarrierField -> Prop, W_nemp c ->  W_upbd c -> exists z, W_sup c z; *)
    real_Archimedean : forall r : real CarrierField, r > real_0 -> exists n, prec n < r;
    real_limit_p : forall f : nat -> real CarrierField, is_fast_cauchy_p f -> {x | is_fast_limit_p x f};
  }.


(* add to hint db *)
Create HintDb real.

Global Hint Resolve real_lt_semidec  real_plus_comm  real_plus_assoc  real_plus_inv real_plus_unit  real_mult_comm  real_mult_assoc  real_mult_inv  real_mult_unit  real_mult_plus_distr  real_1_neq_0  real_1_gt_0 real_total_order  real_lt_nlt  real_lt_lt_lt  real_lt_plus_lt  real_lt_mult_pos_lt real_lt_n_Sn real_lt_0_2 real_ngt_triv real_gt_neq real_2_neq_0 : real.
