Require Export ZArith_base.
Require Import Base.
Require Import Kleene.
Require Import Monad ClassicalMonads.
Require Import MultivalueMonad.


Declare Scope Real_scope.
Delimit Scope Real_scope with Real.
(* Bind Scope Real_scope with Real. *)
Local Open Scope Real_scope.

Section Real_Defs1.

  Generalizable Variables K M.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
          {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
          {M_MultivalueMonad : MultivalueMonad}.

  Class SemiDecOrderedField (Real : Type) :=
    {
      real_0 : Real;
      real_1 : Real;
      real_plus : Real -> Real -> Real;
      real_mult : Real -> Real -> Real;
      real_opp : Real -> Real;
      real_inv : forall {z}, z <> real_0 -> Real;
      real_lt : Real -> Real -> Prop;
      real_lt_semidec : forall x y : Real, semidec (real_lt x y);

      real_plus_comm : forall r1 r2 : Real, real_plus r1 r2 = real_plus r2 r1;
      real_plus_assoc : forall r1 r2 r3 : Real, real_plus (real_plus r1 r2) r3 = real_plus r1 (real_plus r2 r3);
      real_plus_inv : forall r : Real, real_plus r (real_opp r) = real_0;
      real_plus_unit : forall r : Real, real_plus real_0 r = r;
      real_mult_comm : forall r1 r2 : Real, real_mult r1 r2 = real_mult r2 r1;
      real_mult_assoc : forall r1 r2 r3 : Real, real_mult (real_mult r1 r2) r3 = real_mult r1 (real_mult r2 r3);
      real_mult_inv : forall (r : Real) (p : r <> real_0), real_mult (real_inv p) r = real_1;
      real_mult_unit : forall r : Real, real_mult real_1 r = r;
      real_mult_plus_distr: forall r1 r2 r3 : Real, real_mult r1 (real_plus r2 r3) = real_plus (real_mult r1 r2) (real_mult r1  r3);

      real_1_neq_0 : real_1 <> real_0;
      real_1_gt_0 : real_lt real_0 real_1;

      real_total_order : forall r1 r2 : Real, real_lt r1 r2 \/ r1 = r2 \/ real_lt r2 r1;
      real_lt_nlt : forall r1 r2 : Real, real_lt r1 r2 -> ~ real_lt r2 r1;
      real_lt_lt_lt : forall r1 r2 r3 : Real, real_lt r1 r2 -> real_lt r2 r3 -> real_lt r1 r3;
      real_lt_plus_lt : forall r r1 r2 : Real, real_lt r1 r2 -> real_lt (real_plus r r1) (real_plus r r2);
      real_lt_mult_pos_lt : forall r r1 r2 : Real, real_lt real_0 r -> real_lt r1 r2 -> real_lt (real_mult r r1) (real_mult r r2);
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
  
End Real_Defs1.

Infix "+" := (real_plus ) : Real_scope.
Infix "*" := (real_mult ) : Real_scope.
Notation "- x" := (real_opp  x) : Real_scope.
Notation "/ p" := (@real_inv _ _ _ _ _ p ) : Real_scope.
Infix "<" := (real_lt ) : Real_scope.

Section Real_Defs2.

  Generalizable Variables K M Real.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
          {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
          {M_MultivalueMonad : MultivalueMonad}
          {Real : Type}
          {SemiDecOrderedField_Real : SemiDecOrderedField Real}.

  Definition real_gt (x y : Real) : Prop := y < x.
  Definition real_le (x y : Real) : Prop := x < y \/ x = y.
  Definition real_ge (x y : Real) : Prop := real_gt x y \/ x = y.
  Definition real_minus (x y : Real) : Real := x + - y.

  Definition real_div (x : Real) {y : Real} (p:y <> real_0) : Real := x * (/ p).
  Definition real_ltb : Real -> Real -> K.
  Proof.
    intros x y.
    exact (projP1 _ _ (real_lt_semidec x y)).
  Defined.  

  Definition real_gtb (x y : Real) : K := real_ltb y x.

End Real_Defs2.

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

Section Real_Defs3.

  Generalizable Variables K M Real.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
          {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
          {M_MultivalueMonad : MultivalueMonad}
          {Real : Type}
          {SemiDecOrderedField_Real : SemiDecOrderedField Real}.

  (* Definition W_nemp (c : Real -> Prop) := exists z, c z. *)
  (* Definition W_upb (c : Real -> Prop) (u : Real) := forall z : Real, c z -> z <= u. *)
  (* Definition W_upbd (c : Real-> Prop) := exists u, W_upb c u. *)
  (* Definition W_sup (c : Real-> Prop) (s : Real) *)
  (*   := W_upb c s /\ (forall s', W_upb c s' -> s <= s'). *)
  (* Definition is_W_complete (T : SemiDecOrderedField) := *)
  (*   forall c : Real -> Prop, W_nemp c ->  W_upbd c -> exists z, W_sup c z.  *)

  Inductive EZ :=
    Epos : nat -> EZ
  | Ezero : EZ
  | Eneg : nat -> EZ.

  Fixpoint Nreal (n : nat) : Real :=
    match n with
    | O => real_0 | S n => real_1 + Nreal n
    end.

  Arguments Nreal n%nat.

  Definition EZreal (z : EZ) : Real:=
    match z with
    | Epos n => Nreal n
    | Ezero => real_0 | Eneg n => - (Nreal n)
    end.

  (**********)
  Fixpoint IPreal_2 (p:positive) : Real :=
    match p with
    | xH => real_1 + real_1
    | xO p => (real_1 + real_1) * IPreal_2 p
    | xI p => (real_1 + real_1) * (real_1 + IPreal_2 p)
    end.

  Definition IPreal (p:positive) : Real:=
    match p with
    | xH => real_1
    | xO p => IPreal_2 p
    | xI p => real_1 + IPreal_2 p
    end.
  Arguments IPreal p%positive : simpl never.

  Definition IZreal (z : Z) : Real :=
    match z with
    | Z0 => real_0
    | Zpos n => IPreal n
    | Zneg n => - IPreal n
    end.
  Arguments IZreal z%Z : simpl never.

  (**********)
  Fixpoint INreal (n:nat) : Real  :=
    match n with
    | O => real_0
    | S O => real_1 
    | S n => INreal n + real_1
    end.
  Arguments INreal n%nat.

  Definition real_2 : Real := IZreal 2.

  Lemma real_lt_n_Sn : forall (x : Real), x < x + real_1.
  Proof.
    intros.
    rewrite <- (real_plus_unit) at 1.
    rewrite (real_plus_comm (real_0) x).
    apply (real_lt_plus_lt x).
    apply real_1_gt_0.
  Qed.

  Lemma real_lt_0_2 : real_0 < real_2.
  Proof.
    unfold real_2.
    unfold IZreal.
    unfold IPreal.
    unfold IPreal_2.  
    apply real_lt_lt_lt with (real_0 + real_1).
    apply real_lt_n_Sn.
    rewrite real_plus_comm.
    apply real_lt_plus_lt.
    replace (real_1 ) with (real_0 + real_1).
    apply real_lt_n_Sn.
    apply real_plus_unit.
  Qed.

  Lemma real_ngt_triv : forall (x  : Real), ~ x > x.
  Proof.
    intros x.
    intuition.
    pose proof (real_lt_nlt x x H) as H1.
    contradict H.
    intuition.
  Qed.

  Lemma real_gt_neq : forall (z1 z2 : Real), z1 > z2 -> z1 <> z2.
  Proof.
    red.
    intros z1 z2 p q.
    rewrite q in p.
    contradict p.
    apply real_ngt_triv.
  Qed.

  Lemma real_2_neq_0 : real_2 <> real_0.
  Proof.
    apply real_gt_neq.
    exact real_lt_0_2.
  Qed.

  Fixpoint prec (n : nat) : Real :=
    match n with
    | O => real_1
    | S m => (prec m) / (real_2_neq_0)
    end.
  Arguments prec n%nat.

  Definition is_fast_cauchy_p (f : nat -> Real) := forall n m, - prec n - prec m <= f n - f m <= prec n + prec m.
  Definition is_fast_limit_p (x : Real) (f : nat -> Real) := forall n, - prec n <= x - f n <= prec n.

  Class ComplArchiSemiDecOrderedField :=
    {
      (* W_complete : forall c : Real CarrierField -> Prop, W_nemp c ->  W_upbd c -> exists z, W_sup c z; *)
      real_Archimedean : forall r : Real, r > real_0 -> exists n, prec n < r;
      real_limit_p : forall f : nat -> Real, is_fast_cauchy_p f -> {x | is_fast_limit_p x f};
    }.

  (* add to hint db *)
  Create HintDb real.

End Real_Defs3.

Global Hint Resolve real_lt_semidec  real_plus_comm  real_plus_assoc  real_plus_inv real_plus_unit  real_mult_comm  real_mult_assoc  real_mult_inv  real_mult_unit  real_mult_plus_distr  real_1_neq_0  real_1_gt_0 real_total_order  real_lt_nlt  real_lt_lt_lt  real_lt_plus_lt  real_lt_mult_pos_lt real_lt_n_Sn real_lt_0_2 real_ngt_triv real_gt_neq real_2_neq_0 : real.
