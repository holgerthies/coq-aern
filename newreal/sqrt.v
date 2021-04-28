From mathcomp Require Import all_ssreflect.
Require Import Real Reals RealCoqReal.
From Coquelicot Require Import Coquelicot.
Require Import Psatz.

Require Import Interval.Tactic.
Open Scope Real_scope.
Lemma relator_lt x y a b : relator a x -> relator b y -> a < b -> (x < y)%R.
Proof.
  move => R1 R2 H.
  suff :  (y <= x)%R -> False by lra.
  move => H'.
  case (transport_leq b a).
  move => y' x' r1 r2.
  relate => //.
  - by apply Reallt_nlt.
  move => H''.
  move : H.
  rewrite H''.
  by apply Realnlt_triv.
Qed.

Lemma IZReal_relator z : relator (IZReal z) (IZR z).
Proof.
  suff H : forall z', (0 <= z')%Z -> relator (IZReal z') (IZR z').
  - case z => [| p |p]; try by apply H;lia.
    rewrite IZReal_neg IZR_NEG.
    apply relator_subtraction.
    by apply H.
  apply Z_of_nat_prop.
  elim => [| n' IH]; first by rewrite Nat2Z.inj_0;apply relator_constant0.
  rewrite Nat2Z.inj_succ.
  have -> : (Z.succ (Z.of_nat n')) = ((Z.of_nat n') +1)%Z by lia.
  rewrite IZReal_hom plus_IZR.
  apply relator_addition =>//.
  suff -> : (IZReal 1) = Real1 by apply relator_constant1.
  by exact Logic.eq_refl.
Qed.

Lemma relator_IZReal z x : relator (IZReal z) x -> x = (IZR z).
Proof.
  suff H: relator (IZReal z) (IZR z).
  - move => R.
   by relate.
  by apply IZReal_relator.
Qed.

Definition sqrt_approx : forall (x x0 : Real), (Real0 <= x) -> Real0 < x0 -> forall (n : nat), {y | Real0 < y}.
Proof.
  move => x x0 xge0 x0gt0.
  elim =>[| n' [y IH]]; first by exists x0.
  have yneq0 : y <> Real0.
  - classical.
    relate.
    have := (relator_lt _ _ _ _ relator_constant0 H IH).
    by lra.
  exists (/ dReal2 * (y + x / yneq0)).
  rewrite /Realdiv.
  classical. 
  relate.
  apply Rmult_lt_0_compat; first by rewrite (relator_IZReal _ _ Ha3); lra.
  apply Rplus_lt_le_0_compat.
  - by apply (relator_lt _ _ _ _ relator_constant0 Ha2).
  apply Rcomplements.Rdiv_le_0_compat.
  - apply /transport_leq_inv/xge0 => //.
    apply relator_constant0.
  apply /relator_lt/IH => //.
  by apply relator_constant0.
Defined.

Lemma IZReal4neq0 : IZReal 4 <> Real0.
Proof.
  classical.
  relate.
  rewrite (relator_IZReal _ _ H).
  by lra.
Qed.

 
