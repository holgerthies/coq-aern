From mathcomp Require Import all_ssreflect.
Require Import Real Reals RealCoqReal.
Require Import Psatz.
Lemma IZReal_relator z : relate (IZReal z) (IZR z).
Proof.
  suff H : forall z', (0 <= z')%Z -> relate (IZReal z') (IZR z').
  - case z => [| p |p]; try by apply H;lia.
    rewrite IZReal_neg IZR_NEG.
    apply relate_subtraction.
    by apply H.
  apply Z_of_nat_prop.
  elim => [| n' IH]; first by rewrite Nat2Z.inj_0;apply relate_constant0.
  rewrite Nat2Z.inj_succ.
  have -> : (Z.succ (Z.of_nat n')) = ((Z.of_nat n') +1)%Z by lia.
  rewrite IZReal_hom plus_IZR.
  apply relate_addition =>//.
  suff -> : (IZReal 1) = Real1 by apply relate_constant1.
  by exact Logic.eq_refl.
Qed.

Lemma relate_IZReal z x : relate (IZReal z) x -> x = (IZR z).
Proof.
  suff H: relate (IZReal z) (IZR z).
  - move => R.
   by relate.
  by apply IZReal_relator.
Qed.

Lemma relate_prec n : relate (prec n) (/ 2 ^ n)%R.
Proof.
  elim n =>  [ /=  | n' IH ]; first by rewrite Rinv_1; apply relate_constant1.
  have -> : (prec n'.+1) = (prec n') * (prec 1).
  - have -> : n'.+1 = (n'+1)%coq_nat by lia.
    by apply prec_hom.
  have -> : (prec 1) = (Real1 / Real2_neq_Real0) by [].
  rewrite  /= Rinv_mult_distr; [| by lra| by apply pow_nonzero].
  rewrite Rmult_comm.
  apply relate_multiplication => //.
  rewrite /Realdiv.
  have -> : (/ 2 = 1 *  /2)%R by lra.
  apply relate_multiplication; first by apply relate_constant1.
  apply (relate_divison Real2 Real2_neq_Real0 2).
  by apply IZReal_relator.
Qed.

Lemma IZReal4neq0 : IZReal 4 <> Real0.
Proof.
  classical.
  relate.
  rewrite (relate_IZReal _ _ H).
  by lra.
Qed.
