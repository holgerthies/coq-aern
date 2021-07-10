Set Warnings "-parsing".
From mathcomp Require Import all_ssreflect.
Require Import Real Reals RealCoqReal.
Set Warnings "parsing".
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

(* results about (/ 2 ^ n) adapted  from incone *)
Lemma tpmn_lt n: (0 < /2^n)%R.
Proof. apply/Rinv_0_lt_compat/pow_lt; lra. Qed.

Lemma pwr2gtz m: exists n, (2^n > m)%nat.
Proof.
  elim: m => [ | m [n /leP ih]]; first by exists 0%nat; apply /leP => /=; lia.
  by exists n.+1; apply /leP => /=; lia.
Qed.

Lemma dns0_tpmn: forall eps, (0 < eps)%R -> exists n, (/2^n < eps)%R.
Proof.
  move => eps epsprp.
  pose z := Z.to_nat (up (/eps)).
  have [n /leP nprp]:= pwr2gtz z; have g0: (0 < 2^n)%R by apply pow_lt; lra.
  exists n.
  rewrite -[eps]Rinv_involutive; try lra.
  apply Rinv_lt_contravar; first by rewrite Rmult_comm; apply Rdiv_lt_0_compat;  try lra.
  have ->: (2 = INR 2)%R by trivial.
  rewrite -pow_INR.
  apply /Rlt_le_trans/(le_INR _ _ nprp).
  suff : (INR z.+1 > (/ eps))%R by lra.
  apply /Rgt_trans/(archimed (/ eps)).1.
  rewrite S_INR.
  rewrite INR_IZR_INZ.
  unfold z.
  rewrite Z2Nat.id; first by lra.
  apply le_IZR.
  have epsprp' : (0 < / eps)%R by apply Rinv_0_lt_compat.
  suff: ((IZR (up (/ eps))) > (/ eps))%R by lra.
  by apply archimed.
Qed.
