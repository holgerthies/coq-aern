Require Import ConstructiveEpsilon.
Require Import Real.
From mathcomp Require Import all_ssreflect.
Require Import Psatz.
Require Import Nat.
Require Import PeanoNat.

(* 
   Multivalued searching from existing searching:
     constructive_indefinite_ground_description_nat_Acc_PQ
   It is not yet decided if this to be used for our searching.. 
 *)


Definition when_first : forall P Q : nat -> Prop, (forall n : nat, {P n} + {Q n}) -> (nat -> Prop).
Proof.
  intros.
  destruct (H H0).
  exact True.
  exact False.
Defined.
    
Definition epsilon_smallest_PQ
  : forall P Q : nat -> Prop,
       (forall n, {P n} + {Q n}) ->
       (exists n, ~Q n) ->
       {n | P n /\ (forall k, (k < n)%coq_nat -> Q k)}.
Proof.
  intros P Q H H0.
  pose proof (epsilon_smallest (when_first P Q H)).

  (* eliminate first premise of H1: *)
  assert ((forall n : nat, {when_first P Q H n} + {~ when_first P Q H n})).
  clear H1.
  intro.
  unfold when_first.
  destruct (H n).
  left; auto.
  right; auto.
  pose proof (H1 H2).
  clear H1 H2.
     
  (* eliminate another premise of H1 (now H3): *)
  assert (exists n : nat, when_first P Q H n).
  clear H3.
  unfold when_first.
  destruct H0.
  exists x.
  destruct (H x); auto.
  pose proof (H3 H1).
  clear H3 H1.

  destruct H2.
  unfold when_first in a.
  exists x.
  destruct (H x).
  destruct a.
  split. auto.
  intros k kx.
  have Hk := (H2 k kx).
  destruct (H k). by induction Hk. by auto.
  destruct a.
  induction H1.
Defined.

Definition epsilon_smallest_PQ_M
  : forall P Q : nat -> Prop,
       (forall n, M ({P n} + {Q n})) ->
       (exists n, ~Q n) ->
       [n | P n /\ (forall k, (k < n)%coq_nat -> Q k)].
Proof.
  intros.
  apply countableLiftM in X.
  apply (liftM (forall n : nat, {P n} + {Q n})).
  intro.
  apply (epsilon_smallest_PQ P Q); auto.
  exact X.
Defined.

(*********)

Require Import Kleene.
Require Import Reals.
Require Import RealCoqReal RealHelpers.


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


(* ******************************************** *)
(* search for the minimal n with P n for a 
  "non-deterministically choosable" precidate P  *)
(* ******************************************** *)

Definition epsilon_smallest_choose_M
  : forall P : nat -> Prop,
      (forall n : nat, M ({P n.+1} + {~ P n}) ) ->
      (exists n : nat, P n) -> 
      M {n : nat | P (n.+1) /\ (forall k, (k < n)%coq_nat -> ~ P k)}.
Proof.
  intros P P_decM e.
  apply epsilon_smallest_PQ_M.
  exact P_decM.
  destruct e.
  exists x.
  auto.
Defined.
    

Definition lt_prec x n := prec n < x.

Definition is_magnitude1 x n := 
  lt_prec x n.+2 /\ not (lt_prec x n)
.
    (* prec n.+2 < x < prec n. *)

Lemma weaken_orM_r : forall P Q Q': Prop, (Q -> Q') -> M ({P}+{Q}) -> M ({P}+{Q'}).
Proof.
  intros P Q Q' QQ'.
  apply liftM.
  move => [iP|iQ].
  left. by auto.
  right. exact (QQ' iQ).
Qed.

Lemma half_lt_one : Real1 / Real2_neq_Real0 < Real1.
Proof.
classical.
relate.
suff -> : (y = 2)%R by lra.
by apply relate_IZReal.
Qed.

Definition magnitude1 x : (Real0 < x < Real1 / Real2_neq_Real0) 
  -> M { n | is_magnitude1 x n }.
Proof.
  move => [pos lt2].

  (* x < Real1 *)
  have lt1 : x < Real1.
  have h := half_lt_one.
  apply (Reallt_lt_lt _ (Real1 / Real2_neq_Real0) _); auto.

  unfold is_magnitude1.
  Definition P x n := lt_prec x (n.+1).
  suff g1M : M { n : nat | P x n.+1 /\ (forall k : nat, (k < n)%coq_nat -> ~ P x k)}.
  apply (liftM ({n : nat | P x n.+1 /\ (forall k : nat, (k < n)%coq_nat -> ~ P x k)})).
  2: { exact g1M. }
  clear g1M. intro g1.
  destruct g1 as [n H].
  exists n.
  unfold P in H.
  split.
  destruct H. auto.
  destruct H.

  destruct n.
  (* ~ lt_prec x 0 *)
  unfold lt_prec. apply Realgt_ngt. unfold prec. unfold Realgt. auto. 

  (* ~ lt_prec x n.+1 *)
  have H0n := H0 n.
  suff lt_S : (n < n.+1)%coq_nat by auto.
  by lia.
  
  apply (epsilon_smallest_choose_M).
  unfold P. unfold lt_prec.
  intros.
  apply (weaken_orM_r _ (x < prec n.+1) _).
  intros.
  apply Reallt_nlt. auto.

  apply choose.
  auto with Realiny.
  auto with Realiny.

  (* prec n.+2 < x \/ x < prec n.+1 *)
  destruct (Realtotal_order x (prec n.+1)) as [H|[H|H]].
  right. exact H.
  left. rewrite H. apply prec_S.
  left. unfold Realgt in H. apply (Reallt_lt_lt _ (prec n.+1) _).
  apply prec_S. exact H.

  unfold P. unfold lt_prec.
  case (ana1 x) => xr [R1 R2].
  suff : exists n,  (/ 2 ^ n.+1 < xr)%R.
  - case => n nprp.
    exists n.
    have P := (relate_prec n.+1).
    classical.
    by relate.
  have xrpos : (0 < xr)%R.
  apply /transport_lt_inv/pos/R1/relate_constant0.
  have xrlt1 : (xr < 1)%R.
  apply /transport_lt_inv/lt1. auto. 
  apply relate_constant1.

  have H := dns0_tpmn xr xrpos.
  destruct H as [n H].
  destruct n.
  have xrgt1 : (1 < xr)%R. lra. 
  lra. (* contradiction between xrlt1 xrgt1 *)

  exists n. auto.
Defined.

Definition Zpow (x : Real) (xne0 : x <> Real0) z := match z with
                       | 0%Z => Real1
                       | Z.pos p => RealRing.pow x (Pos.to_nat p)
                       | Z.neg p => RealRing.pow (/ xne0) (Pos.to_nat p)
                     end.

Lemma dec_x_lt_2 x : M ({x < Real2} + {Real1 < x}).
Proof.
  have := (M_split x (IZReal 3 / dReal2) (/ dReal2) dReal2_pos).
  apply mjoin.
  case => H.
  right.
  - classical.
    relate.
    suff : ((3 / 2) - (/ 2) < y)%R by lra.
    apply /transport_lt_inv/H/H1.
    by apply /relate_addition/relate_subtraction/relate_divison/IZReal_relator/relate_multiplication/relate_divison/IZReal_relator/IZReal_relator.
  left.
  classical.
  relate.
  have -> : (y = 2)%R by apply relate_IZReal.
  suff : (x0 - ( / 2) < (3 / 2))%R by lra.
  by apply /transport_lt_inv/H/relate_multiplication/relate_divison/IZReal_relator/IZReal_relator/relate_addition/relate_subtraction/relate_divison/IZReal_relator.
Qed.

Lemma Zpow_prec n : Zpow _ Real2_neq_Real0 (- Z.of_nat n) = prec n.
Proof.
  rewrite /Zpow.
  case e :(- Z.of_nat n)%Z => [| p | p]; try by lia.
  - suff  -> : (n = 0) by auto.
    lia.
  have -> : Pos.to_nat p = n by lia.
  elim n => // n' IH /=.
  rewrite Realmult_comm.
  by apply Realeq_eq_mult_eq.
Qed.  


Definition is_magnitude x z := Zpow _ Real2_neq_Real0 (z - 2) <= x <= Zpow _ Real2_neq_Real0 z. 

Lemma Zpow_case x xneq0 z : Zpow x xneq0 z = RealRing.pow x (Z.to_nat z) \/ Zpow x xneq0 z = RealRing.pow (/ xneq0) (Z.to_nat (- z)).
Proof.
  case (Z.neg_nonneg_cases z) => H.
  right.
  - by case e : z => [| p | p] // /=; try lia.
  left.
  by case e : z => [| p | p] // /=; try lia.
Qed.

Lemma magnitude_half x z : is_magnitude (x / Real2_neq_Real0) z -> is_magnitude x (z+1).
Proof.
  move => [H1 H2].
  split.
  simpl.
Admitted.
Lemma magnitude_fourth x z : is_magnitude (x /IZReal4neq0) z -> is_magnitude x (z+2).
Proof.
  suff -> : (x / IZReal4neq0) = (x / Real2_neq_Real0 / Real2_neq_Real0).
  - move => H.
    have H' := (magnitude_half _ _ (magnitude_half _ _ H)).
    have -> : (z + 2 = z + 1 + 1)%Z by lia.
    exact H'.
  classical.
  relate.
  rewrite (relate_IZReal _ _ Hb1).
  rewrite (relate_IZReal _ _ Hb0).
  by lra.
Qed.

Lemma magnitude_inv x (xneq0 : x<> Real0) z : is_magnitude (/ xneq0) z -> is_magnitude x (-z+2).
Proof.
Admitted.

(* first extend magnitude to numbers <= 2 *)
Definition magnitude2 x : (Real0 < x < Real2) -> M { z | is_magnitude x z }.
Proof.
  move => [xgt0 xle1].
  pose y := (x / IZReal4neq0).
  have yB : (Real0 < y < Real1 / Real2_neq_Real0).
  - rewrite /Realdiv; rewrite Realmult_unit/y.
    split;classical;relate;rewrite (relate_IZReal _ _ Hb).
    suff : (0 < x0)%R by lra.
    apply /transport_lt_inv/xgt0/Ha/relate_constant0.
    rewrite (relate_IZReal _ _ Ha0).
    suff : (x1 < 2)%R by lra.
    by apply /transport_lt_inv/xle1/IZReal_relator/Ha.
  have magy n : is_magnitude y n -> is_magnitude x (n+2)%Z by apply magnitude_fourth.
  suff : M { z | is_magnitude y z}.
  - apply liftM.
    case => z zprp.
    exists (z+2)%Z.
    exact (magy _ zprp).
  (* y is less than 1/2 => magnitude1 can be used *)
  have := magnitude1 _ yB.
  apply liftM.
  case => n nprp.
  exists (- Z.of_nat n)%Z.
  split; last by rewrite Zpow_prec; apply Realge_le; apply Realnge_le; apply nprp.
  have -> : ((- Z.of_nat n - 2) = (- Z.of_nat (n.+2)%coq_nat))%Z by lia.
  by rewrite Zpow_prec; apply Reallt_le;apply nprp.
Qed.

Lemma magnitude x : Real0 < x -> M {z | is_magnitude x z}.
Proof.
  move => xgt0.
  have := dec_x_lt_2 x. 
  apply lift_domM.
  case => H; first by apply magnitude2.
  have xneg0 : (x <> Real0) by apply (Realgt_neq _ _ xgt0).
  suff I : (Real0 < / xneg0 < Real2).
  - have := magnitude2 _ I.
    apply liftM.
    case => z zprp.
    exists (-z+2)%Z.
    by apply (magnitude_inv x xneg0).
  split; classical; relate.
  - apply Rinv_0_lt_compat.
    by apply /transport_lt_inv/xgt0/Ha/relate_constant0.
   rewrite (relate_IZReal _ _ H1).
   have -> : (2 = / / 2)%R by lra.
   apply Rinv_lt_contravar.
   suff : (0 < x1)%R by lra.
   apply /transport_lt_inv/xgt0/Ha/relate_constant0.
   suff : (1 < x1)%R by lra.
   apply /transport_lt_inv/H/Ha/relate_constant1.
 Qed.
