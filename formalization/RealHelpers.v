Set Warnings "-parsing".
From mathcomp Require Import all_ssreflect.
Require Import Real Reals RealCoqReal.
Set Warnings "parsing".
Require Import Psatz.

Section RealHelpers.

Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).
#[local] Definition sofReal := @sofReal types casofReal.
#[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).

  (* ring structure on Real *)
  Ltac IZReal_tac t :=
    match t with
    | real_0 => constr:(0%Z)
    | real_1 => constr:(1%Z)
    | IZreal ?u =>
      match isZcst u with
      | true => u
      | _ => constr:(InitialRing.NotConstant)
      end
    | _ => constr:(InitialRing.NotConstant)
    end.

  Add Ring realRing : (realTheory ) (constants [IZReal_tac]).


  Lemma IZreal_relator z : relate (IZreal z) (IZR z).
  Proof.
    suff H : forall z', (0 <= z')%Z -> relate (^IZreal z') (IZR z').
    - case z => [| p |p]; try by apply H;lia.
      rewrite IZreal_neg IZR_NEG.
      apply relate_subtraction.
        by apply H.
        apply Z_of_nat_prop.
        elim => [| n' IH]; first by rewrite Nat2Z.inj_0;apply relate_constant0.
        rewrite Nat2Z.inj_succ.
        have -> : (Z.succ (Z.of_nat n')) = ((Z.of_nat n') +1)%Z by lia.
        rewrite IZreal_hom plus_IZR.
        apply relate_addition =>//.
        suff -> : (^IZreal 1) = (@real_1 types sofReal) by apply relate_constant1.
        intros.
        simpl; auto.
  Qed.

  Lemma relate_IZreal z x : relate (IZreal z) x -> x = (IZR z).
  Proof.
    suff H: relate (^IZreal z) (IZR z).
    - move => R.
        by relate.
          by apply IZreal_relator.
  Qed.

  Lemma relate_prec n : relate (prec n) (/ 2 ^ n)%R.
  Proof.
    elim n =>  [ /=  | n' IH ]; first by rewrite Rinv_1; apply relate_constant1.
    have -> : (prec n'.+1) = (prec n') * (prec 1).
    - have -> : n'.+1 = (n'+1)%coq_nat by lia.
        apply (prec_hom n' 1).
        have -> : (prec 1) = (real_1 / real_2_neq_0) by [].
        rewrite  /= Rinv_mult_distr; [| by lra| by apply pow_nonzero].
        rewrite Rmult_comm.
        apply relate_multiplication => //.
        rewrite /real_div.
        have -> : (/ 2 = 1 *  /2)%R by lra.
        apply relate_multiplication; first by apply relate_constant1.
        apply (relate_divison real_2 real_2_neq_0 2).
          by apply IZreal_relator.
  Qed.

  

(* Ltac classical := *)
(*   match goal with *)
(*   | |- eq ?x ?y => apply transport_eq;   intro; intro; intro; intro; classical (* (fail "not implemented yet") *) *)
(*   | |- ?x < ?y => apply transport_lt; intro; intro; intro; intro; classical *)
(*   | |- ?x > ?y => apply transport_lt; intro; intro; intro; intro; classical *)
(*   | |- ?x >= ?y => apply transport_geq; intro; intro; intro; intro; classical *)
(*   | |- ?x <= ?y => apply transport_leq; intro; intro; intro; intro; classical *)
(*   | |- ?x <> ?y => apply transport_neq; intro; intro; intro; intro; classical      *)
(*   (* | |- exists x : Real, ?A => apply transport_exists;  intro; intro; intro; classical *) *)
(*   | |- forall x , ?A => apply (transport_forall (fun x => A));   intro; intro; intro; classical *)
(*   (* | |- forall x : Real, ?A => apply (transport_forall (fun x => A));   intro; intro; intro; classical *) *)

(*   | |- ?A => apply skip *)
(*                    (* | |- ?A => match A with *) *)
(*                    (*          | ?a = ?b => fail "haha" *) *)
(*                    (*          | _ => fail "FAIL" A *) *)
(*                    (*          end  *) *)


(*   end. *)

  
  Lemma IZreal4neq0 : IZreal 4 <> real_0.
  Proof.
    apply transport_neq.
    intro.
    intro.
    intro.
    intro.
    relate.
    rewrite (relate_IZreal _ _ H).
      by lra.
    

    (* classical. *)
    (* relate. *)
    (* rewrite (relate_IZreal _ _ H). *)
    (*   by lra. *)
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

End RealHelpers.
