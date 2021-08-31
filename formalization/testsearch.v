Require Import ConstructiveEpsilon.
Require Import Real.
Set Warnings "-parsing".
From mathcomp Require Import all_ssreflect.
Require Import Psatz.
Require Import Nat.
Require Import PeanoNat.
Require Import Kleene.
Require Import Reals.
Set Warnings "parsing".
(* 
   Multivalued searching from existing searching:
     constructive_indefinite_ground_description_nat_Acc_PQ
   It is not yet decided if this to be used for our searching.. 
 *)

Section testsearch.
  Generalizable Variables K M.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
          {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
          {M_MultivalueMonad : MultivalueMonad}.


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
      M {n | P n /\ (forall k, (k < n)%coq_nat -> Q k)}.
  Proof.
    intros.
    apply M_countable_lift in X.
    apply (M_lift (forall n : nat, {P n} + {Q n})).
    intro.
    apply (epsilon_smallest_PQ P Q); auto.
    exact X.
  Defined.

  (*********)




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
  

  Lemma weaken_orM_r : forall P Q Q': Prop, (Q -> Q') -> M ({P}+{Q}) -> M ({P}+{Q'}).
  Proof.
    intros P Q Q' QQ'.
    apply M_lift.
    move => [iP|iQ].
    left. by auto.
    right. exact (QQ' iQ).
  Qed.

End testsearch.
