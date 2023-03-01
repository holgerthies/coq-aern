Require Import Kleene.
Require Import Real.
Require Import Lia.
Section S_Defs.
  Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.
  #[local] Notation "^K" := (@K types) (at level 0).
  #[local] Notation "^M" := (@M types) (at level 0).
  Definition sierp := {k : ^K | k <> lazy_bool_false}.

  Definition sierp_up (s : sierp) := (proj1_sig s) = lazy_bool_true.

  Definition sierp_from_kleenean {k} (H : k <> lazy_bool_false) : sierp.
  Proof.
  exists k.
  apply H.
  Defined.

  Axiom kleenean_from_nat_sequence : forall (f : nat -> nat), {k : ^K | k = lazy_bool_true <-> exists n, (f n) = 1}. 

  Axiom kleenean_to_nat_sequence : forall (k : ^K), ^M {f : nat -> nat | k = lazy_bool_true <-> exists n, (f n) = 1}.

  Fixpoint nat_sequence_transform_min (f : nat -> nat) n :=
    match n with
    | 0 => (f 0)
    | (S n') => match (nat_sequence_transform_min f n') with
               | 0 => match (f n) with
                     | 0 => 0
                     | 1 => 1
                     | _ => 2
                     end
               | _ => 2
               end
   end.

  Lemma nat_sequence_transform_min_spec f : forall n, (nat_sequence_transform_min f n) = 1 <-> ((f n) = 1 /\ forall m, (m <n)%nat -> (f m) = 0).
  Proof.
    assert (forall n, (nat_sequence_transform_min f n) = 0 <-> forall m, (m <= n)%nat -> (f m) = 0).
    {
      intros n.
      induction n;simpl.
      - split;intros.
        rewrite Nat.le_0_r in H0;rewrite H0;auto.
        apply H;lia.
      - destruct (nat_sequence_transform_min f n).
        + destruct (f (S n)) eqn:E; [|destruct n0];split;try lia.
          * intros.
            rewrite Nat.le_succ_r in H0.
            destruct H0;auto.
            apply IHn;try lia.
            rewrite H0;auto.
         * intros.
           specialize (H (S n)).
           contradict H;lia.
         * intros.
           specialize (H (S n)).
           contradict H;lia.
      + split;try lia.
        intros.
        assert (S n0 = 0).
        apply IHn.
        intros.
        apply H.
        lia.
        contradict H0.
        lia.
    }
    intros n.
    induction n.
    - split;[split;[auto | lia] | ].
      simpl;intros [-> _];auto.
    - simpl;destruct (nat_sequence_transform_min f n) eqn: Q;[ | split;try lia].
      + destruct (f (S n)) eqn : E;simpl;[lia|].
        destruct n0 eqn: E'; simpl;split;try lia.
        split;auto.
        intros m.
        rewrite Nat.lt_succ_r.
        apply H;auto.
      + intros [H1 H2].
        assert (nat_sequence_transform_min f n = 0).
        apply H.
        intros.
        apply H2.
        lia.
        contradict Q.
        lia.
   Defined.

  Lemma kleenean_from_nat_seq_min (f : nat -> nat) : {k : ^K | k = lazy_bool_true <-> exists n, ((f n ) = 1 /\ forall m, (m < n)%nat -> (f m) = 0)}.
  Proof.
    destruct (kleenean_from_nat_sequence (nat_sequence_transform_min f)) as [k H].
    exists k.
    rewrite H.
    split;intros.
    - destruct H0 as [n H0].
      exists n.
      apply nat_sequence_transform_min_spec;auto.
    - destruct H0 as [n H0].
      exists n.
      apply nat_sequence_transform_min_spec;auto.
  Qed.
  Definition kleene_seq_to_nat_seq_fun (S : nat -> ^K) : forall (n: nat),  ^M nat.
  Proof.
    intros n.
    pose proof (kleenean_to_nat_sequence (S n)).
    revert X.
    apply M_lift.
    intros H.
    destruct H.
    apply (x n).
  Defined. 

  
End S_Defs.
