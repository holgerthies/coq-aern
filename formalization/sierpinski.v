Require Import Kleene.
Require Import Real.
Require Import Lia.
Require Import Dyadic.
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

  Lemma sierp_from_semidec {P} : {k | (lazy_bool_up klb k <-> P)}  -> {s | sierp_up s <-> P}.
  Proof.
  Admitted.
  Axiom kleenean_from_nat_sequence : forall (f : nat -> nat), {k : ^K | k = lazy_bool_true <-> exists n, (f n) = 1}. 

  Axiom kleenean_to_nat_sequence : forall (k : ^K), ^M {f : nat -> nat | k = lazy_bool_true <-> exists n, (f n) = 1}.

  Lemma sierp_from_nat_sequence : forall (f : nat -> nat), {s : sierp | sierp_up s <-> exists n, (f n) = 1}. 
  Proof.
    intros.
    destruct (kleenean_from_nat_sequence f) as [k P].
  Admitted.

  Lemma sierp_to_nat_sequence :  forall (s : sierp), ^M {f : nat -> nat | sierp_up s <-> exists n, (f n) = 1}.
  Proof.
    intros.
    destruct s as [k K].
    pose proof (kleenean_to_nat_sequence k).
    revert X.
    apply M_lift.
    intros.
    destruct H as [f P].
    exists f.
    exact P.
  Defined.

  Lemma multivalued_choice_sequence_sierp (f : forall n, sierp) : ^M {c : nat -> nat | (forall n, (c n) = 0 \/ sierp_up (f (pred (c n)))) /\ forall m, sierp_up (f m) -> exists n, pred (c n) = m}.
  Proof.
  assert (forall n, ^M {g : nat -> nat | sierp_up (f n) <-> exists m, (g m) = 1}).
  {
    intros.
    apply (sierp_to_nat_sequence (f n)).
  }
  apply M_countable_lift in X.
  revert X.
  apply M_lift.
  intros.
  destruct (enumerable_pair _ _ enumerable_nat enumerable_nat) as [e E].
  assert  {h : nat -> nat -> nat | forall n, sierp_up (f n) <-> (exists m, h n m = 1)} as [h H'].
  {
    exists ((fun n => projP1 _ _ (H n))).
    intros.
    destruct (H n).
    auto.
  }
  exists (fun nm => (if (h (fst (e nm)) (snd (e nm))) =? 1 then (S (fst (e nm))) else 0)).
  split.
  - intros nm.
    destruct (h (fst (e nm)) (snd (e nm)) =? 1) eqn : b; [right| left;auto].
    rewrite Nat.pred_succ.
    apply H'.
    exists (snd (e nm)).
    apply Nat.eqb_eq.
    exact b.
  - intros n N.
    destruct (proj1 (H' n) N) as [m M].
    destruct (E (n,m)) as [nm NM].
    exists nm.
    rewrite NM;simpl.
    rewrite M.
    reflexivity.
  Defined.
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
