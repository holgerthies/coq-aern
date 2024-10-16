(* this file proves various results related to continuity of Baire space and generalizations to other types *)
Require Import Lia.
Require Import Real Euclidean List Minmax Classical.Subsets Sierpinski Testsearch Dyadic.
Require Import RealAssumption.
Require Import List.


Import ListNotations.
Lemma continuity : forall {X} (f : (nat -> X) -> sierp) (x : (nat -> X)), sierp_up (f x) -> ^M {m | forall y, (forall n, (n < m)%nat -> x n = y n) -> sierp_up (f y)}.
Proof.
  intros.
  apply (seq_subset_continuity (fn_to_sierpinki_to_kleene f) x H).
Qed.

  Lemma baire_continuity (f : (nat->nat) -> nat -> nat) : ^M ( forall x n,  {m |forall y, (forall i, (i < m)%nat -> x i = y i) -> (forall i, (i < n)%nat -> f x i = f y i)}).
   Proof.
     assert (forall n m, {fn : (nat -> nat) -> sierp | forall x, sierp_up (fn x) <-> f x n = m}).
     {
         intros.
         enough (forall x, {s : sierp | sierp_up s <-> f x n = m}) as H. (exists (fun x => (pr1 _ _ (H x))); intros x; destruct (H x);auto).
         intros.
         apply sierp_from_semidec.
         unfold lazy_bool_up.
         destruct (f x n =? m) eqn:E.
         exists lazy_bool_true;rewrite <-Nat.eqb_eq;split;auto.
         exists lazy_bool_false.
         split;intros.
         contradict H;apply lazy_bool_distinct.
         rewrite Nat.eqb_neq in E;lia.
     }
     assert (forall x,  ^M (forall n, {k : nat | forall y, (forall i : nat, (i < k)%nat -> x i = y i) -> (forall i, (i < n)%nat ->  f x i = f y i)})).
     {
       intros.
       apply M_countable_lift.
       intros.
       induction n.
       - apply M_unit.
         exists 0%nat.
         intros;lia.
       - revert IHn.
         apply M_lift_dom.
         intros [k0 K0].
         destruct (X n (f x n)) as [fn F].
         assert (sierp_up (fn x)) by (apply F;auto).
         specialize (continuity fn _ H).
         apply M_lift.
         intros [k K].
         exists (max k k0).
         intros.
         assert (i < n \/ i = n)%nat by lia.
         destruct H2.
         apply K0;intros;auto.
         apply H0;lia.
         rewrite H2.
         apply eq_sym.
         apply F.
         apply K;auto.
         intros.
         apply H0;lia.
      }
      specialize (baire_choice _ X0).
      apply M_lift.
      intros [X2 _].
      apply X2.
   Qed.

  Lemma M_sierp_to_lazy P t : (forall (x : (nat -> nat)), sierp_up (t x) -> ^M {m : nat | P m x}) -> ^M {m : (nat -> nat) -> nat -> nat | forall x,  (forall k, m x k = 0%nat \/ P (pred (m x k)) x) /\ (sierp_up (t x) -> exists k, (m x k) <> 0%nat)}.
  Proof.
    intros.
    enough (^M (forall x, {m : nat -> nat |(forall k, m k = 0%nat \/ P (pred (m k)) x) /\ (sierp_up (t x) -> exists k, (m k) <> 0%nat)})).
    {
    revert X0.
    apply M_lift.
    intros.
    exists (fun n => (pr1 _ _ (H n))).
    intros.
    destruct (H x);simpl in *;auto.
    }
    enough (forall ϕ : nat -> nat,
             ^M
               {m : nat -> nat
               | (forall k : nat, m k = 0%nat \/ P (Init.Nat.pred (m k)) ϕ) /\
                 (sierp_up (t ϕ) -> exists k : nat, m k <> 0%nat)}).
    {
    pose proof (baire_choice (fun x => {m : nat -> nat | (forall k, m k = 0%nat \/ P (pred (m k)) x) /\ (sierp_up (t x) -> exists k, (m k) <> 0%nat) }) X0).
    revert X1.
    apply M_lift.
    intros [].
    apply x.
    }
    intros Phi.
    specialize (sierp_to_nat_sequence  (t Phi)).
    apply M_lift_dom.
    intros [f F].
    enough (forall k, ^M {m | f k = 1%nat /\ (m <> 0)%nat /\ P (pred m) Phi \/ (f k <> 1)%nat /\ m = 0%nat}).
    {
      apply M_countable_lift in X0.
      revert X0.
      apply M_lift.
      intros H.
      exists (fun k => (pr1 _ _ (H k))).
      split.
      intros.
      destruct (H k).
      simpl.
      destruct o; destruct H0;[destruct H1;right|left];auto.
      intros.
      destruct F.
      destruct (H1 H0).
      exists x.
      destruct (H x).
      simpl in *.
      destruct o.
      destruct H4;destruct H5;auto.
      contradict H3.
      apply H4.
    }
    intros.
    destruct ((f k) =? 1%nat) eqn:E.
    destruct F.
    assert (sierp_up (t Phi)) by (apply H0; exists k; apply Nat.eqb_eq;auto).
    specialize (X _ H1).
    revert X.
    apply M_lift; intros [].
    exists (S x).
    simpl.
    left;split.
    apply Nat.eqb_eq;auto.
    split;try lia;auto.
    apply M_unit.
    exists 0%nat.
    right.
    split;auto.
    apply Nat.eqb_neq;auto.
  Qed.

  Lemma M_sierp_to_lazy_unique P t : (forall (x : (nat -> nat)), sierp_up (t x) -> ^M {m : nat | P m x}) -> ^M {m : (nat -> nat) -> nat -> nat | forall x,  (forall k, m x k = 0%nat \/ P (pred (m x k)) x) /\ (sierp_up (t x) -> (exists k, (m x k) <> 0%nat) /\ (forall k, m x k <> 0%nat -> forall k', (k <> k') -> m x k' = 0%nat)) }.
  Proof.
    intros.
    specialize (M_sierp_to_lazy P t X).
    apply M_lift.
    intros [m Pm].
    enough (forall x k, {n | ((n = 0%nat) \/ n = m x k) /\ (n <> 0%nat <-> ((m x k <> 0)%nat /\ forall i, (i < k)%nat -> m x i = 0%nat))}).
    {
      exists (fun x k => pr1 _ _ (H x k)).
      intros.
      split;intros.
      - destruct (H x k) as [n [N1 N2]];simpl.
        destruct N1.
        left;auto.
        destruct n.
        left;auto.
        right.
        destruct N2.
        rewrite H0.
        destruct (Pm x) as [Pm' _].
        specialize (Pm' k).
        destruct Pm';try lia;auto.
      - pose proof (proj2 (Pm x) H0).
        destruct (dec_inh_nat_subset_has_unique_least_element (fun k => m x k <> 0%nat)) as [k K];intros;try lia;try apply H1.
        split.
        + exists k.
          destruct (H x k) as [n [N1 N2]];simpl in *.
          apply N2.
          split; try apply K.
          intros.
          destruct K.
          destruct H3.
          specialize (H5 i).
          destruct (m x i);auto.
          contradict H2.
          apply Nat.nlt_ge.
          apply H5;auto.
       + intros.
          assert (k0 = k) as ->.
          {
          apply eq_sym.
          apply K.
          destruct (H x k0); simpl in *.
          destruct a.
          destruct H4;try lia.
          split;try lia.
          intros.
          destruct H5.
          specialize (H5 H2).
          destruct H5.
          apply Nat.nlt_ge.
          intros N.
          contradict H6.
          apply H8;auto.
          }
          destruct (H x k') as [n' [N1' N2']];simpl.
          simpl in *.
          destruct N1';auto.
          destruct n';auto.
          destruct N2'.
          clear H6.
          destruct K.
          destruct H6.
          destruct (Lt.nat_total_order_stt _ _ H3).
          contradict H6.
          apply H5;auto.
          assert (m x k' <> 0%nat) by lia.
          specialize (H8 _ H10).
          lia.
        }
        intros.
        enough ({b | b = true <-> forall i, (i < k)%nat -> m x i = 0%nat}) as [b B].
        exists (match (m x k) with 0%nat => 0%nat | (S n') => if b then (S n') else 0%nat end).
        destruct (m x k).
        split;auto;split;intros;[split|];try lia;auto.
        destruct b;split;auto;split;auto;try lia.
        intros;split;auto;intros;apply B;auto.
        intros [_ H2].
        destruct B.
        specialize (H0 H2).
        contradict H0;apply Bool.diff_false_true.

        induction k.
        exists true.
        split;auto;intros _; lia.
        destruct IHk.
        exists (andb x0 (m x k =? 0)%nat).
        split;intros.
        apply andb_prop in H.
        rewrite Nat.lt_succ_r in H0.
        destruct H.
        apply Nat.eqb_eq in H1.
        destruct (Lt.le_lt_or_eq_stt _ _ H0).
        apply i;auto.
        rewrite H2;auto.
        apply Bool.andb_true_iff.
        split.
        apply i;auto.
        apply Nat.eqb_eq.
        apply H;lia.
  Qed.

  Lemma continuity_semidec_eq {A B : Type} (f : (nat -> A) -> B) : (forall (y y' : B), (semidec (y = y'))) -> forall x, ^M {k | forall x', (forall n, (n < k)%nat -> x n = x' n) -> f x = f x'}.  
  Proof.
    intros.
    assert ({e : B -> B -> sierp | forall y y', sierp_up (e y y') <-> y = y'}) as [e E].
    {
      enough (forall (y y' : B), {s | sierp_up s <-> y = y'}) by (exists (fun y y' => (pr1 _ _ (X0 y y')));intros;destruct (X0 y y');auto).
      intros.
      apply sierp_from_semidec.
      destruct (X y y').
      exists x0;auto.
    }
    assert (forall y, {g : (nat -> A) -> sierp | forall x, sierp_up (g x) <-> (f x) = y}).
    {
      intros.
      exists (fun x => e (f x) y).
      intros.
      rewrite E;split;auto.
    }
    destruct (X0 (f x)).
    assert (sierp_up (x0 x)) by (apply i;auto).
    specialize (continuity _ _ H).
    apply M_lift.
    intros [k K].
    exists k.
    intros.
    apply eq_sym.
    apply i.
    apply K;auto.
  Qed.

  Lemma semidec_to_sierp {A} (P: A -> Prop ): (forall x, semidec (P x)) -> {t | forall x, sierp_up (t x) <-> P x}.
  Proof.
      intros.
      enough (forall x, {s | sierp_up s <-> P x}) by (exists (fun x => pr1 _ _  (X0 x));intros;destruct (X0 x);simpl;auto).
      intros.
      destruct (X x).
      apply sierp_from_semidec.
      exists x0;auto.
  Qed.

  Lemma partial_baire_choice :
  forall  (P : (nat -> nat) -> Prop) (Q : nat -> (nat -> nat) -> Prop), (forall x, semidec (P x)) ->  (forall x, P x -> ^M {n | Q n x}) -> (^M (forall x, P x -> {n | Q n x})).
  Proof.
    intros.
    destruct (semidec_to_sierp P) as [t T];auto.
    assert (forall x, sierp_up (t x) -> ^M {n | Q n x}) as H by (intros; apply X0;apply T;auto).
    clear X X0.
    apply M_sierp_to_lazy_unique in H.
    revert H.
    apply M_lift.
    intros [m Pm] x Px.
    destruct (Pm x).
    apply T in Px.
    destruct (H0 Px).
    assert {k | m x k <> 0%nat} as [k K].
    apply ConstructiveEpsilon.constructive_indefinite_ground_description_nat;auto;intros; destruct (m x n);auto.
    exists (pred (m x k)).
    destruct (H k); try lia;auto.
  Qed.
  
  (* Lemma baire_modulus_exists (f : (nat -> nat) -> sierp) : ^M {mu : {x : (nat -> nat) | sierp_up (f x)} -> nat | forall x y, (forall n, (n < mu x)%nat -> pr1 _ _ x n =  y n) -> sierp_up (f y)}.   *)
  (* Proof. *)
  (*   pose proof (continuity f). *)
  (*   apply partial_baire_choice in X0. *)
  (*   revert X0. *)
  (*   apply M_lift. *)
  (*   intros. *)
  (* Admitted. *)

  Lemma semidec_sierp_up s : semidec (sierp_up s).
  Proof.
     destruct s.
     unfold sierp_up, semidec, lazy_bool_up.
     simpl.
     exists x;split;auto.
  Qed.

  Lemma continuity_partial P (f : ({x : nat -> nat | P x} -> nat)) : (forall x, semidec (P x)) -> forall x, ^M {k | forall x', (forall n, (n < k)%nat -> (pr1 _  _ x) n = (pr1 _ _ x') n) -> f x = f x'}.  
    intros.
    assert (^M {g : (nat -> nat) -> nat -> nat | (forall x, P x -> exists k,  g x k <> 0%nat ) /\ forall x  (H : P x) k, g x k <> 0%nat -> g x k = S (f (exist _ x H))}).
    {
      destruct (semidec_to_sierp P) as [t T];auto.
      enough (forall x, ^M {s : nat -> nat | (sierp_up (t x) -> exists k, s k <> 0%nat) /\ (forall H k, s k <> 0%nat -> s k = S (f (exist _ x H)))}).
      {
      pose proof (baire_choice _ X0).
      simpl in X1.
      revert X1.
      apply M_lift.
      intros [H S].
      exists (fun x => pr1 _ _ (H x)).
      split; intros;try rewrite <-T;destruct (H x0);destruct a;simpl in *;auto.
      apply e;apply T;auto.
      }
      intros.
      specialize (sierp_to_nat_sequence (t x0)).
      apply M_lift.
      intros [s Ps].
      assert (forall (n:nat), {m | ((s n) = 1%nat -> forall (H : P x0), m = S (f (exist _ x0 H))) /\ ((m <> 0)%nat -> (s n=1)%nat)}).
      {
        intros.
        destruct (Nat.eq_dec (s n) 1%nat).
        assert (sierp_up (t x0)) by (apply Ps; exists n;auto).
        assert (P x0) by (apply T;auto).
        exists (S (f (exist _ x0 H0))).
        split.
        intros.
        apply f_equal; apply f_equal.
        apply sigma_eqP2;auto.
        intros;auto.
        exists 0%nat;intros;lia.
      }
      exists (fun n => (pr1 _ _ (H n))).
      split.
      - intros.
        destruct Ps.
        destruct (H1 H0).
        exists x1. destruct (H x1);simpl in *.
        assert (P x0) by (apply T;auto).
        destruct a.
        rewrite (H5 H3 H4);lia.
     - intros.
       destruct (H k); simpl in *.
       destruct a.
       assert (P x0) by (apply T;apply Ps;exists k;auto).
       rewrite (H2 (H3 H1) H4).
       apply f_equal;apply f_equal.
       apply sigma_eqP2;auto.
    }
    revert X0.
    apply M_lift_dom.
    intros [g G].
    specialize  (baire_continuity g).
    apply M_lift.
    intros.
    destruct x.
    simpl in *.
    destruct G.
    assert {k | g x k <> 0%nat} as [k K].
    apply ConstructiveEpsilon.constructive_indefinite_ground_description_nat;auto;intros; destruct (g x n);auto.
    destruct (H x (S k)) as [m Pm].
    exists m.
    intros.
    destruct x'.
    simpl in *.
    enough (g x0 k <> 0%nat).
    apply Nat.succ_inj.
    rewrite <- (H1 x p k K).
    rewrite <-(H1 x0 _ k H3).
    apply Pm;try lia.
    intros.
    apply H2;auto.
    rewrite <-Pm;try lia;auto.
  Qed.

  Definition baire_base l := fun n => nth n l (last l 0%nat).

  Lemma initial_sequence x n : {l | (forall i, (i < n)%nat -> x i = (baire_base l i)) /\ length l = n}.
  Proof.
    induction n; [exists [];split;try lia;auto|].
    destruct IHn as [l [IH1 IH2]].
    exists (l ++ [x n]).
    intros.
    assert (length (l ++ [x n]) = S n) by (rewrite app_length;simpl;lia).
    split;auto.
    intros.
    rewrite Nat.lt_succ_r in H0.
    apply Lt.le_lt_or_eq_stt in H0.
    destruct H0;unfold baire_base.
    rewrite app_nth1;try lia.
    rewrite (nth_indep _ _ (last l 0%nat));try lia.
    apply IH1;auto.
    rewrite H0.
    replace n with (length l) at 2.
    rewrite nth_middle;auto.
  Qed.

  Definition to_initial_sequence x n := baire_base (pr1 _ _ (initial_sequence x n)).

  Lemma baire_continuous_modulus (P : (nat -> nat) -> sierp) : ^M {m : {x | sierp_up (P x)} -> nat | (forall x y, (forall n, (n < m x)%nat -> pr1 _ _ x n = y n) ->  (sierp_up (P y)))  /\ forall x, exists n0, forall n, (n > n0)%nat -> exists (H : sierp_up (P (to_initial_sequence (pr1 _ _ x) n))), m (exist _ (to_initial_sequence (pr1 _ _ x) n) H) = m x}.
  Proof.
    pose proof (continuity P).
    apply partial_baire_choice in X; [|intros;apply semidec_sierp_up].
    revert X.
    apply M_lift.
    intros.
    assert (forall (x : {x | sierp_up (P x)}), sierp_up (P (pr1 _ _ x))) by (intros [x Hx];auto).
    remember (fun x => pr1 _ _ (H _ (H0 x))) as f.
    assert (forall x, semidec (sierp_up (P x))) by (intros; apply semidec_sierp_up).
    pose proof (continuity_partial _ f X).
    exists f;simpl.
    rewrite Heqf in *; simpl in *;split; intros.
    destruct (H _ (H0 x)); simpl in *.
    apply s.
    intros;auto.
    apply M_hprop_elim.
    intros a b; apply irrl.
    specialize (X0 x).
    revert X0.
    apply M_lift.
    intros [k K].
    destruct (H _ (H0 x)) as [m Pm];simpl in *.
    assert (exists n0, n0 > k /\ n0 > m)%nat as [n0 [Hn0 Hn0']].
    {
      exists (S (max k m)).
      split;lia.
    }
    exists n0.
    intros.
    assert (sierp_up (P (to_initial_sequence (pr1 _ _ x) n))).
    {
      apply Pm.
      intros.
      destruct x;simpl in *.
      unfold to_initial_sequence.
      destruct (initial_sequence x n).
      simpl.
      apply a.
      lia.
    }
    exists H2.
    simpl.
    specialize (K (exist _ (to_initial_sequence (pr1 _ _ x) n) H2)).
    apply eq_sym.
    apply K.
    destruct x; simpl in *.
    intros.
    unfold to_initial_sequence.
    destruct (initial_sequence x n).
    simpl.
    apply a;lia.
 Qed.

