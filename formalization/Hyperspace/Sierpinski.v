(** Sierpinski space and continuity **)
Require Import Kleene.
Require Import Real Euclidean.
Require Import Lia.
Require Import Dyadic.
Section S_Defs.
  Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.
  #[local] Notation "^K" := (@K types) (at level 0).
  #[local] Notation "^M" := (@M types) (at level 0).

  (** Sierpinski space is defined as a subtype of Kleeneans **)
  Definition sierp := {k : ^K | k <> lazy_bool_false}.
  Definition sierp_up (s : sierp) := (proj1_sig s) = lazy_bool_true.

  Definition sierp_from_kleenean {k} (H : k <> lazy_bool_false) : sierp.
  Proof.
  exists k.
  apply H.
  Defined.

  Lemma kleenean_from_sierp (s: sierp): ^K.
  Proof.
    destruct s.
    auto.
  Defined.

  Lemma sierp_and s1 s2 : {s | sierp_up s <-> sierp_up s1 /\ sierp_up s2}. 
  Proof.
    destruct s1 as [k1 K1].
    destruct s2 as [k2 K2].
    assert (lazy_bool_and k1 k2 <> lazy_bool_false).
    { rewrite lazy_bool_and_down.
      intros H.
      destruct H;auto.
    }
    exists (sierp_from_kleenean H).
    unfold sierp_from_kleenean, sierp_up;simpl.
    rewrite lazy_bool_and_up;split;auto.
  Defined.
  Lemma sierp_from_semidec {P} : {k | (lazy_bool_up klb k <-> P)}  -> {s | sierp_up s <-> P}.
  Proof.
  Admitted.

  Definition fn_to_sierpinki_to_kleene (c: nat -> sierp): (nat -> ^K).
  Proof.
    intro n.
    apply (c n).
  Defined.

  Lemma eventually_true :forall (c : forall (n :nat), sierp), {k | sierp_up k <-> exists n, sierp_up(c n)}.
  Proof.
    intros.
    pose (s:= lazy_bool_countable_or (fn_to_sierpinki_to_kleene c)).
    (* TODO: try to simplify, get rid of fn_to_sierpinki_to_kleene *)
    destruct s as [k [nf co]].
    exists (sierp_from_kleenean nf).
    unfold sierp_from_kleenean, sierp_up;simpl.
    unfold fn_to_sierpinki_to_kleene in co.
    auto.
  Defined.

  Lemma semidec_M_countable_selection (P : nat -> Prop) : (forall n, semidec (P n)) -> (exists n, P n) -> ^M {n | (P n)}.
  Proof.
    intros.
    apply (M_lift {n | projP1 _ _ (X n) = lazy_bool_true}).
    - intros.
      destruct H0 as [n H0].
      destruct (X n).
      exists n.
      apply i.
      apply H0.
    - apply M_countable_selection.
      destruct H.
      exists x.
      destruct (X x).
      apply i.
      exact H.
  Defined.
  (* Axiom kleenean_from_nat_sequence : forall (f : nat -> nat), {k : ^K | k = lazy_bool_true <-> exists n, (f n) = 1}.  *)

  Axiom kleenean_to_nat_sequence : forall (k : ^K), ^M {f : nat -> nat | k = lazy_bool_true <-> exists n, (f n) = 1}.

  (* Lemma sierp_from_nat_sequence : forall (f : nat -> nat), {s : sierp | sierp_up s <-> exists n, (f n) = 1}.  *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct (kleenean_from_nat_sequence f) as [k P]. *)
  (* Admitted. *)

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

  (* Lemma multivalued_choice_sequence_sierp (f : forall n, sierp) : ^M {c : nat -> nat | (forall n, (c n) = 0 \/  sierp_up (f (pred (c n)))) /\ forall m, sierp_up (f m) -> exists n, (c n) <> 0 /\ pred (c n) = m}. *)
  (* Proof. *)
  (* assert (forall n, ^M {g : nat -> nat | sierp_up (f n) <-> exists m, (g m) = 1}). *)
  (* { *)
  (*   intros. *)
  (*   apply (sierp_to_nat_sequence (f n)). *)
  (* } *)
  (* apply M_countable_lift in X. *)
  (* revert X. *)
  (* apply M_lift. *)
  (* intros. *)
  (* destruct (enumerable_pair _ _ enumerable_nat enumerable_nat) as [e E]. *)
  (* assert  {h : nat -> nat -> nat | forall n, sierp_up (f n) <-> (exists m, h n m = 1)} as [h H']. *)
  (* { *)
  (*   exists ((fun n => projP1 _ _ (H n))). *)
  (*   intros. *)
  (*   destruct (H n). *)
  (*   auto. *)
  (* } *)
  (* exists (fun nm => (if (h (fst (e nm)) (snd (e nm))) =? 1 then (S (fst (e nm))) else 0)). *)
  (* split. *)
  (* - intros nm. *)
  (*   destruct (h (fst (e nm)) (snd (e nm)) =? 1) eqn : b; [right| left;auto]. *)
  (*   rewrite Nat.pred_succ. *)
  (*   apply H'. *)
  (*   exists (snd (e nm)). *)
  (*   apply Nat.eqb_eq. *)
  (*   exact b. *)
  (* - intros n N. *)
  (*   destruct (proj1 (H' n) N) as [m M]. *)
  (*   destruct (E (n,m)) as [nm NM]. *)
  (*   exists nm. *)
  (*   rewrite NM;simpl. *)
  (*   rewrite M. *)
  (*   split; [apply Nat.neq_succ_0 |reflexivity]. *)
  (* Defined. *)
  (* Fixpoint nat_sequence_transform_min (f : nat -> nat) n := *)
  (*   match n with *)
  (*   | 0 => (f 0) *)
  (*   | (S n') => match (nat_sequence_transform_min f n') with *)
  (*              | 0 => match (f n) with *)
  (*                    | 0 => 0 *)
  (*                    | 1 => 1 *)
  (*                    | _ => 2 *)
  (*                    end *)
  (*              | _ => 2 *)
  (*              end *)
  (*  end. *)

  (* Lemma nat_sequence_transform_min_spec f : forall n, (nat_sequence_transform_min f n) = 1 <-> ((f n) = 1 /\ forall m, (m <n)%nat -> (f m) = 0). *)
  (* Proof. *)
  (*   assert (forall n, (nat_sequence_transform_min f n) = 0 <-> forall m, (m <= n)%nat -> (f m) = 0). *)
  (*   { *)
  (*     intros n. *)
  (*     induction n;simpl. *)
  (*     - split;intros. *)
  (*       rewrite Nat.le_0_r in H0;rewrite H0;auto. *)
  (*       apply H;lia. *)
  (*     - destruct (nat_sequence_transform_min f n). *)
  (*       + destruct (f (S n)) eqn:E; [|destruct n0];split;try lia. *)
  (*         * intros. *)
  (*           rewrite Nat.le_succ_r in H0. *)
  (*           destruct H0;auto. *)
  (*           apply IHn;try lia. *)
  (*           rewrite H0;auto. *)
  (*        * intros. *)
  (*          specialize (H (S n)). *)
  (*          contradict H;lia. *)
  (*        * intros. *)
  (*          specialize (H (S n)). *)
  (*          contradict H;lia. *)
  (*     + split;try lia. *)
  (*       intros. *)
  (*       assert (S n0 = 0). *)
  (*       apply IHn. *)
  (*       intros. *)
  (*       apply H. *)
  (*       lia. *)
  (*       contradict H0. *)
  (*       lia. *)
  (*   } *)
  (*   intros n. *)
  (*   induction n. *)
  (*   - split;[split;[auto | lia] | ]. *)
  (*     simpl;intros [-> _];auto. *)
  (*   - simpl;destruct (nat_sequence_transform_min f n) eqn: Q;[ | split;try lia]. *)
  (*     + destruct (f (S n)) eqn : E;simpl;[lia|]. *)
  (*       destruct n0 eqn: E'; simpl;split;try lia. *)
  (*       split;auto. *)
  (*       intros m. *)
  (*       rewrite Nat.lt_succ_r. *)
  (*       apply H;auto. *)
  (*     + intros [H1 H2]. *)
  (*       assert (nat_sequence_transform_min f n = 0). *)
  (*       apply H. *)
  (*       intros. *)
  (*       apply H2. *)
  (*       lia. *)
  (*       contradict Q. *)
  (*       lia. *)
  (*  Defined. *)

  (* Lemma kleenean_from_nat_seq_min (f : nat -> nat) : {k : ^K | k = lazy_bool_true <-> exists n, ((f n ) = 1 /\ forall m, (m < n)%nat -> (f m) = 0)}. *)
  (* Proof. *)
  (*   destruct (kleenean_from_nat_sequence (nat_sequence_transform_min f)) as [k H]. *)
  (*   exists k. *)
  (*   rewrite H. *)
  (*   split;intros. *)
  (*   - destruct H0 as [n H0]. *)
  (*     exists n. *)
  (*     apply nat_sequence_transform_min_spec;auto. *)
  (*   - destruct H0 as [n H0]. *)
  (*     exists n. *)
  (*     apply nat_sequence_transform_min_spec;auto. *)
  (* Qed. *)
  (* Definition kleene_seq_to_nat_seq_fun (S : nat -> ^K) : forall (n: nat),  ^M nat. *)
  (* Proof. *)
  (*   intros n. *)
  (*   pose proof (kleenean_to_nat_sequence (S n)). *)
  (*   revert X. *)
  (*   apply M_lift. *)
  (*   intros H. *)
  (*   destruct H. *)
  (*   apply (x n). *)
  (* Defined.  *)

  
End S_Defs.
Section Continuity.
  Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.
  #[local] Notation "^K" := (@K types) (at level 0).
  #[local] Notation "^M" := (@M types) (at level 0).
  #[local] Notation "^Real" := (@Real types) (at level 0).
  #[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).
  #[local] Notation "^euclidean" := (@euclidean types) (at level 0).

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
  (* continuity principle for functions to Sierpinski*)
  Axiom interval_extension_sierp : forall {d} (f : euclidean d -> sierp), ^M {F : DyadicVector -> nat -> bool | (forall v n, (F v n) = true -> forall x, euclidean_max_dist x (to_euclidean v) < prec n -> sierp_up (f x)) /\ forall x, sierp_up (f x) -> exists v n, (euclidean_max_dist x (to_euclidean v)) < prec n /\ (F v n) = true}. 

  Lemma real_archimedean_constructive : forall x, x > real_0 -> ^M {n | prec n < x}.
  Proof.
    intros.
    apply semidec_M_countable_selection.
    intros.
    apply real_lt_semidec.
    apply real_Archimedean.
    exact H.
  Defined.

  Lemma continuity_sierp : forall {d} (f : euclidean d -> sierp) x, sierp_up (f x) -> ^M {n | forall y, euclidean_max_dist x y < prec n -> sierp_up (f y) }.
  Proof.
    intros.
    pose proof (interval_extension_sierp f).
    revert X.
    apply M_lift_dom.
    intros.
    destruct H0 as [F [H1 H2]].
    apply (M_lift_dom ({v & {n | (euclidean_max_dist x (to_euclidean v)) < (prec n) /\ F v n = true}})).
    - intros.
      destruct H0 as [v [n [P1 P2]]].
      apply (M_lift {m | prec m < prec n - (euclidean_max_dist x (to_euclidean v))});[|apply real_archimedean_constructive;apply real_gt_minus_gt_zero;auto].
      intros.
      destruct H0 as [m H0].
      exists m.
      intros.
      apply (H1 _ _ P2).
      apply (real_le_lt_lt _ (euclidean_max_dist y x + euclidean_max_dist x (to_euclidean v))).
      apply euclidean_max_dist_tri.
      replace (prec n) with (prec n - euclidean_max_dist x (to_euclidean v) + euclidean_max_dist x (to_euclidean v)) by ring.
      apply real_lt_plus_r_lt.
      rewrite euclidean_max_dist_sym.
      apply (real_lt_lt_lt _ _ _ H3);auto.
    - destruct (enumerable_pair _ _ enumerable_nat (enumerable_dyadic_vector d)) as [e E].
      apply (M_lift {n | (euclidean_max_dist x (to_euclidean (snd (e n)))) < (prec (fst (e n))) /\ (F (snd (e n)) (fst (e n))) = true}).
      intros.
      destruct H0 as [n H0].
      exists (snd (e n)); exists (fst (e n)).
      exact H0.

      apply semidec_M_countable_selection.
      + intros.
        apply semidec_and.
        apply real_lt_semidec.
        destruct (F (snd (e n)) (fst (e n))).
        exists lazy_bool_true.
        split;intros;unfold lazy_bool_up;auto.
        exists lazy_bool_false.
        unfold lazy_bool_up.
        split;intros.
        contradict H0.
        apply lazy_bool_distinct.
        contradict H0; auto.
    + destruct (H2 _ H) as [v [n P]].
      destruct (E (n,v)) as [m M].
      exists m.
      rewrite M;auto.
  Defined.

  Lemma continuity_euclidean : forall {d} (f : euclidean d -> euclidean d) x m, ^M {n | forall y, euclidean_max_dist x y < prec n -> euclidean_max_dist (f x) (f y) < prec m}.
  Proof.
    intros.
    assert (forall y, {s |(sierp_up s) <-> (euclidean_max_dist (f x) (f y)) < prec m}).
    {
      intros.
      destruct (real_lt_semidec (euclidean_max_dist (f x) (f y)) (prec m)) as [k K].
      apply sierp_from_semidec.
      exists k.
      exact K.
    }
    pose proof (continuity_sierp (fun y => (projP1 _ _ (X y))) x).
    simpl in X0.
    destruct (X x).
    simpl in X0.
    assert (sierp_up x0).
    apply i.
    rewrite ((proj2 (euclidean_max_dist_id _ _)) (eq_refl (f x))).
    apply prec_pos.
    specialize (X0 H).
    revert X0.
    apply M_lift.
    intros.
    destruct H0 as [n H0].
    exists n.
    intros.
    specialize (H0 _ H1).
    destruct (X y).
    simpl in H0.
    apply i0.
    exact H0.
  Defined.
End Continuity.
