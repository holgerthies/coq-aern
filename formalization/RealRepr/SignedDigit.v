(* WIP file by Sewon:
   This file provides various results on signed digit representation
   and use it to derive real number's continuity principle 
 *)
Require Import Lia.
Require Import Real Euclidean List Minmax Classical.Subsets Sierpinski Testsearch Dyadic.
Require Import RealAssumption.

From CAern.Analysis Require Import MultiLimit.
From CAern.Classical Require Import Analysis.


(* some stuffs about prec and pow2 *)
Definition pow2 n := Nreal (Npow2 n). 

Lemma prec_S_lt_real_1 : forall n, prec (S n) < real_1.
Proof.
  intro.
  induction n.
  simpl.
Admitted.

Lemma prec_pow2_cancel_r : forall n m, (n < m)%nat -> prec m * pow2 n = prec (m - n)%nat.
Proof.
  intros.
  assert ((m - n) + n = m)%nat.
  lia.
  rewrite <- H0 at 1.
  rewrite prec_hom.
  rewrite real_mult_assoc.
  unfold pow2.
  rewrite prec_Npow2_unit.
  rewrite real_mult_comm, real_mult_unit.
  auto.
Defined.

Lemma prec_pow2_cancel : forall n, prec n * pow2 n = real_1.
Proof.
  intros.
  unfold pow2.
  auto with real.
Defined.

Lemma pow2_prec_cancel : forall n, pow2 n * prec n = real_1.
Proof.
  intros.
  unfold pow2.
  rewrite real_mult_comm.
  auto with real.
Defined.


Lemma prec_antitone_le : forall n m, (n <= m)%nat -> prec m <= prec n.
Proof.
  intros.
  assert (n = m \/ n < m)%nat.
  lia.
  destruct H0.
  rewrite H0; right; auto.
  left.
  apply prec_monotone.
  exact H0.
Defined.

Lemma Npow2_mult : forall n m,  ((Npow2 (n + m)) =  (Npow2 n * Npow2 m))%nat.
Proof.
  intros.
  induction n.
  simpl.
  auto.
  simpl.
  lia.
Defined.

Lemma pow2_hom : forall n m, pow2 (n + m) = pow2 n * pow2 m.
Proof.
  intros.
  unfold pow2.
  rewrite <- Nreal_mult, Npow2_mult.
  auto.
Defined.

Lemma pow2_pos : forall n, pow2 n > real_0.
Proof.
  intro.
  induction n.
  unfold pow2; simpl.
  rewrite real_plus_comm, real_plus_unit.
  apply real_1_gt_0.  
Admitted.

Lemma prec_1_plus_prec_1 : prec 1  + prec 1 = real_1.
Admitted.

Lemma Nreal_inv_monotone : forall n m, Nreal n < Nreal m -> (n < m)%nat.
Proof.
Admitted.

(* Sign digit representation *)

Inductive sd := sdL | sdO | sdR. 
Definition Real_of_sd sd : ^Real :=
  match sd with
  | sdL => - real_1
  | sdO => real_0
  | sdR => real_1
  end.

Fixpoint sd_repr_p_sum (f : nat -> sd) (n : nat) : ^Real :=
  match n with
  | O => Real_of_sd (f O) * prec 1
  | S m => sd_repr_p_sum f m + prec (S n) * Real_of_sd (f n)
  end.

Lemma sd_repr_p_is_fast_cauchy f : is_fast_cauchy (sd_repr_p_sum f).
Proof.
  apply consecutive_converging_fast_cauchy.
  intro.
  rewrite dist_abs.
  simpl.
  replace (sd_repr_p_sum f n +
             prec n / real_2_neq_0 / real_2_neq_0 * Real_of_sd (f (S n)) -
             sd_repr_p_sum f n) with (prec n / real_2_neq_0 / real_2_neq_0 * Real_of_sd (f (S n))) by ring.
  destruct (f (S n)); simpl.
  replace (prec n / real_2_neq_0 / real_2_neq_0 * - real_1) with
    (- (prec n / real_2_neq_0 / real_2_neq_0)) by ring.
  rewrite <- abs_symm.
  left.
  rewrite abs_pos_id.
  pose proof (prec_S (S n)).
  simpl in H.
  auto.
  left.
  exact (prec_pos (S (S n))).
  replace (prec n / real_2_neq_0 / real_2_neq_0 * real_0) with
    (real_0) by ring.
  destruct (abs_zero real_0).
  rewrite H0; auto.
  left.
  exact (prec_pos (S ( n))).
  replace (prec n / real_2_neq_0 / real_2_neq_0 * real_1) with
    ((prec n / real_2_neq_0 / real_2_neq_0)) by ring.
  left.
  rewrite abs_pos_id.
  pose proof (prec_S (S n)).
  simpl in H.
  auto.
  left.
  exact (prec_pos (S (S n))).
Defined.

Definition sd_repr f := projP1 _ _ (real_limit _ (sd_repr_p_is_fast_cauchy f)).

Definition sd_names_share_n_entries (f g : nat -> sd) n := forall m : nat, (m < n)%nat -> f m = g m.

Lemma fast_limit_upper_bound f x u : (forall n, f n <= u) -> is_fast_limit x f -> x <= u.
Proof.
  intros.
  apply real_nge_le.
  intro.
  apply (real_lt_plus_r_lt (- u)) in H1.
  replace ( u + - u) with real_0 in H1 by ring.
  pose proof (real_Archimedean (x - u) H1) as [n h].
  pose proof (H n).
  pose proof (H0 n).
  (* elementary analysis  *)
Admitted.

Lemma fast_limit_lower_bound f x l : (forall n, l <= f n) -> is_fast_limit x f -> l <= x.
Proof.
  (* elementary analysis  *)
Admitted.


Definition sd_zero := fun n : nat => sdO.

Lemma sd_zero_repr_zero : real_0 = sd_repr sd_zero.
Proof.
  apply real_le_le_eq.
  unfold sd_repr.
  destruct (real_limit (sd_repr_p_sum sd_zero) (sd_repr_p_is_fast_cauchy sd_zero)).
  simpl.
  apply (fast_limit_lower_bound (sd_repr_p_sum sd_zero)); auto.
  intros.
  induction n.
  simpl.
  right.
  ring.
  simpl.
  replace (sd_repr_p_sum sd_zero n + prec n / real_2_neq_0 / real_2_neq_0 * real_0)
    with (sd_repr_p_sum sd_zero n) by ring.
  exact IHn.
  unfold sd_repr.
  destruct (real_limit (sd_repr_p_sum sd_zero) (sd_repr_p_is_fast_cauchy sd_zero)).
  simpl.
  apply (fast_limit_upper_bound (sd_repr_p_sum sd_zero)); auto.
  intros.
  induction n.
  simpl.
  right.
  ring.
  simpl.
  replace (sd_repr_p_sum sd_zero n + prec n / real_2_neq_0 / real_2_neq_0 * real_0)
    with (sd_repr_p_sum sd_zero n) by ring.
  exact IHn.
Defined.

Lemma min_upperbound_exists'
  : forall x : ^Real, real_0 < x -> exists n : nat, Nreal n <= x < Nreal (S n).
Proof.
  intros.
  pose proof (min_upperbound_exists x H) as [n [p q]].
  destruct q.
  exists n; auto.
  exists (S n).
  rewrite H0.
  split; auto.
  right; auto.
  apply Nreal_strict_monotone; auto.
Defined.
     
Lemma round_down x : real_0 <= x -> exists n y, real_0 <= y < real_1 /\ x = Nreal n + y.  
Proof.
  intros.
  destruct H.
  pose proof (min_upperbound_exists' _ H) as [n h].
  exists n.
  exists (x - Nreal n).
  split.
  destruct h.
  apply (real_le_plus_le (-Nreal n)) in H0.
  apply (real_lt_plus_lt (-Nreal n)) in H1.
  replace (- Nreal n + Nreal n) with real_0 in H0 by ring.
  replace (- Nreal n + x) with (x - Nreal n) in H0 by ring.
  replace (- Nreal n + x) with (x - Nreal n) in H1 by ring.
  replace (- Nreal n + Nreal (S n)) with real_1 in H1.
  split; auto.
  simpl.
  ring.
  ring.
  exists O.
  exists real_0.
  split; auto.
  split.
  right; auto.
  auto with real.
  rewrite <- H; simpl; ring.
Defined.
  
Definition is_fractional_part x y := real_0 <= x < real_1 /\ exists n, y = Nreal n + x.

Lemma fractional_part_is_unique x y z : is_fractional_part x z -> is_fractional_part y z -> x = y.
Proof.
  intros.
  destruct H as [a [b c]].
  destruct H0 as [p [q r]].
  rewrite c in r.
Admitted.


Lemma binary_expansion x : real_0 <= x <= real_1 ->
                           exists f : nat -> bool,
                           forall n,
                             (f n = true ->
                              exists y, prec 1 <= y /\ is_fractional_part y (x * pow2 n))
                             /\
                               (f n = false ->
                                exists y, y < prec 1 /\ is_fractional_part y (x * pow2 n)).

Proof.
  intros.
  
  apply (countable_choice bool (fun n b =>
                                  (b = true ->
                                   exists y, prec 1 <= y /\ is_fractional_part y (x * pow2 n))
                                  /\
                                    (b = false ->
                                     exists y, y < prec 1 /\ is_fractional_part y (x * pow2 n)))).
  intros.
  destruct H.
  Search Nreal.
  destruct (round_down (x * pow2 n)).
  pose proof (Nreal_Npow2_pos n).
  Search (_ * _ <= _ * _).
  pose proof (real_le_mult_pos_le _ _ _ H (or_introl  H1)).
  replace (x * real_0) with real_0 in H2 by ring.
  exact H2.
  destruct H1.
  destruct H1.
  destruct (lem (prec 1 <= x1)).
  exists true.
  split; auto.
  intros _ .
  exists x1.
  split; auto.
  split.
  auto.
  exists x0; auto.
  intro.
  contradict H4; apply Bool.diff_true_false.
  exists false.
  split.
  intro.
  contradict H4; apply Bool.diff_false_true.
  intros _ .
  exists x1.
  split.
  apply real_nle_ge; auto.
  split; auto.
  exists x0; auto.
Defined.

Lemma prec_le_real_1 : forall n, prec n <= real_1.
Proof.
  intro.
  induction n.
  simpl.
  right; auto.
  pose proof (prec_S n).
  left.
  apply (real_lt_le_lt _ _ _ H IHn).
Defined.  



Definition binary_to_sd b :=
  match b with
  | true => sdR
  | false => sdO
  end.

Lemma is_fast_limit_iff_is_fast_limit_p x f :
    is_fast_limit x f <-> is_fast_limit_p x f.
Proof.
  split.
  intro.
  intro.
  pose proof (H n).
  apply dist_le_prop in H0.
  exact H0.
  intro.
  intro.
  pose proof (H n).
  apply dist_le_prop in H0.
  exact H0.
Defined.

Lemma fast_limit_is_unique : forall x y f, is_fast_limit x f -> is_fast_limit y f -> x = y.
Proof.
  intros.
  apply is_fast_limit_iff_is_fast_limit_p in H, H0.
  apply (limit_is_unique _ _ _ H H0).
Defined.

Lemma tail_is_fast_limit x f n : is_fast_limit x f -> is_fast_limit x (fun m => f (n + m)%nat).
Proof.
  intros.
  intro.
  pose proof (H (n + n0)%nat).
  assert (n0 <= n+ n0)%nat by lia.
  apply (real_le_le_le _ _ _ H0 (prec_antitone_le _ _ H1)).
Defined.

Lemma S_is_fast_limit x f : is_fast_limit x f -> is_fast_limit x (fun m => f (S m)%nat).
Proof.
  intros.
  intro.
  pose proof (H (S n)%nat).
  assert (n <= S n)%nat by lia.
  apply (real_le_le_le _ _ _ H0 (prec_antitone_le _ _ H1)).
Defined.

Lemma sd_repr_cont_at_sd_zero_aux :
  forall x n, real_0 <= x <= prec (S n) -> exists f, x = sd_repr f /\ 
                                             sd_names_share_n_entries sd_zero f n.
Proof.
  intros.
  destruct H.
  pose proof (real_le_lt_lt _ _ _ H0 (prec_S_lt_real_1 _)) as hhh.
  assert (x <= real_1).
  left; auto.
  pose proof (binary_expansion x (conj H H1)) as [f h].
  exists (fun n => binary_to_sd (f n)).
  split.
  unfold sd_repr.
  destruct ((real_limit (sd_repr_p_sum (fun n0 : nat => binary_to_sd (f n0))))).
  simpl.
  assert (is_fast_limit x (sd_repr_p_sum (fun n0 : nat => binary_to_sd (f n0%nat)))).
  {
    clear i x0.
    assert (forall n,
               let An := (sd_repr_p_sum (fun n0 : nat => binary_to_sd (f n0)) n) in
               (exists k, An * pow2 (S n) = Nreal k) /\
               real_0 <= x - An < prec (S n)).
    {
      intro.
      induction n0.
      {
        simpl.
        split.
        case_eq (f O).
        intro.
        simpl.
        exists 1%nat.
        simpl.
        pose proof (prec_pow2_cancel 1%nat).
        rewrite real_mult_assoc.
        simpl in H3.
        rewrite H3.
        ring.
        simpl.
        intro.
        exists 0%nat.
        simpl.
        ring.
        case_eq (f O); simpl; intro.
        split.
        pose proof (h O) as [p _].
        pose proof (p H2); clear p h.
        destruct H3.
        destruct H3.
        destruct H4.
        fold (prec 1%nat).
        destruct H5.
        unfold pow2 in H5.
        simpl in H5.
        replace ( x * (real_1 + real_0)) with x in H5 by ring.
        pose proof (Nreal_nonneg x1).
        apply (real_le_plus_le x0) in H6.
        rewrite real_plus_comm in H5.
        rewrite <- H5 in H6.
        replace (x0 + real_0) with x0 in H6 by ring.
        pose proof (real_le_le_le _ _ _ H3 H6).
        apply (real_le_plus_le (-prec 1%nat)) in H7.
        replace (- prec 1 + prec 1) with real_0 in H7 by ring.
        replace (- prec 1 + x) with ( x - real_1 * prec 1) in H7 by ring.
        exact H7.
        fold (prec 1%nat).
        rewrite real_mult_unit.
        rewrite <- prec_1_plus_prec_1 in hhh.
        apply (real_lt_plus_lt (-prec 1)) in hhh.
        replace (- prec 1 + (prec 1 + prec 1)) with (prec 1) in hhh by ring.
        replace ( - prec 1 + x) with (x - prec 1) in hhh by ring.
        exact hhh.

        
        pose proof (h O) as [_ p].
        pose proof (p H2); clear p h.
        destruct H3.
        destruct H3.
        destruct H4.
        fold (prec 1%nat).
        destruct H5.
        unfold pow2 in H5.
        simpl in H5.
        replace ( x * (real_1 + real_0)) with x in H5 by ring.
        pose proof (Nreal_nonneg x1).
        rewrite H5 in hhh.
        destruct H4.
        apply (real_lt_plus_lt (-x0)) in hhh.
        replace (- x0 + (Nreal x1 + x0)) with (Nreal x1) in hhh by  ring.
        pose proof H4 as hh.
        apply (real_le_plus_le (-x0 + real_1)) in H4.
        replace (- x0 + real_1 + x0) with real_1 in H4 by ring.
        replace ( - x0 + real_1 + real_0) with (-x0 + real_1) in H4 by ring.
        pose proof (real_lt_le_lt _ _ _ hhh H4).
        assert (real_1 = Nreal 1).
        simpl; auto; ring.
        rewrite H9 in H8.
        apply Nreal_inv_monotone in H8.
        assert (x1 = 0%nat) by lia.
        rewrite H10 in H5.
        simpl in H5.
        rewrite H5.
        replace (real_0 + x0 - real_0 * prec 1) with x0 by ring.
        auto.
      }
      
      
      simpl.
      pose (A := (sd_repr_p_sum (fun n0 : nat => binary_to_sd (f (n0 )%nat)) n0)).
      fold A; fold A in IHn0.
      case_eq (f (S n0)).
      {
        (* when the binary entry was true *)
        intro.
        simpl.
        replace (prec n0 / real_2_neq_0 / real_2_neq_0 * real_1) with (prec (n0 + 2)).
        destruct (h (S n0))  as [p _ ].
        pose proof (p H2) as q; clear p.
        destruct q as [y [p q]].
        destruct IHn0.
        destruct H3.
        assert ( (exists k : nat, (A + prec (n0 + 2)) * pow2 (S (S n0)) = Nreal k)) as j.
        {
          exists (x0 + x0 + 1)%nat.
          replace ((A + prec (n0 + 2)) * pow2 (S (S n0))) with (A * pow2 (S (S n0)) +  prec (n0 + 2) * pow2 (S (S n0))) by ring.
          replace (S (S n0)) with (1 + S n0)%nat at 1 by lia.

          rewrite pow2_hom.
          replace ( A * (pow2 1 * pow2 (S n0)) ) with (A * pow2 (S n0) * pow2 1) by ring.
          rewrite H3.
          replace (S (S n0)) with (n0 + 2)%nat by lia.
          rewrite prec_pow2_cancel.
          unfold pow2.
          simpl.
          rewrite Nreal_hom.
          rewrite Nreal_hom.
          simpl.
          ring.
        }
        split; auto.
        destruct (lem (x < A + prec (S (S n0)))).
        (* contradiction *)
        {
          pose proof (real_lt_mult_pos_lt _ _ _ (pow2_pos (S n0)) H5).
          replace ( pow2 (S n0) * (A + prec (S (S n0))))
            with ( A * pow2 (S n0) +  pow2 (S n0) * prec (S (S n0))) in H6 by ring.
          rewrite H3 in H6.
          replace (S( S n0)) with (S n0 + 1)%nat in H6 by lia.
          rewrite prec_hom in H6.
          rewrite <- real_mult_assoc in H6.
          rewrite pow2_prec_cancel in H6.
          rewrite real_mult_unit in H6.
          assert (is_fractional_part (pow2 (S n0) * x - Nreal x0) (x * pow2 (S n0))).
          split.
          {
            split.
            destruct H4.
            apply (real_le_plus_le A) in H4.
            replace (A + (x - A)) with x in H4 by ring.
            replace ( A + real_0 ) with A in H4 by ring.
            pose proof (real_le_mult_pos_le _ _ _ (or_introl (pow2_pos (S n0))) H4).
            rewrite real_mult_comm in H8.
            rewrite H3 in H8.
            apply (real_le_plus_le (-Nreal x0)) in H8.
            replace ( - Nreal x0 + Nreal x0 ) with real_0 in H8 by ring.
            replace (- Nreal x0 + pow2 (S n0) * x) with (pow2 (S n0) * x - Nreal x0) in H8 by ring.
            exact H8.
            apply (real_lt_plus_lt (-Nreal x0)) in H6.
            replace ( - Nreal x0 + pow2 (S n0) * x) with (pow2 (S n0) * x - Nreal x0) in H6 by ring.
            replace (- Nreal x0 + (Nreal x0 + prec 1)) with (prec 1) in H6 by ring.
            apply (real_lt_le_lt _ _ _ H6 (prec_le_real_1 _)).
          }
          
          exists x0.
          ring.
          pose proof (fractional_part_is_unique _ _ _ q H7).
          clear H7 q.
          apply (real_lt_plus_lt (- Nreal x0)) in H6.
          replace (- Nreal x0 + pow2 (S n0) * x) with (pow2 (S n0) * x - Nreal x0) in H6 by ring.
          replace ( - Nreal x0 + (Nreal x0 + prec 1)) with (prec 1) in H6 by ring.
          rewrite <- H8 in H6.
          pose proof (real_le_lt_lt _ _ _ p H6).
          contradict H7; auto with real.
        }
        apply real_nge_le in H5.
        apply (real_le_plus_le (- A- prec (S (S n0)))) in H5.
        replace ( - A - prec (S (S n0)) + (A + prec (S (S n0)))) with real_0 in H5 by ring. 
        replace ( - A - prec (S (S n0)) + x) with  (x -  (A + prec (S (S n0)))) in H5 by ring.
        split.
        replace (n0 + 2)%nat with (S (S n0)) by lia.
        auto.
        clear H5.
        destruct H4.
        apply (real_lt_plus_lt (- prec (S (S n0)))) in H5.
        replace ( - prec (S (S n0)) + (x - A) ) with (x - (A + prec (S ( S n0))) ) in H5 by ring.
        rewrite <- (prec_twice (S n0)) in H5.
        replace (S n0 + 1)%nat with (S (S n0)) in H5 by lia.
        replace (- prec (S (S n0)) + (prec (S (S n0)) + prec (S (S n0)))) with
          (prec (S (S n0))) in H5 by ring.
        replace (n0 + 2)%nat with (S (S n0)) by lia.
        simpl in H5.
        simpl.
        exact H5.
        replace (n0 + 2)%nat with (S (S n0)) by lia.
        simpl.
        ring.
      }
      
      {
        (* when the binary entry was false *)
        intro.
        simpl.
        replace (A + prec n0 / real_2_neq_0 / real_2_neq_0 * real_0) with A by ring.
        destruct (h (S n0))  as [_ p].
        pose proof (p H2) as q; clear p.
        destruct q as [y [p q]].
        destruct IHn0.
        destruct H3.
        split.
        exists (x0 + x0)%nat.
        rewrite Nreal_hom.
        replace (pow2 (S (S n0))) with  (pow2 (S n0) * pow2 1).
        rewrite <- real_mult_assoc.
        rewrite H3.
        unfold pow2.
        simpl.
        ring.
        unfold pow2.
        simpl.        
        repeat rewrite Nreal_mult.
        simpl.
        ring.
        split; destruct H4; auto.
        destruct (lem (x -A < prec (S (S n0)))); auto.
        apply real_nge_le in H6.
        apply (real_le_plus_le A) in H6.
        pose proof (real_le_mult_pos_le _ _ _ (or_introl (pow2_pos (S n0))) H6).
        replace ( pow2 (S n0) * (A + prec (S (S n0))))
          with ( A * pow2 (S n0) +  pow2 (S n0) * prec (S (S n0))) in H7 by ring.
        rewrite H3 in H7.
        replace (S( S n0)) with (S n0 + 1)%nat in H7 by lia.
        rewrite prec_hom in H7.
        rewrite <- real_mult_assoc in H7.
        rewrite pow2_prec_cancel in H7.
        rewrite real_mult_unit in H7.
        replace ((A + (x - A))) with x in H7 by ring.
        rewrite real_mult_comm in H7.
        assert (is_fractional_part (pow2 (S n0) * x - Nreal x0) (x * pow2 (S n0))).
        split.
        {
            split.
            pose proof (real_le_mult_pos_le _ _ _ (or_introl (pow2_pos (S n0))) H4).
            replace ( pow2 (S n0) * real_0 ) with real_0 in H8 by ring.
            rewrite <- H3.
            replace (pow2 (S n0) * (x - A)) with (pow2 (S n0) * x - A * pow2 (S n0)) in H8 by ring.
            exact H8.
            rewrite <- H3.
            replace (pow2 (S n0) * x - A * pow2 (S n0)) with (pow2 (S n0) * (x - A)) by ring.
            pose proof (real_lt_mult_pos_lt _ _ _ ( (pow2_pos (S n0))) H5).
            rewrite pow2_prec_cancel in H8.
            exact H8.
        }
        exists x0.
        ring.
        pose proof (fractional_part_is_unique _ _ _ q H8).
        clear H8 q.
        apply (real_le_plus_le (- Nreal x0)) in H7.
        replace (- Nreal x0 + x * pow2 (S n0)) with (pow2 (S n0) * x - Nreal x0) in H7 by ring.
        replace ( - Nreal x0 + (Nreal x0 + prec 1)) with (prec 1) in H7 by ring.
        rewrite <- H9 in H7.
        pose proof (real_lt_le_lt _ _ _ p H7).
        contradict H7; auto with real.  
      }
    }
    intro.
    pose proof (H2 n0).
    simpl in H3.
    destruct H3.
    apply dist_le_prop.
    split.
    destruct H4.
    clear H5.
    pose proof (prec_pos n0).
    apply (real_lt_plus_lt (-prec n0)) in H5.
    replace (- prec n0 + real_0) with (- prec n0) in H5 by ring.
    replace (- prec n0 + prec n0) with real_0 in H5 by ring.
    left; apply (real_lt_le_lt _ _ _ H5 H4).
    destruct H4 as [_ H4].
    pose proof (prec_S n0).
    simpl in H5.    
    left; apply (real_lt_lt_lt _ _ _ H4 H5).
  }
  
  apply (fast_limit_is_unique _ _ _ H2 i).
  intro.
  intro.
  unfold sd_zero.
  pose proof (h m) as [p q].
  assert (f m = false).
  {
    assert (exists y : ^Real, y < prec 1 /\ is_fractional_part y (x * pow2 m)).
    pose proof (round_down (x * pow2 m)) as [k [r h1]].
    pose proof (Nreal_Npow2_pos m).
    pose proof (real_le_mult_pos_le _ _ _ H (or_introl  H3)).
    replace (x * real_0) with real_0 in H4 by ring.
    exact H4.
    exists r.
    destruct h1.
    pose proof (Nreal_Npow2_pos m).
    pose proof (real_le_mult_pos_le _ _ _ (or_introl  H5) H0).
    unfold pow2 in H4.
    replace ( Nreal (Npow2 m) * x) with (x *  Nreal (Npow2 m)) in H6 by ring.
    rewrite H4 in H6.
    rewrite real_mult_comm in H6.
    assert (m < S n)%nat by lia. 
    pose proof (prec_pow2_cancel_r _ _ H7) as hh.
    unfold pow2 in hh; rewrite hh in H6; clear hh H7.
    assert (2<=S n-m)%nat by lia.
    apply prec_antitone_le in H7.
    pose proof (real_le_le_le _ _ _ H6 H7).
    assert (1 < 2)%nat by lia.
    pose proof (real_le_lt_lt _ _ _ H8 (prec_monotone _ _ H9)).
    pose proof (real_le_plus_le r _ _ (Nreal_nonneg k)).
    replace (r + real_0) with r in H11 by ring.
    replace (r + Nreal k) with (Nreal k + r) in H11 by ring.
    pose proof (real_le_lt_lt _ _ _ H11 H10).
    split; auto.
    split.
    auto.
    exists k.
    auto.
    destruct (f m); auto.
    pose proof (p eq_refl).
    destruct H3 as [y [h1 h2]].
    destruct H4 as [z [h3 h4]].
    induction (fractional_part_is_unique _ _ _ h2 h4).
    pose proof (real_lt_le_lt _ _ _ h1 h3).
    contradict H3; auto with real.
  }
  rewrite H3; auto.
Defined.

Definition sd_repr_negative f (n : nat) :=
  match f n with
  | sdL => sdR | sdO => sdO | sdR => sdL
  end.

Lemma sd_repr_prop f x : x = sd_repr f <-> is_fast_limit x (sd_repr_p_sum f).
Proof.
  unfold sd_repr.
  destruct ((real_limit (sd_repr_p_sum f) (sd_repr_p_is_fast_cauchy f))).
  simpl.
  split; intro.
  induction H; auto.
  rewrite (fast_limit_is_unique _ _ _ i H); auto.
Defined.

Lemma sd_repr_negative_prop f x : x = sd_repr f -> -x = sd_repr (sd_repr_negative f).
Proof.
  intro.
  apply sd_repr_prop.
  apply sd_repr_prop in H.
  assert (forall n, sd_repr_p_sum f n = - sd_repr_p_sum (sd_repr_negative f) n).
  intro.
  induction n.
  simpl.
  unfold sd_repr_negative.
  destruct (f 0%nat); simpl; ring.
  simpl.
  rewrite IHn.
  unfold sd_repr_negative.
  destruct (f (S n)%nat); simpl; ring.
  intro.
  pose proof (H n).
  rewrite H0 in H1.
  rewrite <- real_metric_plus_inv_invariant.
  replace (- - x) with x by ring.
  auto.
Defined.

  
Lemma sd_repr_cont_at_sd_zero :
  forall x n, abs x <= prec (S n) -> exists f, x = sd_repr f /\ 
                                             sd_names_share_n_entries sd_zero f n.
Proof.
  intros.
  destruct (real_abs_cand _ _ H).
  destruct (lem (real_0 <= x)).
  apply (sd_repr_cont_at_sd_zero_aux _ _ (conj H2 H0)).
  apply real_nle_ge in H2.
  assert (real_0 <= -x <= prec (S n)).
  split.
  left.
  apply (real_lt_plus_lt (-x)) in H2.
  replace (- x + x) with real_0 in H2 by ring.
  replace (- x + real_0) with (-x) in H2 by ring.
  auto.
  auto.
  pose proof (sd_repr_cont_at_sd_zero_aux _ _ H3) as [f [p q]].
  exists (sd_repr_negative f).
  split.
  rewrite <- (sd_repr_negative_prop _ _ p).
  ring.
  intro.
  intro.
  pose proof (q m H4).
  unfold sd_repr_negative.
  rewrite <- H5.
  unfold sd_zero.
  auto.
Defined.

Definition sd_euclidean_repr d : (nat -> Vector.t sd d) -> @euclidean (RealAssumption.types) d.
Proof.
  intros.
  induction d.
  constructor.
  constructor.
  exact (sd_repr (fun n => fst (Vector.uncons (H n)))).
  exact (IHd (fun n => snd (Vector.uncons (H n)))).
Defined.

Definition sd_euclidean_zero d : nat -> Vector.t sd d.
Proof.
  intros.
  induction d.
  constructor.
  constructor.
  exact sdO.
  exact IHd.
Defined.

Lemma sd_euclidean_repr_cont_at_sd_zero d :
  forall x n, euclidean_max_norm x <= prec (S n) ->
              exists f, x = sd_euclidean_repr d f /\
                          forall m, (m < n)%nat -> sd_euclidean_zero d m =  f m.
Proof.
  induction d.
  intros.
  exists (fun n => Vector.nil _).
  simpl.
  split.
  apply dim_zero_destruct.
  auto.
  intros.
  pose proof (IHd (euclidean_tail  x) n).
  assert (euclidean_max_norm (euclidean_tail x) <= prec (S n) ).
  unfold euclidean_tail.
  destruct (dim_succ_destruct x).
  destruct s.
  rewrite e in H.
  simpl in H.
  apply real_max_le_snd_le in H.
  exact H.
  apply H0 in H1.
  clear H0.
  destruct H1 as [g [h1 h2]].
  unfold euclidean_tail in h1.
  destruct (dim_succ_destruct x).
  destruct s.
  rewrite e in H.
  simpl in H.
  pose proof (real_max_le_fst_le _ _ _ H) as h.
  apply real_max_le_snd_le in H.
  pose proof (sd_repr_cont_at_sd_zero _ _ h) as [f' [p q]].
  exists (fun n => Vector.cons _ (f' n) _ (g n)).
  split.
  simpl.
  rewrite e.
  rewrite h1.
  rewrite p.
  auto.
  intros.
  simpl.
  rewrite<- h2; auto.
  rewrite <- q; auto.
Defined.

Lemma sd_euclidean_zero_repr_euclidean_zero d : euclidean_zero d = sd_euclidean_repr d (sd_euclidean_zero d).
Proof.
  induction d.
  simpl.
  auto.
  simpl.
  pose proof sd_zero_repr_zero.
  unfold sd_zero in H.
  rewrite <- H.
  rewrite IHd.
  auto.
Defined.

Axiom continuity : forall {X} (f : (nat -> X) -> sierp) (x : (nat -> X)), sierp_up (f x) -> ^M {m | forall y, (forall n, (n < m)%nat -> x n = y n) -> sierp_up (f y)}.


Lemma continuity_sierp : forall {d} (f : euclidean d -> sierp) x, sierp_up (f x) -> ^M {n | forall y, euclidean_max_dist x y <= prec n -> sierp_up (f y) }.
Proof.
  intros.
  pose (F := fun g => f (euclidean_plus x (sd_euclidean_repr d g))).
  pose proof (continuity F).
  assert (sierp_up (F (sd_euclidean_zero d))).
  {
    unfold F.
    rewrite<- sd_euclidean_zero_repr_euclidean_zero.
    rewrite euclidean_plus_zero.
    exact H.
  }
  apply X in H0.
  clear X.
  apply (M_lift_dom {m : nat
         | forall y : nat -> Vector.t sd d,
           (forall n : nat, (n < m)%nat -> sd_euclidean_zero d n = y n) -> sierp_up (F y)}); auto.
  intro.
  clear H0.
  apply M_unit.
  destruct H1.
  exists (S x0).
  intros.
  rewrite euclidean_max_dist_sym in H0.
  unfold euclidean_max_dist in H0.
  apply sd_euclidean_repr_cont_at_sd_zero in H0.
  destruct H0.
  destruct H0.
  pose proof (s x1).
  pose proof (H2 H1).
  unfold F in H3.
  rewrite <- H0 in H3.
  replace (x + (y - x))%euclidean with y in H3.
  exact H3.
  {
    unfold euclidean_minus.
    rewrite euclidean_plus_comm.
    rewrite <- euclidean_plus_assoc.
    rewrite (euclidean_plus_comm _ x) at 1.
    pose proof (euclidean_plus_inv x).
    unfold euclidean_minus in H4.
    rewrite H4.
    rewrite euclidean_plus_zero.
    apply eq_refl.
  }
Defined.
