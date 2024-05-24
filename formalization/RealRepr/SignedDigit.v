(* WIP file by Sewon:
   This file provides various results on signed digit representation
   and use it to derive real number's continuity principle 
 *)
Require Import Lia.
Require Import Real Euclidean List Minmax Classical.Subsets Sierpinski Testsearch Dyadic.
Require Import RealAssumption.

From CAern.Analysis Require Import MultiLimit.
From CAern.Classical Require Import Analysis.

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

Lemma sd_repr_cont_at_sd_zero :
  forall x n, abs x <= prec n -> exists f, x = sd_repr f /\ 
                                             sd_names_share_n_entries f sd_zero n.
Proof.
Admitted.

Axiom continuity : forall {X} (f : (nat -> X) -> sierp) (x : (nat -> X)), sierp_up (f x) -> ^M {m | forall y, (forall n, (n <= m)%nat -> x n = y n) -> sierp_up (f y)}.


Lemma continuity_sierp : forall {d} (f : euclidean d -> sierp) x, sierp_up (f x) -> ^M {n | forall y, euclidean_max_dist x y < prec n -> sierp_up (f y) }.
Proof.
  Admitted.
