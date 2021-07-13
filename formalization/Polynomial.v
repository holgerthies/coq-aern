Require Import Real.
Require Import Euclidean.

Definition poly (n : nat) := {x : euclidean (S n) | euclidean_head x <> Real0 }.
Fixpoint npow (x : Real) (n : nat) : Real :=
  match n with
  | O => Real1
  | S m => x * (npow x m)
  end.

Lemma npow_pos : forall x, x > Real0 -> forall n, npow x n > Real0.
Proof.
  intros.
  induction n.
  simpl; apply Real1_gt_Real0.
  simpl.
  pose proof (Reallt_mult_r_pos_lt _ _ _ H IHn).
  ring_simplify in H0.
  exact H0.
Defined.
Lemma npow_ge0 : forall x, x >= Real0 -> forall n, npow x n >= Real0.
Proof.
  intros.
  induction n.
  simpl; left; apply Real1_gt_Real0.
  simpl.
  destruct H, IHn.
  pose proof (Reallt_mult_r_pos_lt _ _ _ H H0).
  ring_simplify in H1.
  left; auto.
  rewrite H0; right; ring.
  rewrite H; right; ring.
  rewrite H0; right; ring.
Defined.

Lemma NReal_pos : forall n, NReal (S n) > Real0.
Proof.
  intros.
  induction n.
  simpl; ring_simplify; apply Real1_gt_Real0.
  simpl.
  simpl in IHn.
  apply (Reallt_plus_lt Real1) in IHn.
  replace (Real1 + Real0) with Real1 in IHn by ring.
  exact (Reallt_lt_lt _ _ _ Real1_gt_Real0 IHn).
Defined.

Lemma NReal_ge0 : forall n, NReal (n) >= Real0.
Proof.
  intros.
  induction n.
  right; simpl; auto.
  simpl.
  apply (Realge_plus_ge Real1) in IHn.
  replace (Real1 + Real0) with Real1 in IHn by ring.
  left; exact (Reallt_le_lt _ _ _ Real1_gt_Real0 (Realge_le _ _ IHn) ).
Defined.


Definition poly_eval_pre {n} : euclidean (S n) -> Real -> Real.
Proof.
  intros p x.
  induction n.
  destruct (dim_succ_destruct p) as [hx [tx ex]].
  exact (hx * (npow x O)) .
  destruct (dim_succ_destruct p) as [hx [tx ex]].
  exact (hx * (npow x (S n)) + (IHn tx)).
Defined.

Definition poly_eval {n} : poly n -> Real -> Real.
Proof.
  intros p x.
  destruct p as [p _].
  exact (poly_eval_pre p x).
Defined.

Definition all_non_zero {n} : euclidean (S n) -> Prop.
Proof.
  intros.
  induction n.
  destruct (dim_succ_destruct H).
  exact (x <> Real0).
  destruct (dim_succ_destruct H).
  destruct s.
  exact ((x <> Real0) /\ IHn x0).
Defined.

Lemma all_non_zero_pos_norm : forall {n} (x : euclidean (S n)), all_non_zero x -> euclidean_max_norm x > Real0.
Proof.
  intros.
  induction n.
  destruct (dim_succ_destruct x).
  destruct s.
  rewrite e in H.
  
  induction (eq_sym (dim_zero_destruct x1)).
  simpl in H.
  rewrite e.
  simpl.
  pose proof (abs_pos x0).
  destruct H0.
  destruct (Minmax.Realmax (abs x0) Real0).
  destruct w.
  rewrite (H1 H0).
  exact H0.
  induction (H (proj1 (abs_zero x0) (eq_sym H0))).

  destruct (dim_succ_destruct x).
  destruct s.
  rewrite e in H.
  simpl in H.
  destruct H.
  pose proof (abs_pos x0).
  destruct H1.
  rewrite e; simpl.
  pose proof (Minmax.Realmax_fst_le_le (abs x0) (abs x0) (euclidean_max_norm x1)).
  assert (abs x0 <= abs x0) by (right; auto).
  apply (fun a => Reallt_le_lt _ _ _ a (H2 H3)).
  pose proof (abs_pos x0).
  destruct H4.
  exact H4.
  induction (H (proj1 (abs_zero x0) (eq_sym H4))).
  induction (H (proj1 (abs_zero x0) (eq_sym H1))).
Defined.

Lemma abs_distr_0_l : forall y, abs (Real0 * y) = abs Real0 * abs y.
Proof.
  intros.
  replace (Real0 * y) with Real0 by ring.
  rewrite (proj2 (abs_zero Real0) eq_refl).
  ring.
Defined.

Lemma abs_distr_0_r : forall y, abs (y * Real0) = abs y * abs Real0.
Proof.
  intros.
  rewrite (Realmult_comm).
  rewrite (Realmult_comm (abs y)).
  apply abs_distr_0_l.
Defined.

Lemma abs_prop_pos : forall x, x > Real0 -> abs x = x.
Proof.
  intros.
  unfold abs.
  destruct (abs_prop x).
  destruct a as [a [_ _]].
  exact (a H).
Defined.

Lemma abs_prop_neg : forall x, x < Real0 -> abs x = - x.
Proof.
  intros.
  unfold abs.
  destruct (abs_prop x).
  destruct a as [_ [_ a]].
  exact (a H).
Defined.


Lemma abs_distr : forall x y, abs (x * y) = abs x * abs y.
Proof.
  intros.
  destruct (Realtotal_order x Real0).
  destruct (Realtotal_order y Real0).
  assert (x * y > Real0).
  apply (Reallt_plus_lt (-x)) in H.
  ring_simplify in H.
  pose proof (Reallt_mult_pos_lt _ _ _ H H0).
  apply (Reallt_plus_lt (x * y)) in H1.
  ring_simplify in H1.
  exact H1.
  rewrite (abs_prop_neg x H), (abs_prop_neg y H0), (abs_prop_pos (x * y) H1); ring.
  destruct H0.
  rewrite H0.
  apply abs_distr_0_r.
  pose proof (Reallt_mult_pos_lt _ _ _ H0 H).
  ring_simplify in H1.
  rewrite Realmult_comm in H1.
  rewrite (abs_prop_neg x H), (abs_prop_pos y H0), (abs_prop_neg (x * y) H1); ring.
  destruct H.
  rewrite H.
  apply abs_distr_0_l.
  destruct (Realtotal_order y Real0).
  pose proof (Reallt_mult_pos_lt _ _ _ H H0).
  ring_simplify in H1.
  rewrite (abs_prop_pos x H), (abs_prop_neg y H0), (abs_prop_neg (x * y) H1); ring.
  destruct H0.
  rewrite H0.
  apply abs_distr_0_r.
  pose proof (Reallt_mult_pos_lt _ _ _ H H0).
  ring_simplify in H1.
  rewrite (abs_prop_pos x H), (abs_prop_pos y H0), (abs_prop_pos (x * y) H1); ring.
Qed.

Lemma abs_npow_distr : forall x n, abs (npow x n) = npow (abs x) n. 
Proof.
  intros.
  induction n.
  simpl.
  rewrite (abs_prop_pos _ Real1_gt_Real0); ring.
  simpl.
  rewrite abs_distr.
  rewrite IHn.
  auto.
Defined.

  
Require Import RealOrderTactic.
Require Import Minmax.


Definition all_zero {n} : euclidean (S n) -> Prop.
Proof.
  intros.
  induction n.
  destruct (dim_succ_destruct H).
  exact (x = Real0).
  destruct (dim_succ_destruct H).
  destruct s.
  exact ((x = Real0) /\ IHn x0).
Defined.



(* Lemma all_zero_zero_norm : forall {n} (x : euclidean (S n)), all_non_zero x -> euclidean_max_norm x > Real0. *)
(* Proof. *)
(*   intros. *)
(*   induction n. *)
(*   destruct (dim_succ_destruct x). *)
(*   destruct s. *)
(*   rewrite e in H. *)
  
(*   induction (eq_sym (dim_zero_destruct x1)). *)
(*   simpl in H. *)
(*   rewrite e. *)
(*   simpl. *)
(*   pose proof (abs_pos x0). *)
(*   destruct H0. *)
(*   destruct (Minmax.Realmax (abs x0) Real0). *)
(*   destruct w. *)
(*   rewrite (H1 H0). *)
(*   exact H0. *)
(*   induction (H (proj1 (abs_zero x0) (eq_sym H0))). *)

(*   destruct (dim_succ_destruct x). *)
(*   destruct s. *)
(*   rewrite e in H. *)
(*   simpl in H. *)
(*   destruct H. *)
(*   pose proof (abs_pos x0). *)
(*   destruct H1. *)
(*   rewrite e; simpl. *)
(*   pose proof (Minmax.Realmax_fst_le_le (abs x0) (abs x0) (euclidean_max_norm x1)). *)
(*   assert (abs x0 <= abs x0) by (right; auto). *)
(*   apply (fun a => Reallt_le_lt _ _ _ a (H2 H3)). *)
(*   pose proof (abs_pos x0). *)
(*   destruct H4. *)
(*   exact H4. *)
(*   induction (H (proj1 (abs_zero x0) (eq_sym H4))). *)
(*   induction (H (proj1 (abs_zero x0) (eq_sym H1))). *)
(* Defined. *)
Require Import PeanoNat.
Require Import Psatz.

Definition unwrap_initial {n} m: (m <= n)%nat -> euclidean n -> euclidean (n - m).
Proof.
  intros.
  induction m.
  replace (n - 0)%nat with n by lia.
  exact H0.
  assert (m <= n)%nat.
  lia.
  pose proof (IHm H1).
  assert (n - m = S (n - S m))%nat.
  lia.
  rewrite H3 in H2.
  destruct (dim_succ_destruct H2).
  destruct s.
  exact x0.
Defined.

Definition tail_fragment {n} m: (m <= n)%nat -> euclidean n -> euclidean m.  
Proof.
  intros.
  pose proof (@unwrap_initial n (n - m)).
  assert (n - m <= n) %nat.
  lia.
  replace (n - (n - m))%nat with m in H1 by lia.
  apply (H1 H2 H0).
Defined.

Lemma all_zero_eval_pre : forall {n} (p : euclidean (S n)), all_zero p -> forall x, poly_eval_pre p x = Real0.
Proof.
  intros.
  induction n.
  destruct (dim_succ_destruct p) as [hp [tp ep]].
  induction (eq_sym (dim_zero_destruct tp)).
  rewrite ep.
  simpl.
  rewrite ep in H.
  simpl in H.
  rewrite H; ring.
  destruct (dim_succ_destruct p) as [hp [tp ep]].
  rewrite ep; rewrite ep in H; simpl; simpl in H.
  destruct H.
  rewrite (IHn tp H0), H.
  ring.
Defined.

Lemma Realmax_id : forall x, Realmaxf x x = x.
Proof.
  intros.
  unfold Realmaxf.
  destruct (Realmax x x).
  destruct w as [a [b c]].
  rewrite <- (b eq_refl).
  simpl.
  auto.
Defined.

  
Lemma all_zero_euclidean_max_norm : forall {n} (p : euclidean (S n)), all_zero p -> euclidean_max_norm p = Real0.
Proof.
  intros n p H.
  induction n.
  destruct (dim_succ_destruct p) as [hp [tp ep]].
  induction (eq_sym (dim_zero_destruct tp)).
  rewrite ep.
  simpl.
  rewrite ep in H.
  simpl in H.
  rewrite H.
  rewrite (proj2 (abs_zero Real0) (eq_refl)).
  destruct (Realmax Real0 Real0).
  destruct w as [a [b c]].
  exact (b eq_refl).
  
  
  destruct (dim_succ_destruct p) as [hp [tp ep]].
  rewrite ep; rewrite ep in H; simpl; simpl in H.
  destruct H.
  rewrite (IHn tp H0), H.
  rewrite (proj2 (abs_zero Real0) (eq_refl)).
  destruct (Realmax Real0 Real0).
  destruct w as [a [b c]].
  exact (b eq_refl).
Defined.


Lemma Realmax_le_snd : forall a b, a <= b -> Realmaxf a b = b.
Proof.
  intros.
  unfold Realmaxf.
  destruct (Realmax a b).
  simpl.
  destruct w as [h1 [h2 h3]].
  destruct H.
  exact (h3 H).
  rewrite <- H; exact (h2 H).
Defined.

Lemma Realmax_le_fst : forall a b, b <= a -> Realmaxf a b = a.
Proof.
  intros.
  unfold Realmaxf.
  destruct (Realmax a b).
  simpl.
  destruct w as [h1 [h2 h3]].
  destruct H.
  exact (h1 H).
  exact (h2 (eq_sym H)).
Defined.

Lemma euclidean_max_norm_non_neg : forall {n} x, @euclidean_max_norm n x >= Real0.
Proof.
  intros.
  induction n.
  induction (eq_sym (dim_zero_destruct x)).
  simpl; right; auto.
  destruct (dim_succ_destruct x) as [hx [tx ex]].
  rewrite ex.
  simpl.
  apply Realle_ge, (Realmax_fst_le_le _ _ _ (abs_pos _)).
Defined.

Lemma ge0_ge0_plus_ge0 : forall x y, Real0 <= x -> Real0 <= y -> Real0 <= x + y.
Proof.
  intros.
  pose proof (Realle_le_plus_le _ _ _ _ H H0).
  rewrite Realplus_unit in H1.
  exact H1.
Defined.

Lemma ge0_ge0_mult_ge0 : forall x y, Real0 <= x -> Real0 <= y -> Real0 <= x * y.
Proof.
  intros.
  destruct H, H0.
  left.
  pose proof (Reallt_mult_pos_lt _ _ _ H H0).
  replace (x * Real0) with Real0 in H1 by ring. 
  exact H1.
  rewrite <- H0; right; ring.
  rewrite <- H; right; ring.
  rewrite <- H; right; ring.
Defined.

Definition next_non_zero : forall {d} (p : euclidean (S d)),
    ~ all_zero p ->
    exists m, exists q : euclidean (S m), exists h : (S m <= S d)%nat,
          euclidean_head q <> Real0 /\ (forall x, poly_eval_pre q x = poly_eval_pre p x) /\ euclidean_max_norm q = euclidean_max_norm p.
Proof.
  intros.
  induction d.
  destruct (dim_succ_destruct p) as [hp [tp ep]].
  induction (eq_sym (dim_zero_destruct tp)).
  rewrite ep in H.
  simpl in H.
  exists O.
  exists p.
  assert (j : (1 <= 1)%nat) by lia; exists j.
  rewrite ep.
  split; simpl.
  unfold euclidean_head.
  unfold dim_succ_destruct.
  simpl.
  exact H.
  split.
  intro.
  auto.
  auto.
  
  destruct (dim_succ_destruct p) as [hp [tp ep]].
  rewrite ep in H.
  simpl in H.
  destruct (lem (hp = Real0)) as [jj | jj].
  assert (~all_zero tp).
  intro.
  contradict H; split; auto.


  destruct (IHd _ H0) as [m [q [h [h1 [h2 h3]]]]].
  exists m.
  exists q.
  assert (S m <= S ( S d))%nat by lia.
  exists H1.
  split; auto.
  split.
  intro.
  rewrite (h2 x).
  rewrite ep.
  simpl.
  rewrite jj.
  ring.
  rewrite ep.
  simpl.
  rewrite jj.
  rewrite h3.

  pose proof (euclidean_max_norm_non_neg tp) as H2.
  
  rewrite (proj2 (abs_zero _) (@eq_refl _ Real0)).
  apply eq_sym, Realmax_le_snd, Realge_le, H2.
  
  
  exists (S d).
  exists p.
  assert (S (S d) <= S (S d))%nat by lia.
  exists H0.
  rewrite ep.
  unfold euclidean_head.
  unfold dim_succ_destruct.
  simpl.
  split; auto.
Defined.

(* Definition next_non_zero_max_norm : forall {d} (p : euclidean (S d)), *)
(*     ~ all_zero p -> *)
(*     exists m, exists q : euclidean (S m), exists h : (S m <= S d)%nat, *)
(*           euclidean_head q <> Real0 /\ euclidean_max_norm q = euclidean_max_norm p. *)
(* Proof. *)
(*   intros. *)
(*   induction d. *)
(*   destruct (dim_succ_destruct p) as [hp [tp ep]]. *)
(*   induction (eq_sym (dim_zero_destruct tp)). *)
(*   rewrite ep in H. *)
(*   simpl in H. *)
(*   exists O. *)
(*   exists p. *)
(*   assert (j : (1 <= 1)%nat) by lia; exists j. *)
(*   rewrite ep. *)
(*   split; simpl. *)
(*   unfold euclidean_head. *)
(*   unfold dim_succ_destruct. *)
(*   simpl. *)
(*   exact H. *)
(*   intro. *)
(*   auto. *)
  
(*   destruct (dim_succ_destruct p) as [hp [tp ep]]. *)
(*   rewrite ep in H. *)
(*   simpl in H. *)
(*   destruct (lem (hp = Real0)) as [jj | jj]. *)
(*   assert (~all_zero tp). *)
(*   intro. *)
(*   contradict H; split; auto. *)


(*   destruct (IHd _ H0) as [m [q [h [h1 h2]]]]. *)
(*   exists m. *)
(*   exists q. *)
(*   assert (S m <= S ( S d))%nat by lia. *)
(*   exists H1. *)
(*   split; auto. *)
(*   intro. *)
(*   rewrite (h2 x). *)
(*   rewrite ep. *)
(*   simpl. *)
(*   rewrite jj. *)
(*   ring. *)
  
(*   exists (S d). *)
(*   exists p. *)
(*   assert (S (S d) <= S (S d))%nat by lia. *)
(*   exists H0. *)
(*   rewrite ep. *)
(*   unfold euclidean_head. *)
(*   unfold dim_succ_destruct. *)
(*   simpl. *)
(*   split; auto. *)
(* Defined. *)



(* Lemma possibly_zero_upbd : forall {d} (p : euclidean (S d)), *)
(*     exists q : euclidean (S d), all_non_zero q /\ (forall x, abs (poly_eval_pre p x) <= abs (poly_eval_pre q x)).  *)
(* Proof. *)
(*   intros. *)
(*   induction d. *)
(*   destruct (dim_succ_destruct p) as [hp [tp ep]]. *)
(*   exists (cons (Realmaxf Real1 (abs hp)) nil). *)
(*   split. *)
(*   simpl. *)
(*   intro. *)
(*   pose proof (Realmax_eq_fst_le _ _ _ H). *)
(*   destruct H0. *)
(*   exact (Realgt_ngt _ _ (Real1_gt_Real0) H0). *)
(*   pose proof (Real1_gt_Real0). *)
(*   rewrite H0 in H1. *)
(*   exact (Realngt_triv _ H1). *)
(*   intro. *)
(*   rewrite ep. *)
(*   induction (eq_sym (dim_zero_destruct tp)). *)
(*   simpl. *)
(*   replace (_ * Real1) with hp by ring. *)
(*   replace (_ * Real1) with ( (Realmaxf Real1 (abs hp) )) by ring. *)
(*   admit. *)

  
(*   destruct (dim_succ_destruct p) as [hp [tp ep]]. *)
(*   rewrite ep. *)
(*   pose proof (IHd tp). *)
(*   destruct H. *)
(*   destruct H. *)
(*   destruct (Realtotal_order (poly_eval_pre x x0)). *)
(*   exists (cons ()) *)
  
(*   ring_simplify. *)

(*   rewrite ep. *)
(*   destruct (Realtotal_order hp Real0). *)
(*   exists ( *)
      
(*     x, all_non_zero p -> abs x > Real1 -> abs (poly_eval_pre p x) <= ((npow (abs x) d) * euclidean_max_norm p) * NReal (S d). *)

Lemma Realle_mult_pos_le: forall r r1 r2 : Real, Real0 <= r -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros.
  destruct H, H0.
  left; apply (Reallt_mult_pos_lt _ _ _ H H0).
  rewrite H0; right; auto.
  rewrite <- H; right; ring.
  rewrite <- H; right; ring.
Defined.

Lemma ge0_ge_mult_ge0_ge : forall a b c d, Real0 <= a -> Real0 <= c -> a <= b -> c <= d -> a * c <= b * d.
Proof.
  intros.
  pose proof (Realle_mult_pos_le _ _ _ H H2).
  apply (Realle_le_le _ _ _ H3).
  assert (Real0 <= d).
  apply (Realle_le_le _ _ _ H0 H2).
  pose proof (Realle_mult_pos_le _ _ _ H4 H1).
  replace (b * d) with (d * b) by ring.
  replace (a * d) with (d * a) by ring.
  exact H5.
Defined.

Lemma npow_ge1_monotone : forall a b c, a >= Real1 ->  (b <= c)%nat -> npow a b <= npow a c.
Proof.
  intros.
  induction H0.
  right; auto.
  simpl.
  assert (Real0 <= npow a m).
  apply Realge_le, npow_ge0.
  apply Realle_ge.
  left.
  apply Realge_le in H.
  exact (Reallt_le_lt _ _ _ Real1_gt_Real0 H).
  apply Realge_le in H.
  pose proof (Realle_mult_pos_le _ _ _ H1 H).
  ring_simplify in H2.
  rewrite Realmult_comm.
  exact (Realle_le_le _ _ _ IHle H2).
Defined.

Lemma NReal_monotone : forall a b, (a <= b)%nat -> NReal a <= NReal b.
Proof.
  intros.
  induction H.
  right; auto.
  apply (Realle_le_le _ _ _ IHle).
  simpl.
  left.
  pose proof (Reallt_plus_lt (NReal m) _ _ Real1_gt_Real0).
  replace (NReal m + Real0) with (NReal m) in H0 by ring.
  rewrite Realplus_comm.
  exact H0.
Defined.

  
Require Import Wf_nat.
Lemma leading_term_dominate_aux : forall {d} (p : euclidean (S d)) x, euclidean_head p <> Real0 -> abs x > Real1 -> abs (poly_eval_pre p x) <= ((npow (abs x) d) * euclidean_max_norm p) * NReal (S d).
Proof.
  intros d p x nz ord.
  induction (lt_wf d) as [n _ IH].
  induction n.
  destruct (dim_succ_destruct p) as [x0 [x1 e]].
  rewrite e; simpl.
  destruct (Minmax.Realmax (abs x0)).
  ring_simplify.
  replace (x0 * Real1) with x0 by ring.
  unfold euclidean_max_norm in w.
  induction (eq_sym (dim_zero_destruct x1)).
  simpl in w.
  unfold Minmax.W_M in w.
  destruct w.
  destruct H0.
  pose proof (abs_pos x0).
  destruct H2.  
  rewrite (H H2).
  right; auto.
  rewrite (H0 (eq_sym H2)).
  right; auto.

  
  destruct (dim_succ_destruct p) as [x0 [x1 e]].
  destruct (lem (all_zero x1)).
  rewrite e.
  simpl.
  assert (poly_eval_pre x1 x = Real0).
  apply all_zero_eval_pre, H.

  rewrite H0.
  assert (euclidean_max_norm x1 = Real0).
  apply all_zero_euclidean_max_norm, H.
  rewrite H1.
  replace (let (m, _) := Realmax (abs x0) Real0 in m) with (abs x0).
  replace (x0 * (x * npow x n) + Real0) with (x0 * (x * npow x n)) by ring.
  
  rewrite abs_distr.
  rewrite abs_distr.
  rewrite abs_npow_distr.
  add_both_side_by (- abs x0 * (abs x * npow (abs x) n)).
  apply ge0_ge0_plus_ge0.
  repeat apply ge0_ge0_mult_ge0; try apply abs_pos, npow_pos, NReal_pos.
  apply abs_pos.
  apply abs_pos.
  apply Realge_le, npow_ge0.
  apply Realle_ge, abs_pos.
  destruct n.
  right; unfold NReal; ring.
  left; apply NReal_pos.
  repeat apply ge0_ge0_mult_ge0.
  apply abs_pos.
  apply abs_pos.
  apply Realge_le, npow_ge0.
  apply Realle_ge, abs_pos.
  exact (eq_sym (Realmax_le_fst _ _ (abs_pos x0))).
  
  destruct (next_non_zero _ H) as [m [q [h1 [h2 [h3 h4]]]]].
  pose proof (h3 x).
  clear h3.
  assert (m < S n)%nat.
  lia.
  pose proof (IH m H1 q h2).
  rewrite H0 in H2.
  
  
  ring_simplify.
  
  rewrite e.
  simpl.
  rewrite h4 in H2.

  assert (P :abs (x0 * (x * npow x n)) <= abs x * npow (abs x) n * (let (m0, _) := Realmax (abs x0) (euclidean_max_norm x1) in m0)).
  rewrite abs_distr.
  rewrite abs_distr.
  rewrite abs_npow_distr.
  pose proof (Realmax_fst_le_le (abs x0) (abs x0) (euclidean_max_norm x1)).
  assert (abs x0 <= abs x0) by (right; auto).
  apply H3 in H4.
  replace ( abs x0 * (abs x * npow (abs x) n)) with ((abs x * npow (abs x) n) * abs x0) by ring.
  (* replace ( abs x * npow (abs x) n * (let (m0, _) := Realmax (abs x0) (euclidean_max_norm x1) in m0)) with ( (let (m0, _) := Realmax (abs x0) (euclidean_max_norm x1) in m0) * (abs x * npow (abs x) n)) by ring. *)
  
  apply  (fun y => Realle_mult_pos_le (abs x * npow (abs x) n) _ _ y H4).
  apply ge0_ge0_mult_ge0.
  apply abs_pos.
  apply Realge_le, npow_ge0.
  apply Realle_ge, abs_pos.
  
  assert (Q :abs (poly_eval_pre x1 x) <= abs x * npow (abs x) n * (let (m0, _) := Realmax (abs x0) (euclidean_max_norm x1) in m0) *
                                      ( (Real1 + NReal n))).

  apply (Realle_le_le _ _ _ H2).


  pose proof (Realmax_snd_le_le (euclidean_max_norm x1) (euclidean_max_norm x1) (abs x0)).
  assert ((euclidean_max_norm x1) <= (euclidean_max_norm x1)) by (right; auto).
  apply H3 in H4.
  

  replace (npow (abs x) m * euclidean_max_norm x1 * NReal (S m))  with
      (((npow (abs x) m * NReal (S m)) * euclidean_max_norm x1 * Real1)) by ring.
  replace (abs x * npow (abs x) n * (let (m0, _) := Realmax (abs x0) (euclidean_max_norm x1) in m0) *   (Real1 + NReal n)) with
      (npow (abs x) n *
  (Real1 + NReal n)* (let (m0, _) := Realmax (abs x0) (euclidean_max_norm x1) in m0)  * abs x ) by ring.

  repeat apply ge0_ge_mult_ge0_ge.
  repeat apply ge0_ge0_mult_ge0.
  apply Realge_le, npow_ge0.
  apply Realle_ge, abs_pos.
  apply Realge_le, NReal_ge0.
  apply Realge_le, euclidean_max_norm_non_neg.
  left; apply Real1_gt_Real0.
  repeat apply ge0_ge0_mult_ge0.
  apply Realge_le, npow_ge0.
  apply Realle_ge, abs_pos.
  apply Realge_le, NReal_ge0.
  apply Realge_le, euclidean_max_norm_non_neg.
  apply Realge_le, npow_ge0.
  apply Realle_ge, abs_pos.
  apply Realge_le, NReal_ge0.
  
  replace (Real1 + NReal n) with (NReal (S n)) by (simpl; auto).
  apply npow_ge1_monotone.
  left; apply ord.
  lia.
  replace (Real1 + NReal n) with (NReal (S n)) by (simpl; auto).
  apply NReal_monotone.
  lia.
  apply (Realmax_snd_le_le (euclidean_max_norm x1) (euclidean_max_norm x1) (abs x0)).
  right; auto.
  left; apply ord.


  pose proof (Realle_le_plus_le _ _ _ _ P Q) as PQ.
  pose proof (Realle_le_le _ _ _ (Realge_le _ _ (abs_tri _ _)) PQ).
  apply (Realle_le_le _ _ _ H3).
  right; ring.

Defined.

Definition leading_coef {n} (x : poly n) := euclidean_head (projP1 _ _ x).
Definition coef_max_norm {d} (x : poly d) : Real.
Proof.
  destruct x.
  exact (euclidean_max_norm x).
Defined.

Lemma leading_term_domainate : forall {d} (p : poly d) x,
    abs x > Real1 -> abs (poly_eval p x) <=
                     ((npow (abs x) d) * coef_max_norm p) * NReal (S d).
                                                           
Proof.
  intros.
  unfold poly_eval.
  unfold coef_max_norm.
  destruct p.
  apply leading_term_dominate_aux. 
  exact n.
  exact H.
Defined.



Require Import PeanoNat.

Definition odd_poly {n} (x : poly n) := Even.odd n.
Definition pos_poly {n} (x : poly n) := Real0 < leading_coef x.
Definition neg_poly {n} (x : poly n) := leading_coef x < Real0.

Lemma poly_pos_bound : forall {n} (p : poly n), odd_poly p ->  pos_poly p -> exists x, forall y, y > x -> poly_eval p y > Real0.
Proof.
  



