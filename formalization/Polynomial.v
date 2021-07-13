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
Definition non_zero_upbd : forall {d} (p : euclidean (S d)) x, all_non_zero p -> abs x > Real1 -> abs (poly_eval_pre p x) <= ((npow (abs x) d) * euclidean_max_norm p) * NReal (S d).
Proof.
  intros d p x nz ord.
  induction d.
  destruct (dim_succ_destruct p).
  destruct s.
  rewrite e.
  simpl.
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

  destruct (dim_succ_destruct p) as [hp [tp ep]].
  rewrite ep.
  assert
    (abs (poly_eval_pre (cons hp tp) x) <= abs (hp * npow x (S d)) + abs (poly_eval_pre tp x)).
  apply Realge_le.
  simpl.
  pose proof (abs_tri  (hp * npow  x (S d)) (poly_eval_pre tp x)).
  
  simpl.
  simpl in H.
  exact H.
  (* assert *)
  (*   (times (npow (abs x) (S d) * euclidean_max_norm (cons hp tp)) (S (S d)) = *)
  (*    times ((npow (abs x) (S d)) * (Minmax.Realmaxf (abs hp) (euclidean_max_norm tp))) (S (S d))). *)

  (* admit. *)

  assert (abs (poly_eval_pre tp x) <= (npow (abs x) (S d) * Minmax.Realmaxf (abs hp) (euclidean_max_norm tp)) * (NReal (S d))).
  assert (nz1 : all_non_zero tp).
  rewrite ep in nz.
  simpl in nz.
  destruct nz as [_ nz].
  exact nz.
  pose proof (IHd tp nz1).
  
  apply (Realle_le_le _ _ _ H0).
  assert (Minmax.Realmaxf (abs hp) (euclidean_max_norm tp) >= euclidean_max_norm tp).
  apply Realle_ge.
  apply Minmax.Realmax_snd_le_le.
  right; auto.
  apply Realge_le in H1.
  destruct H1.
  assert ((npow (abs x) d) * (NReal (S d)) > Real0).
  apply Reallt_pos_mult_pos_pos.
  apply npow_pos.
  apply (Reallt_lt_lt _ _ _ Real1_gt_Real0 ord).
  apply NReal_pos.

  
  pose proof (Reallt_mult_r_pos_lt _ _ _ H2 H1).
  
  replace (npow (abs x) d * euclidean_max_norm tp * NReal (S d)) with (euclidean_max_norm tp * (npow (abs x) d * NReal (S d))) by ring.
  
  
  left.
  apply (Reallt_lt_lt _ _ _ H3).
  assert (Minmax.Realmaxf (abs hp) (euclidean_max_norm tp) * (npow (abs x) d * NReal (S d)) > Real0).
  apply Reallt_pos_mult_pos_pos.
  pose proof (Minmax.Realmax_fst_le_le (abs hp) (abs hp) (euclidean_max_norm tp)). 
  assert (abs hp <= abs hp) by (right; auto).
  pose proof (H4 H5).
  assert (Real0 < abs hp).
  pose proof (abs_pos hp).
  destruct H7.
  exact H7.
  unfold all_non_zero in nz.
  rewrite ep, <- (proj1 (abs_zero _) (eq_sym H7)) in nz.
  simpl in nz.
  destruct nz.
  induction (H8 eq_refl).
  exact (Reallt_le_lt _ _ _ H7 H6).
  apply Reallt_pos_mult_pos_pos.
  apply npow_pos.
  apply (Reallt_lt_lt _ _ _ Real1_gt_Real0 ord).
  apply NReal_pos.
  
  
  pose proof (Reallt_mult_r_pos_lt _ _ _  H4 ord).
  ring_simplify in H5.
  replace (npow (abs x) (S d)) with ((npow (abs x) d) * abs x).

  ring_simplify.
  exact H5.
  simpl.
  ring.


  rewrite <- H1.
  replace (npow (abs x) (S d)) with ((abs x) * npow (abs x) d) by (simpl; ring).
  assert (npow (abs x) d * euclidean_max_norm tp * NReal (S d) > Real0).
  apply Reallt_pos_mult_pos_pos.
  apply Reallt_pos_mult_pos_pos.
  apply npow_pos.
  apply (Reallt_lt_lt _ _ _ Real1_gt_Real0 ord).
  apply (all_non_zero_pos_norm _ nz1).
  apply NReal_pos.
  pose proof (Reallt_mult_r_pos_lt _ _ _  H2 ord).
  rewrite (Realmult_unit) in H3.
  ring_simplify in H3.
  ring_simplify.
  left; exact H3.


  assert (abs (hp * npow x (S d)) <= (npow (abs x) (S d) * Minmax.Realmaxf (abs hp) (euclidean_max_norm tp))).
  rewrite (abs_distr).
  rewrite abs_npow_distr.
  pose proof (Minmax.Realmax_fst_le_le (abs hp)  (abs hp) (euclidean_max_norm tp)).
  assert (abs hp <= abs hp) by (right; auto).
  apply H1 in H2.
  destruct H2.
  assert (npow (abs x) (S d) > Real0).
  apply npow_pos.
  apply (Reallt_lt_lt _ _ _ Real1_gt_Real0 ord).
  pose proof (Reallt_mult_r_pos_lt _ _ _  H3 H2).
  left.
  replace ( npow (abs x) (S d) * Minmax.Realmaxf (abs hp) (euclidean_max_norm tp)) with
      (Minmax.Realmaxf (abs hp) (euclidean_max_norm tp) * npow (abs x) (S d)) by ring.
  exact H4.
  rewrite <- H2.
  right; ring.

  
  pose proof (Realle_le_plus_le _ _ _ _ H1 H0).
  pose proof (Realle_le_le _ _ _ H H2).
  
  apply (Realle_le_le _ _ _ H3).
  assert (euclidean_max_norm (cons hp tp) = Minmax.Realmaxf (abs hp) (euclidean_max_norm tp)).
  simpl.
  auto.
  rewrite H4.

  simpl.
  right; ring.
Qed.
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
Admitted.

Lemma all_zero_euclidean_max_norm : forall {n} (p : euclidean (S n)), all_zero p -> euclidean_max_norm p = Real0.
Proof.
Admitted.


Lemma Realmax_le_snd : forall a b, a <= b -> Realmaxf a b = b.
Proof.
Admitted.

Lemma Realmax_le_fst : forall a b, b <= a -> Realmaxf a b = a.
Proof.
Admitted.


Lemma euclidean_max_norm_non_neg : forall {n} x, @euclidean_max_norm n x >= Real0.
Proof.
Admitted.

Lemma ge0_ge0_plus_ge0 : forall x y, Real0 <= x -> Real0 <= y -> Real0 <= x + y.
Proof.
Admitted.

Lemma ge0_ge0_mult_ge0 : forall x y, Real0 <= x -> Real0 <= y -> Real0 <= x * y.
Proof.
Admitted.



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

Require Import Wf_nat.
Goal forall {d} (p : euclidean (S d)) x, euclidean_head p <> Real0 -> abs x > Real1 -> abs (poly_eval_pre p x) <= ((npow (abs x) d) * euclidean_max_norm p) * NReal (S d).
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
  admit.

  assert (Q :abs (poly_eval_pre x1 x) <= abs x * npow (abs x) n * (let (m0, _) := Realmax (abs x0) (euclidean_max_norm x1) in m0) *
                                      ( (Real1 + NReal n))).

  admit.

  pose proof (Realle_le_plus_le _ _ _ _ P Q) as PQ.
  pose proof (Realle_le_le _ _ _ (Realge_le _ _ (abs_tri _ _)) PQ).
  apply (Realle_le_le _ _ _ H3).
  right; ring.

  Qed.
 
  
  
  
  assert ( abs x0 <=  (let (m0, _) := Realmax (abs x0) (euclidean_max_norm x1) in m0)).
  admit.
  assert (euclidean_max_norm x1 <= (let (m0, _) := Realmax (abs x0) (euclidean_max_norm x1) in m0)).
  admit.
  assert (


  
    

  
  
  
  rewrite <- (H0).
  
  rewrite<- (h4).
  
  
  assert
    (abs (poly_eval_pre (cons hp tp) x) <= abs (hp * npow x (S d)) + abs (poly_eval_pre tp x)).
  apply Realge_le.
  simpl.
  pose proof (abs_tri  (hp * npow  x (S d)) (poly_eval_pre tp x)).
  
  simpl.
  simpl in H.
  exact H.
  (* assert *)
  (*   (times (npow (abs x) (S d) * euclidean_max_norm (cons hp tp)) (S (S d)) = *)
  (*    times ((npow (abs x) (S d)) * (Minmax.Realmaxf (abs hp) (euclidean_max_norm tp))) (S (S d))). *)

  (* admit. *)


  

  destruct (lem (all_zero p)).
  
  
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

  destruct (dim_succ_destruct p) as [hp [tp ep]].
  rewrite ep.
  assert
    (abs (poly_eval_pre (cons hp tp) x) <= abs (hp * npow x (S d)) + abs (poly_eval_pre tp x)).
  apply Realge_le.
  simpl.
  pose proof (abs_tri  (hp * npow  x (S d)) (poly_eval_pre tp x)).
  
  simpl.
  simpl in H.
  exact H.
  (* assert *)
  (*   (times (npow (abs x) (S d) * euclidean_max_norm (cons hp tp)) (S (S d)) = *)
  (*    times ((npow (abs x) (S d)) * (Minmax.Realmaxf (abs hp) (euclidean_max_norm tp))) (S (S d))). *)

  (* admit. *)

  assert (abs (poly_eval_pre tp x) <= (npow (abs x) (S d) * Minmax.Realmaxf (abs hp) (euclidean_max_norm tp)) * (NReal (S d))).
  assert (nz1 : all_non_zero tp).
  rewrite ep in nz.
  simpl in nz.
  destruct nz as [_ nz].
  exact nz.
  pose proof (IHd tp nz1).
  
  apply (Realle_le_le _ _ _ H0).
  assert (Minmax.Realmaxf (abs hp) (euclidean_max_norm tp) >= euclidean_max_norm tp).
  apply Realle_ge.
  apply Minmax.Realmax_snd_le_le.
  right; auto.
  apply Realge_le in H1.
  destruct H1.
  assert ((npow (abs x) d) * (NReal (S d)) > Real0).
  apply Reallt_pos_mult_pos_pos.
  apply npow_pos.
  apply (Reallt_lt_lt _ _ _ Real1_gt_Real0 ord).
  apply NReal_pos.

  
  pose proof (Reallt_mult_r_pos_lt _ _ _ H2 H1).
  
  replace (npow (abs x) d * euclidean_max_norm tp * NReal (S d)) with (euclidean_max_norm tp * (npow (abs x) d * NReal (S d))) by ring.
  
  
  left.
  apply (Reallt_lt_lt _ _ _ H3).
  assert (Minmax.Realmaxf (abs hp) (euclidean_max_norm tp) * (npow (abs x) d * NReal (S d)) > Real0).
  apply Reallt_pos_mult_pos_pos.
  pose proof (Minmax.Realmax_fst_le_le (abs hp) (abs hp) (euclidean_max_norm tp)). 
  assert (abs hp <= abs hp) by (right; auto).
  pose proof (H4 H5).
  assert (Real0 < abs hp).
  pose proof (abs_pos hp).
  destruct H7.
  exact H7.
  unfold all_non_zero in nz.
  rewrite ep, <- (proj1 (abs_zero _) (eq_sym H7)) in nz.
  simpl in nz.
  destruct nz.
  induction (H8 eq_refl).
  exact (Reallt_le_lt _ _ _ H7 H6).
  apply Reallt_pos_mult_pos_pos.
  apply npow_pos.
  apply (Reallt_lt_lt _ _ _ Real1_gt_Real0 ord).
  apply NReal_pos.
  
  
  pose proof (Reallt_mult_r_pos_lt _ _ _  H4 ord).
  ring_simplify in H5.
  replace (npow (abs x) (S d)) with ((npow (abs x) d) * abs x).

  ring_simplify.
  exact H5.
  simpl.
  ring.


  rewrite <- H1.
  replace (npow (abs x) (S d)) with ((abs x) * npow (abs x) d) by (simpl; ring).
  assert (npow (abs x) d * euclidean_max_norm tp * NReal (S d) > Real0).
  apply Reallt_pos_mult_pos_pos.
  apply Reallt_pos_mult_pos_pos.
  apply npow_pos.
  apply (Reallt_lt_lt _ _ _ Real1_gt_Real0 ord).
  apply (all_non_zero_pos_norm _ nz1).
  apply NReal_pos.
  pose proof (Reallt_mult_r_pos_lt _ _ _  H2 ord).
  rewrite (Realmult_unit) in H3.
  ring_simplify in H3.
  ring_simplify.
  left; exact H3.


  assert (abs (hp * npow x (S d)) <= (npow (abs x) (S d) * Minmax.Realmaxf (abs hp) (euclidean_max_norm tp))).
  rewrite (abs_distr).
  rewrite abs_npow_distr.
  pose proof (Minmax.Realmax_fst_le_le (abs hp)  (abs hp) (euclidean_max_norm tp)).
  assert (abs hp <= abs hp) by (right; auto).
  apply H1 in H2.
  destruct H2.
  assert (npow (abs x) (S d) > Real0).
  apply npow_pos.
  apply (Reallt_lt_lt _ _ _ Real1_gt_Real0 ord).
  pose proof (Reallt_mult_r_pos_lt _ _ _  H3 H2).
  left.
  replace ( npow (abs x) (S d) * Minmax.Realmaxf (abs hp) (euclidean_max_norm tp)) with
      (Minmax.Realmaxf (abs hp) (euclidean_max_norm tp) * npow (abs x) (S d)) by ring.
  exact H4.
  rewrite <- H2.
  right; ring.

  
  pose proof (Realle_le_plus_le _ _ _ _ H1 H0).
  pose proof (Realle_le_le _ _ _ H H2).
  
  apply (Realle_le_le _ _ _ H3).
  assert (euclidean_max_norm (cons hp tp) = Minmax.Realmaxf (abs hp) (euclidean_max_norm tp)).
  simpl.
  auto.
  rewrite H4.

  simpl.
  right; ring.
Qed.

 
  
Require Import PeanoNat.

Definition leading_coef {n} (x : poly n) := euclidean_head (projP1 _ _ x).
Definition odd_poly {n} (x : poly n) := Even.odd n.
Definition pos_poly {n} (x : poly n) := Real0 < leading_coef x.
Definition neg_poly {n} (x : poly n) := leading_coef x < Real0.

Lemma poly_pos_bound : forall {n} (p : poly n), odd_poly p ->  pos_poly p -> exists x, forall y, y > x -> poly_eval p y > Real0.
Proof.
  intros.
  



Definition test := cons Real1 (cons Real2 (cons (Real1 + Real1 + Real1) nil)).
Definition testt : poly 2.
Proof.
  exists test.
  compute.
  intro.
  apply Real1_neq_Real0.
  exact H.
Defined.




Print (poly_eval testt (Real1 + Real1)).
