Require Import Real.

Definition Rsubset := Real -> Prop.
Definition complement : Rsubset -> Rsubset := fun P x => ~ P x.
Definition is_open : Rsubset -> Prop := fun P => forall x, P x -> exists n, forall y, dist x y < prec n -> P y.
Definition is_closed S := is_open (complement S).
Definition w_approx (P : Real -> Prop) (n : nat) (x : Real) : Prop
  := exists y, P y /\ dist x y <= prec n.

(* a predicate [P : Real -> Prop] is complete if for any converging seqeunce
   [f : nat -> Real] such that [w_approx P n (f n)] holds for all [n : nat],
   the limit point satisfies [P x]. For example, [Real \ {0}] is not complete. *)
Definition is_seq_closed (P : Real -> Prop) :=
  forall f : nat -> Real,
    is_fast_cauchy f -> (forall n, w_approx P n (f n)) -> (forall x, is_fast_limit x f -> P x).

Definition is_closed_is_seq_complete : forall P, is_closed P -> is_seq_closed P.
Proof.
  intros P H f c j a b.
  destruct (lem (P a)); auto.
  pose proof (H _ H0).
  destruct H1.
  
  pose proof (j (S (S x))).
  unfold w_approx in H2.
  destruct H2.
  destruct H2.
  pose proof (H1 x0).
  contradict H2.
  apply H4.
  pose proof (b (S (S x))).
  (* pose proof (proj2 (dist_le_prop a (f (S (S x))) (prec (S (S x)))) H2). *)
  pose proof (dist_tri a (f (S (S x))) x0).
  pose proof (Realle_le_plus_le _ _ _ _ H2 H3).
  apply (Realge_le) in H5.
  pose proof (Realle_le_le _ _ _ H5 H6).
  apply (Realle_lt_lt _ _ _ H7).
  assert ( prec (S (S x)) + prec (S (S x)) = prec (S x)).
  simpl.
  unfold Realdiv.
  replace (prec x * / Real2_neq_Real0 * / Real2_neq_Real0 +
           prec x * / Real2_neq_Real0 * / Real2_neq_Real0) with (prec x * (/ Real2_neq_Real0 * (Real1 + Real1) ) * / Real2_neq_Real0) by ring.
  rewrite Realmult_inv.
  ring_simplify.
  auto.
  rewrite H8.
  apply prec_S.
Defined.

