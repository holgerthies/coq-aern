Require Import Real.
Require Import Minmax.

Inductive euclidean : nat -> Type :=
  nil :  euclidean O 
| cons : forall {n}, Real -> euclidean n -> euclidean (S n).


(* from Vector library (Library Coq.Vectors.VectorDef) *)
Definition case0 (P : euclidean O -> Type) (H:P nil) v:P v
  := match v with
     |nil => H
     |_ => fun devil => False_ind (@IDProp) devil 
     end.

Definition caseS (P : forall {n}, euclidean (S n) -> Type)
           (H : forall h {n} t, @P n (cons h  t)) {n} (v: euclidean (S n)) : P v
  := match v with
     | cons h t => H h t
     |_ => fun devil => False_ind (@IDProp) devil 
     end.

Definition caseS' {n : nat} (v : euclidean (S n))
  : forall (P : euclidean (S n) -> Type) (H : forall h t, P (cons h  t)), P v
  := match v with
     | cons h  t => fun P H => H h t
     | _ => fun devil => False_rect (@IDProp) devil
     end.

Definition rect2 (P:forall {n}, euclidean n -> euclidean n -> Type)
           (bas : P nil nil) (rect : forall {n v1 v2}, P v1 v2 ->
                                                       forall a b, P (cons a v1) (cons b v2))
  := fix rect2_fix {n} (v1 : euclidean n) : forall v2 : euclidean n, P v1 v2 :=
       match v1 with
       | nil => fun v2 => case0 _ bas v2
       | @cons n' h1 t1 =>
         fun v2 =>
        caseS' v2 (fun v2' => P (cons h1 t1) v2') (fun h2 t2 => rect (rect2_fix t1 t2) h1 h2)
       end.

(* destructors of vectors *)
Lemma dim_zero_destruct : forall (x : euclidean O), x = nil.
Proof.
  intros.
  rewrite (case0 (fun y => nil = y) eq_refl x); auto.
Defined.

Definition dim_succ_destruct :  forall {n} (x : euclidean (S n)), {a & {b | x = @cons n a b } }. 
Proof.
  intros.
  apply (caseS' x).
  intros.
  exists h.
  exists t.
  auto.
Defined.


(* metric space *)
Definition euclidean_max_norm {n : nat} (x : euclidean n) : Real.
Proof.
  induction x.
  exact Real0.
  destruct (Realmax (abs r) IHx) as [m h].
  exact m.
Defined.

Definition euclidean_zero (n : nat) : euclidean n.
Proof.
  induction n.
  exact nil.
  exact (cons Real0 IHn).
Defined.


Definition euclidean_plus {n : nat} (x y : euclidean n) : euclidean n.
Proof.
  apply (rect2 (fun n _ _ => euclidean n) nil).
  intros.
  exact (cons (a + b) H).
  exact x.
  exact y.
Defined.

Definition euclidean_opp {n : nat} (x : euclidean n) : euclidean n.
Proof.
  induction n.
  exact nil.
  pose proof (dim_succ_destruct x).
  destruct H.
  destruct s.
  exact (cons (-x0) (IHn x1)).
Defined.

Definition euclidean_minus {n : nat} (x y : euclidean n) : euclidean n
  := euclidean_plus x (euclidean_opp y).

Definition euclidean_max_dist {n : nat} (x y : euclidean n) : Real
  := euclidean_max_norm (euclidean_minus x y).

(* properties of the algebraic operations *)
Lemma euclidean_plus_inv : forall {n} (x : euclidean n), euclidean_minus x x = euclidean_zero n. 
Proof.
  intros.
  induction n.
  apply (dim_zero_destruct).
  destruct (dim_succ_destruct x).
  destruct s.
  pose proof (IHn x1).
  rewrite e.
  unfold euclidean_minus.
  simpl.
  replace (x0 +- x0) with Real0 by ring.
  apply lp.
  exact H.
Qed.


Lemma euclidean_max_dist_pos : forall {n : nat} (x y : euclidean n),
    euclidean_max_dist x y >= Real0.
Proof.
  intros.
  induction n.
  rewrite (dim_zero_destruct x), (dim_zero_destruct y); auto.
  unfold euclidean_max_dist.
  simpl.
  right; auto.
  destruct (dim_succ_destruct x) as [hx [tx ex]].
  destruct (dim_succ_destruct y) as [hy [ty ey]].
  rewrite ex.
  rewrite ey.
  pose proof (IHn tx ty).
  unfold euclidean_max_dist.
  unfold euclidean_max_norm.
  simpl.
  apply Realmax_fst_ge_ge. 
  destruct (abs_pos (hx + - hy)); auto.
  left; auto.
  right; auto.
Qed.

Lemma euclidean_max_dist_cons : forall {n : nat} (tx ty : euclidean n) x y,
    euclidean_max_dist (cons x tx) (cons y ty) =
    (projP1 _ _ (Realmax (dist x y) (euclidean_max_dist tx ty))).
Proof.
  intros.
  unfold euclidean_max_dist at 1.
  unfold euclidean_max_norm.
  simpl.
  unfold projP1.
  unfold dist.
  unfold Realminus.
  assert ((euclidean_rec (fun (n0 : nat) (_ : euclidean n0) => Real) Real0
          (fun (n0 : nat) (r : Real) (_ : euclidean n0) (IHx : Real) =>
             let (m, _) := Realmax (abs r) IHx in m) n (euclidean_plus tx (euclidean_opp ty)))
          =
          (euclidean_max_dist tx ty)).
  auto.
  rewrite H.
  auto.
Qed.

  
Lemma euclidean_max_dist_id : forall {n : nat} (x y : euclidean n),
    euclidean_max_dist x y = Real0 <-> x = y.
Proof.
  intros.
  split.
  intro.
  induction n.
  rewrite (dim_zero_destruct x), (dim_zero_destruct y); auto.
  destruct (dim_succ_destruct x) as [hx [tx ex]].
  destruct (dim_succ_destruct y) as [hy [ty ey]].
  rewrite ex.
  rewrite ey.
  assert (hx = hy).
  unfold euclidean_max_dist in H.
  unfold euclidean_max_norm in H.
  rewrite ex in H.
  rewrite ey in H.
  simpl in H.
  
  pose proof (Realmax_eq_fst_le _ _ _ H).
  pose proof (Realabs_le0_eq0 _ H0).
  apply (lp _ _ (fun k => k + hy)) in H1; ring_simplify in H1; auto.
  induction H0.
  apply lp.
  apply IHn.

  unfold euclidean_max_dist in H.
  unfold euclidean_max_norm in H.
  rewrite ex in H.
  rewrite ey in H.
  simpl in H.
  pose proof (Realmax_eq_snd_le _ _ _ H).
  pose proof (euclidean_max_dist_pos tx ty).
  apply Real_le_ge_eq.
  exact H0.
  exact H1.

  intro.
  induction H.
  induction n.
  rewrite (dim_zero_destruct x); auto.
  destruct (dim_succ_destruct x) as [hx [tx ex]].
  rewrite ex.
  rewrite (euclidean_max_dist_cons tx tx hx hx).
  rewrite (IHn tx).
  rewrite (proj2 (dist_zero hx hx) eq_refl).
  destruct ((Realmax Real0 Real0)).
  simpl.
  destruct w.
  destruct H0.
  exact (H0 eq_refl).
Qed.


(* euclidean space is complete *)
Definition euclidean_is_fast_cauchy {n : nat} (f : nat -> euclidean n) : Prop
  := forall n m, euclidean_max_dist (f n) (f m) <= prec n + prec m.

Definition euclidean_head_sequence {n : nat} (f : nat -> euclidean (S n)) : nat -> Real.
Proof.
  intros.
  pose proof (f H).
  destruct (dim_succ_destruct H0).
  exact x.
Defined.

Definition euclidean_tail_sequence {n : nat} (f : nat -> euclidean (S n)) : nat -> euclidean n.
Proof.
  intros.
  pose proof (f H).
  destruct (dim_succ_destruct H0).
  destruct s.
  exact x0.
Defined.


Definition euclidean_head_sequence_is_fast_cauchy {n : nat} (f : nat -> euclidean (S n)) :
euclidean_is_fast_cauchy f -> is_fast_cauchy (euclidean_head_sequence f). 
Proof.
  intro.
  intros m k.
  unfold euclidean_head_sequence.
  destruct (dim_succ_destruct (f m)).
  destruct (dim_succ_destruct (f k)).
  pose proof (H m k).
  destruct s.
  destruct s0.
  pose proof (euclidean_max_dist_cons x1 x2 x x0).
  rewrite e in H0.
  rewrite e0 in H0.
  rewrite H1 in H0.
  clear H1.
  replace (- prec m - prec k) with (- (prec m + prec k)) by ring.
  apply (proj1 (dist_le_prop x x0 (prec m + prec k))).
  simpl in H0.
  apply Realmax_le_fst_le in H0.
  exact H0.
Defined.

Definition euclidean_tail_sequence_is_fast_cauchy {n : nat} (f : nat -> euclidean (S n)) :
euclidean_is_fast_cauchy f -> euclidean_is_fast_cauchy (euclidean_tail_sequence f). 
Proof.
  intros.
  intros m k.
  unfold euclidean_tail_sequence.
  destruct (dim_succ_destruct (f m)).
  destruct (dim_succ_destruct (f k)).
  destruct s, s0.
  pose proof (H m k).
  pose proof (euclidean_max_dist_cons x1 x2 x x0).
  rewrite e, e0 in H0.
  rewrite H1 in H0.
  apply (Realmax_le_snd_le) in H0.
  exact H0.
Defined.

  
Definition euclidean_is_fast_limit {n : nat} (x : euclidean n) (f : nat -> euclidean n) : Prop
  := forall n,  euclidean_max_dist x  (f n) <= prec n.

Lemma euclidean_limit : forall {n : nat} (f : nat -> euclidean n),
    euclidean_is_fast_cauchy f -> {x : euclidean n | euclidean_is_fast_limit x f}.
Proof.
  intros.
  induction n.
  exists  nil.
  unfold euclidean_is_fast_limit.
  intro n.
  assert (f n = nil).
  apply dim_zero_destruct.
  rewrite H0.
  rewrite (proj2 (euclidean_max_dist_id nil nil) eq_refl).
  left; apply prec_pos.

  exists (
      cons (projP1 _ _ (C_limit _ (euclidean_head_sequence_is_fast_cauchy _ H)))
           (projP1 _ _ (IHn _ (euclidean_tail_sequence_is_fast_cauchy _ H)))).

  intros m.
  destruct (C_limit _ (euclidean_head_sequence_is_fast_cauchy _ H)),
  (IHn _ (euclidean_tail_sequence_is_fast_cauchy _ H)).
  simpl.
  pose proof (i m).
  pose proof (e m).
  unfold euclidean_head_sequence in H0.
  unfold euclidean_tail_sequence in H1.
  destruct (dim_succ_destruct (f m)).
  destruct s.
  rewrite e0.
  pose proof (euclidean_max_dist_cons x0 x2 x x1).
  rewrite H2.
  clear H2.
  apply Realmax_le_le_le.
  exact (proj2 (dist_le_prop x x1 (prec m)) H0).
  exact H1.
Defined.


