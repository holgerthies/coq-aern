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

Lemma euclidean_plus_comm : forall {n} (x y : euclidean n), euclidean_plus x y = euclidean_plus  y x.
Proof.
  intros.
  induction n.
  rewrite (dim_zero_destruct x), (dim_zero_destruct y); auto.
  destruct (dim_succ_destruct x) as [hx [tx ex]], (dim_succ_destruct y) as [hy [ty ey]].
  rewrite ex, ey.
  simpl.
  rewrite (IHn tx ty).
  replace (hx + hy) with (hy + hx) by ring.
  auto.
Qed.

Lemma euclidean_plus_assoc : forall {n} (x y z : euclidean n), euclidean_plus x (euclidean_plus y z) = euclidean_plus (euclidean_plus x y) z.
Proof.
  intros.
  induction n.
  rewrite (dim_zero_destruct x), (dim_zero_destruct y), (dim_zero_destruct z); auto.
  destruct (dim_succ_destruct x) as [hx [tx ex]], (dim_succ_destruct y) as [hy [ty ey]],
   (dim_succ_destruct z) as [hz [tz ez]].
  rewrite ex, ey, ez.
  simpl.
  rewrite (IHn tx ty tz).
  rewrite (Realplus_assoc).
  auto.
Qed.

  

  
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


Definition euclidean_max_norm {n : nat} (x : euclidean n) : Real.
Proof.
  induction x.
  exact Real0.
  destruct (Realmax (abs r) IHx) as [m h].
  exact m.
Defined.

Lemma euclidean_max_norm_abs : forall {n : nat} (x : euclidean n), euclidean_max_norm x = euclidean_max_norm (euclidean_opp x).
Proof.
  intros.
  induction n.
  rewrite (dim_zero_destruct x).
  simpl; auto.
  destruct (dim_succ_destruct x) as [hx [tx ex]].
  rewrite ex.
  pose proof (IHn tx).
  simpl.
  rewrite H.
  rewrite (abs_symm).
  auto.
Qed.

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



Lemma Realmax_aux : forall a b c d,  Realmaxf (a + b) (c + d) <= Realmaxf a c + Realmaxf b d.
Proof.
  intros.
  repeat rewrite Realmax_plus_eq.
  apply Realmax_le_le_le.
  apply Realmax_fst_le_le.
  apply Realmax_fst_le_le.
  right; auto.
  
  apply Realmax_snd_le_le.
  apply Realmax_snd_le_le.
  right; auto.
Qed.


Lemma euclidean_max_dist_tri : forall {n : nat} (x y z: euclidean n),
    euclidean_max_dist x z <= euclidean_max_dist x y + euclidean_max_dist y z.
Proof.
  intros.
  induction n.
  rewrite (dim_zero_destruct x), (dim_zero_destruct y), (dim_zero_destruct z).
  rewrite (proj2 (euclidean_max_dist_id nil nil) eq_refl). 
  right; ring.
  destruct (dim_succ_destruct x) as [hx [tx ex]], (dim_succ_destruct y) as [hy [ty ey]], (dim_succ_destruct z) as [hz [tz ez]].
  rewrite ex, ey, ez.
  repeat rewrite (euclidean_max_dist_cons).
  pose proof (IHn tx ty tz).
  pose proof (dist_tri hx hy hz).
  apply Realge_le in H0.
  pose proof (Realmax_compwise_le _  _ _ _ H0 H).
  apply (Realle_le_le _ _ _ H1 (Realmax_aux _ _ _ _ )).
Qed.
  
Lemma euclidean_max_dist_sym : forall {n : nat} (x y: euclidean n),
    euclidean_max_dist x y = euclidean_max_dist y x.
Proof.
  intros.
  unfold euclidean_max_dist.
  rewrite euclidean_max_norm_abs at 1.
  unfold euclidean_minus.
  induction n.
  rewrite (dim_zero_destruct x), (dim_zero_destruct y); simpl; auto.
  destruct (dim_succ_destruct x) as [hx [tx ex]], (dim_succ_destruct y) as [hy [ty ey]].
  rewrite ex, ey.
  simpl.
  rewrite <- (IHn tx ty).
  replace (- (hx + - hy)) with (hy + - hx) by ring.
  auto.
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
  apply (proj2 (is_fast_cauchy_iff_p _)).
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
  simpl in H0.
  
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
      cons (projP1 _ _ (Real_limit _ (euclidean_head_sequence_is_fast_cauchy _ H)))
           (projP1 _ _ (IHn _ (euclidean_tail_sequence_is_fast_cauchy _ H)))).

  intros m.
  destruct (Real_limit _ (euclidean_head_sequence_is_fast_cauchy _ H)),
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
  exact H0.
  exact H1.
Defined.

Lemma euclidean_limit_is_unique : forall {n : nat} (f : nat -> euclidean n) x y, euclidean_is_fast_limit x f -> euclidean_is_fast_limit y f -> x = y.
Proof.
  intros.
  induction n.
  rewrite (dim_zero_destruct x), (dim_zero_destruct y); auto.
  destruct (dim_succ_destruct x) as [hx [tx ex]], (dim_succ_destruct y) as [hy [ty ey]].
  rewrite ex, ey.
  assert (tx = ty).
  apply (IHn (euclidean_tail_sequence f)).
  intro k.
  pose proof (H k).
  destruct (dim_succ_destruct (f k)) as [hfk [tfk efk]].
  rewrite efk in H1.
  rewrite ex in H1.
  pose proof (euclidean_max_dist_cons tx tfk hx hfk).
  rewrite H2 in H1.
  clear H2.
  pose proof (Realmax_le_snd_le _ _ _ H1).
  unfold euclidean_tail_sequence.
  rewrite efk.
  simpl.
  exact H2.
  intro k.
  pose proof (H0 k).
  destruct (dim_succ_destruct (f k)) as [hfk [tfk efk]].
  rewrite efk in H1.
  rewrite ey in H1.
  pose proof (euclidean_max_dist_cons ty tfk hy hfk).
  rewrite H2 in H1.
  clear H2.
  pose proof (Realmax_le_snd_le _ _ _ H1).
  unfold euclidean_tail_sequence.
  rewrite efk.
  simpl.
  exact H2.
  rewrite H1.
  assert (hx = hy).
  clear H1.
  apply (limit_is_unique (euclidean_head_sequence f)).
  intro k.
  pose proof (H k).
  destruct (dim_succ_destruct (f k)) as [hfk [tfk efk]].
  rewrite efk in H1.
  rewrite ex in H1.
  pose proof (euclidean_max_dist_cons tx tfk hx hfk).
  rewrite H2 in H1.
  clear H2.
  pose proof (Realmax_le_fst_le _ _ _ H1).
  unfold euclidean_head_sequence.
  rewrite efk.
  simpl.
  exact (proj1 (dist_le_prop hx hfk (prec k)) H2).

  intro k.
  pose proof (H0 k).
  destruct (dim_succ_destruct (f k)) as [hfk [tfk efk]].
  rewrite efk in H1.
  rewrite ey in H1.
  pose proof (euclidean_max_dist_cons ty tfk hy hfk).
  rewrite H2 in H1.
  clear H2.
  pose proof (Realmax_le_fst_le _ _ _ H1).
  unfold euclidean_head_sequence.
  rewrite efk.
  simpl.
  exact (proj1 (dist_le_prop hy hfk (prec k)) H2).
  rewrite H2; auto.
Qed.


  
Lemma euclidean_limit_P : forall {n : nat} (P : euclidean n -> Prop),
    (exists! x, P x) -> (forall m, {e  | exists a, P a /\ euclidean_max_dist e a <= prec m}) -> {a | P a}.
Proof.
  intros.
  assert (euclidean_is_fast_cauchy (fun k => projP1 _ _ (H0 k))).
  intros l m.
  simpl.
  destruct (H0 l), (H0 m).
  simpl.
  destruct e, e0.
  destruct H1, H2.
  destruct H.
  destruct H.
  induction (H5 _ H1).
  induction (H5 _ H2).
  rewrite euclidean_max_dist_sym in H4.
  pose proof (Realle_le_plus_le _ _ _ _ H3 H4).
  pose proof (euclidean_max_dist_tri x x3 x0).
  apply (Realle_le_le _ _ _ H7 H6).
  exists (projP1 _ _  (euclidean_limit _ H1)).
  destruct H.
  assert ( (projP1 (euclidean n)
       (fun x0 : euclidean n =>
        euclidean_is_fast_limit x0
          (fun k : nat =>
           projP1 (euclidean n)
             (fun e : euclidean n =>
              exists a : euclidean n, P a /\ euclidean_max_dist e a <= prec k) 
             (H0 k)))
       (euclidean_limit
          (fun k : nat =>
           projP1 (euclidean n)
             (fun e : euclidean n =>
              exists a : euclidean n, P a /\ euclidean_max_dist e a <= prec k) 
             (H0 k)) H1))
           = x).
  destruct (
       (euclidean_limit
       (fun k : nat =>
        projP1 (euclidean n)
          (fun e : euclidean n =>
           exists a : euclidean n, P a /\ euclidean_max_dist e a <= prec k) 
          (H0 k)) H1)).
  simpl.
  apply (euclidean_limit_is_unique _ _ _ e).
  intro k.
  destruct (H0 k).
  simpl.
  destruct e0.
  destruct H2.
  destruct H.
  induction (H4 _ H2).
  rewrite (euclidean_max_dist_sym).
  exact H3.
  rewrite H2.
  destruct H.
  exact H.
Defined.


Lemma euclidean_mslimit_P : forall {n : nat} (P : euclidean n -> Prop),
    (exists! x, P x) -> (forall m, M {e  | exists a, P a /\ euclidean_max_dist e a <= prec m}) -> {a | P a}.
Proof.
  intros.
  apply singletonM.
  intros x y.
  destruct x, y.
  destruct H.
  destruct H.
  assert (x = x0).
  rewrite <- (H0 _ p), <- (H0 _ p0); auto.
  induction H1.
  assert (p = p0) by apply irrl.
  rewrite H1.
  auto.
  apply countableLiftM in X.
  apply (fun f => liftM _ _ f X). 
  intro.
  apply (euclidean_limit_P P H H0).
Defined.

Require Import MultiLimit.
Definition w_approx {n} (P : euclidean n -> Prop) (k : nat) (x : euclidean n) : Prop
  := exists y, P y /\ euclidean_max_dist x y <= prec k.

Definition closed_predicate {n} (P : euclidean n -> Prop) :=
  forall f : nat -> euclidean n,
    euclidean_is_fast_cauchy f -> (forall n, w_approx P n (f n)) -> (forall x, euclidean_is_fast_limit x f -> P x).
Lemma euclidean_consecutive_converging_fast_cauchy  : forall {d} (f : nat -> euclidean d),
    (forall n, euclidean_max_dist (f n) (f (S n)) <= prec (S n)) -> euclidean_is_fast_cauchy f.
Proof.
  intros.
  induction d.
  intros n k.
  rewrite (dim_zero_destruct (f n)), (dim_zero_destruct (f k)).
  rewrite (proj2 (euclidean_max_dist_id nil nil) eq_refl).
  pose proof (prec_pos n).
  pose proof (prec_pos k).
  left.
  pose proof (Reallt_lt_plus_lt _ _ _ _ H0 H1).
  ring_simplify in H2.
  auto.
  intros n k.
  pose proof (IHd (euclidean_tail_sequence f)).
  assert (euclidean_is_fast_cauchy (euclidean_tail_sequence f)).
  apply H0.
  intro.
  clear IHd.
  clear H0.
  pose proof (H n0).
  unfold euclidean_tail_sequence.
  destruct (dim_succ_destruct (f n0)) as [hfn [tfn efn]].
  destruct (dim_succ_destruct (f (S n0))) as [hfsn [tfsn efsn]].
  rewrite efn, efsn in H0.
  pose proof (euclidean_max_dist_cons tfn tfsn hfn hfsn).
  rewrite H1 in H0.
  apply (Realmax_le_snd_le) in H0.
  exact H0.
  pose proof (H1 n k).
  clear IHd H1 H0.
  assert (is_fast_cauchy (euclidean_head_sequence f)).
  apply consecutive_converging_fast_cauchy.
  intro.
  pose proof (H n0).
  unfold euclidean_head_sequence.
  destruct (dim_succ_destruct (f n0)) as [hfn [tfn efn]].
  destruct (dim_succ_destruct (f (S n0))) as [hfsn [tfsn efsn]].
  rewrite efn, efsn in H0.
  pose proof (euclidean_max_dist_cons tfn tfsn hfn hfsn).
  rewrite H1 in H0.
  apply (Realmax_le_fst_le) in H0.
  exact H0.
  pose proof (H0 n k).
  destruct (dim_succ_destruct (f n)) as [hfn [tfn efn]].
  destruct (dim_succ_destruct (f k)) as [hfk [tfk efk]].
  rewrite efn, efk.
  pose proof (euclidean_max_dist_cons tfn tfk hfn hfk).
  rewrite H3.
  unfold euclidean_tail_sequence in H2.
  rewrite efn, efk in H2.
  simpl in H2.
  replace (-prec n - prec k) with (- (prec n + prec k)) in H1 by ring.
  unfold euclidean_head_sequence in H1.
  rewrite efn, efk in H1.
  simpl in H1.
  exact (Realmax_le_le_le _ _ _ H1 H2).  
Qed.


Definition euclidean_mlimit_P {d} : forall P : euclidean d -> Prop,
    closed_predicate P ->
    M {x | w_approx P O x} ->
    (forall n x, w_approx P n x ->
                 M {y  | w_approx P (S n) y /\ euclidean_max_dist x y <= prec (S n)}) ->
    M {x | P x}. 
Proof.
  intros P c X f.
  assert ((forall n (x : {x | w_approx P n x}),
              M {y : { y | w_approx P (S n) y} | euclidean_max_dist (projP1 _ _ x) (projP1 _ _ y) <= prec  (S n)})).
  intros.
  destruct x.
  pose proof (f n x w).
  apply (liftM {y  | w_approx P (S n) y /\ euclidean_max_dist x y <= prec (S n)}).
  intro.
  destruct H.
  destruct a.
  exists (exist _ x0 H).
  simpl.
  exact H0.
  exact X0.
  pose proof (pathsM _ _ X X0).
  simpl in X1.
  apply (lift_domM {x | w_approx P 0 x}).
  intro.
  apply (liftM {f : forall n : nat, {x  | w_approx P n x}
               | forall m : nat,
                   euclidean_max_dist (projP1 _ (fun x  => w_approx P m x) (f m))
                        (projP1 _ (fun y  => w_approx P (S m) y) (f (S m))) <= prec (S m)}).
  intro.
  destruct H.
  destruct H0.
  simpl in r.
  assert (euclidean_is_fast_cauchy (fun n => projP1 _ _ (x0 n))).
  apply euclidean_consecutive_converging_fast_cauchy.
  exact r.
  pose proof (euclidean_limit _ H).
  destruct H0.
  exists x1.
  pose proof (c (fun n => projP1 _ _ (x0 n)) H).
  assert (forall n : nat, w_approx P n ((fun n0 : nat => projP1 _ (w_approx P n0) (x0 n0)) n)).
  intro.
  destruct (x0 n).
  simpl.
  exact w0.
  apply (H0 H1).
  
  exact e.
  exact X1.
  exact X.
Defined.


  
