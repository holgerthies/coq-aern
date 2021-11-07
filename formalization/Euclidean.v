Require Import Real.
Require Import Minmax.
Require Import MultiLimit.


Section Euclidean.
  
  Generalizable Variables K M Real.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
          {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
          {M_MultivalueMonad : MultivalueMonad}
          {Real : Type}
          {SemiDecOrderedField_Real : SemiDecOrderedField Real}
          {ComplArchiSemiDecOrderedField_Real : ComplArchiSemiDecOrderedField}.

  (* ring structure on Real *)
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

  Definition euclidean_head {n : nat} : euclidean (S n) -> Real.
  Proof.
    intros.
    destruct (dim_succ_destruct X).
    exact x.
  Defined.

  Definition euclidean_tail {n : nat} : euclidean (S n) -> euclidean n.
  Proof.
    intros.
    destruct (dim_succ_destruct X).
    destruct s.
    exact x0.
  Defined.


  (* metric space *)


  Definition euclidean_zero (n : nat) : euclidean n.
  Proof.
    induction n.
    exact nil.
    exact (cons real_0 IHn).
  Defined.


  Definition euclidean_plus {n : nat} (x y : euclidean n) : euclidean n.
  Proof.
    apply (rect2 (fun n _ _ => euclidean n) nil).
    intros.
    exact (cons (a + b) X).
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
    rewrite (real_plus_assoc).
    auto.
  Qed.

  

  
  Definition euclidean_opp {n : nat} (x : euclidean n) : euclidean n.
  Proof.
    induction n.
    exact nil.
    pose proof (dim_succ_destruct x).
    destruct X.
    destruct s.
    exact (cons (-x0) (IHn x1)).
  Defined.

  Definition euclidean_minus {n : nat} (x y : euclidean n) : euclidean n
    := euclidean_plus x (euclidean_opp y).


  Definition euclidean_max_norm {n : nat} (x : euclidean n) : Real.
  Proof.
    induction x.
    exact real_0.
    exact (real_max (abs r) IHx). 
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
    replace (x0 +- x0) with real_0 by ring.
    apply lp.
    exact H.
  Qed.


  Lemma euclidean_max_dist_pos : forall {n : nat} (x y : euclidean n),
      euclidean_max_dist x y >= real_0.
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
    apply real_max_fst_ge_ge. 
    destruct (abs_pos (hx + - hy)); auto.
    left; auto.
    right; auto.
  Qed.

  Lemma euclidean_max_dist_cons : forall {n : nat} (tx ty : euclidean n) x y,
      euclidean_max_dist (cons x tx) (cons y ty) =
      real_max (dist x y) (euclidean_max_dist tx ty).
  Proof.
    intros.
    unfold euclidean_max_dist at 1.
    unfold euclidean_max_norm.
    simpl.
    unfold projP1.
    unfold dist.
    unfold real_minus.
    assert ((euclidean_rect (fun (n0 : nat) (_ : euclidean n0) => Real) real_0
       (fun (n0 : nat) (r : Real) (_ : euclidean n0) (IHx : Real) => real_max (abs r) IHx) n
       (euclidean_plus tx (euclidean_opp ty)))
            =
            (euclidean_max_dist tx ty)).
    auto.
    rewrite H.
    auto.
  Qed.

  
  Lemma euclidean_max_dist_id : forall {n : nat} (x y : euclidean n),
      euclidean_max_dist x y = real_0 <-> x = y.
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
    
    pose proof (real_max_eq_fst_le _ _ _ H).
    pose proof (real_abs_le0_eq0 _ H0).
    apply (lp _ _ (fun k => k + hy)) in H1; ring_simplify in H1; auto.
    induction H0.
    apply lp.
    apply IHn.

    unfold euclidean_max_dist in H.
    unfold euclidean_max_norm in H.
    rewrite ex in H.
    rewrite ey in H.
    simpl in H.
    pose proof (real_max_eq_snd_le _ _ _ H).
    pose proof (euclidean_max_dist_pos tx ty).
    apply real_le_ge_eq.
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
    destruct ((real_max_cand real_0 real_0)); auto.
  Qed.



  Lemma real_max_aux : forall a b c d : Real,  real_max (a + b) (c + d) <= real_max a c + real_max b d.
  Proof.
    intros.
    repeat rewrite real_max_plus_eq.
    apply real_max_le_le_le.
    apply real_max_fst_le_le.
    apply real_max_fst_le_le.
    right; auto.
    
    apply real_max_snd_le_le.
    apply real_max_snd_le_le.
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
    apply real_ge_le in H0.
    pose proof (real_max_compwise_le _  _ _ _ H0 H).
    apply (real_le_le_le _ _ _ H1 (real_max_aux _ _ _ _ )).
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
    destruct (dim_succ_destruct X).
    exact x.
  Defined.

  Definition euclidean_tail_sequence {n : nat} (f : nat -> euclidean (S n)) : nat -> euclidean n.
  Proof.
    intros.
    pose proof (f H).
    destruct (dim_succ_destruct X).
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
    apply real_max_le_fst_le in H0.
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
    apply (real_max_le_snd_le) in H0.
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
        cons (projP1 _ _ (real_limit _ (euclidean_head_sequence_is_fast_cauchy _ H)))
             (projP1 _ _ (IHn _ (euclidean_tail_sequence_is_fast_cauchy _ H)))).

    intros m.
    destruct (real_limit _ (euclidean_head_sequence_is_fast_cauchy _ H)),
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
    apply real_max_le_le_le.
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
    pose proof (real_max_le_snd_le _ _ _ H1).
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
    pose proof (real_max_le_snd_le _ _ _ H1).
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
    pose proof (real_max_le_fst_le _ _ _ H1).
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
    pose proof (real_max_le_fst_le _ _ _ H1).
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
    rename X into H0.
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
    pose proof (real_le_le_plus_le _ _ _ _ H3 H4).
    pose proof (euclidean_max_dist_tri x x3 x0).
    apply (real_le_le_le _ _ _ H7 H6).
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
    apply M_hprop_elim_f.
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
    apply M_countable_lift in X.
    apply (fun f => M_lift _ _ f X). 
    intro.
    apply (euclidean_limit_P P H X0).
  Defined.



  (* Subsets of Euclidean space *)
  Definition euclidean_complement {T} : (T -> Prop) -> (T -> Prop)   := fun P x => ~ P x.
  Definition euclidean_is_open {n} (P : euclidean n -> Prop) :  Prop
    :=  forall x, P x -> exists n, forall y, euclidean_max_dist x y < prec n -> P y.
  Definition euclidean_is_closed {n} (S : euclidean n -> Prop) := euclidean_is_open (euclidean_complement S).
  Definition euclidean_w_approx {n} (P : euclidean n -> Prop) (k : nat) (x : euclidean n) : Prop
    := exists y, P y /\ euclidean_max_dist x y <= prec k.

  Definition euclidean_is_seq_closed {n} (P : euclidean n -> Prop) :=
    forall f, 
      euclidean_is_fast_cauchy f -> (forall n, euclidean_w_approx P n (f n)) -> (forall x, euclidean_is_fast_limit x f -> P x).

  Definition euclidean_is_closed_is_seq_complete : forall {n} (P : euclidean n -> Prop), euclidean_is_closed P -> euclidean_is_seq_closed P.
  Proof.
    intros d P H f c j a b.
    destruct (lem (P a)); auto.
    pose proof (H _ H0).
    destruct H1.
    
    pose proof (j (S (S x))).
    unfold euclidean_w_approx in H2.
    destruct H2.
    destruct H2.
    pose proof (H1 x0).
    contradict H2.
    apply H4.
    pose proof (b (S (S x))).
    (* pose proof (proj2 (dist_le_prop a (f (S (S x))) (prec (S (S x)))) H2). *)
    pose proof (euclidean_max_dist_tri a (f (S (S x))) x0).
    pose proof (real_le_le_plus_le _ _ _ _ H2 H3).
    (* apply (real_ge_le) in H5. *)
    pose proof (real_le_le_le _ _ _ H5 H6).
    apply (real_le_lt_lt _ _ _ H7).
    assert ( prec (S (S x)) + prec (S (S x)) = prec (S x)).
    simpl.
    unfold real_div.
    replace (prec x * / real_2_neq_0 * / real_2_neq_0 +
             prec x * / real_2_neq_0 * / real_2_neq_0) with (prec x * (/ real_2_neq_0 * (real_1 + real_1) ) * / real_2_neq_0) by ring.
    rewrite real_mult_inv.
    ring_simplify.
    auto.
    rewrite H8.
    apply prec_S.
  Defined.



  (* multi limit of euclidean space *)
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
    pose proof (real_lt_lt_plus_lt _ _ _ _ H0 H1).
    rewrite real_plus_unit in H2.
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
    apply (real_max_le_snd_le) in H0.
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
    apply (real_max_le_fst_le) in H0.
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
    (* replace (-prec n - prec k) with (- (prec n + prec k)) in H1 by ring. *)
    unfold euclidean_head_sequence in H1.
    rewrite efn, efk in H1.
    simpl in H1.
    exact (real_max_le_le_le _ _ _ H1 H2).  
  Qed.


  Definition euclidean_mlimit_P {d} : forall P : euclidean d -> Prop,
      euclidean_is_seq_closed P ->
      M {x : euclidean d | euclidean_w_approx P O x} ->
      (forall n x, euclidean_w_approx P n x ->
                   M {y  | euclidean_w_approx P (S n) y /\ euclidean_max_dist x y <= prec (S n)}) ->
      M {x | P x}. 
  Proof.
    intros P c X f.
    assert ((forall n (x : {x | euclidean_w_approx P n x}),
                M {y : { y | euclidean_w_approx P (S n) y} | euclidean_max_dist (projP1 _ _ x) (projP1 _ _ y) <= prec  (S n)})).
    intros.
    destruct x.
    pose proof (f n x e).
    apply (M_lift {y  | euclidean_w_approx P (S n) y /\ euclidean_max_dist x y <= prec (S n)}).
    intro.
    rename X1 into H.
    destruct H.
    destruct a.
    exists (exist _ x0 H).
    simpl.
    exact H0.
    exact X0.
    pose proof (M_paths _ _ X X0).
    simpl in X1.
    apply (M_lift_dom {x | euclidean_w_approx P 0 x}).
    intro.
    apply (M_lift {f : forall n : nat, {x  | euclidean_w_approx P n x}
                 | forall m : nat,
                     euclidean_max_dist (projP1 _ (fun x  => euclidean_w_approx P m x) (f m))
                                        (projP1 _ (fun y  => euclidean_w_approx P (S m) y) (f (S m))) <= prec (S m)}).
    intro.
    rename X2 into H.
    rename X3 into H0.
    destruct H.
    destruct H0.
    simpl in r.
    assert (euclidean_is_fast_cauchy (fun n => projP1 _ _ (x0 n))).
    apply euclidean_consecutive_converging_fast_cauchy.
    exact r.
    pose proof (euclidean_limit _ H).
    destruct X2.
    exists x1.
    pose proof (c (fun n => projP1 _ _ (x0 n)) H).
    assert (forall n : nat, euclidean_w_approx P n ((fun n0 : nat => projP1 _ (euclidean_w_approx P n0) (x0 n0)) n)).
    intro.
    destruct (x0 n).
    simpl.
    exact e1.
    apply (H0 H1).
    
    exact e0.
    exact X1.
    exact X.
  Defined.

  Definition euclidean_mlimit_PQ {d} : forall P : euclidean d -> Prop, forall (Q : nat -> euclidean d -> Set), 
      euclidean_is_seq_closed P ->
      M {x : euclidean d & {_ : Q 0 x | euclidean_w_approx P O x} } ->
      (forall n x, euclidean_w_approx P n x -> Q n x -> 
                   M {y  & {_ : Q (S n) y | (euclidean_w_approx P (S n) y) /\ euclidean_max_dist x y <= prec (S n)}}) ->
      M {x | P x}. 
  Proof.
    intros P Q c X f.

    Check projT1.
    assert ((forall n (x : {x & {_:  Q n x | euclidean_w_approx P n x }}),
                M {y : { y  & { _ : Q (S n) y | euclidean_w_approx P (S n) y}}  | euclidean_max_dist (projT1 x) (projT1 y) <= prec  (S n)} )).
    - intros.
      destruct x.
      destruct s.
      pose proof (f n x e x0).
    apply (M_lift {y  & {_ : Q (S n) y | (euclidean_w_approx P (S n) y) /\ euclidean_max_dist x y <= prec (S n) }}).
    intro.
    rename X1 into H.
    destruct H.
    destruct s.
    destruct a.
    exists (existT _  x1 (exist _ x2 H)).
    simpl.
    exact H0.
    exact X0.
  - pose proof (M_paths _ _ X X0).
    simpl in X1.
    apply (M_lift_dom {x &  {_  : Q 0 x | euclidean_w_approx P 0 x}}).
    + intro.
      apply (M_lift {f : forall n : nat, {x & {_ : Q n x | euclidean_w_approx P n x}}
                 | forall m : nat,
                     euclidean_max_dist (projT1 (f m))
                                        (projT1 (f (S m))) <= prec (S m)}).
      intro.
      rename X2 into H.
      rename X3 into H0.
      destruct H.
      destruct H0.
      simpl in r.
      assert (euclidean_is_fast_cauchy (fun n => projT1 (x0 n))).
      apply euclidean_consecutive_converging_fast_cauchy.
      exact r.
      pose proof (euclidean_limit _ H).
      destruct X2.
      exists x1.
      pose proof (c (fun n => projT1 (x0 n)) H).
      apply H0.
      intro.
      destruct (x0 n).
      simpl.
      destruct s0.
      exact e0.
      exact e.
      exact X1.
   + exact X.
Defined.
End Euclidean.
