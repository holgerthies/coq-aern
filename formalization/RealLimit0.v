Require Import Base.
Require Import Monad.
Require Import ClassicalMonads.
Require Import Nabla.
Require Import Kleene.
Require Import MultivalueMonad.
Require Import RealAxioms.
Require Import RealRing.
Require Import RealOrder.
Require Export RealOrderTactic.

Require Import Psatz.

(* This file proves that Real is order complete in classical sense *)

Section RealLimit0.
Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).

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



  
  Lemma limit_only_if_fast_cauchy : forall f (x : Real), is_fast_limit_p x f -> is_fast_cauchy_p f.
  Proof.
    intros f x H n m.
    pose proof (H n).
    pose proof (H m).
    destruct H0, H1.
    split.
    pose proof (real_le_le_plus_le _ _ _ _ H2 H1).
    apply (real_le_plus_le (-x + f n - prec n)) in H4.
    ring_simplify in H4.
    exact H4.
    pose proof (real_le_le_plus_le _ _ _ _ H0 H3).
    apply (real_le_plus_le (f n + prec n - x)) in H4.
    ring_simplify in H4.
    exact H4.
  Qed.
    
  (*  *)
  Definition is_W_limit_p (x : Real) (f : nat -> Real) :=
    forall n, exists N, forall m, (N <= m)%nat ->  - prec n <= x - f m <= prec n.

  Definition is_W_cauchy_p (f : nat -> Real) :=
    forall n, exists N, forall m k, (N <= m)%nat -> (N <= k)%nat -> - prec n <= f m - f k <= prec n.

  Lemma W_limit_p_aux_1 :
    forall (f : nat -> Real),
      is_W_cauchy_p f ->
      exists h : nat -> nat, 
        forall n m k,  (h n <= m)%nat -> (h n <= k)%nat -> -prec n <= f m - f k <= prec n. 
  Proof.
    intros.
    apply (countable_choice nat (fun N FN => forall m k, (FN <= m)%nat -> (FN <= k)%nat -> -prec N <= f m - f k <= prec N)).
    intros.
    exact (H n).
  Defined.
    
  Lemma W_limit_p :
    forall (f : nat -> Real), is_W_cauchy_p f -> exists x, is_W_limit_p x f.
  Proof.
    intros.
    destruct (W_limit_p_aux_1 f H) as [g p].

    pose proof (real_limit_p (fun n => f ( g n))).

    assert ( is_fast_cauchy_p (fun n : nat => f ( g n))).
    + intros n m .
      assert True by auto.
      assert (g n < g m \/ g m <= g n)%nat by lia.
      destruct H1.    
    ++
      pose proof (p n ( g n) ( g m)).
      assert  (g n <= g n)%nat by lia; assert (g n <= g m)%nat by lia.
      pose proof (H2 H3 H4).
      split.
      destruct H5.
      left.
      apply (fun a => real_lt_le_lt _ _ _ a  H5).
      apply (real_lt_add_r (prec n + prec m)).
      replace ( - prec n - prec m + (prec n + prec m)) with real_0 by ring.
      replace (- prec n + (prec n + prec m)) with (prec m) by ring.
      apply prec_pos.
      destruct H5.
      left.
      apply (real_le_lt_lt _ _ _ H6).
      apply (real_lt_add_r (-prec n)).
      replace
        (prec n + - prec n) with real_0 by ring.
      replace (prec n + prec m + - prec n) with (prec m) by ring.
      apply prec_pos.
    ++
      pose proof (p m ( g n) ( g m)).
      assert  (g m <= g n)%nat by lia; assert (g m <= g m)%nat by lia.
      pose proof (H2 H3 H4).
      split.
      destruct H5.
      left.
      apply (fun a => real_lt_le_lt _ _ _ a  H5).
      apply (real_lt_add_r (prec n + prec m)).
      replace (- prec n - prec m + (prec n + prec m)) with real_0 by ring.
      replace ( - prec m + (prec n + prec m)) with (prec n) by ring.
      apply prec_pos.
      destruct H5.
      left.
      apply (real_le_lt_lt _ _ _ H6).
      apply (real_lt_add_r (-prec m)).
      replace ( prec m + - prec m) with real_0 by ring.
      replace (prec n + prec m + - prec m) with (prec n) by ring.
      apply prec_pos.
    +
      rename H0 into H1.
      rename X into H0.
      apply H0 in H1.
      clear H0.

      destruct (H1).
      exists x.
      intros n.
      exists (g (n + 1)%nat).
      intros.
      pose proof (i (n + 1)%nat).
      simpl in H2.
      pose proof (p (n + 1)%nat (g (n + 1)%nat) m).
      assert (g (n + 1) <= g (n + 1))%nat by lia; assert (g (n + 1) <= m)%nat by lia.
      pose proof (H3 H4 H5).
      clear H3 H4 H5.
      destruct H2, H6.
      split.
      pose proof (real_le_le_plus_le _ _ _ _ H2 H4).
      replace ( - prec (n + 1) + - prec (n + 1)) with (- (prec (n + 1) + prec (n+1))) in H6 by ring.
      rewrite prec_twice in H6.
      replace (x - f (g (n + 1)%nat) + (f (g (n + 1)%nat) - f m)) with (x - f m) in H6 by ring.
      exact H6.

      pose proof (real_le_le_plus_le _ _ _ _ H3 H5).
      replace (x - f (g (n + 1)%nat) + (f (g (n + 1)%nat) - f m)) with (x - f m) in H6 by ring.
      rewrite prec_twice in H6.
      exact H6.
  Defined.
  


  
  Definition W_is_non_empty (P : ^Real -> Prop) := exists z, P z.
  Definition W_is_upper_bound  (P : Real -> Prop) (u : Real ) := forall z : Real, P z -> z <= u.
  Definition W_is_strict_upper_bound  (P : Real -> Prop) (u : Real ) := forall z : Real, P z -> z < u.
  Definition W_is_bounded_above (P : Real -> Prop) := exists u, W_is_upper_bound P u.
  Definition W_is_strictly_bounded_above (P : Real -> Prop) := exists u, W_is_strict_upper_bound P u.
  
  (* Definition W_upbd (P : Real -> Prop) := exists u, W_upb P u. *)
  Definition W_is_sup  (P : Real-> Prop) (s : Real) := W_is_upper_bound P s /\ (forall s', W_is_upper_bound P s' -> s <= s').
   
  Lemma W_complete_aux :
    forall P : Real -> Prop,
      W_is_non_empty P ->  W_is_strictly_bounded_above P ->
      exists w, w > real_0 /\ exists f : nat -> Real,
          (forall n, ~ W_is_strict_upper_bound P (f n) /\ W_is_strict_upper_bound P (f n + w * prec n)). 
  Proof.
    intros.
    destruct H.
    destruct H0.
    exists (x0 - x).
    split.
    pose proof (H0  _ H).
    apply (real_lt_plus_lt (-x)) in H1.
    replace (-x + x) with real_0 in H1 by ring.
    replace (-x + x0) with (x0 - x) in H1 by ring.
    exact H1.
    apply (countable_choice Real (fun n y => ~ W_is_strict_upper_bound P y /\ W_is_strict_upper_bound P (y + (x0 - x) * prec n))).
    intro.
    induction n.
    exists x.
    split; auto.
    intro.
    exact (real_nlt_triv  _ (H1 _ H)).
    
    simpl prec.
    replace ((x + (x0 - x) * real_1)) with x0 by ring.
    exact H0.

    destruct IHn.
    destruct H1.
    pose (m := (x1 + (x0 - x) * prec (S n))).
    destruct (lem (W_is_strict_upper_bound P m)).
    
    exists x1.
    split; auto.

    exists m.
    split; auto.    
    assert ( (m + (x0 - x) * prec (S n)) = (x1 + (x0 - x) * prec n)).
    unfold m.
    replace ( x1 + (x0 - x) * prec (S n) + (x0 - x) * prec (S n))
      with  ( x1 + (x0 - x) * (prec (S n) +  prec (S n))) by ring.
    replace (S n) with (n + 1)%nat by lia.
    rewrite (prec_twice n).
    ring.
    rewrite H4.
    exact H2.
  Defined.

  Lemma W_log : forall x : Real, x > real_0 -> exists n, x * prec n < real_1.
  Proof.
    intros.
    pose proof (real_Archimedean  (/ (dg0  H))).
    pose proof (real_pos_inv_pos2  _ H).
    apply H0 in H1.
    destruct H1.
    exists x0.
    apply (real_lt_mult_pos_lt x _ _ H) in H1.
    replace ( x * /dg0 H) with (/dg0 H * x) in H1 by ring.
    rewrite (real_mult_inv) in H1.
    exact H1.
  Qed.
  
  
  Lemma prec_monotone : forall n m, (n < m)%nat -> prec m < prec n.
  Proof.
    intros.
    induction H.
    apply prec_S.
    pose proof (prec_S m).
    apply (real_lt_lt_lt _ _ _ H0 IHle).
  Qed.
   
  Lemma W_complete_aux_2 : forall (P : Real -> Prop) x,
      ~ W_is_strict_upper_bound P x -> exists y, x <= y /\ P y.
  Proof.
    intros.
    unfold W_is_strict_upper_bound in H.
    destruct (lem (exists y : Real, x <= y /\ P y)); auto.
    contradict H.
    intros.
    destruct (lem (z < x)); auto.
    contradict H0.
    exists z.
    split; auto.
    destruct (real_total_order x z).
    left; exact H0.
    destruct H0.
    right; exact H0.
    contradict (H1 H0).
  Qed.

  Lemma real_le_lt_plus_lt : forall a b c d : Real, a <= b -> c < d -> a + c < b + d.
  Proof.
    intros.
    destruct H.
    apply (real_lt_lt_plus_lt _ _ _ _ H H0).
    rewrite H.
    apply (real_lt_plus_lt b  _ _ H0).
  Qed.
  
  
    
  Theorem W_complete : forall P : Real -> Prop,
      W_is_non_empty P ->  W_is_bounded_above P ->
       exists z, W_is_sup P z.
  Proof.
    intros P H H0.
    destruct H0.
    destruct (lem (W_is_strict_upper_bound P x)).
    assert (W_is_strictly_bounded_above P) by (exists x; auto). 
    pose proof (W_complete_aux P H H2) as [w [pw [f h]]].
    pose proof (W_limit_p f).
    assert (is_W_cauchy_p f ).
    intros n.
    +                           (* prove is Cauchy *)
      
    destruct (W_log _ pw) as [i j].
    exists (i + n + 1)%nat.
    intros.
    (* destruct (lem (f m - f n > prec n \/ f n - f m > prec n)). *)
    (* destruct H6. *)
    pose proof (h m) as [pm nm].
    pose proof (h k) as [pk nk].
    pose proof (W_complete_aux_2 P _ pm) as [q [qq qqq] ].
    pose proof (nk _ qqq).
    
    pose proof (W_complete_aux_2 P _ pk) as [p [pp ppp]].
    pose proof (nm _ ppp).
    pose proof (@real_le_lt_plus_lt _ _ _ _ qq H6). 
    pose proof (@real_le_lt_plus_lt _ _ _ _ pp H7). 
    apply (real_lt_plus_lt (- q - f k)) in H8.
    apply (real_lt_plus_lt (- p - f k - w * prec m)) in H9.
    ring_simplify in H8.
    ring_simplify in H9.
    replace (f m - f k) with (- f k + f m) by ring.
    split; left.
    apply (fun a => real_lt_lt_lt _ _ _ a H9).
    apply (real_lt_add_r (prec n + w * prec m)). 
    ring_simplify.
    apply (real_lt_mult_pos_lt (prec n) _ _ (prec_pos _)) in j.
    ring_simplify in j.
    apply (fun a => real_lt_lt_lt _ _ _ a j).
    replace (prec n * w * prec i) with (w * (prec n  * prec i)) by ring.
    apply (real_lt_mult_pos_lt w _ _ pw).
    rewrite <- prec_hom.
    apply prec_monotone.
    lia.

    apply (real_lt_lt_lt _ _ _ H8).
    apply (real_lt_mult_pos_lt (prec n) _ _ (prec_pos _)) in j.
    ring_simplify in j.
    apply (fun a => real_lt_lt_lt _ _ _ a j).
    replace (prec n * w * prec i) with (w * (prec n  * prec i)) by ring.
    apply (real_lt_mult_pos_lt w _ _ pw).
    rewrite <- prec_hom.
    apply prec_monotone.
    lia.

    +
    destruct (H3 H4).
    exists x0.
    split.
    intros z p.
    destruct (real_total_order z x0).
    left; auto.
    destruct H6.
    right; auto.
    destruct (padding _ _ H6) as [eps [pos e]].
    destruct (real_Archimedean _ pos) as [k pk].

    destruct (W_log _ pw) as [i j].
    

    destruct (H5 (k + 1 )%nat) as [N g].

    pose proof (g (N + k + 2 + i)%nat).
    assert (N <= N + k  + 2 + i)%nat by lia.
    apply H7 in H8.
    clear H7.
    pose proof (h (N + k  + 2 + i)%nat) as [_ hh].
    assert (f (N + k  + 2 + i)%nat + w * prec (N + k  + 2 + i) < z).
    rewrite e.
    rewrite prec_hom.
    pose proof (real_lt_mult_pos_lt (prec (N + k + 2 )) _ _ (prec_pos (N + k + 2 )) j ).
    apply (real_lt_plus_lt (f (N + k  + 2 + i)%nat)) in H7.
    replace ( f (N + k  + 2 + i)%nat + prec (N  + k + 2 ) * (w * prec i)) with ( f (N + k  + 2 + i)%nat + w * (prec (N + k + 2 ) * prec i)) in H7 by ring.
    apply (real_lt_lt_lt _ _ _ H7).
    
    destruct H8 as [H8 _].
    apply (real_le_plus_le (f (N + k  + 2 + i)%nat + prec (k + 1) + prec (N + k + 2 ))) in H8.
    ring_simplify in H8.
    replace (prec (N +  k + 2 ) * real_1) with (prec (N + k + 2 )) by ring.
    apply (real_le_lt_lt _ _ _ H8).
    apply (real_lt_add_r (-x0)).
    ring_simplify.
    apply (fun a => real_lt_lt_lt _ _ _ a pk).
    rewrite <- (prec_twice k).
    apply (real_lt_add_r (-prec (k + 1))).
    ring_simplify.
    apply prec_monotone.
    lia.
    pose proof (hh _ p).
    contradict (real_nlt_triv _ (real_lt_lt_lt _ _ _ H7 H9)).



    intros z qp.
    destruct (real_total_order z x0).    
    destruct (padding _ _ H6) as [eps [pos e]].
    destruct (real_Archimedean _ pos) as [k pk].

    destruct (W_log _ pw) as [i j].
    

    destruct (H5 (k + 1 )%nat) as [N g].

    
    pose proof (g (N)%nat).
    assert (N <= N)%nat by lia.
    apply H7 in H8.
    clear H7.
    pose proof (h (N)%nat) as [hh _].
    assert (z < f N).
    apply (lp _ _ (fun k => k - eps)) in e.
    ring_simplify in e.
    rewrite <- e.
    destruct H8 as [_ H8].
    assert (x0 - f N + prec k < prec (k + 1) + eps).
    destruct H8.
    apply (real_lt_lt_plus_lt _ _ _ _ H7 pk).
    rewrite H7.
    apply (real_lt_plus_lt (prec (k + 1))  _ _   pk).
    apply (real_lt_plus_lt (-eps + f N - prec k)) in H7.
    ring_simplify in H7.
    replace (- eps + x0) with (x0 - eps) in H7 by ring.
    apply (real_lt_lt_lt _ _ _ H7).
    apply (real_lt_add_r (- f N + prec k)).
    ring_simplify.
    apply prec_monotone.
    lia.

    contradict hh.
    intros sp ep.
    pose proof (qp _ ep).
    apply (real_le_lt_lt _ _ _ H9 H7).

    unfold real_le.
    destruct H6; auto.


    +
    exists x.
    split; auto.
    intros.
    assert (P x).
    destruct (lem (P x)); auto.
    contradict H1.
    intros z H1.
     pose proof (H0 _ H1).
    destruct H4; auto.
    rewrite H4 in H1; induction (H3 H1).
    exact (H2 _ H3).
  Qed.
  
End RealLimit0.

