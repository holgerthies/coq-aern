(* this file proves various properties of subsets of real numbers *)


Require Import Lia.
Require Import Real Euclidean List Minmax.
Section SubsetM.

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
Section Subsets.
  

  Context (d : nat).

  Definition euclidean_subset :=  (@euclidean Real d) -> Prop.
  Definition union (A B : euclidean_subset) := fun x => A x \/ B x.
  Definition intersection (A B : euclidean_subset) := fun x => A x /\ B x.
  Definition intersects (A B : euclidean_subset) := exists x, intersection A B x.
  Definition is_subset (A B : euclidean_subset) := forall x, A x -> B x.

  Definition empty_set : euclidean_subset := fun x => False.

  Definition ball := ((@euclidean Real d) * Real)%type.
  Definition ball_to_subset (b : ball)  : euclidean_subset := (fun x => (euclidean_max_dist x (fst b)) <= (snd b)).  

  Definition diam (L : list ball) := (fold_right (fun b1 r => (real_max (snd b1) r)) real_0 L).
  Definition is_compact (M : euclidean_subset) := {L : nat -> list ball |
                                                    (forall n, diam (L n) <= prec n) /\
                                                    (forall n, Forall (fun b => intersects (ball_to_subset b) M) (L n)) /\
                                                    forall n, forall x,  M x ->  Exists (fun b => (ball_to_subset b) x) (L n)
                                                    }. 

End Subsets.

Section Examples.
  Lemma split_euclidean2 (P : (@euclidean Real 2)) : { x & {y | P = (Euclidean.cons x (Euclidean.cons y Euclidean.nil))}}.
  Proof.
    pose proof  (dim_succ_destruct P).
    destruct X as [x P'].
    destruct P' as [P0 P1].
    pose proof (dim_succ_destruct P0).
    destruct X as [y P2].
    exists x.
    exists y.
    rewrite P1.
    destruct P2.
    f_equal.
    rewrite e.
    f_equal.
    apply dim_zero_destruct.
  Defined.

  Definition make_euclidean2 (x y : Real) := Euclidean.cons x (Euclidean.cons y Euclidean.nil).
  Definition make_ball (x y r : Real) : ball 2 := ((make_euclidean2 x y), r).
  
  Definition Tn_ball (n k j :nat) : (ball 2) := make_ball (Nreal (2*k+1) * prec (S n)) (Nreal (2*j+1) * prec (S n)) (prec (S n)).

  Fixpoint Tn_col n k j l :=
  match j with
      0 => (Tn_ball n k 0) :: l
    | (S j') => Tn_col n k j' ((Tn_ball n k j) :: l)
   end.
  
  Fixpoint Tn_row n k l :=
  match k with
      0 => (Tn_col n 0 ((Npow2 n)-1) l)
     | (S k') => (Tn_row n k' (Tn_col n k ((Npow2 n)-k-1) l))
  end.
                                                                      
  Definition Tn n : list (ball 2) := Tn_row n ((Npow2 n)-1) nil.

  Lemma Tn_col_diam n k j: forall l, (diam 2 l) <= prec n -> diam 2 (Tn_col n k j l) <= prec n.
  Proof using Type.
    induction j as [ | l IH].
    - intros l H.
      simpl.
      apply real_max_le_le_le.
      apply real_lt_le.
      apply prec_S.
      apply H.
   - intros l' H.
     simpl.
     apply IH.      
     unfold diam.
     unfold fold_right.
     apply real_max_le_le_le.
     apply real_lt_le.
     apply prec_S.
     destruct l'.
     apply real_lt_le.
     apply prec_pos.
     unfold diam in H.
     exact H.
  Qed.

  Lemma Tn_row_diam n k : forall l, (diam 2 l) <= prec n -> diam 2 (Tn_row n k l) <= prec n.
  Proof using Type.
    induction k as [ | k' IH].
    - intros l H.
      apply Tn_col_diam.
      exact H.
    - intros l H.
      apply IH.
      apply Tn_col_diam.
      apply H.
  Qed.


  Lemma Tn_diam n : (diam 2 (Tn n)) <= prec n.
  Proof using Type.
    apply Tn_row_diam.
    apply real_lt_le.
    apply prec_pos.
  Qed.

  Definition T : (euclidean_subset 2).
    unfold euclidean_subset.
    intro P.
    destruct (split_euclidean2 P) as [x [y P']].
    apply ((real_le real_0 x) /\ (real_le real_0 y) /\ (real_le (x + y) real_1)).
  Defined.

  Lemma Tn_ball_intersects (n k j : nat) : (j + k+ 1 <= (Npow2 n))%nat ->  intersects 2 (ball_to_subset 2 (Tn_ball n k j)) T.
  Proof using Type.
    intros H.
    exists (fst (Tn_ball n k j)).
    split.
    unfold ball_to_subset.
    Search euclidean_max_dist.
    pose proof (euclidean_max_dist_id (fst (Tn_ball n k j)) (fst (Tn_ball n k j))).
    destruct H0.
    rewrite H1.
    apply real_lt_le.
    apply prec_pos.
    reflexivity.
    split.
    apply real_lt_le.
    apply real_lt_pos_mult_pos_pos.
    apply Nreal_pos.
    lia.
    apply prec_pos.
    split.
    apply real_lt_le.
    apply real_lt_pos_mult_pos_pos.
    apply Nreal_pos.
    lia.
    apply prec_pos.
    rewrite real_mult_comm.
    rewrite (real_mult_comm (Nreal _)).
    rewrite <-real_mult_plus_distr.
    rewrite <-Nreal_hom.
    rewrite <-(prec_Npow2_unit (S n)).
    apply real_le_mult_pos_le.
    apply prec_pos.
    apply Nreal_monotone.
    simpl.
    lia.
  Qed.
  
  Lemma Npow2_pos : forall n, (0 < Npow2 n)%nat.
  Proof using Type.
  induction n; simpl; lia.
  Qed.

  Lemma Tn_col_intersects_T n k j : (k <= Npow2 n - 1)%nat -> (j <= (Npow2 n)-k-1)%nat -> forall l, Forall (fun b => intersects 2 (ball_to_subset 2 b) T) l ->  Forall (fun b => intersects 2 (ball_to_subset 2 b) T) (Tn_col n k j l).
  Proof using Type.
    intros Klt Jlt.
    induction j as [ | j' IH].
    - intros H.
      apply Forall_cons.
      apply Tn_ball_intersects.
      pose proof (Npow2_pos n).
      lia.
   - intros l H.
     simpl.
     apply IH.
     lia.
     apply Forall_cons.
     apply Tn_ball_intersects.
     lia.
     exact H.
  Qed.

  Lemma Tn_row_intersects_T n k : (k <= Npow2 n - 1)%nat -> forall l, Forall (fun b => intersects 2 (ball_to_subset 2 b) T) l ->  Forall (fun b => intersects 2 (ball_to_subset 2 b) T) (Tn_row n k l).
  Proof using Type.
    intros Klt.
    induction k as [ | k' IH].
    - intros l H.
      apply Tn_col_intersects_T; try lia.
      exact H.
    - intros l H.
      apply IH.
      lia.
      apply Tn_col_intersects_T; try lia.
      apply H.
  Qed.


  Lemma Tn_intersects_T n :  Forall (fun b => intersects 2 (ball_to_subset 2 b) T) (Tn n).
  Proof using Type.
    apply Tn_row_intersects_T; try lia.
    apply Forall_nil.
  Qed.

  Lemma Tn_col_incl n j k l : forall l', incl l l' -> incl l (Tn_col n k j l').
  Proof.
    induction j as [ | j' IH].
    intros l' P.
    apply incl_tl.
    exact P.
    intros l' P.
    apply IH.
    apply incl_tl.
    exact P.
  Qed.

  Lemma Tn_row_incl n k l : forall l', incl l l' -> incl l (Tn_row n k l').
  Proof.
    induction k as [ | k' IH].
    intros l' P.
    apply Tn_col_incl.
    exact P.
    intros l' P.
    apply IH.
    apply Tn_col_incl.
    exact P.
  Qed.

  Lemma Tn_col_contains n j k : forall l j',  (j' <= j)%nat -> In (Tn_ball n k j') (Tn_col n k j l).
  Proof.
    induction j as [ | j IH].
    - intros.
      apply Nat.le_0_r in H.
      rewrite H.
      left.
      reflexivity.
   - intros l j' P.
     destruct (le_lt_or_eq _ _ P).
     apply IH.
     lia.
     rewrite H.
     simpl.

     pose proof (@incl_cons_inv _ (Tn_ball n k (S j)) l (Tn_col n k j (Tn_ball n k (S j) :: l))).
     destruct H0.
     apply Tn_col_incl.
     apply incl_refl.
     exact H0.
  Qed.

  Lemma Tn_row_contains n k : forall l k' j', (k' <= k)%nat -> (j' <= Npow2 n - k' - 1)%nat -> In (Tn_ball n k' j') (Tn_row n k l).
   Proof. 
     induction k as [| k IH].
     - intros.
       apply Nat.le_0_r in H.
       rewrite H.
       apply Tn_col_contains; try lia.
     - intros.
       destruct (le_lt_or_eq _ _ H).
       apply IH; try lia.
       rewrite H1.
       simpl.
       pose proof (Tn_row_incl n (S k) (Tn_col n (S k) (Npow2 (n - S k - 1)%nat) l)).
       assert (incl (Tn_col n (S k) (Npow2 n - S k - 1) l) (Tn_row n k (Tn_col n (S k) (Npow2 n - S k - 1) l))).
      apply Tn_row_incl;apply incl_refl.
       pose proof (incl_Forall_in_iff (Tn_col n (S k) (Npow2 n - S k - 1) l)
 (Tn_row n k (Tn_col n (S k) (Npow2 n - S k - 1) l))) as [I _].
       pose proof (I H3) as I'.
       rewrite Forall_forall in I'.
       apply I'.
       apply Tn_col_contains.
       lia.
   Qed.
       
  Lemma Tn_contains n k j : (k + j + 1 <= Npow2 n)%nat -> In (Tn_ball n k j) (Tn n).
  Proof.
    intro H.
    apply Tn_row_contains;lia.
  Qed.
  (* Lemma real_coordinate x n : (real_0 <= x) -> (x <= real_1) -> exists k, dist x (Nreal (2*k+1) * prec (S n)) <= prec (S n). *)
  (* Proof. *)
  (*   intros H1 H2. *)
  (*   induction n as [| n' IH]. *)
  (*   - exists 0. *)
  (*     rewrite Nat.mul_0_r, plus_O_n. *)
  (*     unfold Nreal. *)
  (*     rewrite real_plus_comm, real_plus_unit, real_mult_unit. *)
  (*     rewrite dist_le_prop. *)
  (*     split. *)
  (*     apply (real_le_add_r (prec 1)). *)
  (*     ring_simplify. *)
  (*     exact H1. *)
  (*     apply (real_le_add_r (prec 1)). *)
  (*     rewrite (prec_twice 0). *)
  (*     unfold prec. *)
  (*     ring_simplify. *)
  (*     exact H2. *)
  (*  - destruct IH as [k kprp]. *)
  (*    destruct (real_total_order x (Nreal (2 * k + 1) * prec (S n'))). *)
  (*    exists (2*k)%nat. *)
  (*    admit. *)
  (*    admit.     *)
  (* Admitted. *)

  Lemma real_coordinate' x n : (real_0 < x) -> (x <= real_1) -> exists k, x > (Nreal k * prec n) /\ x <= Nreal (S k) * prec n.
  Proof.
    intros H1 H2.
    induction n as [| n' IH].
    - 
      exists 0.
      split.
      unfold Nreal.
      unfold prec.
      ring_simplify.
      exact H1.
      unfold Nreal.
      ring_simplify.
      unfold prec.
      exact H2.
   -admit.
  Admitted.

  Lemma real_coordinate x n : (real_0 <= x) -> (x <= real_1) -> exists k, x = real_0 /\ k = 0 \/ x > (Nreal k * prec n) /\ x <= Nreal (S k) * prec n.
  Admitted.

  Lemma Nreal_nat_lt : forall m, forall n, Nreal n < Nreal m -> (n < m)%nat.
  Proof.
    induction m as [ | m' IH]; intros n H.
    - destruct n.
      simpl in H.
      apply real_nlt_triv in H.
      contradict H.
      Search Nreal.
      pose proof (Nreal_pos (S n)).
      contradict H.
      apply real_lt_nlt.
      apply H0.
      lia.
   - destruct n; [lia |].
     apply lt_n_S.
     simpl in H.
     rewrite !(real_plus_comm real_1) in H.
     apply real_lt_add_r in H.    
     apply IH.
     apply H.
  Qed.

  Lemma dist_half x y z : (real_0 <= y) -> (y <= x) -> (x <= z) -> abs (x - (y+z) / real_2_neq_0) <= (y+z) / real_2_neq_0.
  Proof.
    intros H1 H2 H3.
    assert (real_0 <= x /\ real_0 <= z) as [H4 H5].
    split;apply (real_le_le_le _ y); auto.
    apply (real_le_le_le _ x);auto.
    assert (real_0 <= x - (y + z) / real_2_neq_0).
    {
      
    }
    assert (y <= z).
    apply (real_le_le_le _ x); auto.
    assert (forall a b, a <= b -> a - b/real_2_neq_0 <= b/real_2_neq_0).
    { intros.
      apply (real_le_add_r (b / real_2_neq_0)).
      ring_simplify.
      unfold real_div.
      ring_simplify.
      rewrite real_mult_comm,<-real_mult_assoc.
      rewrite real_mult_inv.
      ring_simplify; auto.
    }
    destruct (real_total_order (x- (y+z) / real_2_neq_0) real_0).
    rewrite abs_pos_id.
    apply H0.
    Search _ (_ <= (_ + _)).
  Lemma T_is_compact : is_compact 2 T.
  Proof.
   exists Tn.
   split; [apply Tn_diam | split; [apply Tn_intersects_T | ]].
   intros n P Tx.
   unfold T in Tx.
   destruct (split_euclidean2 P) as [x [y prp]].
   destruct Tx as [T1 [T2 T3]].
   assert ((x <= real_1) /\ (y <= real_1)) as [B1 B2].
   admit.
   destruct (real_coordinate x n T1 B1) as [k Hk].
   destruct (real_coordinate y n T2 B2) as [j Hj].
   apply Exists_exists.
   exists (Tn_ball n k j).
   split.
   apply Tn_contains.
   assert (forall m n y, y > Nreal m * prec n -> Nreal m < Nreal (Npow2 n) * y) as U.
   { intros.
     apply (real_lt_mult_pos_cancel (prec n0)); [apply prec_pos |].
     rewrite (real_mult_comm (_ * _)), <-real_mult_assoc.  
     rewrite prec_Npow2_unit.
     ring_simplify.
     exact H.
   }
   destruct Hk as [[x0 ->] | [kprp1 kprp2] ]; destruct Hj as [[y0 ->] | [jprp1 jprp2]].
   induction n; simpl;lia.
   apply lt_n_Sm_le.
   apply Nreal_nat_lt.
   rewrite !Nreal_hom.
   simpl;ring_simplify.
   apply real_lt_plus_r_lt.
   apply (real_lt_le_lt _ (Nreal (Npow2 n)*y)).
   apply U; auto.
   rewrite <-real_mult_unit, (real_mult_comm real_1).
   apply real_le_mult_pos_le.
   apply Nreal_Npow2_pos.
   exact B2.
   apply lt_n_Sm_le.
   apply Nreal_nat_lt.
   rewrite !Nreal_hom.
   simpl;ring_simplify.
   apply real_lt_plus_r_lt.
   apply (real_lt_le_lt _ (Nreal (Npow2 n)*x)).
   apply U; auto.
   rewrite <-real_mult_unit, (real_mult_comm real_1).
   apply real_le_mult_pos_le.
   apply Nreal_Npow2_pos.
   exact B1.
   apply lt_n_Sm_le.
   apply Nreal_nat_lt.
   rewrite !Nreal_hom.
   simpl;ring_simplify.
   apply real_lt_plus_r_lt.
   apply (real_lt_le_lt _ (Nreal (Npow2 n)*x + Nreal (Npow2 n)*y)).
   apply real_lt_lt_plus_lt; auto.
   rewrite <-real_mult_plus_distr.
   rewrite <-real_mult_unit, (real_mult_comm real_1).
   apply real_le_mult_pos_le.
   apply Nreal_Npow2_pos.
   exact T3.
   unfold ball_to_subset.
   unfold euclidean_max_dist.
   rewrite prp.
   simpl.
   apply real_max_le_le_le.
   destruct Hk as [[-> ->] | ].
   simpl.
   rewrite real_plus_unit, real_plus_comm, real_plus_unit, real_mult_unit, <-abs_symm.
   rewrite abs_pos_id.
   apply real_eq_le; auto.
   apply real_lt_le.
   apply (prec_pos (S n)).
   
   apply real_max_le_le_le.
   admit.
   apply real_lt_le.
   apply (prec_pos (S n)).
 Qed.
 (*  Definition process (b : ball 2) : (ball 2) * (ball 2) * (ball 2). *)
 (*  Proof. *)
 (*    pose ((snd b) / real_2_neq_0) as r'. *)
 (*    destruct (split_euclidean2 (fst b)) as [x [y P']]. *)
 (*    split. *)
 (*    split. *)
 (*    split. *)
 (*    apply (make_euclidean2 (x-r') (y-r')). *)
 (*    apply r'. *)
 (*    split. *)
 (*    apply (make_euclidean2 (x-r') (y+r')). *)
 (*    apply r'. *)
 (*    split. *)
 (*    apply (make_euclidean2 (x+r') (y-r')). *)
 (*    apply r'. *)
 (* Defined. *)


 (*  Fixpoint coverIter (n : nat) (b : (ball 2)) : (list (ball 2)). *)
 (*  Proof.   *)
 (*    induction n as [| n' result].     *)
 (*    apply (b :: nil). *)
 (*    pose (process b). *)
 (*    destruct p as [[p1 p2] p3]. *)
 (*    pose (coverIter n' p2) as l2. *)
 (*    pose (coverIter n' p3) as l3. *)
 (*    apply (p1 :: (app l2 l3)). *)
 (*  Defined. *)
 (*  Definition coverT (n : nat) : list (ball 2) := coverIter n (make_ball (real_1 / real_2_neq_0) (real_1 / real_2_neq_0) (real_1 / real_2_neq_0)). *)

 (*  Lemma cover_iter_diam : forall n b, diam 2 (coverIter (S n) b) = (real_1 / real_2_neq_0) * diam 2 (coverIter n b). *)
 (*  Proof. *)
 (*    intros. *)
 (*    induction n. *)
 (*    - simpl. *)
      
 (*  Lemma T_is_compact : is_compact 2 T. *)
 (*  Proof.    *)
 (*    exists coverT. *)
 (*    split. *)
 (*    - induction n. *)
 (*      admit. *)
 (*      intros. *)
 (*    - simpl. *)
 (*      split. *)
 (*      + admit. *)
 (*      + intros m b B. *)
 (*        split. *)

End Examples.
 
End SubsetM. 