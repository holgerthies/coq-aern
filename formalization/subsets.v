(* this file proves various properties of subsets of real numbers *)
Require Import Lia.
Require Import Real Euclidean List Minmax.
Section SubsetM.

Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).
#[local] Definition sofReal := @sofReal types casofReal.
#[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).
#[local] Notation "^euclidean" := (@euclidean types) (at level 0).

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

  Definition euclidean_subset :=  (^euclidean d) -> Prop.
  Definition union (A B : euclidean_subset) := fun x => A x \/ B x.
  Definition intersection (A B : euclidean_subset) := fun x => A x /\ B x.
  Definition intersects (A B : euclidean_subset) := exists x, intersection A B x.
  Definition is_subset (A B : euclidean_subset) := forall x, A x -> B x.

  Definition empty_set : euclidean_subset := fun x => False.

  Definition ball := ((^euclidean d) * ^Real)%type.
  Definition ball_to_subset (b : ball)  : euclidean_subset := (fun x => (euclidean_max_dist x (fst b)) <= (snd b)).  

  Definition diam (L : list ball) := (fold_right (fun b1 r => (real_max (snd b1) r)) real_0 L).

  Definition Hausdorff_dist_bound (S T : euclidean_subset) n :=
    (forall x, S x -> exists y, T y /\ euclidean_max_dist x y <= n) /\
      (forall y, T y -> exists x, S x /\ euclidean_max_dist x y <= n).
      Lemma split_euclidean2 (P : (^euclidean 2)) : { x & {y | P = (Euclidean.cons x (Euclidean.cons y Euclidean.nil))}}.
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
  
    Definition make_euclidean2 (x y : ^Real) := Euclidean.cons x (Euclidean.cons y Euclidean.nil).


  Definition is_compact (M : euclidean_subset) := forall n, {Ln : list ball |
                                                    diam Ln <= prec n /\
                                                    Forall (fun b => intersects (ball_to_subset b) M) Ln /\
                                                    forall x,  M x ->  Exists (fun b => (ball_to_subset b) x) Ln
                                                    }. 
(*   Lemma is_compact_lim : *)
(*     forall k : euclidean_subset, *)
(*       (forall n : nat, {X :  euclidean_subset & prod (is_compact X) (Hausdorff_dist_bound X k (prec n))})   *)
(*       -> is_compact k. *)
(*   Proof. *)
(*     intros. *)
(*     intro p. *)
(*     destruct (X (S p)). *)
(*     destruct p0. *)
(*     destruct (i (S p)). *)
(*     exists x0. *)

(*     split. *)
(*     destruct a. *)
(*     assert (forall k0, *)
(*                (exists y : euclidean d, x y /\ euclidean_max_dist k0 y <= prec (S p)) -> *)
(*                exists y : euclidean d, k y /\ euclidean_max_dist k0 y <= prec p). *)
(*     intros. *)
(*     destruct H1. *)
(*     destruct H1. *)
(*     destruct h. *)
(*     pose proof (H3 x1 H1). *)
(*     destruct H5. *)
(*     exists x2. *)
(*     destruct H5; split; auto. *)
(*     pose proof (euclidean_max_dist_tri k0 x1 x2). *)
(*     pose proof (real_le_le_plus_le _ _ _ _ H2 H6). *)
(*     replace (S p) with (p + 1)%nat in H8. *)
(*     rewrite prec_twice in H8. *)
(*     apply (real_le_le_le _ _ _ H7 H8). *)
(*     lia. *)
(*     apply (Forall_impl _ H1 H0). *)
(*     destruct a. *)
(*     intros. *)
(*     destruct h. *)
(*     pose proof (H3 y H1). *)
(*     destruct H4. *)
(*     destruct H4. *)
(*     pose proof (H0 x1 H4). *)
(*     assert (forall k0, *)
(*                (euclidean_max_dist k0 x1 <= prec (S p)) -> *)
(*                euclidean_max_dist k0 y <= prec p). *)
(*     intros. *)
(*     pose proof (euclidean_max_dist_tri k0 x1 y). *)
(*     pose proof (real_le_le_plus_le _ _ _ _ H7 H5). *)
(*     replace (S p) with (p + 1)%nat in H9 by lia. *)
(*     rewrite prec_twice in H9. *)
(*     apply (real_le_le_le _ _ _ H8 H9). *)
(*     apply (Exists_impl _ H7 H6). *)
(*   Defined.   *)
End Subsets.

Section SimpleTriangle.

  Definition T : (euclidean_subset 2).
  unfold euclidean_subset.
  intro P.
  destruct (split_euclidean2 P) as [x [y P']].
  apply ((real_0 <= x) /\ (real_0 <= y) /\ ((x + y) <= real_1)).
  Defined.

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

  Lemma Tn_ball_intersects (n k j : nat) : (j + k+ 1 <= (Npow2 n))%nat ->  intersects 2 (ball_to_subset 2 (Tn_ball n k j)) T.
  Proof using Type.
    intros H.
    exists (fst (Tn_ball n k j)).
    split.
    unfold ball_to_subset.
    (* Search euclidean_max_dist. *)
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
  
  Lemma prec_mult_two n : (Nreal 2) * prec (S n) = prec n.
  Proof.
    (* simpl. *)
    rewrite <-(prec_twice n).
    assert (forall x, (Nreal 2) * x = x + x).
    intro x.
    unfold Nreal.
    ring.
    rewrite H.
    rewrite (Nat.add_1_r).
    auto.
  Qed.

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
   - destruct IH as [k' [IH_xgt IH_xle]].
     assert (Nreal k' * prec n' = Nreal (2 * k') * prec (S n')) as E.
       rewrite <-(prec_twice n').
       rewrite Nreal_mult.
       rewrite (real_mult_comm (Nreal 2)).
       rewrite real_mult_assoc.
       rewrite prec_twice.
       rewrite prec_mult_two.
       auto.
     destruct (real_total_order x (Nreal (2*k' + 1) * prec (S n'))) as [H | [H | H]].
      + exists (2*k')%nat.
        split.
        rewrite <-E. auto.
        apply real_lt_le.
        rewrite <-(Nat.add_1_r). auto.
      + exists (2*k')%nat.
        split.
        rewrite <-E. auto.
        apply real_eq_le.
        rewrite <-(Nat.add_1_r). auto.
      + exists (2*k' +1)%nat.
        split.
        auto.
        rewrite <-prec_mult_two in IH_xle.
        rewrite <-real_mult_assoc in IH_xle.
        rewrite <-Nreal_mult in IH_xle.
        assert (S k' * 2 = S (2 * k' + 1))%nat as E2. lia.
        rewrite <-E2. auto.
  Qed.

  Lemma real_coordinate x n : (real_0 <= x) -> (x <= real_1) -> exists k, x = real_0 /\ k = 0 \/ x > (Nreal k * prec n) /\ x <= Nreal (S k) * prec n.
  Proof.
    intros H1 H2.
    destruct H1.
    - destruct (real_coordinate' x n H H2) as [k'].
     exists k'.
     right. auto.
    - exists 0.
    left. auto.
  Qed.
    
  Lemma Nreal_nat_lt : forall m, forall n, Nreal n < Nreal m -> (n < m)%nat.
  Proof.
    induction m as [ | m' IH]; intros n H.
    - destruct n.
      simpl in H.
      apply real_nlt_triv in H.
      contradict H.
      (* Search Nreal. *)
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

  Lemma dist_half x y z : (real_0 <= y) -> (y <= x) -> (x <= z) -> abs (x - (y+z) / real_2_neq_0) <= (z-y) / real_2_neq_0.
  Proof.
    intros H1 H2 H3.
    assert (real_0 <= x /\ real_0 <= z) as [H4 H5].
    split;apply (real_le_le_le _ y); auto.
    apply (real_le_le_le _ x);auto.
    assert (forall a b,  abs a <= b -> abs(a / real_2_neq_0) <= b / real_2_neq_0 ) as absd2.
    {
      intros.
      unfold real_div.
      rewrite abs_mult.
      rewrite (abs_pos_id (/ _)).
      rewrite real_mult_comm, (real_mult_comm b).
      apply real_le_mult_pos_le; auto.
      apply d2_pos.
      apply real_lt_le.
      apply d2_pos.
    }
    assert (x  - (y + z) / real_2_neq_0 = ((real_2 * x - (y+ z)) / real_2_neq_0)). 
    {
      unfold real_minus.
      rewrite <-(real_div_distr (real_2 * x)).
      unfold real_div.
      assert (forall x y , - x * y = - (x * y)) as ->.
      intros; ring.
      apply real_eq_plus_eq.
      ring_simplify.
      rewrite real_mult_assoc, (real_mult_comm real_2), real_mult_inv.
      ring.
    }
    rewrite H.
    apply absd2.
    assert (forall x,  x < real_0 \/ real_0 <= x) as T.
    {
      intros.
      destruct (real_total_order x0 real_0) as [T| [T| T]]; [| right; apply real_eq_le | right; apply real_lt_le  ];auto.
    }
    destruct (T (real_2 * x - (y + z))) as [T' | T'].
    rewrite abs_neg_id_neg; [| auto].
    apply (real_le_add_r (real_2*x)).
    ring_simplify.
    apply (real_le_le_le _ (real_2*y - y + z)).
    apply real_eq_le.
    unfold real_2; simpl.
    ring.
    unfold real_minus.
    rewrite !real_plus_assoc, !(real_plus_comm (real_2 * _)).
    apply real_le_plus_le.
    apply real_le_mult_pos_le; auto.
    apply real_lt_0_2.
    rewrite abs_pos_id; [| auto].
    apply (real_le_le_le _ (real_2 * z - (y + z))).
    unfold real_minus.
    rewrite !(real_plus_comm (real_2 * _)).
    apply real_le_plus_le.
    apply real_le_mult_pos_le; auto; apply real_lt_0_2.
    unfold real_2.
    ring_simplify.   
    apply real_eq_le; auto.
  Qed.


  Lemma real_0_mult_le x y : real_0 <= x -> real_0 <= y -> real_0 <= x * y.
  Proof.
    intros.
    destruct H.
    replace real_0 with (x * real_0) by ring.
    apply (real_le_mult_pos_le x real_0 y H H0).
    rewrite <-H.
    apply real_eq_le.
    ring.
  Qed.
  Lemma T_is_compact : is_compact 2 T.
  Proof.
   intro n.
   exists (Tn n).
   split; [apply Tn_diam | split; [apply Tn_intersects_T | ]].
   intros P Tx.
   unfold T in Tx.
   destruct (split_euclidean2 P) as [x [y prp]].
   destruct Tx as [T1 [T2 T3]].
   assert ((x <= real_1) /\ (y <= real_1)) as [B1 B2].
   split.
   - apply (real_le_add_r y).
     apply (real_le_le_le _ real_1); auto.
     rewrite <-(real_plus_unit real_1) at 1.
     rewrite real_plus_comm.
     apply real_le_plus_le; auto.
   - apply (real_le_add_r x).
     rewrite real_plus_comm.
     apply (real_le_le_le _ real_1); auto.
     rewrite <-(real_plus_unit real_1) at 1.
     rewrite real_plus_comm.
     apply real_le_plus_le; auto.
   - destruct (real_coordinate x n T1 B1) as [k Hk].
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
   assert (real_0 <= Nreal k * prec n).
   apply real_0_mult_le; [destruct k; [apply real_eq_le;auto |apply real_lt_le; apply Nreal_pos;lia ] | apply real_lt_le; apply prec_pos].
   assert (Nreal k * prec n <= x).
   apply real_lt_le;apply H.
   assert (x <= Nreal (S k) * prec n).
   apply H.
   pose proof (dist_half x (Nreal k * prec n) (Nreal (S k) * prec n) H0 H1 H2).   
   apply (real_le_le_le _ (abs (x - (Nreal k * prec n + Nreal (S k) * prec n) / real_2_neq_0))).
   apply real_eq_le.
    f_equal.
   rewrite !Nreal_hom.
   unfold real_minus.
   unfold real_div.
   simpl.
   ring.
   apply (real_le_le_le _ ((Nreal (S k) * prec n - Nreal k * prec n) / real_2_neq_0)); auto.
   apply real_eq_le.
   unfold real_div.
   simpl.
   ring.
   apply real_max_le_le_le.
   destruct Hj as [[-> ->] | ].
   simpl.
   rewrite real_plus_unit, real_plus_comm, real_plus_unit, real_mult_unit, <-abs_symm.
   rewrite abs_pos_id.
   apply real_eq_le; auto.
   apply real_lt_le.
   apply (prec_pos (S n)).
   assert (real_0 <= Nreal j * prec n).
   apply real_0_mult_le; [destruct j; [apply real_eq_le;auto |apply real_lt_le; apply Nreal_pos;lia ] | apply real_lt_le; apply prec_pos].
   assert (Nreal j * prec n <= y).
   apply real_lt_le;apply H.
   assert (y <= Nreal (S j) * prec n).
   apply H.
   pose proof (dist_half y (Nreal j * prec n) (Nreal (S j) * prec n) H0 H1 H2).   
   apply (real_le_le_le _ (abs (y - (Nreal j * prec n + Nreal (S j) * prec n) / real_2_neq_0))).
   apply real_eq_le.
    f_equal.
   rewrite !Nreal_hom.
   unfold real_minus.
   unfold real_div.
   simpl.
   ring.
   apply (real_le_le_le _ ((Nreal (S j) * prec n - Nreal j * prec n) / real_2_neq_0)); auto.
   apply real_eq_le.
   unfold real_div.
   simpl.
   ring.
   apply real_lt_le.
   apply (prec_pos (S n)).
 Qed.

End SimpleTriangle.

Section SierpinskiTriangle.

  Definition ST_v1 := make_euclidean2 (- real_1) real_1.
  Definition ST_v2 := make_euclidean2 (- real_1) (- real_1).
  Definition ST_v3 := make_euclidean2 real_1 (- real_1).

  Definition has_ST_v123 (s : euclidean_subset 2) : Prop :=
    (s ST_v1) \/ (s ST_v2) \/ (s ST_v3).

  Definition ST_weighted_pt (c1 c2 c3 : ^Real) : ^euclidean 2.
    destruct (split_euclidean2 ST_v1) as [x1 [y1 _]].
    destruct (split_euclidean2 ST_v2) as [x2 [y2 _]].
    destruct (split_euclidean2 ST_v3) as [x3 [y3 _]].
    pose (c1 * x1 + c2 * x2 + c3 * x3) as x.
    pose (c1 * y1 + c2 * y2 + c3 * y3) as y.
    apply (make_euclidean2 x y).
  Defined.

  Definition inside_ST_hull (s : euclidean_subset 2) : Prop :=
    forall pt : ^euclidean 2, s pt -> exists c1 c2 c3 : ^Real, pt = (ST_weighted_pt c1 c2 c3) /\ c1 >= real_0 /\ c1 >= real_0 /\ c3 >= real_0.

  Definition point_point_mid (p1 : ^euclidean 2) (p2 : ^euclidean 2) : ^euclidean 2.
    destruct (split_euclidean2 p1) as [x1 [y1 _]].
    destruct (split_euclidean2 p2) as [x2 [y2 _]].
    apply (make_euclidean2 ((x1 + x2) / real_2_neq_0) ((y1 + y2) / real_2_neq_0)).
  Defined.

  Definition point_ball_mid (p : ^euclidean 2) (b : ball 2) : ball 2.
    destruct b as [bc br].
    apply (pair (point_point_mid p bc) (br / real_2_neq_0)).
  Defined.

  Definition ST_selfSimilar (s : euclidean_subset 2) : Prop :=
    forall pt : ^euclidean 2, 
    s pt = s (point_point_mid ST_v1 pt)
    /\ 
    s pt = s (point_point_mid ST_v2 pt)
    /\ 
    s pt = s (point_point_mid ST_v3 pt).  

  Definition ST (s : euclidean_subset 2) : Prop :=
    has_ST_v123 s /\ inside_ST_hull s /\ ST_selfSimilar s.

  Definition ST_split_ball (b : ball 2) :=
    (point_ball_mid ST_v1 b) :: 
    (point_ball_mid ST_v2 b) :: 
    (point_ball_mid ST_v3 b) :: nil.

  Fixpoint STn n : list (ball 2) := 
    match n with
    | 0 => (make_ball real_0 real_0 real_1) :: nil 
           (* the initial cover is the square ([-1,1],[-1,1]) *) 
    | (S n') => List.concat (List.map ST_split_ball (STn n'))
    end.

  
End SierpinskiTriangle.

 
End SubsetM. 
