Require Import Real Hyperspace.Subsets Euclidean List Lia Minmax Classical.Subsets EuclideanSubsets.

Section SimpleTriangle.

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

  Definition T : (@euclidean_subset 2).
  unfold euclidean_subset.
  intro P.
  destruct (split_euclidean2 P) as [x [y P']].
  apply ((real_0 <= x) /\ (real_0 <= y) /\ ((x + y) <= real_1)).
  Defined.


  Definition Tn_ball (n k j :nat) : (ball ) := make_ball2 (Nreal (n2*k+n1) * prec (S n)) (Nreal (n2*j+n1) * prec (S n)) (prec (S n)).

  Fixpoint Tn_col n k j l :=
  match j with
      0 => (Tn_ball n k 0) :: l
    | (S j') => Tn_col n k j' ((Tn_ball n k j) :: l)
   end.
  
  Fixpoint Tn_row n k l :=
  match k with
      0 => (Tn_col n 0 ((Npow2 n)-n1) l)
     | (S k') => (Tn_row n k' (Tn_col n k ((Npow2 n)-k-n1) l))
  end.
                                                                      
  Definition Tn n : list ball := Tn_row n ((Npow2 n)-n1) nil.

  Lemma Tn_col_rad n k j: forall l, (rad l) <= prec (S n) -> rad (Tn_col n k j l) <= prec (S n).
  Proof using Type.
    induction j as [ | l IH].
    - intros l H.
      simpl.
      apply real_max_le_le_le.
      apply real_le_triv.
      apply H.
   - intros l' H.
     simpl.
     apply IH.      
     unfold rad.
     unfold fold_right.
     apply real_max_le_le_le.
     unfold Tn_ball. simpl.
     apply real_le_triv.
     destruct l'.
     unfold rad in H.
     left.
     apply prec_pos.
     exact H.
  Qed.

  Lemma Tn_row_rad n k : forall l, (rad l) <= prec (S n) -> rad (Tn_row n k l) <= prec (S n).
  Proof using Type.
    induction k as [ | k' IH].
    - intros l H.
      apply Tn_col_rad.
      exact H.
    - intros l H.
      apply IH.
      apply Tn_col_rad.
      apply H.
  Qed.


  Lemma Tn_rad n : (rad (Tn n)) <= prec (S n).
  Proof using Type.
    apply Tn_row_rad.
    apply real_lt_le.
    apply prec_pos.
  Qed.

  Lemma Tn_rad' n : (rad (Tn (pred n))) <= prec n.
  Proof.
    destruct n.
    apply (real_le_le_le _ (prec 1)).
    apply Tn_rad.
    left; apply prec_S.
    apply Tn_rad.
  Qed.
  Lemma Tn_ball_intersects (n k j : nat) : (j + k+ 1 <= (Npow2 n))%nat ->  intersects (closed_ball_to_subset (Tn_ball n k j)) T.
  Proof using Type.
    intros H.
    exists (fst (Tn_ball n k j)).
    split.
    unfold closed_ball_to_subset.
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
    unfold n1,n2.
    lia.
    apply prec_pos.
    split.
    apply real_lt_le.
    apply real_lt_pos_mult_pos_pos.
    apply Nreal_pos.
    unfold n1,n2.
    lia.
    apply prec_pos.
    rewrite real_mult_comm.
    rewrite (real_mult_comm (Nreal _)).
    rewrite <-real_mult_plus_distr.
    rewrite <-Nreal_hom.
    rewrite <-(prec_Npow2_unit (S n)).
    apply real_le_mult_pos_le.
    left; apply prec_pos.
    apply Nreal_monotone.
    simpl.
    unfold n1,n2.
    lia.
  Qed.
  
  Lemma Npow2_pos : forall n, (0 < Npow2 n)%nat.
  Proof using Type.
  induction n; simpl; lia.
  Qed.

  Lemma Tn_col_intersects_T n k j : (k <= Npow2 n - 1)%nat -> (j <= (Npow2 n)-k-1)%nat -> forall l, Forall (fun b => intersects (closed_ball_to_subset b) T) l ->  Forall (fun b => intersects (closed_ball_to_subset b) T) (Tn_col n k j l).
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

  Lemma Tn_row_intersects_T n k : (k <= Npow2 n - 1)%nat -> forall l, Forall (fun b => intersects (closed_ball_to_subset b) T) l ->  Forall (fun b => intersects (closed_ball_to_subset b) T) (Tn_row n k l).
  Proof using Type.
    intros Klt.
    induction k as [ | k' IH].
    - intros l H.
      apply Tn_col_intersects_T; unfold n1,n2; try lia.
      exact H.
    - intros l H.
      apply IH.
      lia.
      apply Tn_col_intersects_T; unfold n1,n2; try lia.
      apply H.
  Qed.


  Lemma Tn_intersects_T n :  Forall (fun b => intersects (closed_ball_to_subset b) T) (Tn n).
  Proof using Type.
    apply Tn_row_intersects_T; unfold n1,n2; try lia.
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
       apply Tn_col_contains.
       unfold n1,n2.
       lia.
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
    apply Tn_row_contains; unfold n1,n2; lia.
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
      exists 0%nat.
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

  Lemma real_coordinate x n : (real_0 <= x) -> (x <= real_1) -> exists k, x = real_0 /\ k = 0%nat \/ x > (Nreal k * prec n) /\ x <= Nreal (S k) * prec n.
  Proof.
    intros H1 H2.
    destruct H1.
    - destruct (real_coordinate' x n H H2) as [k'].
     exists k'.
     right. auto.
    - exists 0%nat.
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
      left; apply d2_pos.
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
    rewrite abs_neg_id_neg; [| left; auto].
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
    left;apply real_lt_0_2.
    rewrite abs_pos_id; [| auto].
    apply (real_le_le_le _ (real_2 * z - (y + z))).
    unfold real_minus.
    rewrite !(real_plus_comm (real_2 * _)).
    apply real_le_plus_le.
    apply real_le_mult_pos_le; auto; left; apply real_lt_0_2.
    unfold real_2.
    ring_simplify.   
    apply real_eq_le.
    ring.
  Qed.


  Lemma T_tbounded : totally_bounded T.
  Proof.
   intro n.
   exists (Tn (pred n)).
   split; [apply Tn_rad' | split; [apply Tn_intersects_T | ]].
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
   - destruct (real_coordinate x (pred n) T1 B1) as [k Hk].
   destruct (real_coordinate y (pred n) T2 B2) as [j Hj].
   apply Exists_exists.
   exists (Tn_ball (pred n) k j).
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
   induction n; simpl. lia.
   destruct n. simpl. lia. simpl in IHn.
   replace (Npow2 (S n)) with (2 * (Npow2 n))%nat. lia.
   simpl. lia.
   apply lt_n_Sm_le.
   apply Nreal_nat_lt.
   rewrite !Nreal_hom.
   simpl;ring_simplify.
   apply real_lt_plus_r_lt.
   apply (real_lt_le_lt _ (Nreal (Npow2 (pred n))*y)).
   apply U; auto.
   rewrite <-real_mult_unit, (real_mult_comm real_1).
   simpl.
   apply real_le_mult_pos_le.
   left; apply Nreal_Npow2_pos.
   exact B2.
   apply lt_n_Sm_le.
   apply Nreal_nat_lt.
   rewrite !Nreal_hom.
   simpl;ring_simplify.
   apply real_lt_plus_r_lt.
   apply (real_lt_le_lt _ (Nreal (Npow2 (pred n))*x)).
   apply U; auto.
   rewrite <-real_mult_unit, (real_mult_comm real_1).
   apply real_le_mult_pos_le.
   left; apply Nreal_Npow2_pos.
   exact B1.
   apply lt_n_Sm_le.
   apply Nreal_nat_lt.
   rewrite !Nreal_hom.
   simpl;ring_simplify.
   apply real_lt_plus_r_lt.
   apply (real_lt_le_lt _ (Nreal (Npow2 (pred n))*x + Nreal (Npow2 (pred n))*y)).
   apply real_lt_lt_plus_lt; auto.
   rewrite <-real_mult_plus_distr.
   rewrite <-real_mult_unit, (real_mult_comm real_1).
   apply real_le_mult_pos_le.
   left; apply Nreal_Npow2_pos.
   exact T3.
   unfold closed_ball_to_subset.
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
   apply (prec_pos (S (pred n))).
   assert (real_0 <= Nreal k * prec (pred n)).
   apply real_le_pos_mult_pos_pos; [destruct k; [apply real_eq_le;auto |apply real_lt_le; apply Nreal_pos;lia ] | apply real_lt_le; apply prec_pos].
   assert (Nreal k * prec (pred n) <= x).
   apply real_lt_le;apply H.
   assert (x <= Nreal (S k) * prec (pred n)).
   apply H.
   pose proof (dist_half x (Nreal k * prec (pred n)) (Nreal (S k) * prec (pred n)) H0 H1 H2).   
   apply (real_le_le_le _ (abs (x - (Nreal k * prec (pred n) + Nreal (S k) * prec (pred n)) / real_2_neq_0))).
   apply real_eq_le.
    f_equal.
   rewrite !Nreal_hom.
   unfold real_minus.
   unfold real_div.
   simpl.
   ring.
   apply (real_le_le_le _ ((Nreal (S k) * prec (pred n) - Nreal k * prec (pred n)) / real_2_neq_0)); auto.
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
   apply (prec_pos (S (pred n))).
   assert (real_0 <= Nreal j * prec (pred n)).
   apply real_le_pos_mult_pos_pos; [destruct j; [apply real_eq_le;auto |apply real_lt_le; apply Nreal_pos;lia ] | apply real_lt_le; apply prec_pos].
   assert (Nreal j * prec (pred n) <= y).
   apply real_lt_le;apply H.
   assert (y <= Nreal (S j) * prec (pred n)).
   apply H.
   pose proof (dist_half y (Nreal j * prec (pred n)) (Nreal (S j) * prec (pred n)) H0 H1 H2).   
   apply (real_le_le_le _ (abs (y - (Nreal j * prec (pred n) + Nreal (S j) * prec (pred n)) / real_2_neq_0))).
   apply real_eq_le.
    f_equal.
   rewrite !Nreal_hom.
   unfold real_minus.
   unfold real_div.
   simpl.
   ring.
   apply (real_le_le_le _ ((Nreal (S j) * prec (pred n) - Nreal j * prec (pred n)) / real_2_neq_0)); auto.
   apply real_eq_le.
   unfold real_div.
   simpl.
   ring.
   apply real_lt_le.
   apply (prec_pos (S (pred n))).
 Qed.

  Definition multi_triangles (n : nat) : (@euclidean_subset 2).
  Proof.
    induction n.
    apply empty_set.
    apply union.
    apply T.
    apply translation.
    apply IHn.
    apply (make_euclidean2 (- /real_2_neq_0) (- /real_2_neq_0)).
 Defined.

 Lemma empty_set_is_tbounded : totally_bounded (@empty_set 2).
 Proof.
    intro n.
    exists nil.
    simpl.
    split; [|split].
    apply real_lt_le.
    apply prec_pos.
    apply Forall_forall.
    intros.
    contradict H.
    intros.
    apply Exists_exists.
    contradict H.
 Qed.
 Lemma multi_triangles_tbounded (n : nat) : totally_bounded (multi_triangles n).
 Proof.
   induction n.
   apply empty_set_is_tbounded.
   apply tbounded_union.
   apply T_tbounded.
   apply tbounded_translation.
   apply IHn.
 Defined.

End SimpleTriangle.
