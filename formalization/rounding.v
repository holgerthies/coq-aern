(* Prove that all real number instances are equivalent *)

Require Import Real.
Require Import testsearch.
Require Import Psatz.
        
Section rounding.

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


  Lemma naive_rounding_pos : forall x : Real, x > real_0 -> ^M {k  | Nreal k < x < Nreal (k + 4) }.
    intros.
    pose proof (epsilon_smallest_PQ_M (fun n => x < Nreal (n) + prec 1) (fun n => Nreal (n) - prec 1 < x)).
    simpl in X.
    assert ((forall n : nat,
       ^M ({x < Nreal (n ) + real_1 / real_2_neq_0} + {Nreal (n ) - real_1 / real_2_neq_0 < x}))).
    intro.
    apply choose; auto with real.
    pose proof (W_split x (Nreal n) (real_1 / real_2_neq_0)).
    assert (real_1 / real_2_neq_0 > real_0).
    pose proof (prec_pos (S O)).
    simpl in H1.
    exact H1.
    apply H0 in H1; clear H0.
    destruct H1; auto.
    left.
    apply (real_lt_plus_lt (real_1 / real_2_neq_0)) in H0.
    replace (real_1 / real_2_neq_0 + (x - real_1 / real_2_neq_0)) with x in H0 by ring.
    rewrite real_plus_comm; auto.
    
    apply X in X0; clear X.
    apply (fun a => M_lift _  _ a X0).
    intro.
    destruct H0.
    destruct a.
    destruct x0.
    simpl in H0.
    exists O.
    split;  auto.
    apply (real_lt_lt_lt _ _ _ H0).
    rewrite real_plus_unit.
    assert (jj :  real_1 / real_2_neq_0 < real_1) by ( apply real_gt_half, real_1_gt_0).
    apply (real_lt_lt_lt _ _ _ jj).
    rewrite <- (real_plus_unit real_1).
    rewrite real_plus_comm.
    fold (Nreal 1).
    apply Nreal_strict_monotone.
    lia.

    destruct x0.
    exists O.
    split; auto.
    apply (real_lt_lt_lt _ _ _ H0).
    assert (jj :  real_1 / real_2_neq_0 < real_1) by ( apply real_gt_half, real_1_gt_0).
    apply (real_lt_plus_lt (Nreal 1)) in jj.
    
    apply (real_lt_lt_lt _ _ _ jj).
    replace (Nreal 1 + real_1) with (Nreal 2) by (simpl; ring).    
    apply Nreal_strict_monotone.
    lia.

    exists (x0)%nat.
    split.
    pose proof (H1 (S x0)).
    assert (j : (S x0 < S (S x0))%nat) by lia.
    apply H2 in j; clear H2.
    apply (fun a => real_lt_lt_lt _ _ _ a j).
    rewrite Nreal_S.
    (* replace (Nreal (x0 + 1)) with (real_1 + Nreal x0). *)
    apply (real_lt_add_r (- Nreal x0 + real_1 / real_2_neq_0)).

    replace (Nreal x0 + (- Nreal x0 + real_1 / real_2_neq_0)) with (real_1 / real_2_neq_0) by ring.
    replace ( real_1 + Nreal x0 - real_1 / real_2_neq_0 + (- Nreal x0 + real_1 / real_2_neq_0)) with real_1 by ring.
    apply real_gt_half, real_1_gt_0.
    apply (real_lt_lt_lt _ _ _  H0).

    replace (Nreal (x0 + 4)) with (Nreal (S (S x0)) + real_1 + real_1).
    apply (real_lt_add_r (- Nreal (S (S x0)))).
    replace ( Nreal (S (S x0)) + real_1 / real_2_neq_0 + - Nreal (S (S x0))) with (real_1 / real_2_neq_0) by ring.
    replace ( Nreal (S (S x0)) + real_1 + real_1 + - Nreal (S (S x0))) with (real_1 + real_1) by ring.
    assert (jj :  real_1 / real_2_neq_0 < real_1) by ( apply real_gt_half, real_1_gt_0).
    pose proof (real_lt_lt_plus_lt _ _ _ _ jj (real_1_gt_0)).
    
    rewrite real_plus_comm, real_plus_unit in H2.
    exact H2.
    replace (x0 + 4)%nat with (S (S (S (S x0)))) by lia.
    replace (Nreal (S (S x0)) + real_1 + real_1) with (real_1 + (real_1 + Nreal (S (S x0)))) by ring.
    rewrite <-  Nreal_S.
    rewrite <-  Nreal_S.
    apply eq_refl.

    assert (x + real_1 > real_0).
    pose proof (real_lt_lt_plus_lt _ _ _ _ H real_1_gt_0).
    rewrite real_plus_unit in H0.
    exact H0.
    pose proof (nat_bound_above (x + real_1) H0).
    destruct H1.
    exists x0.
    apply real_lt_nlt.
    apply (real_lt_plus_lt (- real_1)) in H1.
    replace ( - real_1 + (x + real_1)) with x in H1 by ring.
    apply (real_lt_lt_lt _ _ _ H1).
    apply (real_lt_add_r (real_1 + real_1/real_2_neq_0 - Nreal x0)).
    replace (- real_1 + Nreal x0 + (real_1 + real_1 / real_2_neq_0 - Nreal x0)) with (real_1 / real_2_neq_0) by ring.
    replace (Nreal x0 - real_1 / real_2_neq_0 + (real_1 + real_1 / real_2_neq_0 - Nreal x0)) with real_1 by ring.
    apply real_gt_half, real_1_gt_0.
  Defined.



  Lemma naive_rounding : forall x : Real,  ^M {k  | IZreal k < x < IZreal (k + 4) }.
  Proof.
    intro.
    pose proof (choose (- prec 1 < x < prec 1) (real_0 < x \/ x < real_0)).
    apply (M_lift_dom ({- prec 1 < x < prec 1} + {real_0 < x \/ x < real_0})).
    intro.
    clear X.
    destruct H.
    apply M_unit.
    exists (-1)%Z.
    simpl.
    unfold IZreal.
    unfold IPreal.
    unfold IPreal_2.
    split.
    destruct a.
    
    apply (fun a =>  real_lt_lt_lt _ _ _ a H).
    apply (real_lt_add_r (real_1 + prec 1)).
    replace (- real_1 + (real_1 + prec 1)) with (prec 1) by ring.
    replace ( - prec 1 + (real_1 + prec 1)) with real_1 by ring.
    apply real_gt_half, real_1_gt_0.
    
    destruct a.
    apply (real_lt_lt_lt _ _ _ H0).
    assert (prec 1 < real_1) by (apply real_gt_half, real_1_gt_0).
    apply (real_lt_lt_lt _ _ _ H1).
    replace (real_1 + (real_1 + real_1)) with (Nreal 3) by (simpl; ring).
    replace (real_1 ) with (Nreal 1) by (simpl; ring).
    apply Nreal_strict_monotone; lia.
    pose proof (choose (real_0 < x) (x < real_0)) as X.
    assert (H : semidec (real_0 < x)) by auto with real.
    assert (H0 : semidec (x < real_0)) by auto with real.
    pose proof (X H H0 o).
    clear o X H H0.
    apply M_hprop_elim_f in X0.
    destruct X0.
    pose proof (naive_rounding_pos _ r).
    apply (fun f => M_lift _ _ f X).
    intro.
    clear X; destruct H.
    exists (Z.of_nat x0).
    replace (Z.of_nat x0 + 4)%Z with (Z.of_nat (x0 + 4)).
    rewrite (IZreal_Nreal) in a.
    rewrite (IZreal_Nreal) in a.
    exact a.
    lia.
    assert (real_0 < - x).
    apply (real_lt_add_r x).
    replace (real_0 + x) with x by ring.
    replace (-x + x) with real_0 by ring.
    exact r.
    pose proof (naive_rounding_pos _ H).
    apply (fun f => M_lift _ _ f X).
    intro.
    clear X; destruct H0.
    exists (- Z.of_nat x0 - 4)%Z.
    replace (- Z.of_nat x0 - 4)%Z with (- (Z.of_nat (x0 +4)))%Z by lia.
    replace ((- (Z.of_nat (x0 + 4)) + 4))%Z with (- Z.of_nat x0)%Z by lia. 
    rewrite IZ_asym.
    rewrite IZ_asym.
    destruct a.
    apply (real_lt_plus_lt (x - Nreal (x0 + 4))) in H1.
    replace (x - Nreal (x0 + 4) + - x) with (- Nreal (x0 + 4)) in H1 by ring.
    replace (x - Nreal (x0 + 4) + Nreal (x0 + 4)) with x in H1 by ring.
    apply (real_lt_plus_lt (x - Nreal (x0 ))) in H0.
    replace (x - Nreal (x0 ) + - x) with (- Nreal (x0 )) in H0 by ring.
    replace (x - Nreal (x0 ) + Nreal (x0 )) with x in H0 by ring.
    rewrite (IZreal_Nreal) in H0.
    rewrite (IZreal_Nreal) in H1.
    split; auto.
    intros i j.
    destruct i, j.
    assert (r = r0) by apply irrl.
    rewrite H; auto.
    contradict (real_lt_nlt _ _ r r0).
    contradict (real_lt_nlt _ _ r r0).
    assert (r = r0) by apply irrl.
    rewrite H; auto.
    

    
    apply X.
    apply semidec_and; auto with real.
    apply semidec_or; auto with real.

    destruct (real_total_order x real_0).
    auto.
    destruct H.
    left.
    rewrite H.
    split.
    apply (real_lt_add_r (prec 1)).
    replace (- prec 1 + prec 1) with real_0 by ring.
    replace (real_0 + prec 1) with (prec 1) by ring.
    apply prec_pos.
    apply prec_pos.
    auto.
    

  Defined.
  
  Lemma rounding : forall x : Real,  ^M {k  | IZreal (k - 1) < x < IZreal (k + 1) }.
  Proof.
    intros.
    pose proof (naive_rounding x).
    apply (fun f => M_lift_dom _ _ f X).
    intro.
    destruct H.
    pose proof (choose (IZreal x0 < x < IZreal (x0 + 3)) (IZreal (x0 + 2) < x < IZreal (x0 + 4))).
    assert (semidec (IZreal x0 < x < IZreal (x0 + 3))) by (apply semidec_and; auto with real).
    assert (semidec (IZreal (x0 + 2) < x < IZreal (x0 + 4))) by (apply semidec_and; auto with real).
    assert (IZreal x0 < x < IZreal (x0 + 3) \/ IZreal (x0 + 2) < x < IZreal (x0 + 4)).
    apply overlapping; auto.
    apply IZreal_strict_monotone.
    lia.
    rename H into H1.
    rename X1 into H.
    rename X2 into H0.
    pose proof (X0 H H0 H1); clear X0 H H0 H1.
    apply (fun f => M_lift_dom _ _ f X1).
    intro; clear X1.
    destruct H.
    pose proof (choose (IZreal x0 < x < IZreal (x0 + 2)) (IZreal (x0 + 1) < x < IZreal (x0 + 3))).
    assert (semidec (IZreal x0 < x < IZreal (x0 + 2))) by (apply semidec_and; auto with real).
    assert (semidec (IZreal (x0 + 1) < x < IZreal (x0 + 3))) by (apply semidec_and; auto with real).
    assert (IZreal x0 < x < IZreal (x0 + 2) \/ IZreal (x0 + 1) < x < IZreal (x0 + 3)).
    apply overlapping; auto.
    apply IZreal_strict_monotone.
    lia.
    rename H into H1.
    rename X1 into H.
    rename X2 into H0.
    pose proof (X0 H H0 H1); clear H H0 H1.
    apply (fun f => M_lift_dom _ _ f X1).
    intro; clear X1.
    destruct H.
    apply M_unit.
    exists (x0 + 1)%Z.
    replace (x0 + 1 - 1)%Z with x0 by lia.
    replace (x0 + 1 + 1)%Z with (x0 + 2)%Z by lia.
    exact a1.
    apply M_unit.
    exists (x0 + 2)%Z.
    replace (x0 + 2 - 1)%Z with (x0 + 1)%Z by lia.
    replace (x0 + 2 + 1)%Z with (x0 + 3)%Z by lia.
    exact a1.
    apply M_unit.
    exists (x0 + 3)%Z.
    replace (x0 + 3 - 1)%Z with (x0 + 2)%Z by lia.
    replace (x0 + 3 + 1)%Z with (x0 + 4)%Z by lia.
    exact a0.
  Defined.

  
    
  Lemma M_approx_seq : forall x : Real, forall n,  ^M {z  | dist (prec n * IZreal z) x <= prec n}.
  Proof.
    intros.
    pose proof (rounding (x * Nreal (Npow2 n))).
    apply (fun f => M_lift _ _ f X).
    intro.
    destruct H.
    exists x0.
    apply (proj2   (dist_le_prop (prec n * IZreal x0) x (prec n) )).
    destruct a.
    apply (real_lt_mult_pos_lt _ _ _ (prec_pos n)) in H.
    replace (prec n * (x * Nreal (Npow2 n)))
      with ((prec n * Nreal (Npow2 n)) * x) in H by ring.
    rewrite prec_Npow2_unit in H.
    rewrite real_mult_unit in H.
    replace (IZreal (x0 - 1)) with (IZreal x0 - real_1) in H.
    replace (prec n * (IZreal x0 - real_1)) with (prec n * IZreal x0 - prec n) in H by ring.
    apply (real_lt_plus_lt (-x + prec n)) in H.
    replace (- x + prec n + (prec n * IZreal x0 - prec n)) with (prec n * IZreal x0 - x) in H by ring.
    replace (- x + prec n + x) with (prec n) in H by ring.

    apply (real_lt_mult_pos_lt _ _ _ (prec_pos n)) in H0.
    replace (prec n * (x * Nreal (Npow2 n)))
      with ((prec n * Nreal (Npow2 n)) * x) in H0 by ring.
    rewrite prec_Npow2_unit in H0.
    rewrite real_mult_unit in H0.
    replace (IZreal (x0 + 1)) with (IZreal x0 + real_1) in H0.
    replace (prec n * (IZreal x0 + real_1)) with (prec n * IZreal x0 + prec n) in H0 by ring.
    apply (real_lt_plus_lt (-x - prec n)) in H0.
    replace (- x - prec n + (prec n * IZreal x0 + prec n)) with (prec n * IZreal x0 - x) in H0 by ring.
    replace (- x - prec n + x) with (- prec n) in H0 by ring.
    split; left; auto.
    rewrite IZreal_hom.
    ring.
    replace (x0 - 1)%Z with (x0 + (-1))%Z by lia.
    rewrite IZreal_hom.
    
    ring.
  Defined.

  Definition dyadic_sequence : (nat -> Z) -> (nat -> Real) := fun f n => prec n * IZreal (f n).

  Definition dyadic_M_sequence : (nat -> ^M Z) -> (nat -> ^M ^Real).
  Proof.
    intros f n.
    apply (fun g => M_lift _ _ g (f n)).
    intro z.
    exact (prec n * IZreal z).
  Defined.
  
  Lemma approx_dyadic_sequence : forall x : Real, ^M {f : nat -> Z | is_fast_limit x (dyadic_sequence f)}.
  Proof.
    intros.
    pose proof (M_countable_lift _ (M_approx_seq x)).
    apply (fun f => M_lift _ _ f X).
    intro; clear X.
    exists (fun n => projP1 _ _ (H n)).
    intro n.
    unfold dyadic_sequence.
    destruct (H n).
    simpl.
    rewrite dist_symm.
    exact r.
  Defined.

  Definition converging_dyadic_M_sequence : forall x : Real, {f : nat -> M Z | M_is_fast_cauchy (dyadic_M_sequence f) /\ M_is_fast_limit_all x (dyadic_M_sequence f)}. 
  Proof.
    intros.
    exists (fun n => projP1 _ _ (M_existence_to_all _ _  (M_approx_seq x n))). 
    split.
    simpl.
       
    unfold M_is_fast_cauchy.
    intros.
    
    rewrite M_all_picture_1.
    intro.
    rewrite M_all_picture_1.
    intros.
    unfold dyadic_M_sequence in H, H0.
    pose proof (@M_fun_cont _ _ Z Real (fun z : Z => prec n * IZreal z) (M_projP1 Z (fun z : Z => dist (prec n * IZreal z) x <= prec n) (M_approx_seq x n)) a).
    unfold M_lift in H.
    simpl in H.
    fold M_lift in H.
    rewrite H1 in H; clear H1.

    pose proof (@M_fun_cont _ _ Z Real (fun z : Z => prec m * IZreal z) (M_projP1 Z (fun z : Z => dist (prec m * IZreal z) x <= prec m) (M_approx_seq x m)) a0).
    unfold M_lift in H0.
    simpl in H0.
    fold M_lift in H0.
    rewrite H1 in H0; clear H1.
    destruct H, H0.
    destruct H.
    destruct H0.
    rewrite H1, H2.
    unfold M_projP1 in H.
    pose proof (M_fun_cont  (fun X0 : {x0 : Z | dist (prec n * IZreal x0) x <= prec n} => let (x0, _) := X0 in x0) (M_approx_seq x n) x0).
    fold M_lift in H.
    rewrite H3 in H; clear H3.
    destruct H.
    destruct x2.

    destruct H.
    

    pose proof (M_fun_cont  (fun X0 : {x0 : Z | dist (prec m * IZreal x0) x <= prec m} => let (x0, _) := X0 in x0) (M_approx_seq x m) x1).
    unfold M_projP1 in H0.
    fold M_lift in H0.
    rewrite H4 in H0; clear H4.
    destruct H0.
    destruct x3.
    destruct H0.
    induction H3.
    induction H4.
    clear H0 H.
    rewrite <- H2; rewrite<- H2 in r0.
    rewrite <- H1; rewrite<- H1 in r.
    rewrite dist_symm in r0.
    pose proof (real_le_le_plus_le _ _ _ _  r r0).
    exact (real_le_le_le _ _ _ (real_ge_le _ _ (dist_tri a x a0)) H). 


    intro.
    rewrite M_all_picture_1.
    intro.
    intros.
    unfold dyadic_M_sequence in H.
    rewrite (M_fun_cont (fun z : Z => prec n * IZreal z)) in H.
    destruct H.
    destruct H.
    unfold projP1 in H.
    unfold M_existence_to_all in H.
    unfold M_projP1 in H.
    fold M_lift in H.
    rewrite M_fun_cont in H.
    destruct H.
    destruct H.
    destruct x1.
    induction H1.
    clear H.
    rewrite <- H0 in r.
    rewrite dist_symm.
    exact r.
    
  Defined.
  


    
End rounding.
  
