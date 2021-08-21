(* Prove that all real number instances are equivalent *)

Require Import Real.
Require Import testsearch.
Require Import rounding.
Require Import Psatz.
        
Section RealEquivalent.
  
  Context (S T : ComplArchiSemiDecOrderedField).
  Notation SR := (CarrierField S).
  Notation TR := (CarrierField T).
  
  Ltac S_IZReal_tac t :=
    match t with
    | @real_0 SR => constr:(0%Z)
    | @real_1 SR => constr:(1%Z)
    | @IZreal SR ?u =>
      match isZcst u with
      | true => u
      | _ => constr:(InitialRing.NotConstant)
      end
    | _ => constr:(InitialRing.NotConstant)
    end.

  Add Ring realRing : (realTheory SR) (constants [S_IZReal_tac]).

  Ltac T_IZReal_tac t :=
    match t with
    | @real_0 TR => constr:(0%Z)
    | @real_1 TR => constr:(1%Z)
    | @IZreal TR ?u =>
      match isZcst u with
      | true => u
      | _ => constr:(InitialRing.NotConstant)
      end
    | _ => constr:(InitialRing.NotConstant)
    end.

  Add Ring realRing : (realTheory TR) (constants [T_IZReal_tac]).

  
  (* Notation real_ := (real SR). *)
  (* Notation real_0_ := (@real_0 SR). *)
  (* Notation real_1_ := (@real_1 SR). *)
  (* Notation prec_ := (@prec SR). *)
  (* Search (nat -> Z). *)
  Set Print Implifit.
    
  Definition translation : real SR -> real TR.
  Proof.
    intros x.
    pose proof (M_approx_seq x).
    assert ({y : real TR | forall n, dist 
    
  Lemma naive_rounding_pos : forall x : real_, x > real_0_ -> M {k  | Nreal k < x < Nreal (k + 4) }.
    intros.
    pose proof (epsilon_smallest_PQ_M (fun n => x < Nreal (n) + prec 1) (fun n => Nreal (n) - prec 1 < x)).
    simpl in X.
    assert ((forall n : nat,
       M ({x < Nreal (n ) + real_1_ / real_2_neq_0} + {Nreal (n ) - real_1_ / real_2_neq_0 < x}))).
    intro.
    apply choose; auto with real.
    pose proof (W_split x (Nreal n) (real_1_ / real_2_neq_0)).
    assert (real_1_ / real_2_neq_0 > real_0).
    pose proof (@prec_pos T (S O)).
    simpl in H1.
    exact H1.
    apply H0 in H1; clear H0.
    destruct H1; auto.
    left.
    apply (real_lt_plus_lt (real_1_ / real_2_neq_0)) in H0.
    replace (real_1_ / real_2_neq_0 + (x - real_1_ / real_2_neq_0)) with x in H0 by ring.
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
    assert (jj :  real_1_ / real_2_neq_0 < real_1_) by ( apply real_gt_half, real_1_gt_0).
    apply (real_lt_lt_lt _ _ _ jj).
    rewrite <- (real_plus_unit real_1_).
    rewrite real_plus_comm.
    fold (@Nreal CR 1).
    apply Nreal_strict_monotone.
    lia.

    destruct x0.
    exists O.
    split; auto.
    apply (real_lt_lt_lt _ _ _ H0).
    assert (jj :  real_1_ / real_2_neq_0 < real_1_) by ( apply real_gt_half, real_1_gt_0).
    apply (real_lt_plus_lt (Nreal 1)) in jj.
    
    apply (real_lt_lt_lt _ _ _ jj).
    replace (Nreal 1 + real_1_) with (@Nreal CR 2) by (simpl; ring).    
    apply Nreal_strict_monotone.
    lia.

    exists (x0)%nat.
    split.
    pose proof (H1 (S x0)).
    assert (j : (S x0 < S (S x0))%nat) by lia.
    apply H2 in j; clear H2.
    apply (fun a => real_lt_lt_lt _ _ _ a j).
    rewrite Nreal_S.
    (* replace (Nreal (x0 + 1)) with (real_1_ + Nreal x0). *)
    apply (real_lt_add_r (- Nreal x0 + real_1_ / real_2_neq_0)).

    replace (Nreal x0 + (- Nreal x0 + real_1_ / real_2_neq_0)) with (real_1_ / real_2_neq_0) by ring.
    replace ( real_1_ + Nreal x0 - real_1_ / real_2_neq_0 + (- Nreal x0 + real_1_ / real_2_neq_0)) with real_1_ by ring.
    apply real_gt_half, real_1_gt_0.
    apply (real_lt_lt_lt _ _ _  H0).

    replace (Nreal (x0 + 4)) with (Nreal (S (S x0)) + real_1 + real_1_).
    apply (real_lt_add_r (- Nreal (S (S x0)))).
    replace ( Nreal (S (S x0)) + real_1_ / real_2_neq_0 + - Nreal (S (S x0))) with (real_1_ / real_2_neq_0) by ring.
    replace ( Nreal (S (S x0)) + real_1_ + real_1_ + - Nreal (S (S x0))) with (real_1_ + real_1) by ring.
    assert (jj :  real_1_ / real_2_neq_0 < real_1_) by ( apply real_gt_half, real_1_gt_0).
    pose proof (real_lt_lt_plus_lt _ _ _ _ jj (real_1_gt_0)).
    
    rewrite real_plus_comm, real_plus_unit in H2.
    exact H2.
    replace (x0 + 4)%nat with (S (S (S (S x0)))) by lia.
    replace (Nreal (S (S x0)) + real_1_ + real_1_) with (real_1_ + (real_1 + Nreal (S (S x0)))) by ring.
    rewrite <-  Nreal_S.
    rewrite <-  Nreal_S.
    apply eq_refl.

    assert (x + real_1_ > real_0).
    pose proof (real_lt_lt_plus_lt _ _ _ _ H real_1_gt_0).
    rewrite real_plus_unit in H0.
    exact H0.
    pose proof (nat_bound_above (x + real_1) H0).
    destruct H1.
    exists x0.
    apply real_lt_nlt.
    apply (real_lt_plus_lt (- real_1)) in H1.
    replace ( - real_1_ + (x + real_1_)) with x in H1 by ring.
    apply (real_lt_lt_lt _ _ _ H1).
    apply (real_lt_add_r (real_1 + real_1_/real_2_neq_0 - Nreal x0)).
    replace (- real_1_ + Nreal x0 + (real_1_ + real_1_ / real_2_neq_0 - Nreal x0)) with (real_1_ / real_2_neq_0) by ring.
    replace (Nreal x0 - real_1_ / real_2_neq_0 + (real_1_ + real_1_ / real_2_neq_0 - Nreal x0)) with real_1_ by ring.
    apply real_gt_half, real_1_gt_0.
  Defined.

  Lemma semidec_and P Q : semidec P -> semidec Q -> semidec (P /\ Q).
  Proof.
    intros.
    destruct H as [k1 e1].
    destruct H0 as [k2 e2].
    exists (kleenean_and k1 k2).
    split; intro p.
    rewrite kleenean_and_up in p.
    destruct p as [H H1].
    split.
    apply proj1 in e1; apply e1, H.
    apply proj1 in e2; apply e2, H1.
    rewrite kleenean_and_up.
    destruct p as [H H1].
    split.
    apply proj2 in e1; apply e1, H.
    apply proj2 in e2; apply e2, H1.
  Defined.

  Lemma naive_rounding : forall x : real_,  M {k  | IZreal k < x < IZreal (k + 4) }.
  Proof.
    intro.
    pose proof (choose (- prec 1 < x < prec 1) (real_0_ < x \/ x < real_0_)).
    apply (M_lift_dom ({- prec_ 1 < x < prec_ 1} + {real_0_ < x \/ x < real_0_})).
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
    apply (real_lt_add_r (real_1_ + prec 1)).
    replace (- real_1_ + (real_1_ + prec_ 1)) with (prec_ 1) by ring.
    replace ( - prec_ 1 + (real_1_ + prec_ 1)) with real_1_ by ring.
    apply real_gt_half, real_1_gt_0.
    
    destruct a.
    apply (real_lt_lt_lt _ _ _ H0).
    assert (prec_ 1 < real_1_) by (apply real_gt_half, real_1_gt_0).
    apply (real_lt_lt_lt _ _ _ H1).
    replace (real_1_ + (real_1_ + real_1_)) with (@Nreal CR 3) by (simpl; ring).
    replace (real_1_ ) with (@Nreal CR 1) by (simpl; ring).
    apply Nreal_strict_monotone; lia.
    pose proof (choose (real_0_ < x) (x < real_0_)).
    assert (semidec (real_0_ < x)) by auto with real.
    assert (semidec (x < real_0_)) by auto with real.
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
    assert (real_0_ < - x).
    apply (real_lt_add_r x).
    replace (real_0_ + x) with x by ring.
    replace (-x + x) with real_0_ by ring.
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
    replace (x - Nreal (x0 + 4) + - x) with (- @Nreal CR (x0 + 4)) in H1 by ring.
    replace (x - Nreal (x0 + 4) + Nreal (x0 + 4)) with x in H1 by ring.
    apply (real_lt_plus_lt (x - Nreal (x0 ))) in H0.
    replace (x - Nreal (x0 ) + - x) with (- @Nreal CR (x0 )) in H0 by ring.
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
    apply (real_lt_add_r (prec_ 1)).
    replace (- prec_ 1 + prec_ 1) with real_0_ by ring.
    replace (real_0_ + prec_ 1) with (prec_ 1) by ring.
    apply prec_pos.
    apply prec_pos.
    auto.
    

  Defined.
  
  Lemma rounding : forall x : real_,  M {k  | IZreal (k - 1) < x < IZreal (k + 1) }.
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

  
    
  Lemma M_approx_seq : forall x : real_, forall n,  M {z  | dist (prec n * IZreal z) x <= prec n}.
  Proof.
    intros.
    pose proof (rounding (x * Nreal (Npow2 n))).
    apply (fun f => M_lift _ _ f X).
    intro.
    destruct H.
    exists x0.
    apply (proj2   (@dist_le_prop T (prec_ n * IZreal x0) x (prec_ n) )).
    destruct a.
    apply (real_lt_mult_pos_lt _ _ _ (@prec_pos T n)) in H.
    replace (prec_ n * (x * Nreal (Npow2 n)))
      with ((prec_ n * Nreal (Npow2 n)) * x) in H by ring.
    rewrite prec_Npow2_unit in H.
    rewrite real_mult_unit in H.
    replace (IZreal (x0 - 1)) with (IZreal x0 - real_1_) in H.
    replace (prec_ n * (IZreal x0 - real_1_)) with (prec_ n * IZreal x0 - prec_ n) in H by ring.
    apply (real_lt_plus_lt (-x + prec_ n)) in H.
    replace (- x + prec_ n + (prec_ n * IZreal x0 - prec_ n)) with (prec_ n * IZreal x0 - x) in H by ring.
    replace (- x + prec_ n + x) with (prec_ n) in H by ring.

    apply (real_lt_mult_pos_lt _ _ _ (@prec_pos T n)) in H0.
    replace (prec_ n * (x * Nreal (Npow2 n)))
      with ((prec_ n * Nreal (Npow2 n)) * x) in H0 by ring.
    rewrite prec_Npow2_unit in H0.
    rewrite real_mult_unit in H0.
    replace (IZreal (x0 + 1)) with (IZreal x0 + real_1_) in H0.
    replace (prec_ n * (IZreal x0 + real_1_)) with (prec_ n * IZreal x0 + prec_ n) in H0 by ring.
    apply (real_lt_plus_lt (-x - prec_ n)) in H0.
    replace (- x - prec_ n + (prec_ n * IZreal x0 + prec_ n)) with (prec_ n * IZreal x0 - x) in H0 by ring.
    replace (- x - prec_ n + x) with (- prec_ n) in H0 by ring.
    split; left; auto.
    rewrite IZreal_hom.
    ring.
    replace (x0 - 1)%Z with (x0 + (-1))%Z by lia.
    rewrite IZreal_hom.
    
    ring.
  Defined.

  Lemma approx_M_seq : forall x : real_, M (forall n,  M {z  | dist (prec n * IZreal z) x <= prec n}.
  Proof.
    intros.
    pose proof (rounding (x * Nreal (Npow2 n))).
    apply (fun f => M_lift _ _ f X).
    intro.
    destruct H.
    exists x0.
    apply (proj2   (@dist_le_prop T (prec_ n * IZreal x0) x (prec_ n) )).
    destruct a.
    apply (real_lt_mult_pos_lt _ _ _ (@prec_pos T n)) in H.
    replace (prec_ n * (x * Nreal (Npow2 n)))
      with ((prec_ n * Nreal (Npow2 n)) * x) in H by ring.
    rewrite prec_Npow2_unit in H.
    rewrite real_mult_unit in H.
    replace (IZreal (x0 - 1)) with (IZreal x0 - real_1_) in H.
    replace (prec_ n * (IZreal x0 - real_1_)) with (prec_ n * IZreal x0 - prec_ n) in H by ring.
    apply (real_lt_plus_lt (-x + prec_ n)) in H.
    replace (- x + prec_ n + (prec_ n * IZreal x0 - prec_ n)) with (prec_ n * IZreal x0 - x) in H by ring.
    replace (- x + prec_ n + x) with (prec_ n) in H by ring.

    apply (real_lt_mult_pos_lt _ _ _ (@prec_pos T n)) in H0.
    replace (prec_ n * (x * Nreal (Npow2 n)))
      with ((prec_ n * Nreal (Npow2 n)) * x) in H0 by ring.
    rewrite prec_Npow2_unit in H0.
    rewrite real_mult_unit in H0.
    replace (IZreal (x0 + 1)) with (IZreal x0 + real_1_) in H0.
    replace (prec_ n * (IZreal x0 + real_1_)) with (prec_ n * IZreal x0 + prec_ n) in H0 by ring.
    apply (real_lt_plus_lt (-x - prec_ n)) in H0.
    replace (- x - prec_ n + (prec_ n * IZreal x0 + prec_ n)) with (prec_ n * IZreal x0 - x) in H0 by ring.
    replace (- x - prec_ n + x) with (- prec_ n) in H0 by ring.
    split; left; auto.
    rewrite IZreal_hom.
    ring.
    replace (x0 - 1)%Z with (x0 + (-1))%Z by lia.
    rewrite IZreal_hom.
    
    ring.
  Defined.
