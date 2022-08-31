(* Prove that all real number instances are equivalent *)

Require Import Real.
Require Import testsearch.
Require Import rounding.
Require Import Psatz.

Lemma Npow2_hom : forall n m, Npow2 (n + m)%nat = ((Npow2 n) * (Npow2 m))%nat.
Proof.
  intros.
  induction n.
  simpl; lia.
  simpl.
  rewrite IHn.
  lia.
Defined.

  
Section RealEquivalent.

Context {typesS : RealTypes} { casofRealS : ComplArchiSemiDecOrderedField_Real typesS }.

#[local] Notation "^K" := (@K typesS) (at level 0).
#[local] Notation "^M" := (@M typesS) (at level 0).
#[local] Notation "^RealS" := (@Real typesS) (at level 0).
#[local] Definition sofRealS := @sofReal typesS casofRealS.
#[local] Notation "^IZrealS" := (@IZreal typesS sofReal) (at level 0).

Context {typesT : RealTypes} { casofRealT : ComplArchiSemiDecOrderedField_Real typesT }.

Context {eqKST : @K typesS = @K typesT}.
Context {eqMST : @M typesS = @M typesT}.
#[local] Notation "^RealT" := (@Real typesT) (at level 0).
#[local] Definition sofRealT := @sofReal typesT casofRealT.
#[local] Notation "^IZrealT" := (@IZreal typesT sofReal) (at level 0).

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

  Add Ring realRing : (@realTheory _ sofRealS ) (constants [IZReal_tac]).
  Add Ring realRing : (@realTheory _ sofRealT ) (constants [IZReal_tac]).


  
  
  (* Context (S T : ComplArchiSemiDecOrderedField). *)
  (* Notation SR := (CarrierField S). *)
  (* Notation TR := (CarrierField T). *)
  
  (* Ltac S_IZReal_tac t := *)
  (*   match t with *)
  (*   | @real_0 SR => constr:(0%Z) *)
  (*   | @real_1 SR => constr:(1%Z) *)
  (*   | @IZreal SR ?u => *)
  (*     match isZcst u with *)
  (*     | true => u *)
  (*     | _ => constr:(InitialRing.NotConstant) *)
  (*     end *)
  (*   | _ => constr:(InitialRing.NotConstant) *)
  (*   end. *)

  (* Add Ring realRing : (realTheory SR) (constants [S_IZReal_tac]). *)

  (* Ltac T_IZReal_tac t := *)
  (*   match t with *)
  (*   | @real_0 TR => constr:(0%Z) *)
  (*   | @real_1 TR => constr:(1%Z) *)
  (*   | @IZreal TR ?u => *)
  (*     match isZcst u with *)
  (*     | true => u *)
  (*     | _ => constr:(InitialRing.NotConstant) *)
  (*     end *)
  (*   | _ => constr:(InitialRing.NotConstant) *)
  (*   end. *)

  (* Add Ring realRing : (realTheory TR) (constants [T_IZReal_tac]). *)


 
  
  Lemma converging_dyadic_sequence_converging :
    forall f : nat -> ^M Z, @M_is_fast_cauchy _ casofRealS (@dyadic_M_sequence _ casofRealS f) -> @M_is_fast_cauchy _ casofRealT (@dyadic_M_sequence _ casofRealT f).
  Proof. 
    intros.
    intros n m.
    rewrite M_all_picture_1.
    intros.
    rewrite M_all_picture_1.
    intros.
    pose proof (H n m).
    rewrite M_all_picture_1 in H2.
    unfold dyadic_M_sequence in H0.
    unfold dyadic_M_sequence in H1.
    rewrite M_fun_cont in H0.
    rewrite M_fun_cont in H1.
    destruct H0.
    destruct H0.
    destruct H1.
    destruct H1.
    induction (eq_sym H3).
    induction (eq_sym H4).
    clear H3 H4.
    assert (@dist _ _ _ _ _ _  Real_S _ _ (prec n * IZreal x) (prec m * IZreal x0) <= (@prec _ _ Real_S _   n) + (@prec _ _ Real_S _ m)).
    pose proof (H2 (prec n * IZreal x)).
    unfold dyadic_M_sequence in H3.
    rewrite M_fun_cont in H3.
    assert (exists a : Z, M_picture_1 (f n) a /\ @prec _ _ Real_S _ n * IZreal x = prec n * IZreal a).
    exists x.
    split; auto.
    pose proof (H3 H4).
    rewrite M_all_picture_1 in H5.
    pose proof (H5 (prec m * IZreal x0)).
    apply H6.
    rewrite M_fun_cont.
    exists x0.
    auto.

    apply (real_le_mult_pos_le (@Nreal _ _ Real_S _ (Npow2 (n + m)%nat)) _ _ (Nreal_Npow2_pos _ )) in H3.
    rewrite (@dist_scale _ _ _ _ _ _ Real_S _ _ (prec n * IZreal x) (prec m * IZreal x0) (Nreal (Npow2 (n + m)%nat)) (Nreal_Npow2_pos _)) in H3.
    rewrite Npow2_hom in H3.
    rewrite Nreal_mult in H3.
    replace (Nreal (Npow2 n) * Nreal (Npow2 m) * (prec n * IZreal x)) with
        (prec n * @Nreal _ _ Real_S _ (Npow2 n) * (Nreal (Npow2 m) * IZreal x)) in H3 by ring. 
    replace (Nreal (Npow2 n) * Nreal (Npow2 m) * (prec m * IZreal x0)) with
        (prec m * @Nreal _ _ Real_S _ (Npow2 m)  * (Nreal (Npow2 n) * IZreal x0)) in H3 by ring.
    
    replace (  Nreal (Npow2 n) * Nreal (Npow2 m) * (prec n + prec m)) with
        ((@prec _ _ Real_S _ n * Nreal (Npow2 n)) * Nreal (Npow2 m) + (prec m * Nreal (Npow2 m) * Nreal (Npow2 n))) in H3 by ring.

    rewrite prec_Npow2_unit in H3.
    rewrite prec_Npow2_unit in H3.
    rewrite real_mult_unit in H3.
    rewrite real_mult_unit in H3.
    rewrite real_mult_unit in H3.
    rewrite real_mult_unit in H3.

    rewrite IZreal_Nreal in H3.
    rewrite IZreal_Nreal in H3.
    rewrite <- IZreal_hom in H3.
    rewrite <- IZreal_mult_hom in H3.
    rewrite <- IZreal_mult_hom in H3.
    rewrite IZreal_dist in H3.
    rewrite IZreal_le in H3.

    rewrite <- (@IZreal_le _ _ Real_T _) in H3.
    rewrite <- IZreal_dist in H3.
    rewrite  IZreal_mult_hom in H3.
    rewrite  IZreal_mult_hom in H3.
    rewrite  IZreal_hom in H3.
    rewrite <- IZreal_Nreal in H3.
    rewrite <- IZreal_Nreal in H3.
    apply (real_le_mult_pos_le ((prec (n + m)%nat)) _ _ (prec_pos _ )) in H3.
    rewrite dist_scale in H3.
    rewrite prec_hom in H3.
    replace  (prec n * prec m * (Nreal (Npow2 m) * IZreal x))  with
         (@prec _ _ Real_T _ m * Nreal (Npow2 m) * prec n * IZreal x) in H3 by ring.
    replace  (prec n * prec m * (Nreal (Npow2 n) * IZreal x0))  with
         (@prec _ _ Real_T _ n * Nreal (Npow2 n) * prec m * IZreal x0) in H3 by ring.
    replace (prec n * prec m * (Nreal (Npow2 m) + Nreal (Npow2 n))) with
        (@prec _ _ Real_T _ m * Nreal (Npow2 m) * prec n + prec n * Nreal (Npow2 n) * prec m) in H3 by ring.
    rewrite prec_Npow2_unit in H3.
    rewrite prec_Npow2_unit in H3.
    rewrite real_mult_unit in H3.
    rewrite real_mult_unit in H3.
    exact H3.
    apply prec_pos.
  Defined.

  
  Definition translate_inj :
    forall a b f g x y,
      M_is_fast_limit_all a (@dyadic_M_sequence _ _ _ _ Real_S _ f) -> 
      M_is_fast_limit_all b (@dyadic_M_sequence _ _ _ _ Real_S _ g) ->
      M_is_fast_limit_all x (@dyadic_M_sequence _ _ _ _ Real_T _ f) -> 
      M_is_fast_limit_all y (@dyadic_M_sequence _ _ _ _ Real_T _ g) ->
      a = b -> x = y.
  Proof.
    intros.
    induction H3.
    apply (proj1  (dist_zero x y)).
    destruct (dist_pos x y); auto.
    pose proof (real_Archimedean _ H3).
    destruct H4 as [p].
    pose proof (M_W_destruct (f (p + 2)%nat)).
    destruct H5.
    pose proof (M_W_destruct (g (p + 2)%nat)).
    destruct H6.
    pose proof (H (p + 2)%nat).
    pose proof (H0 (p + 2)%nat).
    rewrite M_all_picture_1 in H7.
    rewrite M_all_picture_1 in H8.
    assert (dist a (prec (p + 2)%nat * IZreal x0 ) <= prec (p + 2)%nat).
    apply H7.  
    unfold dyadic_M_sequence.
    rewrite M_fun_cont.
    exists x0.
    split; auto.
    assert (dist a (prec (p + 2)%nat * IZreal x1 ) <= prec (p + 2)%nat).
    apply H8.  
    unfold dyadic_M_sequence.
    rewrite M_fun_cont.
    exists x1.
    split; auto.
    clear H7 H8.
    rewrite dist_symm in H10.
    pose proof (real_le_le_plus_le _ _ _ _ H10 H9).
    pose proof (real_le_le_le _ _ _ (real_ge_le _ _ (dist_tri _ _ _ )) H7).
    clear H9 H10 H7.
    pose proof (H1 (p + 2)%nat).
    rewrite M_all_picture_1 in H7.
    assert (dist x (prec (p + 2) * IZreal x0) <= prec (p + 2)).
    apply H7.
    unfold dyadic_M_sequence.
    rewrite M_fun_cont.
    exists x0; auto.
    clear H7.
    pose proof (H2 (p + 2)%nat).
    rewrite M_all_picture_1 in H7.
    assert (dist y (prec (p + 2) * IZreal x1) <= prec (p + 2)).
    apply H7.
    unfold dyadic_M_sequence.
    rewrite M_fun_cont.
    exists x1; auto.
    clear H7.

    (* transporting *)
    assert (
        @dist _ _ _ _ _ _ Real_T _ _  (prec (p + 2) * IZreal x1) (prec (p + 2) * IZreal x0) <= prec (p + 2) + prec (p + 2)
      ).
    clear H5 H6 H9 H10.
    apply (real_le_mult_pos_le (@Nreal _ _ Real_S _ (Npow2 (p + 2)%nat)) _ _ (Nreal_Npow2_pos _ )) in H8.
    rewrite (dist_scale) in H8.
    replace  (Nreal (Npow2 (p + 2)) * (prec (p + 2) * IZreal x1)) with
         (@prec _ _ Real_S _ (p + 2) * Nreal (Npow2 (p + 2)) * IZreal x1) in H8 by ring.
    replace  (Nreal (Npow2 (p + 2)) * (prec (p + 2) * IZreal x0)) with
         (@prec _ _ Real_S _ (p + 2) * Nreal (Npow2 (p + 2)) * IZreal x0) in H8 by ring.
    replace (Nreal (Npow2 (p + 2)) * (prec (p + 2) + prec (p + 2))) with
        (@prec _ _ Real_S _ (p + 2) * Nreal (Npow2 (p + 2)) + prec (p + 2) * Nreal (Npow2 (p + 2))) in H8 by ring.
    
    rewrite prec_Npow2_unit in H8.
    rewrite real_mult_unit in H8.
    rewrite real_mult_unit in H8.
    replace (real_1 + real_1) with (@IZreal _ _ Real_S _ 2) in H8 by ring.
    rewrite IZreal_dist in H8.
    rewrite IZreal_le in H8.
 
    rewrite <- (@IZreal_le _ _ Real_T _ ) in H8.
    rewrite <- IZreal_dist in H8.
    (* replace (IZreal x1) with (@real_1 TR * IZreal x1) in H8 by ring. *)
    (* replace (IZreal x0) with (@real_1 TR * IZreal x0) in H8 by ring. *)
    replace (IZreal 2) with (@real_1 _ _ Real_T _ + real_1) in H8 by ring.
    apply (real_le_mult_pos_le ((prec (p + 2)%nat)) _ _ (prec_pos _ )) in H8.
    rewrite dist_scale in H8.
    replace (prec (p + 2) * (real_1 + real_1)) with (@prec _ _ Real_T _ (p + 2) + prec (p + 2)) in H8 by ring. 
    exact H8.
    apply prec_pos.
    apply Nreal_Npow2_pos.
    (* done *)
    clear H8.
    pose proof (real_le_le_plus_le _ _ _ _ H10 H7).
    pose proof (real_le_le_le _ _ _ (real_ge_le _ _ (dist_tri _ _ _)) H8).
    rewrite dist_symm in H9.
    pose proof (real_le_le_plus_le _ _ _ _ H11 H9).
    pose proof (real_le_le_le _ _ _ (real_ge_le _ _ (dist_tri _ _ _)) H12).
    replace (p + 2)%nat with (p + 1 + 1)%nat in H13 by lia.
    rewrite prec_twice in H13.
    rewrite real_plus_comm in H13.
    rewrite <- real_plus_assoc in H13.
    rewrite prec_twice in H13.
    rewrite prec_twice in H13.
    rewrite dist_symm in H13.
    contradiction (real_gt_nle _ _ H4 H13).
  Defined.
  
  
End RealEquivalent.

Section RealEquivalent2.

  Generalizable Variables K M Real_S Real_T.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
          {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
          {M_MultivalueMonad : MultivalueMonad}
          {Real_S : Type}
          {SemiDecOrderedField_Real_S : SemiDecOrderedField Real_S}
          {ComplArchiSemiDecOrderedField_Real_S : @ComplArchiSemiDecOrderedField _ _ _ SemiDecOrderedField_Real_S}
          {Real_T : Type}
          {SemiDecOrderedField_Real_T : SemiDecOrderedField Real_T}
          {ComplArchiSemiDecOrderedField_Real_T : @ComplArchiSemiDecOrderedField _ _ _ SemiDecOrderedField_Real_T}.

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

  Add Ring realRing : (@realTheory _ _ Real_S _ ) (constants [IZReal_tac]).
  Add Ring realRing : (@realTheory _ _ Real_T _ ) (constants [IZReal_tac]).




  Definition translation : Real_S -> Real_T.
  Proof.
    intros x.
    pose proof (converging_dyadic_M_sequence x).
    destruct X.
    destruct a.

    pose proof (@converging_dyadic_sequence_converging _ _ _ _ _ _ Real_S _ _ Real_T _ _ x0 H).
    pose proof (real_mslimit_all (@dyadic_M_sequence _ _ _ _ Real_T _ x0) H1).
    destruct X.
    exact x1.
  Defined.

  Definition translation_inv : Real_T -> Real_S.
  Proof.
    intros x.
    pose proof (converging_dyadic_M_sequence x).
    destruct X.
    destruct a.
    pose proof (@converging_dyadic_sequence_converging _ _ _ _ _ _  Real_T _ _ Real_S _ _ x0 H).
    pose proof (real_mslimit_all (@dyadic_M_sequence _ _ _ _ Real_S _ x0) H1).
    destruct X.
    exact x1.
  Defined.


  Theorem Reals_equivalent : is_equiv translation.
  Proof.
    exists translation_inv.
    split.
    unfold translation.
    unfold translation_inv.
    unfold id.
    unfold fc.
    apply fun_ext; intro.
    destruct (converging_dyadic_M_sequence x).
    destruct a.
    destruct ( real_mslimit_all (dyadic_M_sequence x0) (@converging_dyadic_sequence_converging _ _ _ _ _ _  Real_S _ _ Real_T _ _ x0 m)).
    destruct ( converging_dyadic_M_sequence x1).
    destruct a.
    destruct (real_mslimit_all (dyadic_M_sequence x2) (@converging_dyadic_sequence_converging _ _ _ _ _ _ Real_T _ _ Real_S _ _ x2 m2)).
    apply eq_sym, (translate_inj x1 x1 x0 x2 x x3 m1 m3 ); auto.

    unfold translation.
    unfold translation_inv.
    unfold id.
    unfold fc.
    apply fun_ext; intro.
    destruct (converging_dyadic_M_sequence x).
    destruct a.
    destruct ( @real_mslimit_all _ _ _ _ _ _ _ _ _ (@dyadic_M_sequence _ _ _ _ Real_S _ x0) (@converging_dyadic_sequence_converging _ _ _ _ _ _ Real_T _ _  Real_S _ _  x0 m)).
    destruct (@converging_dyadic_M_sequence _ _ _ _ _ _ Real_S _ _  x1 ).
    destruct a.
    destruct (@real_mslimit_all _ _ _ _ _ _ _ _ _  (@dyadic_M_sequence _ _ _ _ Real_T _ x2) (@converging_dyadic_sequence_converging _ _ _ _ _ _ Real_S _ _  Real_T _ _ x2 m2)).
    
    apply eq_sym, (translate_inj x1 x1 x0 x2 x x3 m1 m3 ); auto.
  Defined.
  
    
End RealEquivalent2.

   
