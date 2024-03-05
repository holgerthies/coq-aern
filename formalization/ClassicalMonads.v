Require Import Base.
Require Import Monad.

(* classical non-empty subset monad *)
Section NonemptyPowersetMonad.
  Definition NPset : Type -> Type := fun A => {P : A ->  Prop | exists x, P x}.
  Definition NPset_fun_map : forall A B (f : A -> B), NPset A -> NPset B.
  Proof.
    intros A B f [x e].
    exists (fun b => exists a, x a /\ b = f a).
    destruct e as [x0 H].
    exists (f x0).
    exists x0.
    auto.
  Defined.

  Definition NPset_functorial_comp : forall A B C (f : A -> B) (g : B -> C),
      NPset_fun_map _ _ (fun x => g (f x)) = fun x => (NPset_fun_map _ _ g) ((NPset_fun_map _ _ f) x).
  Proof.
    intros.
    apply fun_ext.
    intro.
    unfold NPset_fun_map.
    destruct x.
    destruct e.
    simpl.
    apply sigma_eqP2.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    destruct H.
    exists (f x3); auto.
    split.
    exists x3.
    split; auto.
    destruct H; auto.
    destruct H; auto.
    intro.
    destruct H.
    destruct H.
    destruct H.
    exists x4.
    destruct H.
    rewrite H0.
    rewrite H1.
    auto.
  Defined.

  

  Definition NPset_functorial_id :  forall A, (fun x : NPset A => x) = NPset_fun_map A A (fun x => x).
  Proof.
    intros.
    apply fun_ext.
    intro.
    unfold NPset_fun_map.
    destruct x.
    apply sigma_eqP2.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    destruct e.
    exists x0; auto.
    intro.
    destruct H.
    destruct H.
    rewrite H0; auto.
  Defined.
  
  

  
  (* monad has unit and mult *)
  Definition NPset_unit : forall A : Type, A -> NPset A.
  Proof.
    intros.
    exists (fun a => a = X).
    exists X; auto.
  Defined.
  
  Definition NPset_mult : forall A : Type, NPset (NPset A) -> NPset A.
  Proof.
    intros.
    destruct X.
    exists (fun a => exists X, x X /\  projP1 _ _ X a). 
    destruct e.
    destruct x0.
    destruct e.
    exists x1.
    exists (exist _ x0 (ex_intro _ x1 x2)).
    split.
    assert ((exist (fun P : A -> Prop => exists x : A, P x) x0 (ex_intro (fun x : A => x0 x) x1 x2)) = (exist (ex (A:=A)) x0 (ex_intro x0 x1 x2))).
    apply sigma_eqP2; auto.
    rewrite <- H0; auto.
    simpl; auto.
  Defined.
  
  
  (* unit and mult are nat. trans.  *)
  Definition NPset_unit_ntrans : forall A B (f : A -> B) x, (NPset_fun_map A B f) (NPset_unit A x) = NPset_unit B (f x).
  Proof.
    intros.
    unfold NPset_unit.
    unfold NPset_fun_map.
    apply sigma_eqP2.
    apply fun_ext; intro.
    apply Prop_ext.
    intro.
    destruct H.
    destruct H.
    rewrite H in H0.
    exact H0.
    intro.
    rewrite H.
    exists x; auto.
  Defined.
  
  Definition NPset_mult_ntrans : forall A B (f : A -> B) x, NPset_mult B ((NPset_fun_map (NPset A) (NPset B) (NPset_fun_map A B f)) x) = (NPset_fun_map A B f) (NPset_mult A x).
  Proof.
    intros.
    unfold NPset_mult.
    unfold NPset_fun_map.
    destruct x.
    apply sigma_eqP2.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    destruct e.
    destruct x1.
    destruct e.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    destruct x5.
    rewrite H2 in H1.
    simpl in H1.
    destruct H1.
    destruct H1.
    exists x6.
    split; auto.
    exists (exist _ x5 (ex_intro _ x6 H1)).
    simpl.
    split; auto.
    assert ((exist (ex (A:=A)) x5 (ex_intro x5 x6 H1)) = (exist (fun P : A -> Prop => exists x : A, P x) x5 e)).
    apply sigma_eqP2.
    auto.
    rewrite H4; auto.
    intro.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    exists (NPset_fun_map _ _ f x2).
    split.
    exists x2.
    split; auto.
    unfold NPset_fun_map.
    destruct x2.
    simpl.
    exists x1; auto.
  Defined.
  
  (* coherence conditions *)
  Definition NPset_coh1 : forall A x, NPset_mult A (NPset_unit (NPset A) x) = x.
  Proof.
    intros.
    destruct x.
    unfold NPset_mult.
    unfold NPset_unit.
    apply sigma_eqP2.
    apply fun_ext; intro.
    apply Prop_ext.
    intro.
    destruct H.
    destruct x1.
    simpl in H.
    destruct H.
    apply sigma_eqP_pr1 in H.
    rewrite <- H; auto.
    intro.
    exists (exist _ x (ex_intro _ x0 H)).
    simpl.
    split.
    apply sigma_eqP2; auto.
    auto.
  Defined.
  
  Definition NPset_coh2 : forall A x, NPset_mult A (NPset_fun_map A (NPset A) (NPset_unit A)  x) = x.
  Proof.
    intros.
    unfold NPset_mult, NPset_fun_map, NPset, NPset_unit.
    destruct x.
    apply sigma_eqP2.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    rewrite H1 in H0.
    simpl in H0.
    rewrite H0; auto.
    intro.
    
    destruct e.
    exists (exist _ (fun b => b = x0) (ex_intro _ x0 eq_refl)).
    split.
    exists x0.
    split; auto.
    simpl.
    auto.
  Defined.
  
  Definition NPset_coh3 : forall A x, NPset_mult A (NPset_mult (NPset A) x) = NPset_mult A (NPset_fun_map (NPset (NPset A)) (NPset A) (NPset_mult A) x).
  Proof.
    unfold NPset_mult, NPset_mult, NPset, NPset_fun_map.
    intros.
    destruct x.
    apply sigma_eqP2.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    destruct H.
    destruct H.
    destruct H.
    simpl in H.
    destruct x2.
    simpl in H.
    assert (exists a : A, exists X, x2 X /\ projP1 _ _ X  a).
    destruct e0.
    destruct H.
    destruct x1.
    destruct e0.
    destruct x3.
    destruct e0.
    exists x7.
    exists (exist _ x3 (ex_intro _ x7 x8)).
    simpl.
    split; auto.  
    exists (exist _ (fun a => exists X, x2 X /\ projP1 _ _ X a) H1).
    split; auto.
    exists (exist _ x2 e0).
    split; auto.
    destruct H.
    exact H.
    apply sigma_eqP2.
    auto.
    simpl.
    exists x1.
    split; auto.
    destruct H; auto.

    intro.
    repeat destruct H.
    destruct x2.
    destruct x1.
    apply (lp _ _ (projP1 _ _ )) in H1.
    simpl in H1.
    simpl in H0.
    rewrite H1 in H0.
    destruct H0.
    exists x3.
    simpl.
    split; auto.
    exists (exist _ x2 e0).
    simpl.
    split; auto.
    destruct H0; auto.
    destruct H0; auto.
  Defined.

  (* classical nonempty powerest monad *)

  #[global] Instance NPset_Monad : Monad NPset := {
      Monad_fun_map := NPset_fun_map;
      Monad_functorial_comp := NPset_functorial_comp;
      Monad_functorial_id := NPset_functorial_id;
      Monad_unit := NPset_unit;
      Monad_mult := NPset_mult;
      Monad_unit_ntrans := NPset_unit_ntrans;
      Monad_mult_ntrans := NPset_mult_ntrans;
      Monad_coh1 := NPset_coh1;
      Monad_coh2 := NPset_coh2;
      Monad_coh3 := NPset_coh3;
    }.

End NonemptyPowersetMonad.



(* Nabla is classical singletons *)
Section NablaMonad.
  Definition Nabla : Type -> Type := fun A => {P : A -> Prop | exists! a, P a}.
  Definition Nabla_fun_map : forall A B (f : A -> B), Nabla A -> Nabla B.
  Proof.
    intros.
    destruct X.
    exists (fun b => exists a : A, x a /\ b = f a).
    destruct e.
    exists (f x0).
    split.
    exists x0.
    destruct H.
    split; auto.
    intros.
    destruct H0.
    destruct H0.
    destruct H.
    induction (H2 _ H0).
    auto.
  Defined.

  
  Definition Nabla_functorial_comp : forall A B C (f : A -> B) (g : B -> C),
      Nabla_fun_map _ _ (fun x => g (f x)) = fun x => (Nabla_fun_map _ _ g) ((Nabla_fun_map _ _ f) x).
  Proof.
    intros.
    apply fun_ext.
    intro.
    unfold NPset_fun_map.
    destruct x.
    destruct e.
    simpl.
    apply sigma_eqP2.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    destruct H.
    exists (f x2); auto.
    split.
    exists x2.
    split; auto.
    destruct H; auto.
    destruct H; auto.
    intro.
    destruct H.
    destruct H.
    destruct H.
    exists x3.
    destruct H.
    rewrite H0.
    rewrite H1.
    auto.
  Defined.
  
  Definition Nabla_functorial_id :  forall A, (fun x : Nabla A => x) = Nabla_fun_map A A (fun x => x).
  Proof.
    intros.
    apply fun_ext.
    intro.
    (* unfold NPset_fun_map. *)
    destruct x.
    apply sigma_eqP2.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    destruct e.
    exists x0; auto.
    intro.
    destruct H.
    destruct H.
    rewrite H0; auto.
  Defined.
  
  Definition Nabla_unit : forall A : Type, A -> Nabla A.
  Proof.
    intros.
    exists (fun a => a = X).
    exists X.
    split.
    exact (eq_refl _).
    intros.
    induction H.
    exact (eq_refl _).
  Defined.

  Definition Nabla_mult : forall A : Type, Nabla (Nabla A) -> Nabla A.
  Proof.
    intros.
    destruct X.
    
    exists (fun a => x (Nabla_unit A a)).
    destruct e.
    destruct x0.
    destruct e.
    exists x1.
    split.
    destruct u.
    destruct H.
    unfold Nabla_unit.
    assert (
        (exist (fun P : A -> Prop => exists ! a : A, P a) x0
               (ex_intro (unique (fun a : A => x0 a)) x1 (conj x2 e)))
        = 
          (exist (fun P : A -> Prop => exists ! a : A, P a) (fun a : A => a = x1)
                 (ex_intro (unique (fun a : A => a = x1)) x1
                           (conj eq_refl (fun (x' : A) (H1 : x' = x1) => eq_ind x' (fun X : A => X = x') eq_refl x1 H1))))
      ).
    assert (x0 = (fun a : A => a = x1)).
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    pose proof (e _ H1).
    rewrite H2; auto.
    intro.
    rewrite H1.
    exact x2.
    apply (sigma_eqP _ _ _ _ _ _ H1).
    apply irrl.
    rewrite<- H1.
    exact H.

    intros.
    destruct H.
    pose proof (H1 _ H0).
    unfold Nabla_unit in H2.
    pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H2).
    apply (lp _ _ (fun f => f x1)) in H3.
    rewrite <- H3.
    destruct u.
    auto.
  Defined.
  

  Definition Nabla_unit_ntrans : forall A B (f : A -> B) x, (Nabla_fun_map A B f) (Nabla_unit A x) = Nabla_unit B (f x).
  Proof.
    intros.
    apply eq_sym.
    unfold Nabla_fun_map.
    case_eq (Nabla_unit _ x); intros.
    unfold Nabla_unit.
    assert ((fun a : B => a = f x) =  (fun b : B => exists a : A, x0 a /\ b = f a)).
    apply fun_ext.
    intros.
    apply Prop_ext.
    intros.
    exists x.
    split; auto.

    unfold Nabla_unit in H.
    pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H).
    apply (lp _ _ (fun f => f x)) in H1.
    rewrite <- H1; apply eq_refl.
    intro.
    repeat destruct H0.
    rewrite H1; clear H1.
    unfold Nabla_unit in H.
    pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H).
    apply (lp _ _ (fun f => f x)) in H1.
    assert (x0 x) by (rewrite <- H1; apply eq_refl).
    destruct e.
    destruct u.
    pose proof (e _ H0).
    pose proof (e _ H2).
    rewrite <- H3, <- H4.
    auto.
    apply (sigma_eqP _ _ _ _ _ _ H0).
    apply irrl.
  Qed.
  
  Definition Nabla_mult_ntrans : forall A B (f : A -> B) x, Nabla_mult B ((Nabla_fun_map (Nabla A) (Nabla B) (Nabla_fun_map A B f)) x) = (Nabla_fun_map A B f) (Nabla_mult A x).
  Proof.
    intros.
    unfold Nabla_mult.
    unfold Nabla_fun_map.
    destruct x.
    apply sigma_eqP2.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    destruct H.
    destruct H.
    destruct x1.
    destruct e0.
    unfold Nabla_unit in H0.
    apply sigma_eqP_pr1 in H0. 
    apply (lp _ _ (fun g => g x0)) in H0.
    assert ( (exists a : A, x1 a /\ x0 = f a)) by (rewrite <- H0; auto).
    destruct H1.
    exists x3; auto.
    split; auto.
    assert ((Nabla_unit A x3) = (exist (fun P : A -> Prop => exists ! a : A, P a) x1 (ex_intro (unique (fun a : A => x1 a)) x2 u))).
    unfold Nabla_unit.
    apply sigma_eqP2.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    rewrite H2.
    destruct H1; auto.
    intro.
    destruct u.
    destruct H1.
    rewrite <- (e0 _ H1). 
    rewrite <- (e0 _ H2).
    auto.
    rewrite H2; auto.
    destruct H1; auto.
    intro.
    destruct e.
    exists x1.
    destruct H0.
    split; auto.
    destruct x1.
    apply sigma_eqP2.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    rewrite H2.
    destruct H.
    exists x3.
    split; auto.
    destruct H.
    pose proof (H1 _ H).
    apply sigma_eqP_pr1 in H4.
    rewrite H4; auto.
    destruct H; auto.
    intro.
    destruct H2.
    destruct H2.
    rewrite H3.
    destruct H.
    destruct H.
    pose proof (H1 _ H).
    apply sigma_eqP_pr1 in H5.
    rewrite H4.
    apply (lp _ _ (fun g => g x3)) in H5.
    assert (x3 = x4) by (rewrite <- H5; auto).
    rewrite H6; auto.
  Defined.
  

  (* coherence conditions *)
  Definition Nabla_coh1 : forall A x, Nabla_mult A (Nabla_unit (Nabla A) x) = x.
  Proof.
    intros.
    destruct x.
    apply sigma_eqP2.
    apply fun_ext; intro.
    apply Prop_ext.
    intro.
    apply sigma_eqP_pr1 in H.
    apply (lp _ _ (fun g => g x0)) in H.
    rewrite <- H; auto.
    intro.
    apply sigma_eqP2.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    rewrite H0; auto.
    intro.
    destruct e.
    destruct H1.
    rewrite <- (H2 _ H).
    rewrite <- (H2 _ H0).
    auto.
  Defined.


  
  Definition Nabla_coh2 : forall A x, Nabla_mult A (Nabla_fun_map A (Nabla A) (Nabla_unit A)  x) = x.
  Proof.
    intros.
    destruct x.
    apply sigma_eqP2.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    destruct H.
    destruct H.
    apply sigma_eqP_pr1 in H0.
    apply (lp _ _ (fun g => g x0)) in H0.
    assert (x0 = x1) by (rewrite <- H0; auto).
    rewrite H1; auto.
    intro.
    exists x0.
    split; auto.
  Defined.

  Lemma nabla_eq_at : forall A (a b : Nabla A), projP1 _  _ a = projP1 _ _ b -> a = b.
  Proof.
    intros.
    destruct a, b.
    simpl in H.
    apply (sigma_eqP _ _ _ _ _ _ H).
    apply irrl.
  Qed.

  Definition Nabla_unit_mult_inverse : forall A, (forall x : Nabla A, Nabla_mult _ (Nabla_unit _ x) = x) /\
                                                   (forall x : Nabla (Nabla A), Nabla_unit _ (Nabla_mult _ x) = x).
  Proof.
    intro.
    split.
    intro.
    apply nabla_eq_at.
    simpl.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    rewrite <- H.
    simpl.
    exact eq_refl.
    intro.
    destruct x.
    simpl in H.
    destruct e.
    destruct u.
    pose proof (e _ H).
    induction H0.
    apply nabla_eq_at.
    simpl.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    induction H0.
    exact H.
    intro.
    rewrite (e _ H0); auto.


    intro.
    apply nabla_eq_at.
    simpl.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    rewrite H.
    
    destruct x.
    
    destruct e.
    destruct u.
    assert (x1 = (Nabla_mult A
                             (exist (fun P : Nabla A -> Prop => exists ! a : Nabla A, P a) x
                                    (ex_intro (unique (fun a : Nabla A => x a)) x1 (conj x2 e))))).
    simpl.
    apply nabla_eq_at.
    simpl.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    destruct x1.
    simpl in H0.
    destruct e0.
    destruct u.
    pose proof (e0 _ H0).
    induction H1.
    assert (
        (exist (fun P : A -> Prop => exists ! a : A, P a) x1
               (ex_intro (unique (fun a : A => x1 a)) x4 (conj x5 e0)))
        =
          Nabla_unit A x4).
    apply nabla_eq_at.
    simpl.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    pose proof (e0 _ H1).
    rewrite (H2).
    apply eq_refl.
    intro.
    rewrite H1.
    exact H0.
    clear H.
    rewrite H1 in x2.
    exact x2.
    intro.
    clear H.
    destruct x1.
    simpl.
    destruct e0.
    destruct u.
    assert (
        (exist (fun P : A -> Prop => exists ! a : A, P a) x1
               (ex_intro (unique (fun a : A => x1 a)) x4 (conj x5 e0)))
        =
          
          (Nabla_unit A x3)).
    apply nabla_eq_at.
    simpl.
    apply fun_ext.
    intro.
    apply Prop_ext.

    intro.
    pose proof ( e _ H0).
    pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H1).
    apply (lp _ _ (fun k => k x3)) in H2.
    assert (x1 x3) by (rewrite H2; auto).
    pose proof (e0 _ H3).
    pose proof (e0 _  H).
    rewrite <- H4, <- H5.
    auto.

    intro.
    rewrite H.
    pose proof ( e _ H0).
    pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H1).
    rewrite H2.
    auto.
    
    pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H).
    rewrite H1.
    auto.
    rewrite <- H0.
    simpl.
    exact x2.

    intros.
    destruct x.
    simpl in H.
    apply nabla_eq_at.
    simpl.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    assert (x0 = (Nabla_unit A x1)).
    apply nabla_eq_at.
    simpl.
    apply fun_ext.
    intros.
    apply Prop_ext.
    intros.
    destruct x0.
    simpl in H0, H1.
    destruct e0.
    destruct u.
    pose proof (e0 _ H0).

    pose proof (e0 _ H1).
    induction H2.
    induction H3.
    auto.

    intros.
    destruct x0.
    simpl.
    simpl in H, H0.
    rewrite H1.
    exact H0.
    rewrite <- H1.
    exact H.

    intro.
    destruct x0.
    simpl.
    destruct e0.
    destruct u.
    destruct e.

    destruct H1.
    pose proof (H2 _ H0).
    pose proof (H2 _ H).
    rewrite H3 in H4.
    pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H4).
    apply (lp _ _ (fun l => l x1)) in H5.
    rewrite <- H5.
    auto.
  Defined.

  Definition Nabla_coh3 : forall A x, Nabla_mult A (Nabla_mult (Nabla A) x) = Nabla_mult A (Nabla_fun_map (Nabla (Nabla A)) (Nabla A) (Nabla_mult A) x).
  Proof.
    intros.
    destruct x.
    apply sigma_eqP2.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    exists (Nabla_unit _ (Nabla_unit _ x0)).
    split; auto.
    apply sigma_eqP2.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    rewrite H0; auto.
    intro.
    apply sigma_eqP_pr1 in H0.
    apply (lp _ _ (fun g => g x1)) in H0.
    rewrite <- H0; auto.
    intro.
    destruct H.
    destruct H.
    rewrite H0.
    assert ((Nabla_unit (Nabla A) (Nabla_mult A x1)) = x1).
    apply (proj2   (Nabla_unit_mult_inverse A)).
    rewrite H1; auto.
  Defined.
  

  Lemma test : forall P : Prop, Nabla P -> P.
  Proof.
    intros.
    destruct X.
    destruct e.
    exact x0.
  Defined.

  Lemma Props_are_modal : forall P : Prop, is_equiv (Nabla_unit P).
  Proof.
    intros.
    exists (test P).
    unfold fc, id; split.
    apply fun_ext.
    intro.
    apply irrl.
    apply fun_ext; intro.
    apply nabla_eq_at.
    simpl.
    destruct x.
    simpl.
    destruct e.
    apply fun_ext; intro.
    apply Prop_ext; intro.

    induction H.
    destruct u; auto.
    destruct u.
    induction (H1 _ H); auto.
  Defined.

  #[global] Instance Nabla_Monad : Monad Nabla := {
      Monad_fun_map := Nabla_fun_map;
      Monad_functorial_comp := Nabla_functorial_comp;
      Monad_functorial_id := Nabla_functorial_id;
      Monad_unit := Nabla_unit;
      Monad_mult := Nabla_mult;
      Monad_unit_ntrans := Nabla_unit_ntrans;
      Monad_mult_ntrans := Nabla_mult_ntrans;
      Monad_coh1 := Nabla_coh1;
      Monad_coh2 := Nabla_coh2;
      Monad_coh3 := Nabla_coh3;
    }.

End NablaMonad.


(* Let us construct more convenient operations related to the 
   Nabla monad *)
Section SomeMoreNabla.
  Definition Nabla_lift_binary  A B C (f : A -> B -> C) : Nabla A -> Nabla B -> Nabla C.
  Proof.
    intros.
    destruct X.
    destruct X0.
    exists (fun c => exists a b, x a /\ x0 b  /\ c = f a b ).
    destruct e, e0.
    exists (f x1 x2).
    split.
    exists x1.
    exists x2.
    destruct H, H0.
    repeat split; auto.

    intros.
    destruct H, H0, H1.
    destruct H1.
    destruct H1.
    destruct H4.
    induction (H2 _ H1).
    induction (H3 _ H4).
    auto.
  Defined.

  Definition Nabla_bind_binary  A B C (f : A -> B -> Nabla C) : Nabla A -> Nabla B -> Nabla C.
  Proof.
    intros.
    apply Nabla_mult.
    apply (Nabla_lift_binary _ _ _ f).
    exact X.
    exact X0.
  Defined.
  
  Lemma Nabla_lift_binary_commute : forall A B C (f : A -> B -> C) x y,
      Nabla_unit _ (f x y) = Nabla_lift_binary _ _ _ f (Nabla_unit _ x) (Nabla_unit _ y).
  Proof.
    intros.
    unfold Nabla_lift_binary.
    case_eq (Nabla_unit _ x); intros.
    case_eq (Nabla_unit _ y); intros.
    unfold Nabla_unit.
    
    assert ( (fun a : C => a = f x y) = (fun c : C => exists (a : A) (b : B), x0 a /\ x1 b /\ c = f a b)).
    apply fun_ext.
    intros.
    apply Prop_ext.
    intro.
    exists x.
    exists y.

    unfold Nabla_unit in H.
    pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H). 
    unfold Nabla_unit in H0.
    pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H0). 
    
    apply (lp _ _ (fun f => f x)) in H2.
    apply (lp _ _ (fun f => f y)) in H3.
    rewrite <- H2.
    rewrite <- H3.
    
    repeat split; auto.
    intro.
    repeat destruct H1.
    destruct H2.
    rewrite H3; clear H3.
    
    unfold Nabla_unit in H.
    pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H). 
    unfold Nabla_unit in H0.
    pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H0). 
    apply (lp _ _ (fun f => f x)) in H3.
    apply (lp _ _ (fun f => f y)) in H4.
    assert (x0 x) by (rewrite<- H3; apply eq_refl).
    assert (x1 y) by (rewrite<- H4; apply eq_refl).
    clear H3 H4.
    destruct e, e0.
    destruct u, u0.
    pose proof (e _ H1).
    pose proof (e _ H5).
    pose proof (e0 _ H2).
    pose proof (e0 _ H6).
    rewrite <- H8, <- H7, <- H4,<- H3.
    apply eq_refl.
    apply (sigma_eqP _ _ _ _ _ _ H1).
    apply irrl.
  Qed.
  

  Definition Nabla_bind {X} {Y} (f : X -> Nabla Y) : Nabla X -> Nabla Y.
  Proof.
    intro.
    apply Nabla_mult.
    apply (Nabla_fun_map _ _ f).
    exact X0.
  Defined.
  
  
  Definition Nabla_bind2 {X} {Y} (x : Nabla X) (f : X -> Nabla Y) :  Nabla Y.
  Proof.
    apply Nabla_mult.
    apply (Nabla_fun_map _ _ f).
    exact x.
  Defined.
  
  Definition Nabla_unit_surjective {X} : forall x : Nabla X, exists t : X, x = Nabla_unit _ t.
  Proof.
    intros.
    destruct x.
    destruct e.
    exists x0.
    unfold Nabla_unit.
    assert (x =(fun a : X => a = x0)).
    apply fun_ext.
    intros.
    apply Prop_ext.
    intro.
    destruct u.
    rewrite (H1 _ H); auto.
    intro.
    destruct u.
    rewrite H; auto.
    apply (sigma_eqP (X -> Prop)  (fun P : X -> Prop => exists ! a : X, P a) _ _  (ex_intro (unique (fun a : X => x a)) x0 u) (ex_intro (unique (fun a : X => a = x0)) x0 (conj eq_refl (fun (x' : X) (H0 : x' = x0) => eq_ind x' (fun X0 : X => X0 = x') eq_refl x0 H0))) H).
    apply irrl.
  Defined.
  
  
  
  Lemma Nabla_unit_mono : forall A (x y : A), Nabla_unit _ x = Nabla_unit _ y -> x = y.
  Proof.
    intros.
    apply sigma_eqP_pr1 in H.
    
    apply (lp _ _  (fun f => f x)) in H.
    induction H.
    apply eq_refl.
  Defined.


End SomeMoreNabla.


(* Nabla is classical monad as it is a double negation sheafification monad.
   In other words, for any subsingleton P, (even if it is not in Prop)
   for any type [A : Type], [Nabla A] sees [P] and its classical version 
   [not (not P)] identically in the sense that there is equivalence
   between [not (not P) -> Nabla A] and [P -> Nabla A].
   That means in order to construct a classical element [t : Nabla A],
   for any constructive propositoin [P], we can assume it even when 
   we only have its classical evidence [not (not P)].
   A frequent example is when [P] is [(A + not A) : Type] for [A : Prop]. 
   Since [not (not (A + not A))] is provable for any proposition [A], 
   that means we can always do case distinction on [A] or [not A]
   when we construct a classical element. 
 *)
Section NablaIsClassical.
  Definition neg A := A -> False.

  Lemma Prop_dn_elim : forall P : Prop, neg (neg P) -> P.
  Proof.
    intros.
    destruct (lem P); auto.
    contradict (H H0).
  Defined.
  
  Lemma hprop_Nabla_hprop : forall P, is_hprop P -> is_hprop (Nabla P).
  Proof.
    intros.
    intros [p1 h1] [p2 h2].
    assert (p1 = p2).
    apply fun_ext.
    intros.
    apply Prop_ext.
    intro.
    destruct h2.
    destruct H1.
    rewrite (H x x0).
    exact H1.
    intro.
    destruct h1.
    destruct H1.
    rewrite (H x x0).
    exact H1.
    destruct H0.
    assert (h1 = h2).
    apply irrl.
    destruct H0.
    auto.
  Defined.
  
  Lemma False_hprop : is_hprop False.
  Proof.
    intros x y.
    contradict x.
  Defined.

  Definition dn_lift {A B} (f : A -> B) : neg (neg A) -> neg (neg B).
  Proof.
    intros.
    
    intro.
    exact (H (fun a : A => H0 (f a))).
  Defined.

  Definition dn_unit {A} : A -> neg (neg A).
  Proof.
    intros.
    intro.
    exact (H X).
  Defined.
  
  Lemma dn_hprop : forall P, is_hprop (neg (neg P)).
  Proof.
    intros.
    intros x y.
    apply fun_ext.
    intros.
    apply False_hprop.
  Defined.
  
  
  Definition Nabla_dn_precompose : forall P A, is_hprop P -> (neg (neg P) -> Nabla A) -> P -> Nabla A
    := fun P A h f x => f (dn_unit x).

  (* . *)
  (* Proof. *)
    
  (*   intros P A h f x. *)
  (*   exact ( *)
  (*   apply X. *)
  (*   intro. *)
  (*   exact (H0 X0). *)
  (* Defined. *)
  
  Definition Nabla_dn_extend : forall P A, is_hprop P -> (P -> Nabla A) -> (neg (neg P) -> Nabla A).
  Proof.
    intros.
    apply (Nabla_bind X).
    clear X A.
    exists (fun p : P => True).
    destruct (lem (exists p : P, True)).
    destruct H1.
    exists x.
    split.
    auto.
    intros.
    apply H.
    assert (forall p : P, False).
    intro.
    contradict H1.
    exists p; auto.
    contradict (H0 H2).
  Defined.
  
  Lemma Nabla_dn_sheaf_1 : forall P A h x, 
      Nabla_dn_precompose P A h (Nabla_dn_extend P A h x) = x.
  Proof.
    intros.
    apply fun_ext.
    intro.
    unfold Nabla_dn_extend.
    unfold Nabla_bind.
    unfold Nabla_dn_precompose.
    destruct (lem (exists _ : P, True)).
    destruct e.
    induction (h x0 x1).
    assert ((exist (fun P0 : P -> Prop => exists ! a : P, P0 a) (fun _ : P => True)
                   (ex_intro (unique (fun _ : P => True)) x0 (conj t (fun (x' : P) (_ : True) => h x0 x')))) = Nabla_unit _ x0).
    apply hprop_Nabla_hprop.
    exact h.
    rewrite H.
    rewrite Nabla_unit_ntrans.
    rewrite Nabla_coh1.
    exact eq_refl.
    contradict n.
    exists x0; auto.
  Defined.
  
  Lemma Nabla_dn_sheaf_2 : forall P A h x, 
      Nabla_dn_extend P A h (Nabla_dn_precompose P A h x) = x.
  Proof.
    intros.
    apply fun_ext.
    intros.
    unfold Nabla_dn_extend.
    unfold Nabla_bind.
    unfold Nabla_dn_precompose.
    destruct (lem (exists _ : P, True)).
    destruct e.
    assert ((exist (fun P0 : P -> Prop => exists ! a : P, P0 a) (fun _ : P => True)
                   (ex_intro (unique (fun _ : P => True)) x1 (conj t (fun (x' : P) (_ : True) => h x1 x')))) = Nabla_unit _ x1).
    apply hprop_Nabla_hprop.
    exact h.
    rewrite H.
    rewrite Nabla_unit_ntrans.
    rewrite Nabla_coh1.
    unfold dn_unit.
    rewrite (dn_hprop P  (fun H0 : neg P => H0 x1) x0).
    apply eq_refl.
    contradict n.
    destruct (lem (neg P)).
    contradict (x0 H).
    apply Prop_dn_elim.
    apply (dn_lift (fun p : P => ex_intro _ p I)). 
    exact x0.
  Defined.

  Lemma dn_lem : forall A, neg (neg (A + neg A)).
  Proof.
    intros.
    intro p.
    assert (neg A).
    intro.
    assert (A + neg A).
    left; auto.
    exact (p X0).
    assert (A + neg A).
    right; auto.
    exact (p X).
  Defined.     

  Definition Nabla_hprop_lem {A} : forall P, is_hprop P -> ((P + neg P) -> Nabla A) -> Nabla A.
  Proof.
    intros P h f.
    apply (Nabla_dn_extend (P + neg P) A).
    intros x y.
    destruct x, y.
    rewrite (h p p0); auto.
    contradict (n p).
    contradict (n p).
    assert (n = n0).
    apply fun_ext.
    intro.
    contradict (n x).
    rewrite H; auto.
    exact f.
    apply dn_lem.
  Defined.

  Definition Nabla_dn_extend_reduce :
    forall P A (h : is_hprop P) (f : P -> Nabla A) (t : P),
      Nabla_dn_extend P A h f (dn_unit t) = f t.
  Proof.
    intros.
    pose proof (Nabla_dn_sheaf_1 P A h f).
    unfold Nabla_dn_precompose in H.
    apply (lp _ _ (fun f => f t)) in H.  
    exact H.
  Defined.

  Definition Nabla_hprop_lem_reduce A P (h : is_hprop P) :
    forall (f : ((P + neg P) -> Nabla A)) t,
      @Nabla_hprop_lem A P h f = f t.
  Proof.
    intros.
    unfold Nabla_hprop_lem.
    assert (dn_lem P = dn_unit t) by apply irrl.
    rewrite H.
    rewrite Nabla_dn_extend_reduce.
    apply eq_refl.
  Defined.

  
  Definition Nabla_hprop_lem_reduce_eq A P (h : is_hprop P) :
    forall (f : ((P + neg P) -> Nabla A)) y,
      (forall t : P, f (inl t) = y) ->  (forall t : neg P, f (inr t) = y) ->
      @Nabla_hprop_lem A P h f = y.
  Proof.
    intros.
    apply Prop_dn_elim.
    pose proof (dn_lem P).
    apply (@dn_lift (P + neg P) _ ).
    intro.
    rewrite (Nabla_hprop_lem_reduce _ _ _ _ X).
    destruct X.
    auto.
    auto.
    auto.
  Defined.
    
  Definition Nabla_Prop_lem {A} : forall P : Prop, ((P + ~ P) -> Nabla A) -> Nabla A.
  Proof.
    intro P.
    assert (is_hprop P).
    intros x y.
    apply irrl.
    apply Nabla_hprop_lem.
    exact H.
  Defined.

  
  
End NablaIsClassical.
