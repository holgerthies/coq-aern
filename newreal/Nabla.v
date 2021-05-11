Require Import Base.

Module Nabla.

  (* Nabla is a idempotent monad *)
  Definition nabla (A : Type) := {P : A -> Prop | exists! a, P a}.
  Definition nabla_unit (A : Type) : A -> nabla A.
  Proof.
    intro.
    exists (fun a => a = X).
    exists X.
    split.
    exact (eq_refl _).
    intros.
    induction H.
    exact (eq_refl _).
  Defined.

  Definition nabla_mult (A : Type) : nabla (nabla A) -> nabla A.
  Proof.
    intro.
    destruct X.
    
    exists (fun a => x (nabla_unit A a)).
    destruct e.
    destruct x0.
    destruct e.
    exists x1.
    split.
    destruct u.
    destruct H.
    unfold nabla_unit.
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
    apply (sewonsewonp _ _ _ _ _ _ H1).
    apply irrl.
    rewrite<- H1.
    exact H.

    intros.
    destruct H.
    pose proof (H1 _ H0).
    unfold nabla_unit in H2.
    pose proof (sewon_sewonp _ _ _ _ _ _ H2).
    apply (lp _ _ (fun f => f x1)) in H3.
    rewrite <- H3.
    destruct u.
    auto.
  Defined.

  Lemma nabla_eq_at : forall A (a b : nabla A), projP1 _  _ a = projP1 _ _ b -> a = b.
  Proof.
    intros.
    destruct a, b.
    simpl in H.
    apply (sewonsewonp _ _ _ _ _ _ H).
    apply irrl.
  Qed.
  
  Definition nabla_is_modal : forall A, is_equiv (nabla_unit (nabla A)).
  Proof.
    intros.
    exists (nabla_mult A).
    unfold fc, id.
    split.


    apply fun_ext.
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


    apply fun_ext.
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
    assert (x1 = (nabla_mult A
       (exist (fun P : nabla A -> Prop => exists ! a : nabla A, P a) x
          (ex_intro (unique (fun a : nabla A => x a)) x1 (conj x2 e))))).
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
        nabla_unit A x4).
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
        
        (nabla_unit A x3)).
    apply nabla_eq_at.
    simpl.
    apply fun_ext.
    intro.
    apply Prop_ext.

    intro.
    pose proof ( e _ H0).
    pose proof (sewon_sewonp _ _ _ _ _ _ H1).
    apply (lp _ _ (fun k => k x3)) in H2.
    assert (x1 x3) by (rewrite H2; auto).
    pose proof (e0 _ H3).
    pose proof (e0 _  H).
    rewrite <- H4, <- H5.
    auto.

    intro.
    rewrite H.
    pose proof ( e _ H0).
    pose proof (sewon_sewonp _ _ _ _ _ _ H1).
    rewrite H2.
    auto.
    
    pose proof (sewon_sewonp _ _ _ _ _ _ H).
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
    assert (x0 = (nabla_unit A x1)).
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
    pose proof (sewon_sewonp _ _ _ _ _ _ H4).
    apply (lp _ _ (fun l => l x1)) in H5.
    rewrite <- H5.
    auto.
  Defined.
  
     
    

  Definition transport_fiber (A : Type) : (A -> Prop) -> (nabla A -> Prop).
  Proof.
    intros.
    exact (forall x, nabla_unit _  x = X0 -> X x).
  Defined.

  Definition transport_forall : forall A P,  (forall a : nabla A, transport_fiber A P a) -> forall a : A, P a.
  Proof.
    intros.
    unfold transport_fiber in H.
    apply (H (nabla_unit _ a)).
    apply eq_refl.
  Defined.

    
  
  Definition transport_eq : forall A (a b : A), nabla_unit _ a = nabla_unit _ b -> a = b.
  Proof.
    intros.
    unfold nabla_unit in H.
    pose proof (sewon_sewonp _ _ _ _ _ _ H).
    apply (lp _ _ (fun f => f a)) in H0.
    induction H0.
    apply eq_refl.
  Defined.


  Definition lift_unary  A B (f : A -> B) : nabla A -> nabla B.
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

  Definition lift_binary  A B C (f : A -> B -> C) : nabla A -> nabla B -> nabla C.
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

  Lemma lift_binary_commute : forall A B C (f : A -> B -> C) x y,
      nabla_unit _ (f x y) = lift_binary _ _ _ f (nabla_unit _ x) (nabla_unit _ y).
  Proof.
    intros.
    unfold lift_binary.
    case_eq (nabla_unit _ x); intros.
    case_eq (nabla_unit _ y); intros.
    unfold nabla_unit.
    
    assert ( (fun a : C => a = f x y) = (fun c : C => exists (a : A) (b : B), x0 a /\ x1 b /\ c = f a b)).
    apply fun_ext.
    intros.
    apply Prop_ext.
    intro.
    exists x.
    exists y.

    unfold nabla_unit in H.
    pose proof (sewon_sewonp _ _ _ _ _ _ H). 
    unfold nabla_unit in H0.
    pose proof (sewon_sewonp _ _ _ _ _ _ H0). 
   
    apply (lp _ _ (fun f => f x)) in H2.
    apply (lp _ _ (fun f => f y)) in H3.
    rewrite <- H2.
    rewrite <- H3.
    
    repeat split; auto.
    intro.
    repeat destruct H1.
    destruct H2.
    rewrite H3; clear H3.
    
    unfold nabla_unit in H.
    pose proof (sewon_sewonp _ _ _ _ _ _ H). 
    unfold nabla_unit in H0.
    pose proof (sewon_sewonp _ _ _ _ _ _ H0). 
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
    apply (sewonsewonp _ _ _ _ _ _ H1).
    apply irrl.
  Qed.
  
  Lemma lift_unary_commute : forall A B (f : A -> B) x, nabla_unit _ (f x) = lift_unary _ _ f (nabla_unit _ x).
  Proof.
    intros.
    unfold lift_unary.
    case_eq (nabla_unit _ x); intros.
    unfold nabla_unit.
    assert ((fun a : B => a = f x) =  (fun b : B => exists a : A, x0 a /\ b = f a)).
    apply fun_ext.
    intros.
    apply Prop_ext.
    intros.
    exists x.
    split; auto.

    unfold nabla_unit in H.
    pose proof (sewon_sewonp _ _ _ _ _ _ H).
    apply (lp _ _ (fun f => f x)) in H1.
    rewrite <- H1; apply eq_refl.
    intro.
    repeat destruct H0.
    rewrite H1; clear H1.
    unfold nabla_unit in H.
    pose proof (sewon_sewonp _ _ _ _ _ _ H).
    apply (lp _ _ (fun f => f x)) in H1.
    assert (x0 x) by (rewrite <- H1; apply eq_refl).
    destruct e.
    destruct u.
    pose proof (e _ H0).
    pose proof (e _ H2).
    rewrite <- H3, <- H4.
    auto.
    apply (sewonsewonp _ _ _ _ _ _ H0).
    apply irrl.
  Qed.
    
    
  
  Definition lift_domain_unary A B (f : A -> B) (e : is_equiv (nabla_unit B)) : nabla A -> B.
  Proof.
    destruct e.
    intro.
    apply x.
    exact (lift_unary A B f X).
  Defined.

  Definition lift_domain_binary A B C (f : A -> B -> C) (e : is_equiv (nabla_unit C)) : nabla A -> nabla B -> C.
  Proof.
    destruct e.
    intros.
    apply x.
    exact (lift_binary A B C f X X0).
  Defined.

  (* Definition fancy_lift_unary_tmp  A B : forall x : nabla A, (forall z : A, x = nabla_unit A z -> B) -> (B -> Prop). *)
  (* Proof. *)
  (*   intros. *)
  (*   exact (   *)
  (*   destruct x. *)
  (*   exists  *)
  (*   destruct e. *)
    
  Lemma nabla_mono : forall A (x y : A), nabla_unit _ x = nabla_unit _ y -> x = y.
  Proof.
    intros.
    apply sewon_sewonp in H.
    
    apply (lp _ _  (fun f => f x)) in H.
    induction H.
    apply eq_refl.
  Defined.


  
  Definition fancy_lift_unary  A B : forall x : nabla A, (forall z : A, x = nabla_unit A z -> B) -> nabla  B.
  Proof.

    intros.
    exists (fun b => forall (a : A) (p : x = nabla_unit A a), b = X a p).  

    destruct x.

    destruct e.
    destruct u.
    assert ( exist (fun P : A -> Prop => exists ! a : A, P a) x (ex_intro (unique (fun a : A => x a)) x0 (conj x1 e)) = nabla_unit A x0).
    apply nabla_eq_at.
    simpl.
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    rewrite (e _ H); auto.
    intro.
    rewrite H; exact x1.
    exists (X _ H).
    split.

    intros.
    assert (x0 = a).
    rewrite H in p.
    apply nabla_mono in p.
    exact p.
    induction H0.
    assert (H = p) by apply irrl.
    rewrite H0.
    apply eq_refl.


    intros.
    apply eq_sym.
    apply H0.
  Defined.
  
  

  Definition transport_ex : forall A P, (nabla {x : nabla A | transport_fiber _ P x}) -> nabla {x | P x}.
  Proof.
    intros.
    unfold transport_fiber in X.
    apply (lift_domain_unary  {x : nabla A | forall x0 : A, nabla_unit A x0 = x -> P x0}  _).
    intro.
    destruct X0.
    apply (fancy_lift_unary _ _ x).
    intros.
    exists z.
    apply p.
    rewrite H; auto.
    apply nabla_is_modal.
    apply X.
  Defined.
  


  Lemma nabla_unit2 : forall A (x y : nabla A),(forall a b, ((x = nabla_unit _ a) /\ (y = nabla_unit _ b)) -> a = b) ->  (x = y).
  Proof.
    intros.
    

    
    destruct x, y.
    destruct e, e0.
    assert (x1 = x2).
    pose proof (H x1 x2).
    apply H0.
    split.
    apply nabla_eq_at.
    simpl.
    apply fun_ext.
    intros.
    apply Prop_ext.
    intro.
    destruct u.
    pose proof (e _ H1).
    rewrite H2; auto.
    intro.
    induction H1.
    destruct u.
    exact x1.
    apply nabla_eq_at.
    simpl.
    apply fun_ext.
    intros.
    apply Prop_ext.
    intro.
    destruct u0.
    pose proof (e _ H1).
    rewrite H2; auto.
    intro.
    induction H1.
    destruct u0.
    exact x2.
    assert (x = x0).
    apply fun_ext.
    intro.
    destruct u, u0.
    apply Prop_ext; intro.
    
    induction (e _ H1).
    induction H0.
    exact x5.

    induction (e0 _ H1).
    induction H0.
    exact x4.
    
    
    apply (sewonsewonp _ _ _ _ _ _ H1).
    apply irrl.
  Qed.
  

  Definition nabla_lift (A B : Type) : (A -> B) -> (nabla A) -> nabla B.
  Proof.
    intros.
    exists (fun a => exists x, a = (X x) /\ X0 = nabla_unit _ x).
    destruct X0.
    destruct e.
    exists (X x0).
    split.
    exists x0.
    split; auto.
    destruct u.

    
    
    unfold nabla_unit.


    assert (x = fun a : A => a = x0).
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    induction (e _ H).

    apply eq_refl.
    intro.
    induction H.
    exact x1.


    apply (sewonsewonp _ _ _ _ _ _ H).
    apply irrl.

    
    intros.
    destruct H.
    destruct H.
    rewrite H.
    apply lp.
    apply nabla_mono.
    induction H0.
    unfold nabla_unit.
    assert ((fun a : A => a = x0) = x).
    apply fun_ext.
    intro.
    apply Prop_ext.
    intro.
    induction H0.
    destruct u; auto.
    intro.
    destruct u.
    induction (H2 _ H0).
    apply eq_refl.
    
    
    apply (sewonsewonp _ _ _ _ _ _ H0).
    apply irrl.
  Defined.

  (* Definition nabla_mult (A : Type) : nabla (nabla A) -> nabla A. *)
  (* Proof. *)
  (*   intro. *)
  (*   exists (fun a : A => nabla_unit _ (nabla_unit _ a) = X). *)
  (*   destruct X. *)
  (*   destruct e. *)
  (*   destruct x0. *)
  (*   destruct e. *)

  (*   exists x1. *)

  
  



  (* Prop is nabla Prop *)
  Lemma Prop_is_nabla_modal : is_equiv (nabla_unit Prop).
  Proof.
    exists (fun X => X = nabla_unit _ True).
    split.


    

    apply fun_ext.
    intro P.
    apply Prop_ext.
    intros H.

    pose proof (sewon_sewonp _ _ _ _ _ _ H).
    apply (lp _ _ (fun x => x P)) in H0.
    assert (P = True).
    induction H0.
    apply eq_refl.
    rewrite H1.
    unfold id; auto.
    intros.
    assert (P = True).
    apply Prop_ext; auto.
    unfold fc; induction H0; auto.

   
    apply fun_ext.
    intro.
    apply nabla_unit2.
    intros.
    destruct H.

    apply (transport_eq) in H.
    unfold id in H0; rewrite H0 in H.
    rewrite<- H.
    apply Prop_ext.
    intro.
    apply transport_eq in H1.
    rewrite H1; auto.
    intro.
    assert (b = True).
    
    apply Prop_ext; auto.
    induction H2; auto.
  Qed.
  

    
  
  Definition lift2 : forall A B (x : Nabla.nabla A) (f : A -> B), Nabla.nabla B.
  Proof.
    intros.
    apply (Nabla.lift_unary A _).
    apply f.
    apply x.
  Defined.
  

End Nabla.
