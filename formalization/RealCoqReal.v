Require Import Real.
Require Import Nabla.
Require Import Reals.
Require Export Relator.
  
Definition relate : Real -> R -> Prop.
Proof.
  intros x y.
  destruct (relator x).
  exact (exists l : is_total y, x0 (exist _ y l)).
Defined.

Lemma relate_total : forall x y, relate x y -> is_total y.
Proof.
  intros.
  unfold relate in H.
  destruct (relator x ).
  destruct H.
  exact x1.
Defined.
  
      
(* relator homomorphism *)
Lemma relate_constant0 : relate Real0 R0.
Proof.
  pose proof relator_constant0.
  unfold relate.
  rewrite H.
  exists is_total_constant0.
  apply (sigma_eqP _ _ _ _ _ _ (eq_refl _)).
  apply irrl.
Qed.
  
Lemma relate_constant1 : relate Real1 R1.
Proof.
  pose proof relator_constant1.
  unfold relate.
  rewrite H.
  exists is_total_constant1.
  apply (sigma_eqP _ _ _ _ _ _ (eq_refl _)).
  apply irrl.
Qed.


Lemma relate_addition : forall x y a b, relate x a -> relate y b -> relate (x + y) (a + b)%R.
Proof.

  intros.
  
  unfold relate.

  case_eq (relator (x + y)).  
  intros.
  
  exists (is_total_addition a b (relate_total x a H) (relate_total y b H0)).
  

  pose proof (relator_addition x y).
  rewrite H2 in H1.
  clear H2.

  unfold Nabla.lift_binary in H1.
  case_eq (relator x); intros.
  case_eq (relator y); intros.
  rewrite H2 in H1.
  rewrite H3 in H1.
  pose proof (sigma_eqP_pr1 _ _ _ _ _ _  H1).
  rewrite<- H4.

  clear H1.
  unfold totalRadd.

  destruct e0.
  destruct e1.
  exists x3.
  exists x4.
  destruct u, u0.
  repeat split; auto.
  
  destruct x3, x4.
  assert (a + b = x3 + x4)%R.
  assert (a = x3).
  clear H3 H4.
  unfold relate in H.
  destruct (relator x).
  destruct H.
  pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H2).
  induction H1.
  destruct e2.
  destruct u.
  pose proof (e2 _ H).
  pose proof (e2 _ x5).
  rewrite H1 in H3.
  exact (sigma_eqP_pr1 _ _ _ _ _ _ H3).
  assert (b = x4).
  clear H2 H4.
  unfold relate in H0.
  destruct (relator y).
  destruct H0.
  pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H3).
  induction H2.
  destruct e2.
  destruct u.
  pose proof (e2 _ x6).
  pose proof (e2 _ H0).
  rewrite H4 in H2.
  exact (sigma_eqP_pr1 _ _ _ _ _ _ H2).
  rewrite H1; rewrite H5; apply eq_refl.
  apply (sigma_eqP _ _ _ _ _ _ H1).
  apply irrl.
Qed.

  

Lemma relate_multiplication : forall x y a b, relate x a -> relate y b -> relate (x * y) (a * b)%R.
Proof.
  intros.
  unfold relate.
  case_eq (relator (x * y)).  
  intros.
  exists (is_total_multiplication a b (relate_total x a H) (relate_total y b H0)).
  

  pose proof (relator_multiplication x y).
  rewrite H2 in H1.
  clear H2.

  unfold Nabla.lift_binary in H1.
  case_eq (relator x); intros.
  case_eq (relator y); intros.
  rewrite H2 in H1.
  rewrite H3 in H1.
  pose proof (sigma_eqP_pr1 _ _ _ _ _ _  H1).
  rewrite<- H4.

  clear H1.
  unfold totalRadd.

  destruct e0.
  destruct e1.
  exists x3.
  exists x4.
  destruct u, u0.
  repeat split; auto.
  
  destruct x3, x4.
  assert (a * b = x3 * x4)%R.
  assert (a = x3).
  clear H3 H4.
  unfold relate in H.
  destruct (relator x).
  destruct H.
  pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H2).
  induction H1.
  destruct e2.
  destruct u.
  pose proof (e2 _ H).
  pose proof (e2 _ x5).
  rewrite H1 in H3.
  exact (sigma_eqP_pr1 _ _ _ _ _ _ H3).
  assert (b = x4).
  clear H2 H4.
  unfold relate in H0.
  destruct (relator y).
  destruct H0.
  pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H3).
  induction H2.
  destruct e2.
  destruct u.
  pose proof (e2 _ x6).
  pose proof (e2 _ H0).
  rewrite H4 in H2.
  exact (sigma_eqP_pr1 _ _ _ _ _ _ H2).
  rewrite H1; rewrite H5; apply eq_refl.
  apply (sigma_eqP _ _ _ _ _ _ H1).
  apply irrl.
Qed.




Lemma relate_subtraction : forall x a, relate x a ->  relate (-x) (-a)%R.
Proof.
  intros.
  unfold relate.
  case_eq (relator (- x)).  
  intros.
  exists (is_total_subtraction a (relate_total x a H) ).
  

  pose proof (relator_subtraction x ).
  rewrite H1 in H0.
  clear H1.

  unfold Nabla.lift_binary in H0.
  case_eq (relator x); intros.
  rewrite H1 in H0.
  pose proof (sigma_eqP_pr1 _ _ _ _ _ _  H0).
  rewrite<- H2.

  unfold totalRsub.

  destruct e0.
  exists x2.
  destruct u.
  repeat split; auto.
  
  destruct x2.
  assert (-a = -x2)%R.
  assert (a = x2).
  unfold relate in H.
  destruct (relator x).
  destruct H.
  pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H1).
  induction H3.
  
  
  destruct e1.
  destruct u.
  pose proof (e1 _ H).
  pose proof (e1 _ x3).
  rewrite H4 in H3.
  pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H3).
  rewrite H5; auto.
  rewrite H3; auto.
  apply (sigma_eqP _ _ _ _ _ _ H3).
  apply irrl.
Qed.

  
Lemma relate_divison : forall x (p : x <> Real0) a, relate x a -> relate (/ p) (/a)%R. 
Proof.
  intros.
  unfold relate.
  case_eq (relator (/p)).
  intros.
  assert (a <> R0).
  pose proof (relator_mono_neg _ _ p).
  unfold relate in H.
  destruct (relator x).
  intro.
  induction (eq_sym H2).
  contradict H1.
  apply Nabla.nabla_eq_at.
  simpl.
  pose proof (relator_constant0).
  rewrite H1.
  simpl.
  apply fun_ext.
  intro.
  apply Prop_ext; intro.
  destruct H.
  destruct e0.
  destruct H4.
  pose proof (H5 _ H).
  pose proof (H5 _ H3).
  rewrite H6 in H7.
  rewrite <- H7.
  apply (sigma_eqP _ _ _ _ _ _ (eq_refl R0)).
  apply irrl.
  rewrite H3.
  destruct H.
  assert ((exist (fun x : R => is_total x) R0 x3) = totalR0).
  apply (sigma_eqP _ _ _ _ _ _ (eq_refl R0)).
  apply irrl.
  rewrite <- H4; auto.
  pose proof (relate_total _ _ H).
  
  exists (is_total_division _ H2 H1).

  pose proof (relator_division x p).
  
  rewrite H0 in H3.
  
  unfold relator_div_tmp in H3.
  unfold Nabla.lift_unary in H3.
  unfold Nabla.transport_ex in H3.
  unfold Nabla.lift_domain_unary in H3.
  unfold Nabla.lift_unary in H3.
  unfold Nabla.nabla_is_modal in H3.
  unfold Nabla.fancy_lift_unary in H3.
  unfold Nabla.nabla_mult in H3.
  
  pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H3).
  clear H3.
  rewrite H4.

  clear H4.
  assert (exist _ a H2 <> totalR0).
  intro.
  apply sigma_eqP_pr1 in H3.
  exact (H1 H3).
  exists (exist _ (exist _ a H2) H3).
  assert (forall x2 : totalR, Nabla.nabla_unit totalR x2 = Nabla.nabla_unit _ (exist _ a H2) -> x2 <> totalR0).
  intros.
  intro.
  
  induction (eq_sym H5).
  contradict H1.
  apply Nabla.nabla_mono in H4.
  apply sigma_eqP_pr1 in H4.
  rewrite H4; auto.


  split.
  exists (exist _ ( Nabla.nabla_unit _ (exist _ a H2)) H4).
  split.
  intros.

  unfold Nabla.transport_fiber.
  assert ( (Nabla.nabla_unit {x1 : R | is_total x1} (exist (fun x1 : R => is_total x1) a H2))
           = (Nabla.nabla_unit totalR a0)).
  apply Nabla.nabla_eq_at.
  simpl.
  apply fun_ext.
  intro.
  apply Prop_ext; intro.
  rewrite H5.
  unfold relate in H.
  destruct (relator x).
  destruct e0.
  destruct u.
  apply sigma_eqP_pr1 in p0.
  apply (lp _ _ (fun k => k a0)) in p0.
  assert (x2 a0) by (rewrite p0; auto).
  pose proof (e0 _ H6).
  destruct H.
  pose proof (e0 _ H).
  rewrite <- H7, H8.
  apply (sigma_eqP _ _ _ _ _ _ (eq_refl _)).
  apply irrl.
  induction (eq_sym H5).
  
  unfold relate in H.
  destruct (relator x).
  destruct e0.
  destruct u.
  apply sigma_eqP_pr1 in p0.
  apply (lp _ _ (fun k => k a0)) in p0.
  assert (x1 a0) by (rewrite p0; auto).
  pose proof (e0 _ H6).
  destruct H.
  pose proof (e0 _ H).
  rewrite <- H7, H8.
  apply (sigma_eqP _ _ _ _ _ _ (eq_refl _)).
  apply irrl.

  
  apply (sigma_eqP _ _ _ _ _ _ H5).
  apply irrl.

  apply Nabla.nabla_eq_at.
  simpl.
  apply fun_ext.
  intro.
  apply Prop_ext; intros.
  rewrite H5.
  assert (
      (exist (fun x2 : R => is_total x2) a H2)
      =
      a0).
  apply sigma_eqP_pr1 in p0.
  apply (lp _ _ (fun k => k a0)) in p0.
  apply eq_sym; rewrite p0.
  apply eq_refl.
  apply (sigma_eqP _ _ _ _ _ _ H6).
  apply irrl.
  pose proof (H5 (exist _ a H2) (eq_refl _)).
  rewrite H6.
  apply (sigma_eqP _ _ _ _ _ _ (eq_refl _)).
  apply irrl.


  unfold totalRdiv.
  apply (sigma_eqP _ _ _ _ _ _ (eq_refl _)).
  apply irrl.

Defined.



(* relator is an anafunction *)

Lemma ana1 : forall x : Real, exists! y : R, relate x y.
Proof.
  intros.
  unfold relate.  
  destruct (relator x).
  destruct e.
  destruct x1.
  exists x1.
  split.
  exists i.
  destruct H.
  exact H.
  intro.
  intro.
  destruct H.
  destruct H0.
  pose proof (H1 _ H0).
  pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H2).
  exact H3.
Defined.

Lemma ana2 : forall x : R, is_total x -> exists! y : Real, relate y x.
Proof.
  intros.
  unfold relate.
  pose proof (relator_epi (Nabla.nabla_unit _ (exist _ x H))). 
  destruct H0.
  exists x0.
  split; auto.
  destruct (relator x0).
  pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H0).
  rewrite <- H1.
  exists H.
  auto.
  intro.

  pose proof (relator_mono x0 x').
  intro.
  apply H1.
  clear H1.
  
  rewrite <- H0.
  destruct (relator x').
  unfold Nabla.nabla_unit.
  assert ( (fun a : {x2 : R | is_total x2} => a = exist (fun x2 : R => is_total x2) x H)
           =
           x1).
  apply fun_ext.
  intro.
  apply Prop_ext.
  intro.
  rewrite H1.
  destruct e.
  destruct H2.
  destruct H3.
  pose proof (H4 _ H2).
  assert (x4 = H) by apply irrl.
  induction H6.
  rewrite H5 in H3.
  exact H3.
  intro.
  destruct e.

  destruct H3.

  destruct H2.
  destruct x2.
  pose proof (H4 _ H2).
  pose proof (H4 _ H1).
  rewrite H6 in H5.
  pose proof (sigma_eqP_pr1 _ _ _ _ _ _ H5).
  apply (sigma_eqP _ _ _ _ _ _ H7).
  apply irrl.
  apply (sigma_eqP _ _ _ _ _ _ H1).
  apply irrl.
Defined.


Lemma relate_unique_R : forall x y a b, relate x a -> relate y b -> x = y -> a = b.
Proof.
  intros.
  rewrite H1 in H.
  destruct (ana1 y).
  destruct H2.
  rewrite <- (H3 _ H).
  rewrite <- (H3 _ H0).
  exact (eq_refl _).
Qed.

Lemma relate_unique_Real : forall x y a b, relate x a -> relate y b -> a = b -> x = y.
Proof.
  intros.
  rewrite H1 in H.
  pose proof (ana2 _ (relate_total _ _ H)).
  pose proof (ana2 _ (relate_total _ _ H0)).
  destruct H2 as [i1 [j1 k1]].
  destruct H3 as [i2 [j2 k2]].
  rewrite<- (k1 _ H).
  rewrite<- (k1 _ H0).
  exact (eq_refl _).
Qed.

Ltac total :=
  auto;
  match goal with
  | H : (relate ?x ?y) |- is_total ?y => exact (relate_total _ _ H)
  | |- is_total R0 => exact is_total_constant0
  | |- is_total R1 => exact is_total_constant1
  | |- is_total (?x + ?y) => apply is_total_addition; [total | total] 
  | |- is_total (?x * ?y) => apply is_total_multiplication; [total | total] 
  | |- is_total (-?x) => apply is_total_subtraction; total 
  | |- is_total (?x - ?y) => apply is_total_minus; [total | total] 
  | |- is_total (/?x) => apply is_total_division; [total | auto] 
  | |- is_total (?x / ?y) => apply is_total_division2; [total | total |auto] 
  end.

  

Lemma transport_eq : forall a b : Real, (forall x y, relate a x -> relate b y -> x = y) -> a = b.
Proof.
  intros.
  pose proof (relator_mono a b).
  apply H0.
  clear H0.
  unfold relate in H.
  destruct (relator a).
  destruct (relator b).
  destruct e, e0.
  destruct x1, x2.
  pose proof (H x1 x2).
  assert  (exists l : is_total x1, x (exist (fun x : R => is_total x) x1 l)).
  exists i.
  destruct u; auto.
  assert ((exists l : is_total x2, x0 (exist (fun x : R => is_total x) x2 l))).
  exists i0.
  destruct u0; auto.

  pose proof (H0 H1 H2).
  induction H3.
  assert (x = x0).
  apply fun_ext.
  intro.
  apply Prop_ext.
  intro.
  destruct u, u0.
  pose proof (H5 _ H3).
  assert (i = i0) by apply irrl.
  induction H9.
  rewrite H8 in H6.
  exact H6.
  intro.
  destruct u, u0.
  pose proof (H7 _ H3).
  assert (i = i0) by apply irrl.
  induction H9.
  rewrite H8 in H4.
  exact H4.
  apply (sigma_eqP _ _ _ _ _ _ H3).
  apply irrl.
Defined.


Lemma transport_eq_inv : forall a b x y, relate a x -> relate b y -> a = b -> x = y.
Proof.
  intros.
  induction H1.
  unfold relate in H, H0.
  destruct (relator a).
  destruct e, H, H0.
  destruct H1.
  pose proof (H2 _ H).
  pose proof (H2 _ H0).
  rewrite H3 in H4.
  apply (sigma_eqP_pr1 _ _ _ _ _ _ ) in H4.
  exact H4.
Defined.

Lemma transport_lt : forall a b : Real, (forall x y, relate a x -> relate b y -> (x < y)%R) -> a < b.
Proof.
  intros.
  pose proof (relator_lt a b).
  rewrite H0.
  clear H0.
  unfold relate in H.
  destruct (relator a), (relator b).
  destruct e, e0.
  destruct x1, x2.
  pose proof (H x1 x2).
  assert ( (exists l : is_total x1, x (exist (fun x : R => is_total x) x1 l))).
  exists i.
  destruct u.
  exact H1.
  assert ((exists l : is_total x2, x0 (exist (fun x : R => is_total x) x2 l))).
  exists i0.
  destruct u0.
  exact H2.
  pose proof (H0 H1 H2).
  clear H0 H1 H2.
  unfold Nabla.lift_domain_binary.
  destruct (Nabla.Prop_is_nabla_modal).

  assert (  (exist (fun P : totalR -> Prop => exists ! a1 : totalR, P a1) x
                   (ex_intro (unique (fun a1 : totalR => x a1)) (exist (fun x4 : R => is_total x4) x1 i) u))
            = Nabla.nabla_unit _ (exist _ x1 i)).
  unfold Nabla.nabla_unit.
  assert (x = 
          (fun a1 : {x4 : R | is_total x4} => a1 = exist (fun x4 : R => is_total x4) x1 i)).
  apply fun_ext.
  intros.
  apply Prop_ext.
  intros.
  destruct u.
  pose proof (H2 _ H0).
  rewrite H4; auto.
  intro.
  rewrite H0.
  destruct u.
  exact H1.
  apply (sigma_eqP _ _ _ _ _ _ H0).
  apply irrl.
  rewrite H0.
  clear H0.

  assert ( (exist (fun P : totalR -> Prop => exists ! a1 : totalR, P a1) x0
                  (ex_intro (unique (fun a1 : totalR => x0 a1)) (exist (fun x4 : R => is_total x4) x2 i0) u0))
           = Nabla.nabla_unit _ (exist _ x2 i0)).
  unfold Nabla.nabla_unit.
  assert (x0 = 
           (fun a1 : {x4 : R | is_total x4} => a1 = exist (fun x4 : R => is_total x4) x2 i0)).
  apply fun_ext.
  intros.
  apply Prop_ext.
  intros.
  destruct u0.
  pose proof (H2 _ H0).
  rewrite H4; auto.
  intro.
  rewrite H0.
  destruct u0.
  exact H1.
  apply (sigma_eqP _ _ _ _ _ _ H0).
  apply irrl.
  rewrite H0.
  clear H0.
  pose proof  (Nabla.lift_binary_commute totalR totalR Prop totalRlt (exist _ x1 i) (exist _ x2 i0) ).

  replace
    (Nabla.lift_binary totalR totalR Prop totalRlt
                       (Nabla.nabla_unit {x4 : R | is_total x4} (exist (fun x4 : R => is_total x4) x1 i))
                       (Nabla.nabla_unit {x4 : R | is_total x4} (exist (fun x4 : R => is_total x4) x2 i0)))
    with
      (Nabla.lift_binary totalR totalR Prop totalRlt
      (Nabla.nabla_unit totalR (exist (fun x : R => is_total x) x1 i))
      (Nabla.nabla_unit totalR (exist (fun x : R => is_total x) x2 i0)))
    by auto.
  rewrite<- H0.

  clear H0.

  unfold fc, id in a0.
  destruct a0.
  unfold totalRlt.
  assert (x1 < x2 = True)%R.
  apply Prop_ext; auto.
  rewrite H2.
  pose proof (lp _ _ (fun f => f True) _ _  H0).
  simpl in H4.
  rewrite H4.
  unfold Base.id.
  auto.
Qed.


Lemma transport_lt_inv : forall a b x y, relate a x -> relate b y -> (a < b) -> (x < y)%R.
Proof.
  intros.
  intros.
  pose proof (relator_lt a b).
  rewrite H2 in H1.
  clear H2.
  pose proof (relate_total _ _ H).
  pose proof (relate_total _ _ H0).
  assert (relator a = Nabla.nabla_unit _ (exist _ x H2)).
  unfold relate in H.
  destruct (relator a).
  unfold Nabla.nabla_unit.
  assert (x0 = (fun a0 : {x1 : R | is_total x1} => a0 = exist (fun x1 : R => is_total x1) x H2)).
  apply fun_ext.
  intro.
  apply Prop_ext.
  intro.
  destruct e.
  destruct u.
  pose proof (e _ H4).
  destruct H.
  pose proof (e _ H).
  assert (x4 = H2) by apply irrl.
  rewrite H7 in H6.
  rewrite <- H5.
  exact H6.
  intro.
  rewrite H4.
  destruct H.
  assert (x2 = H2) by apply irrl.
  rewrite H5 in H.
  exact H.
  apply (sigma_eqP _ _ _ _ _ _ H4).
  apply irrl.
  rewrite H4 in H1.
  clear H4.

  assert (relator b = Nabla.nabla_unit _ (exist _ y H3)).
  unfold relate in H0.
  destruct (relator b).
  unfold Nabla.nabla_unit.
  assert (x0 =  (fun a0 : {x1 : R | is_total x1} => a0 = exist (fun x1 : R => is_total x1) y H3)).
  apply fun_ext.
  intro.
  apply Prop_ext.
  intro.
  destruct e.
  destruct u.
  pose proof (e _ H4).
  destruct H0.
  pose proof (e _ H0).
  assert (x4 = H3) by apply irrl.
  rewrite H7 in H6.
  rewrite <- H5.
  exact H6.
  intro.
  rewrite H4.
  destruct H0.
  assert (x2 = H3) by apply irrl.
  rewrite H5 in H0.
  exact H0.
  apply (sigma_eqP _ _ _ _ _ _ H4).
  apply irrl.
  rewrite H4 in H1.
  clear H4.

  unfold Nabla.lift_domain_binary in H1.
  destruct (Nabla.Prop_is_nabla_modal).
  
  
  pose proof (Nabla.lift_binary_commute totalR totalR Prop totalRlt
                                        (exist _ x H2) (exist _ y H3)).
  replace
    ((Nabla.lift_binary totalR totalR Prop totalRlt
            (Nabla.nabla_unit {x : R | is_total x} (exist (fun x : R => is_total x) x H2))
            (Nabla.nabla_unit {x : R | is_total x} (exist (fun x : R => is_total x) y H3))))
         
    with
      
      ( Nabla.lift_binary totalR totalR Prop totalRlt
         (Nabla.nabla_unit totalR (exist (fun x : R => is_total x) x H2))
         (Nabla.nabla_unit totalR (exist (fun x : R => is_total x) y H3)))
    in H1
    
    by auto.
  
  rewrite <- H4 in H1.

  clear H4.
  unfold totalRlt in H1.
  unfold fc, Base.id in a0;  destruct a0.
  apply (lp _ _ (fun f => f (x< y)%R)) in H4.
  rewrite <- H4.
  exact H1.
Defined.




Lemma transport_eq2 : forall a b x y, relate a x -> relate b y -> x = y -> a = b.
Proof.
  apply relate_unique_Real.
Defined.


Lemma transport_lt2 : forall a b x y, relate a x -> relate b y -> (x < y)%R -> a < b.
Proof.
  intros.
  apply transport_lt.
  intros.
  induction (relate_unique_R _ _ _ _ H H2).
  induction (relate_unique_R _ _ _ _ H0 H3).
  exact H1.
  apply eq_refl. 
  apply eq_refl. 
Defined.
  

Definition transport_fiber : (Real -> Prop) -> (R -> Prop).
Proof.
  intros.
  exact (forall x : Real, relate x H -> X x).
Defined.


Definition transport_leq : forall a b : Real, (forall x y, relate a x -> relate b y -> (x <= y)%R) -> a <= b.
Proof.
  intros.
  destruct (ana1 a) as [aa [hh _]].
  destruct (ana1 b) as [bb [jj _]].
  pose proof (H _ _ hh jj).
  destruct H0.
  left.
  apply (transport_lt2 _ _ _ _ hh jj H0).
  right; apply (transport_eq2 _ _ _ _ hh jj H0).
Qed.


Definition transport_geq : forall a b : Real, (forall x y, relate a x -> relate b y -> (x >= y)%R) -> a >= b.
Proof.
  intros.
  destruct (ana1 a) as [aa [hh _]].
  destruct (ana1 b) as [bb [jj _]].
  pose proof (H _ _ hh jj).
  destruct H0.
  left.
  apply (transport_lt2 _ _ _ _ jj hh H0).
  right; apply (transport_eq2 _ _ _ _ hh jj H0).
Qed.

Definition transport_neq : forall a b : Real, (forall x y, relate a x -> relate b y -> (x <> y)%R) -> a <> b.
Proof.
  intros.
  destruct (ana1 a) as [aa [hh _]].
  destruct (ana1 b) as [bb [jj _]].
  pose proof (H _ _ hh jj).
  intro.
  
  destruct H0.
  induction H1.
  apply (relate_unique_R _ _ _ _ hh jj).
  apply eq_refl.
Qed.


Definition transport_forall : forall P : Real -> Prop, (forall x : R, (transport_fiber P) x) -> (forall x : Real, P x).
  intros.
  unfold transport_fiber in H.
  destruct (ana1 x).
  destruct H0.
  exact (H x0 x H0).
Defined.
  

(* Definition transport_exists : forall P : Real -> Prop, (exists x : R, (transport_fiber P) x) -> (exists x : Real, P x). *)
(* Proof. *)
(*   intros. *)
(*   destruct H. *)
(*   unfold transport_fiber in H. *)
(*   destruct (ana2 x). *)
(*   destruct H0. *)
(*   exists x0. *)
(*   exact (H _ H0). *)
(* Defined. *)


Definition transport_leq_inv : forall a b x y, relate a x -> relate b y -> (a <= b) -> (x <= y)%R.
Proof.
  intros.
  destruct H1.
  left.
  apply (transport_lt_inv a b x y H H0).
  exact H1.
  right.
  induction H1.
  apply (relate_unique_R _ _ _ _ H H0 (eq_refl _)).
Qed.

Definition transport_geq_inv : forall a b x y, relate a x -> relate b y -> (a >= b) -> (x >= y)%R.
Proof.
  intros.
  destruct H1.
  left.
  apply (transport_lt_inv b a y x  H0 H).
  exact H1.
  right.
  induction H1.
  apply (relate_unique_R _ _ _ _ H H0 (eq_refl _)).
Qed.


Definition transport_neq_inv : forall a b x y, relate a x -> relate b y -> (a <> b) -> (x <> y)%R.
Proof.
  intros.
  intro.
  induction H2.
  exact (H1 (relate_unique_Real _ _ _ _ H H0 (eq_refl _))).
Defined.


Ltac Holger s :=
  match type of s with
  | ?x = ?y =>
    let xx := fresh "x" in
    let yy := fresh "y" in
    let Hx := fresh "Hx" in
    let Hy := fresh "Hy" in
    let H := fresh "H" in
    
    destruct (ana1 x) as [xx [Hx _ ]];
    destruct (ana1 y) as [yy [Hy _ ]];
    pose proof (transport_eq_inv _ _ _ _ Hx Hy s) as H;
    clear s

  | ?x < ?y =>
    let xx := fresh "x" in
    let yy := fresh "y" in
    let Hx := fresh "Hx" in
    let Hy := fresh "Hy" in
    let H := fresh "H" in
    
    destruct (ana1 x) as [xx [Hx _ ]];
    destruct (ana1 y) as [yy [Hy _ ]];
    pose proof (transport_lt_inv _ _ _ _ Hx Hy s) as H;
    clear s


  | ?x <= ?y =>
    let xx := fresh "x" in
    let yy := fresh "y" in
    let Hx := fresh "Hx" in
    let Hy := fresh "Hy" in
    let H := fresh "H" in
    
    destruct (ana1 x) as [xx [Hx _ ]];
    destruct (ana1 y) as [yy [Hy _ ]];
    pose proof (transport_leq_inv _ _ _ _ Hx Hy s) as H;
    clear s


  | ?x >= ?y =>
    let xx := fresh "x" in
    let yy := fresh "y" in
    let Hx := fresh "Hx" in
    let Hy := fresh "Hy" in
    let H := fresh "H" in
    
    destruct (ana1 x) as [xx [Hx _ ]];
    destruct (ana1 y) as [yy [Hy _ ]];
    pose proof (transport_geq_inv _ _ _ _ Hx Hy s) as H;
    clear s


  | ?x <> ?y =>
    let xx := fresh "x" in
    let yy := fresh "y" in
    let Hx := fresh "Hx" in
    let Hy := fresh "Hy" in
    let H := fresh "H" in
    
    destruct (ana1 x) as [xx [Hx _ ]];
    destruct (ana1 y) as [yy [Hy _ ]];
    pose proof (transport_neq_inv _ _ _ _ Hx Hy s) as H;
    clear s
                    
          
  end.

Definition skip : forall A,A -> A.
Proof.
  intros.
  exact X.
Defined.


Definition Holber0: forall x, relate Real0 x -> x = R0.
Proof.
  intros.
  rewrite (relate_unique_R _ _ _ _ relate_constant0 H (eq_refl _)).
  apply eq_refl.
Qed.

Definition Holber1: forall x, relate Real1 x -> x = R1.
Proof.
  intros.
  rewrite (relate_unique_R _ _ _ _ relate_constant1 H (eq_refl _)).
  apply eq_refl.
Qed.


Definition Holber2 : forall a b x y z, relate x a -> relate y b -> relate (x + y) z ->
                                  z = (a + b)%R.
Proof.
  intros.
  pose proof (relate_addition x y a b H H0).
  exact (relate_unique_R _ _ _ _ H1 H2 (eq_refl _)).
Defined.





Definition Holber3 : forall a b x y z, relate x a -> relate y b -> relate (x * y) z ->
                                  z = (a * b)%R.
Proof.
  intros.
  pose proof (relate_multiplication x y a b H H0).
  exact (relate_unique_R _ _ _ _ H1 H2 (eq_refl _)).
Defined.

Definition Holber4 : forall a  x  z, relate x a -> relate (-x) z ->
                                  z = (-a)%R.
Proof.
  intros.
  pose proof (relate_subtraction x a H).
  exact (relate_unique_R _ _ _ _ H0 H1 (eq_refl _)).
Defined.

Definition Holber6 : forall a  x  z (p : x <> Real0), relate x a -> relate (/p) z ->
                                  z = (/a)%R.
Proof.
  intros.
  pose proof (relate_divison x p a H).
  exact (relate_unique_R _ _ _ _ H0 H1 (eq_refl _)).
Defined.

Definition Holber7 : forall a b x y z (p : y <> Real0), relate x a -> relate y b -> relate (x / p) z -> z = (a/b)%R.
Proof.
  intros.
  replace (a / b)%R with (a * / b)%R by auto.
  replace (x / p) with (x */ p) in H1 by auto.
  pose proof (relate_divison y p b H0).
  apply (Holber3 _ _ _ _ _ H H2).
  exact H1.
Defined.


Definition Holber5 : forall a b x y z, relate x a -> relate y b -> relate (x - y) z ->
                                  z = (a - b)%R.
Proof.
  intros.
  replace (a - b)%R with (a + - b)%R by ring.
  replace (x - y) with (x + - y) in H1 by ring.
  pose proof (relate_subtraction y b H0).
  apply (Holber2 _ _ _ _ _ H H2 H1).
Defined.




  
Lemma eq_symm : forall {T} {x y : T}, x = y -> y = x.  
Proof.
  intros.
  rewrite H.
  apply eq_refl.
Defined.

Ltac classical :=
  match goal with
  | |- @eq Real ?x ?y => apply transport_eq;   intro; intro; intro; intro; classical (* (fail "not implemented yet") *)
  | |- ?x < ?y => apply transport_lt; intro; intro; intro; intro; classical
  | |- ?x > ?y => apply transport_lt; intro; intro; intro; intro; classical
  | |- ?x >= ?y => apply transport_geq; intro; intro; intro; intro; classical
  | |- ?x <= ?y => apply transport_leq; intro; intro; intro; intro; classical
  | |- ?x <> ?y => apply transport_neq; intro; intro; intro; intro; classical     
  (* | |- exists x : Real, ?A => apply transport_exists;  intro; intro; intro; classical *)
  | |- forall x : Real, ?A => apply (transport_forall (fun x => A));   intro; intro; intro; classical
  (* | |- forall x : Real, ?A => apply (transport_forall (fun x => A));   intro; intro; intro; classical *)

  | |- ?A => apply skip
  (* | |- ?A => match A with *)
  (*          | ?a = ?b => fail "haha" *)
  (*          | _ => fail "FAIL" A *)
  (*          end  *)


  end.


  
Ltac relate :=
  
  match goal with
  | H : (relate Real0 ?x) |- _ => (apply Holber0 in H; try induction (eq_symm H); clear H; relate)
  | H : (relate Real1 ?x) |- _ => (apply Holber1 in H; try induction (eq_symm H); clear H; relate)
  | H : (relate (?x + ?y) (?z)) |- _ =>
    (idtac ""x; 
     let a := fresh "x" in
     let b := fresh "y" in
     let Ha := fresh "Ha" in
     let Hb := fresh "Hb" in
     let Hc := fresh H in
     (destruct (ana1 x) as [a [Ha _]];
      destruct (ana1 y) as [b [Hb _]];
      pose proof (eq_symm (Holber2 _ _ _ _ _ Ha Hb H)) as Hc;
      induction ( Hc);
      clear Hc;
      clear H;
      relate
    ))

  | H : (relate (?x - ?y) (?z)) |- _ =>
    (idtac " "; 
     let a := fresh "x" in
     let b := fresh "y" in
     let Ha := fresh "Ha" in
     let Hb := fresh "Hb" in
     let Hc := fresh H in
     (destruct (ana1 x) as [a [Ha _]];
      destruct (ana1 y) as [b [Hb _]];
      pose proof (eq_symm (Holber5 _ _ _ _ _ Ha Hb H)) as Hc;
      induction ( Hc);
      clear Hc;
      clear H;
      relate
    ))

  | H : (relate (?x / ?p) (?z)) |- _ =>
    match type of  p with
    | ?y <> Real0 =>
      (idtac "";
       let a := fresh "x" in
       let b := fresh "y" in
       let Ha := fresh "Ha" in
       let Hb := fresh "Hb" in
       let Hc := fresh H in
       (destruct (ana1 x) as [a [Ha _]];
        destruct (ana1 y) as [b [Hb _]];
        pose proof (eq_symm (Holber7 _ _ _ _ _ p Ha Hb H)) as Hc;
        induction ( Hc);
        clear Hc;
        clear H;
        relate
      ))
        
    | _ => idtac "" 
    end
      
  | H : (relate (?x * ?y) (?z)) |- _ =>
    (idtac " "; 
     let a := fresh "x" in
     let b := fresh "y" in
     let Ha := fresh "Ha" in
     let Hb := fresh "Hb" in
     let Hc := fresh H in
     (destruct (ana1 x) as [a [Ha _]];
      destruct (ana1 y) as [b [Hb _]];
      pose proof (eq_symm (Holber3 _ _ _ _ _ Ha Hb H)) as Hc;
      induction ( Hc);
      clear Hc;
      clear H;
      relate
    ))

  | H : (relate (- ?x) (?y)) |- _ =>
    (idtac " "
     ;
     let a := fresh "x" in
     let Ha := fresh "Ha" in
     let Hc := fresh H in
     (destruct (ana1 x) as [a [Ha _]];
      pose proof (eq_symm (Holber3 _ _ _  Ha  H)) as Hc;
      induction ( Hc);
      clear Hc;
      clear H;
      relate
    )
)



  | H : (relate (@Realdiv ?x ?p) (?y)) |- _ =>
    (idtac ""
     (* ;  *)
     (* let a := fresh "x" in *)
     (* let Ha := fresh "Ha" in *)
     (* let Hc := fresh H in *)
     (* (destruct (ana1 x) as [a [Ha _]]; *)
     (*  pose proof (eq_symm (Holber6 _ _ _ p  Ha  H)) as Hc; *)
     (*  induction ( Hc); *)
     (*  clear Hc; *)
     (*  clear H; *)
     (*  relate *)
     (* ) *)
    )
  | H : (relate (/ ?p) (?y)) |- _ =>
    match type of p with
    | ?x <> Real0 =>
      let a := fresh "x" in
      let Ha := fresh "Ha" in
      let Hc := fresh H in
      (destruct (ana1 x) as [a [Ha _]];
       pose proof (eq_symm (Holber6 _ _ _ p  Ha  H)) as Hc;
       induction ( Hc);
       clear Hc;
       clear H;
       relate
      )

    | _ => apply skip
    end 
      
  | H1 : (relate (?x) (?y)), H2 : (relate (?x) (?z))  |- _ =>
    (idtac " ";
     induction (relate_unique_R _ _ _ _ H1 H2 (eq_refl _));
     clear H1;
     relate
    )
      
  | H1 : (relate (?x) (?z)), H2 : (relate (?y) (?z))  |- _ =>
    (idtac " ";
     induction (relate_unique_Real _ _ _ _ H1 H2 (eq_refl _));
     clear H1;
     relate
    )
                                         
  | _ => apply skip
  end.
