Require Import Real.
Require Import Euclidean.
Require Import List.
Require Import Psatz.
Import ListNotations.
(* Require Import Poly. *)
Require Import ClassicalMonads.
Require Import Minmax.


Require Import RealAssumption.



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

Section ClassicalParitalFunctions.
  
  Definition pc X := Nabla (option X).

  Definition pc_unit (A : Type) : A -> pc A := fun x => Nabla_unit _ (Some x).

  Definition pc_bot {A : Type} := Nabla_unit (option A) None.
  
  Definition pc_mult (A : Type) : pc (pc A) -> pc A.
  Proof.
    intro.
    apply (Nabla_bind2 X).
    intro.
    destruct X0.
    exact p.
    exact pc_bot.
  Defined.
      
  Definition pc_lift {A B} (f : A -> B) : pc A -> pc B.
  Proof.
    intro.
    apply (Nabla_bind2 X).
    intro.
    destruct X0.
    exact (pc_unit _ (f a)). 
    exact pc_bot.
  Defined.
  
  Definition defined_to {X} (x : pc X) (y : X) := x = pc_unit _ y.
  
  Definition defined {X} (x : pc X) := exists t, defined_to x t.
    
  Definition domain {X Y} (f : X -> pc Y) := fun x :X => defined (f x).
   
  Definition comp {X Y Z} (g : Y -> pc Z) (f : X -> pc Y) : X -> pc Z.
  Proof.
    intro.
    apply f in X0.
    apply (Nabla_bind2 X0).
    intros y'.
    destruct y' as [y' | _].
    exact (g y').
    exact pc_bot.
  Defined.

  Lemma comp_iff {X Y Z} (g : Y -> pc Z) (f : X -> pc Y) :
    forall x z, defined_to (comp g f x) z <-> exists y, defined_to (f x) y /\ defined_to (g y) z.
  Proof.
    intros.
    split.
    intros.
    unfold comp in H.
    unfold defined_to in H.
    unfold Nabla_bind2 in H.

    pose proof (Nabla_unit_surjective (f x)).
    destruct H0.
    rewrite H0 in H.
    rewrite Nabla_unit_ntrans in H.
    rewrite Nabla_coh1 in H.
    destruct x0.
    exists y.
    rewrite H, H0.
    split; auto;
      unfold defined_to;
      apply eq_refl.
    apply Nabla_unit_mono in H.
    discriminate H.

    intro.
    destruct H as [y [p q]].
    unfold defined_to in p, q.
    unfold defined_to.
    unfold comp.
    unfold Nabla_bind2.
    rewrite p.
    unfold pc_unit.
    rewrite Nabla_unit_ntrans.
    rewrite q.
    rewrite Nabla_coh1.
    auto.
  Defined.
  
  
  Definition pointwise_op {X} {Y} {Z} (f g : X -> pc Y) (o : Y -> Y -> pc Z) : X -> pc Z.
  Proof.
    intro.
    pose proof (f X0) as x.
    pose proof (g X0) as y.
    apply (Nabla_bind2 x).
    intro x'.
    apply (Nabla_bind2 y).
    intro y'.
    destruct x' as [x' | x'].
    destruct y' as [y' | y'].
    exact (o x' y').
    exact pc_bot.
    exact pc_bot. 
  Defined.

  Definition pc_pair {A B} : pc A -> pc B -> pc (A * B).
  Proof.
    intros x y.
    apply (Nabla_bind2 x).
    intro x'.
    destruct x'.
    apply (Nabla_bind2 y).
    intro y'.
    destruct y'.
    exact (pc_unit _ (a, b)). 
    exact pc_bot.
    exact pc_bot.
  Defined.

  Lemma pc_pair_iff {A B} (x : pc A) (y : pc B) :
    forall x' y', 
      defined_to x x' /\ defined_to y y' <-> defined_to (pc_pair x y) (x', y'). 
  Proof.
    intros.
    split.
    intros [p q].
    unfold pc_pair.
    unfold Nabla_bind2.
    unfold defined_to in p.
    rewrite p.
    unfold pc_unit.
    rewrite Nabla_unit_ntrans.
    unfold defined_to in q.
    rewrite q.
    unfold pc_lift, pc_unit.

    rewrite Nabla_unit_ntrans.
    rewrite Nabla_coh1.
    rewrite Nabla_coh1.
    unfold defined_to.
    auto.
    intros.
    unfold pc_pair in H.
    unfold Nabla_bind2 in H.
    unfold defined_to in H.
    pose proof (Nabla_unit_surjective x) as [x'' p].
    pose proof (Nabla_unit_surjective y) as [y'' q].
    rewrite p, q in H.
    rewrite Nabla_unit_ntrans in H.
    rewrite Nabla_coh1 in H.
    destruct x''.
    
    rewrite Nabla_unit_ntrans in H.
    rewrite Nabla_coh1 in H.
    destruct y''.
    apply Nabla_unit_mono in H.
    injection H; intros.
    induction H0, H1.
    rewrite p, q.
    unfold defined_to; auto.
    apply Nabla_unit_mono in H.
    discriminate H.
    apply Nabla_unit_mono in H.
    discriminate H.
  Defined.

  Lemma pc_pair_fst_bot {A B} (x : pc B) : @pc_pair A B pc_bot x = pc_bot.
  Proof.
    unfold pc_pair.
    unfold Nabla_bind2.
    unfold pc_bot.
    rewrite Nabla_unit_ntrans.
    rewrite Nabla_coh1.
    auto.
  Defined.

  Lemma pc_case {A} : forall x : pc A, x = pc_bot \/ exists x', x = pc_unit _ x'.
  Proof.
    intros.
    destruct (Nabla_unit_surjective x).
    destruct x0.
    right.
    exists a; auto.
    left; auto.
  Defined.
  
    
  Lemma pc_pair_snd_bot {A B} (x : pc A) : @pc_pair A B x pc_bot = pc_bot.
  Proof.
    unfold pc_pair.
    unfold Nabla_bind2.
    unfold pc_bot.
    destruct (pc_case x).
    induction (eq_sym H).
    unfold pc_bot.
    rewrite Nabla_unit_ntrans.
    rewrite Nabla_coh1.
    auto.
    destruct H.
    rewrite H.
    unfold pc_unit.
    rewrite Nabla_unit_ntrans.
    rewrite Nabla_coh1.
    rewrite Nabla_unit_ntrans.
    rewrite Nabla_coh1.
    auto.
  Defined.
  
  Lemma pc_unit_mono : forall (A : Type) (x y : A), pc_unit A x = pc_unit A y -> x = y.
  Proof.
    intros.
    apply Nabla_unit_mono in H.
    injection H; auto.
  Defined.
  
  Lemma pc_pair_bot_case {A B} {x} {y} : @pc_pair A B x y = pc_bot -> x = pc_bot \/ y = pc_bot.
  Proof.
    intro.
    destruct (pc_case x).
    left; auto.
    destruct (pc_case y).
    right; auto.
    destruct H0 as [x' p].
    destruct H1 as [y' q].
    pose proof (pc_pair_iff x y x' y').
    destruct H0.
    pose proof (H0 (conj p q)).
    rewrite H2 in H.
    apply Nabla_unit_mono in H.
    discriminate H.
  Defined.
      
  Lemma pc_unit_ntrans : forall (A B : Type) (f : A -> B) (x : A),
      pc_lift f (pc_unit A x) = pc_unit B (f x).
  Proof.
    intros.
    unfold pc_lift.
    unfold pc_unit.
    unfold Nabla_bind2.
    unfold pc_unit.
    rewrite Nabla_unit_ntrans.
    rewrite Nabla_coh1.
    auto.
  Defined.

  Lemma pc_lift_bot : forall {A B} (f : A -> B),
      pc_lift f pc_bot = pc_bot.
  Proof.
    intros.
    unfold pc_lift.
    unfold Nabla_bind2.
    unfold pc_bot.
    rewrite Nabla_unit_ntrans.
    rewrite Nabla_coh1.
    auto.
  Defined.
  
  
  Lemma pc_mult_ntrans : forall (A B : Type) (f : A -> B) (x : pc (pc A)),
       pc_mult B (pc_lift (pc_lift f) x) = pc_lift f (pc_mult A x).
  Proof.
  Admitted.
  
    
  Definition pc_bind {A B} (f : A -> pc B) : pc A -> pc B.
  Proof.
    intro.
    apply pc_mult.
    apply (pc_lift f).
    exact X.
  Defined.

  Lemma pc_bot_defined_to_absurd {A} : forall {x : A}, defined_to pc_bot x -> False.
  Proof.
    intros.
    apply Nabla_unit_mono in H.
    discriminate H.
  Defined.
  
  Definition pc_lift2 {A B C} (f : A -> B -> C) : pc A -> pc B -> pc C.
  Proof. 
    intros.
    pose proof (pc_pair X X0).
    apply (pc_lift (fun x => f (fst x) (snd x))).
    exact X1.
  Defined.

  

  Definition pc_lift2_iff {A B C} (f : A -> B -> C) :
    forall x y z',
      defined_to (pc_lift2 f x y) z' <-> exists x' y', defined_to x x' /\ defined_to y y' /\ z' = f x' y'.
  Proof.
    intros.
    split.
    intro.
    destruct (pc_case x).
    rewrite H0 in H.
    unfold pc_lift2 in H.
    rewrite pc_pair_fst_bot in H.
    rewrite pc_lift_bot in H.
    contradiction (pc_bot_defined_to_absurd H).
    destruct (pc_case y).
    rewrite H1 in H.
    unfold pc_lift2 in H.
    rewrite pc_pair_snd_bot in H.
    rewrite pc_lift_bot in H.
    contradiction (pc_bot_defined_to_absurd H).
    destruct H0 as [x' p].
    destruct H1 as [y' q].
    exists x', y'.
    split.
    exact p.
    split.
    exact q.
    
    unfold defined_to in H.
    unfold pc_lift2 in H.
    destruct (pc_pair_iff x y x' y') as [l _].
    pose proof (l (conj p q)).
    rewrite H0 in H.
    rewrite pc_unit_ntrans in H.
    simpl in H.
    apply pc_unit_mono in H.
    rewrite H; auto.

    intros [x' [y' [p [q r]]]].
    rewrite r.
    unfold pc_lift2.
    destruct (pc_pair_iff x y x' y') as [l _].
    pose proof (l (conj p q)).
    rewrite H.
    rewrite pc_unit_ntrans.
    simpl.
    apply eq_refl.
  Defined.
  
    
    
End ClassicalParitalFunctions.

Class MetricSpace (A : Type) :=
  {
    metric : A -> A -> Real ;
    metric_axiom_identity : forall x, metric x x = real_0 ;
    metric_axiom_positivity : forall x y, x <> y -> metric x y > real_0 ;
    metric_axiom_symmetry : forall x y, metric x y = metric y x ;
    metric_axiom_triangle : forall x y z, metric x z <= metric x y + metric y z 
  }.

Section ClassicalContinuity1.

  Generalizable Variables A B C.
  Context `{mA : MetricSpace A}.
  Context `{mB : MetricSpace B}.
  
  Definition t_cont_at (f : A -> Nabla B) x :=
    forall eps, eps > real_0 -> exists delta, delta > real_0 /\ forall y fx fy,
            metric x y <= delta -> f x = Nabla_unit _ fx -> f y = Nabla_unit _ fy -> metric fx fy <= eps. 

  
  Definition cont_at (f : A -> pc B) x :=
    defined (f x) /\ forall eps, eps > real_0 -> exists delta, delta > real_0 /\ forall y fx fy,
            metric x y <= delta -> defined_to (f x) fx -> defined_to (f y) fy -> metric fx fy <= eps. 

End ClassicalContinuity1.

Section ClassicalContinuity2.

  Generalizable Variables A B C.
  Context `{mA : MetricSpace A}.
  Context `{mB : MetricSpace B}.
  Context `{mC : MetricSpace C}.

  Lemma cont_at_comp (f : A -> pc B) (g : B -> pc C) :
    forall x, cont_at f x -> forall fx, defined_to (f x) fx -> cont_at g fx -> cont_at (comp g f) x.
  Proof.
    intros.
    split.
    (* defined *)
    destruct H1.
    destruct H1.
    exists x0.
    apply (comp_iff g f x x0).
    exists fx.
    split; auto.

    (* eps-delta *)
    intros.
    destruct H as [definedA contf].
    destruct H1 as [definedB contg].
    destruct (contg eps H2) as [delta' [p1 p2]].
    destruct (contf delta' p1) as [delta [q1 q2]].
    exists delta.
    split; auto.
    intros y gfx gfy o ex ey.
    pose proof (comp_iff g f x gfx) as [h _].
    pose proof (h ex) as [fx' [p q]].
    assert (fx = fx').
    unfold defined_to in H0, p.
    rewrite p in H0.
    apply Nabla_unit_mono in H0; auto.
    injection H0; auto.
    induction H.
    clear p.

    pose proof (comp_iff g f y gfy) as [h3 _].
    pose proof (h3 ey) as [fy [h1 h2]].
    clear h h3.

    apply (p2 fy); auto.
    apply (q2 y); auto.
  Defined.
      
End ClassicalContinuity2.

Section ProductMaxDist.
  Generalizable Variables A B.
  Context `{mA : MetricSpace A}.
  Context `{mB : MetricSpace B}.

  Definition max_metric : A * B -> A * B -> ^Real.
  Proof.
    intros [x1 y1] [x2 y2].
    exact (real_max (metric x1 x2) (metric y1 y2)).
  Defined.

  Lemma max_metric_axiom_identity : forall x, max_metric x x = real_0.
  Proof.
    intros.
    unfold max_metric.
    destruct x.
    rewrite metric_axiom_identity.
    rewrite metric_axiom_identity.
    destruct (real_max_cand real_0 real_0); auto.
  Defined.

  Lemma max_metric_axiom_positivity : forall x y, x <> y -> max_metric x y > real_0.
  Proof.
  Admitted.
  
  Lemma max_metric_axiom_symmetry : forall x y, max_metric x y = max_metric y x.
  Proof.
  Admitted.
  
  Lemma max_metric_axiom_triangle : forall x y z, max_metric x z <= max_metric x y + max_metric y z.
  Proof.
  Admitted.

  Instance prod_max_metric_space : MetricSpace (A * B) :=
    {
      metric := max_metric ;
      metric_axiom_identity := max_metric_axiom_identity ;
      metric_axiom_positivity := max_metric_axiom_positivity ;
      metric_axiom_symmetry := max_metric_axiom_symmetry ;
      metric_axiom_triangle := max_metric_axiom_triangle 
    }.
  
End ProductMaxDist.


Section ClassicalContinuity3.

  Generalizable Variables A B C.
  Context `{mA : MetricSpace A}.
  Context `{mB : MetricSpace B}.
  Context `{mC : MetricSpace C}.

  Lemma cont_at_prod (f : A -> pc B) (g : A -> pc C) :
    forall x, cont_at f x -> cont_at g x -> @cont_at _ _ (B * C) prod_max_metric_space (fun x => pc_pair (f x) (g x)) x.
  Proof.
    intros x contf contg.
    destruct contf as [[fx fxe] contf].
    destruct contg as [[gx gxe] contg].
    split.
    (* defined *)
    pose proof (pc_pair_iff (f x) (g x) fx gx) as [h _].
    exists (fx, gx).
    apply h.
    clear h.
    auto.
    (* eps delta *)
    intros eps eps_pos.
    pose proof (contf eps eps_pos) as [deltaf [deltaf_pos pf]].    
    pose proof (contg eps eps_pos) as [deltag [deltag_pos pg]].
    exists (real_min deltaf deltag).
    split.
    destruct (real_min_cand deltaf deltag); auto.
    rewrite H; auto.
    rewrite H; auto.

    intros.
    unfold metric.
    unfold prod_max_metric_space.
    unfold max_metric.
    destruct fx0.
    destruct fy.
    destruct (real_max_cand (metric b b0) (metric c c0)).
    rewrite H2.
    clear H2.
    apply (pf y); auto.
    pose proof (real_min_fst_le deltaf deltag).
    apply (real_le_le_le _ _ _ H H2).
    pose proof (pc_pair_iff (f x) (g x) b c) as [_ h].
    apply h in H0.
    destruct H0; auto.
    pose proof (pc_pair_iff (f y) (g y) b0 c0) as [_ h].
    apply h in H1.
    destruct H1; auto.
    rewrite H2.
    clear H2.
    apply (pg y); auto.
    pose proof (real_min_snd_le deltaf deltag).
    apply (real_le_le_le _ _ _ H H2).
    pose proof (pc_pair_iff (f x) (g x) b c) as [_ h].
    apply h in H0.
    destruct H0; auto.
    pose proof (pc_pair_iff (f y) (g y) b0 c0) as [_ h].
    apply h in H1.
    destruct H1; auto.
  Defined.
  
End ClassicalContinuity3.

Declare Scope pcreal_scope.
Delimit Scope pcreal_scope with pcreal.

Notation pcReal := (pc Real).
Notation "x + y" := (pc_lift2 (fun a b => a + b) x y) : pcreal_scope.
Notation "x - y" := (pc_lift2 (fun a b => a - b) x y) : pcreal_scope.
Notation "x * y" := (pc_lift2 (fun a b => a * b) x y) : pcreal_scope.



  Lemma dist_axiom_identity : forall x, dist x x = real_0.
  Proof.
    intro x.
    destruct (dist_prop x x).
    destruct H0.
    apply H0; auto.
  Defined.
  
  Lemma real_le_eq_or_lt : forall x y, x <= y -> x = y \/ x < y.
  Proof.
  Admitted.
  
  Lemma dist_axiom_positivity : forall x y, x <> y -> dist x y > real_0.
  Proof.
    intros x y o.
    pose proof (dist_pos_t x y).
    pose proof (dist_zero x y).
    destruct (real_le_eq_or_lt _ _ H).
    apply eq_sym in H1.
    destruct H0.
    apply H0 in H1.
    contradict (o H1).
    exact H1.
  Defined.

  Lemma dist_axiom_symmetry : forall x y, dist x y = dist y x.
  Proof.
    apply dist_symm.
  Defined.
  
  Lemma dist_axiom_triangle : forall x y z, dist x z <= dist x y + dist y z.
  Proof.
    intros.
    apply dist_tri.
  Defined.
  
    
  Instance real_metric_space : MetricSpace ^Real :=
    {
      metric := dist ;
      metric_axiom_identity := dist_axiom_identity ;
      metric_axiom_positivity := dist_axiom_positivity ;
      metric_axiom_symmetry := dist_axiom_symmetry ;
      metric_axiom_triangle := dist_axiom_triangle
    }.

  Section ClassicalContinuityRealOps.

  Lemma dist_plus_le a b c d : dist (a+b) (c+d) <= dist a c + dist b d.
  Proof.
    unfold dist.
    assert (a+b - (c+d) = (a-c) + (b-d)) as -> by ring.
    apply abs_tri.
  Qed.

  Lemma dist_bound x y eps : dist x y <= eps -> abs y <= abs x + eps.
  Proof.
    intros.
    replace y with (x + (y-x)) by ring.
    rewrite dist_symm in H.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    apply real_le_le_plus_le; [apply real_le_triv | apply H].
  Qed.

 Lemma half_twice x : (x / real_2_neq_0) + (x / real_2_neq_0) = x.
 Proof.
    rewrite real_div_distr.

    replace (x + x) with (x * real_2) by (unfold real_2; simpl;ring).
    unfold real_div; rewrite real_mult_assoc, (real_mult_comm real_2), real_mult_inv.
    ring.
 Qed.

 Lemma half_le_le x y : (x <= y) -> (x / real_2_neq_0) <= (y / real_2_neq_0).
 Proof.
   intros.
   unfold real_div.
   apply (real_le_mult_pos_cancel real_2); [apply real_2_pos|].
   rewrite !real_mult_assoc.
   rewrite real_mult_inv.
   ring_simplify;auto.
 Qed.

  Lemma abs_plus_1_gt_0 : forall x, (abs x)+real_1 > real_0.
  Proof.
    intros.
    apply (real_lt_le_lt _ (real_0 + real_1)); [rewrite real_plus_unit; apply real_1_gt_0 |].
    apply real_le_le_plus_le; [apply abs_pos|apply real_le_triv].
  Qed.

  Lemma real_plus_cont : forall x,
      @cont_at (^Real * ^Real) prod_max_metric_space _ _ (fun x => Nabla_unit _ (Some ((fst x) + (snd x)))) x.
  Proof.
    intros [x y].
    split.
    exists (x + y).
    simpl.
    unfold defined_to; auto.

    intros eps eps_pos.
    exists (eps / real_2_neq_0).
    split.
    apply real_half_gt_zero; auto.
    intros [x' y'] x'' y''.
    simpl.
    intro ord.
    intros p q.
    apply Nabla_unit_mono in p.
    apply Nabla_unit_mono in q.
    injection p; intro h1.
    injection q; intro h2.
    rewrite <- h1, <- h2.
    clear p q h1 h2.
    apply (real_le_le_le _ _ _ (dist_plus_le _ _ _ _)).
    rewrite <-half_twice.
    apply real_le_le_plus_le.
    apply real_max_le_fst_le in ord.
    exact ord.
    apply real_max_le_snd_le in ord.
    exact ord.
  Defined.

  Lemma real_mult_cont : forall x, 
      @cont_at (^Real * ^Real) prod_max_metric_space _ _ (fun x => Nabla_unit _ (Some ((fst x) * (snd x)))) x.
  Proof.
    intros [x y].
    split.
    exists (x * y).
    simpl.
    unfold defined_to; auto.

    intros.
    
    pose proof (abs_plus_1_gt_0 x).
    remember (Minmax.real_min real_1 (eps / (real_gt_neq _ _ H0) / real_2_neq_0)) as eps0.
    assert (eps0 > real_0) as eps0gt0.
    {
      rewrite Heqeps0.
      destruct (Minmax.real_min_cand real_1 (eps / (real_gt_neq _ _ H0) / real_2_neq_0)) as [-> | ->].
      apply real_1_gt_0.
      apply real_half_gt_zero.
      unfold real_div.
      apply real_lt_pos_mult_pos_pos;auto.
      apply real_pos_inv_pos;auto.
    }
    assert (abs (y) + eps0  > real_0) as f2xepsgt0.
    {
      
      apply (real_lt_le_lt _ (real_0 + eps0)); [rewrite real_plus_unit; auto |].
      apply real_le_le_plus_le; [apply abs_pos|apply real_le_triv].
    }
    pose proof (abs_plus_1_gt_0 y).
    remember (eps / (real_gt_neq _ _ H1) / real_2_neq_0) as eps1.
    assert (eps1 > real_0) as eps1gt0.
    {
      rewrite Heqeps1.
      apply real_half_gt_zero.
      unfold real_div.
      apply real_lt_pos_mult_pos_pos;auto.
      apply real_pos_inv_pos;auto.
    }
    assert (forall a b c (cn0 : c <> real_0), a * (b / cn0) = (a*b)/ cn0) as diff by (intros;unfold real_div;ring_simplify;auto).
    exists (real_min eps0 eps1).
    simpl.
    split; [destruct (Minmax.real_min_cand eps0 eps1) as [-> | ->];auto|].
    intros.
    rename x into f1x.
    rename y into f2x.
    replace fx with (f1x *f2x).
    destruct y0 as [f1y f2y].
    replace fy with (f1y *f2y).
    unfold dist.
    replace (f1x * f2x - f1y * f2y) with ((f1x * (f2x -  f2y)) + (f2y * ( f1x - f1y))) by ring.
    replace eps with (eps / real_2_neq_0 + eps / real_2_neq_0) by apply half_twice.
    apply (real_le_le_le _ _ _ (abs_tri _ _)).
    apply real_le_le_plus_le;rewrite abs_mult.
    - apply (real_le_le_le _ (abs (f1x) * eps0)).
      + apply real_le_mult_pos_le; [apply abs_pos |].
        pose proof (real_le_le_le _ _ _ H2 (real_min_fst_le eps0 eps1)).
        pose proof (real_le_le_le _ _ _ (real_max_snd_ge  (dist f1x f1y) (dist f2x f2y)) H5).
        exact H6.
      + apply (real_le_le_le _ (abs f1x * (eps / real_gt_neq (abs f1x + real_1) real_0 H0 / real_2_neq_0))).
        rewrite Heqeps0.
        apply real_le_mult_pos_le;[apply abs_pos|].
        apply Minmax.real_min_snd_le.
        rewrite diff.
        apply half_le_le.
        unfold real_div.
        rewrite <-real_mult_assoc, real_mult_comm, <-real_mult_assoc, real_mult_comm.
        replace eps with ( eps * real_1) at 2 by ring.
        apply real_le_mult_pos_le;[apply real_lt_le;auto|].
        apply (real_le_mult_pos_cancel (abs (f1x) + real_1));auto.
        rewrite real_mult_assoc, (real_mult_comm (abs (f1x))), <-real_mult_assoc, real_mult_inv, !real_mult_unit.
        add_both_side_by (-abs (f1x)).
        apply real_lt_le;apply real_1_gt_0.
    - apply (real_le_le_le _ (abs (f2y) * eps1)).
      + apply real_le_mult_pos_le; [apply abs_pos |].
        pose proof (real_le_le_le _ _ _ H2 (real_min_snd_le eps0 eps1)).
        pose proof (real_le_le_le _ _ _ (real_max_fst_ge  (dist f1x f1y) (dist f2x f2y)) H5).
        exact H6.
      + rewrite Heqeps1.
        rewrite diff.
        apply half_le_le.
        unfold real_div.
        rewrite <-real_mult_assoc, real_mult_comm, <-real_mult_assoc, real_mult_comm.
        replace eps with ( eps * real_1) at 2 by ring.
        apply real_le_mult_pos_le;[apply real_lt_le;auto|].
        apply (real_le_mult_pos_cancel (abs (f2x) + real_1));auto.
        rewrite real_mult_assoc, (real_mult_comm (abs (f2y))), <-real_mult_assoc, real_mult_inv, !real_mult_unit.
        apply (real_le_le_le _ (abs f2x + eps0)).
        apply dist_bound.
        pose proof (real_le_le_le _ _ _ H2 (real_min_fst_le eps0 eps1)).
        pose proof (real_le_le_le _ _ _ (real_max_snd_ge  (dist f1x f1y) (dist f2x f2y)) H5).
        exact H6.
        apply real_le_plus_le.
        rewrite Heqeps0.
        apply Minmax.real_min_fst_le.
    -
      apply Nabla_unit_mono in H4.
      injection H4; intros; auto.
    -
      apply Nabla_unit_mono in H3.
      injection H3; intros; auto.
  Defined.
  
End ClassicalContinuityRealOps.


Section ClassicalDerivatives.
  Definition derivative_pt (f: Real -> pc Real) (gx : Real) x :=
    defined (f x) /\
      forall eps, eps > real_0 ->
                  exists delta, delta > real_0 /\
                                  forall y fx fy,
                                    dist x y <= delta ->
                                    defined_to (f x) fx -> defined_to (f y) fy ->
                                    abs (fy - fx - gx * (y -x)) <= eps * abs(y-x) .

  Definition cderivative (f g : Real -> pc Real) x0 r :=
    forall x, exists gx, defined_to (g x) gx /\  dist x x0 <= r -> derivative_pt f gx x.

  Fixpoint nth_derivative (f g : Real -> pc Real) x0 r n :=
    match n with
    | 0 => forall x, dist x x0 < r /\ defined (f x) -> forall y, defined_to (f x) y -> defined_to (g x) y
    | S n' => exists f', cderivative f f' x0 r /\ nth_derivative f' g x0 r n'
    end.

End ClassicalDerivatives.

Section ConstructiveVersions.
  Definition continuous (f: Real -> Real) x := forall eps, eps > real_0 -> {d : Real | d > real_0 /\ forall y, dist x y <= d -> dist (f x) (f y) <= eps}.

  Lemma continuous_ccontinuous f x : continuous f x -> @cont_at _ real_metric_space _ real_metric_space (fun x => Nabla_unit _ (Some (f x))) x.
  Proof.
    intros H.
    split.
    exists (f x).
    apply eq_refl. 

    intros.
    destruct (H eps) as [delta [H1 H2]];auto.
    exists delta;split;auto.
    intros.
    apply Nabla_unit_mono in H4, H5.
    injection H4; intros; injection H5; intros.
    rewrite <-H6, <-H7.
    apply H2.
    auto.
  Qed.
End ConstructiveVersions.

Section Examples.
  (* Definition sqrt: cfun. *)
  (* Proof. *)
  (*   exists (fun xy => (snd xy >= real_0) /\ (snd xy * snd xy) = fst xy ). *)
  (*   simpl. *)
  (*   intros x y1 y2 [[H1 H2] [H1' H2']]. *)
  (*   assert (forall z, z*z = real_0 -> z = real_0). *)
  (*   { *)
  (*     intros. *)
  (*     destruct (real_total_order z real_0) as [Z| [-> | Z]];auto; apply (real_eq_mult_cancel z); try rewrite H;try ring. *)
  (*     apply real_lt_neq;auto. *)
  (*     apply real_gt_neq;auto. *)
  (*   } *)
  (*   destruct H1;destruct H1'. *)
  (*   - apply real_pos_square_eq_eq; [| | rewrite H2, H2'];auto. *)
  (*   -  rewrite <-H1. *)
  (*      apply H. *)
  (*      rewrite H2. *)
  (*      rewrite <-H2'. *)
  (*      rewrite <-H1. *)
  (*      ring. *)
  (*   -  rewrite <-H0. *)
  (*      rewrite H;auto. *)
  (*      rewrite H2'. *)
  (*      rewrite <-H2. *)
  (*      rewrite <-H0;ring. *)
  (*   - rewrite <-H0, <-H1;auto. *)
  (* Qed. *)
End Examples.
