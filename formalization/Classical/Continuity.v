Require Import Real.
Require Import ClassicalMonads.
Require Import Minmax.


Require Import RealAssumption.
Require Import Classical.Partiality.
Require Import Classical.PartialReals.




Class MetricSpace (A : Type) :=
  {
    metric : A -> A -> Real ;
    metric_axiom_identity : forall x, metric x x = real_0 ;
    metric_axiom_positivity : forall x y, x <> y -> metric x y > real_0 ;
    metric_axiom_symmetry : forall x y, metric x y = metric y x ;
    metric_axiom_triangle : forall x y z, metric x z <= metric x y + metric y z 
  }.

Section MetricSpaceProperties.
  Generalizable Variables A.
  Context `{mA : MetricSpace A}.

  Lemma metric_non_negativity : forall x y, real_0 <= metric x y.
  Proof.
    intros.
    destruct (lem (x = y)).
    rewrite H.
    rewrite metric_axiom_identity.
    right; auto.
    left.
    exact (metric_axiom_positivity x y H).
  Defined.
  
End MetricSpaceProperties.

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
    intros [x y] [a b] nc.
    assert (x <> a \/ y <> b).
    destruct (lem ( x <> a \/ y <> b)); auto.
    assert (x = a).
    apply Prop_dn_elim.
    intro.
    contradict H.
    left; auto.
    assert (y = b).
    apply Prop_dn_elim.
    intro.
    contradict H.
    right; auto.
    contradict nc.
    rewrite H0, H1; auto.
    destruct H.
    pose proof (real_max_fst_ge (metric x a) (metric y b)).
    pose proof (@metric_axiom_positivity A mA x a H).
    apply (real_lt_le_lt _ _ _ H1 H0).
    pose proof (real_max_snd_ge (metric x a) (metric y b)).
    pose proof (metric_axiom_positivity _ _  H).
    apply (real_lt_le_lt _ _ _ H1 H0).
  Defined.
    
  Lemma max_metric_axiom_symmetry : forall x y, max_metric x y = max_metric y x.
  Proof.
    intros [x y] [a b].
    unfold max_metric.
    rewrite (metric_axiom_symmetry x a).
    rewrite (metric_axiom_symmetry y b).
    auto.
  Defined.
  
  Lemma max_metric_axiom_triangle : forall x y z, max_metric x z <= max_metric x y + max_metric y z.
  Proof.
    intros [x y] [a b] [i j].
    unfold max_metric.
    rewrite !real_max_plus_eq.
    apply real_max_compwise_le.
    apply real_max_fst_le_le.
    apply metric_axiom_triangle.
    apply real_max_snd_le_le.
    apply metric_axiom_triangle.
  Defined.
  

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



