Require Import Base.
Require Import Kleene.
Require Import Monad ClassicalMonads MultivalueMonad.
Section Sierpinski.
  
  Generalizable Variables K M.

  Context `{klb : LazyBool K} `{M_Monad : Monad M}
          {MultivalueMonad_description : Monoid_hom M_Monad NPset_Monad} 
          {M_MultivalueMonad : MultivalueMonad}
          .

  

  Definition S :=  {k : K | k <> lazy_bool_false}.
  Definition S_top : S.
  Proof.
    exists lazy_bool_true.
    apply lazy_bool_true_neq_false.
  Defined.

  Definition S_bot : S.
  Proof.
    exists lazy_bool_undef.
    intro.
    apply lazy_bool_false_neq_undef.
    apply eq_sym, H.
  Defined.

  Definition is_S_defined s := s = S_top.
  Definition is_S_undefined s := s = S_bot.
  
  Definition S_semidec (P : Prop) := {s : S | is_S_defined s = P}.

  Definition K_to_S : K -> S.
  Proof.
    intro.
    pose proof (lazy_bool_retract_to_true).
    destruct X0.
    exists (x X).
    pose proof (lazy_bool_all X).
    destruct H.
    destruct a as [a _].
    rewrite H.
    rewrite a.
    apply lazy_bool_true_neq_false.
    destruct H.
    rewrite H.
    destruct a as [_ [_ a]].
    rewrite a.
    intro.
    apply lazy_bool_false_neq_undef.
    apply eq_sym, H0.
    rewrite H.
    destruct a as [_ [a _]].
    rewrite a.
    intro.
    apply lazy_bool_false_neq_undef.
    apply eq_sym, H0.
  Defined.
      
  Lemma K_semidec_is_S_semidec : forall P, semidec P -> S_semidec P.
  Proof.
    intro.
    intro.
    destruct X.
    exists (K_to_S x).
    rewrite <- e.
    apply Prop_ext.
    intro.
    unfold K_to_S, is_S_defined, S_top in H.
    destruct (lazy_bool_retract_to_true).
    apply (lp _ _ (@projP1 _ _ )) in H. 
    simpl in H.
    destruct (lazy_bool_all x).
    exact H0.
    destruct H0.
    rewrite H0 in H.
    destruct a as [_ [_ a]].
    rewrite H in a.
    contradict (lazy_bool_true_neq_undef a).
    rewrite H0 in H.
    destruct a as [_ [a _]].
    rewrite H in a.
    contradict (lazy_bool_true_neq_undef a).
    intro.
    unfold is_S_defined, K_to_S, S_top.
    destruct (lazy_bool_retract_to_true).
    unfold lazy_bool_up in H.
    rewrite H.
    assert ((x0 lazy_bool_true) = lazy_bool_true).
    destruct a as [a _]; apply a.
    apply (sigma_eqP _ _ _ _ _ _ H0).
    apply irrl.
  Defined.
  
  Lemma S_countable_up : forall f : nat -> S, {s : S | (is_S_defined s = exists n, is_S_defined (f n))}.
  Proof.
    intros.
    unfold S in f.
    pose proof (M_countable_andor (fun n => @projP1 _ _ (f n))).
    apply M_hprop_elim in X.
    destruct X.
    destruct a as [a [b c]].
    assert (x <> lazy_bool_false).
    intro.
    pose proof (b H).
    destruct H0.
    destruct (f x0).
    simpl in H0.
    contradict (n H0).
    exists (exist _ x H).
    apply Prop_ext.
    intro.
    unfold is_S_defined in H0.
    apply (lp _ _ (fun k => @projP1 _ _ k)) in H0.
    simpl in H0.
    pose proof (a H0).
    destruct H1.
    exists x0.
    destruct (f x0).
    simpl.
    unfold lazy_bool_up in H1.
    simpl in H1.
    unfold is_S_defined.
    unfold S_top.
    apply (sigma_eqP _ _ _ _ _ _ H1).
    apply irrl.
    intro.
    destruct H0.
    destruct (lazy_bool_all x).
    apply (sigma_eqP _ _ _ _ _ _ H1).
    apply irrl.
    destruct H1.
    contradict (H H1).
    unfold lazy_bool_lazy in c.
    rewrite c in H1.
    pose proof (H1 x0).
    unfold is_S_defined in H0.
    destruct (f x0).
    simpl in H2.
    apply (lp _ _ (fun k => @projP1 _ _ k )) in H0.
    simpl in H0.
    rewrite H0 in H2.
    contradict (lazy_bool_true_neq_undef H2).

    intros x y.
    destruct x, y.
    assert (x = x0).
    destruct a as [a [b c]].
    destruct a0 as [aa [bb cc]].
    destruct (lazy_bool_all x).
    destruct (lazy_bool_all x0).
    rewrite H, H0; auto.
    destruct H0.
    pose proof (bb H0).
    destruct H1.
    destruct (f x1).
    simpl in H1.
    contradict (n H1).
    unfold lazy_bool_lazy in cc.
    rewrite cc in H0.
    pose proof (a H).
    destruct H1.
    pose proof (H0 x1).
    rewrite H2 in H1.
    apply eq_sym in H1.
    contradict (lazy_bool_true_neq_undef H1).
    destruct H.
    pose proof (b H).
    destruct H0.
    destruct (f x1).
    simpl in H0.
    contradict (n H0).
    unfold lazy_bool_lazy in c.
    rewrite H.
    rewrite c in H.
    destruct (lazy_bool_all x0).
    pose proof (aa H0).
    destruct H1.
    pose proof (H x1).
    destruct (f x1).
    simpl in H2.
    simpl in H1.
    rewrite H2 in H1.
    apply eq_sym in H1.
    contradict (lazy_bool_true_neq_undef H1).
    destruct H0.
    pose proof (bb H0).
    destruct H1.
    destruct (f x1).
    simpl in H1.
    contradict (n H1).
    rewrite H0.
    apply eq_refl.
    apply (sigma_eqP _ _ _ _ _ _ H).
    apply irrl.
  Defined.
  
    
End Sierpinski.
