Require Import Base.
Require Import Kleene.

Section Sierpinski.
  Generalizable Variable K.
  Context `{klb : LazyBool K}.


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
    
End Sierpinski.
