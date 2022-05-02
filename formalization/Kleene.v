Require Import Base.

(** Kleene type **)
Class LazyBool (LB : Type) :=
  {
    lazy_bool_true : LB;
    lazy_bool_false : LB;
    lazy_bool_undef : LB;

    lazy_bool_all : forall k : LB, (k = lazy_bool_true) \/ (k = lazy_bool_false) \/ (k = lazy_bool_undef);
      
    lazy_bool_true_neq_false : lazy_bool_true <> lazy_bool_false;
    lazy_bool_true_neq_undef : lazy_bool_true <> lazy_bool_undef;
    lazy_bool_false_neq_undef : lazy_bool_false <> lazy_bool_undef;


    lazy_bool_retract_to_true : {r : LB -> LB | r lazy_bool_true = lazy_bool_true /\ r lazy_bool_undef = lazy_bool_undef /\ r lazy_bool_false = lazy_bool_undef};  
    lazy_bool_retract_to_false: {r : LB -> LB | r lazy_bool_true = lazy_bool_undef /\ r lazy_bool_undef = lazy_bool_undef /\ r lazy_bool_false = lazy_bool_false};  
    
    lazy_bool_neg : LB -> LB;
    lazy_bool_or : LB -> LB -> LB;
    lazy_bool_and : LB -> LB -> LB;

    lazy_bool_defined_is_bool : forall k,
        (k = lazy_bool_true \/ k = lazy_bool_false) -> ({k = lazy_bool_true} + {k = lazy_bool_false});
    lazy_bool_neg_up : forall k, (lazy_bool_neg k = lazy_bool_true) = (k = lazy_bool_false);
    lazy_bool_neg_down : forall k, (lazy_bool_neg k = lazy_bool_false) = (k = lazy_bool_true);

    lazy_bool_and_up : forall a b, (lazy_bool_and a b = lazy_bool_true) = (a = lazy_bool_true /\ b = lazy_bool_true);
    lazy_bool_and_down : forall a b, (lazy_bool_and a b = lazy_bool_false) = (a = lazy_bool_false \/ b = lazy_bool_false);

    lazy_bool_or_up : forall a b, (lazy_bool_or a b = lazy_bool_true) = (a = lazy_bool_true \/ b = lazy_bool_true);
    lazy_bool_or_down : forall a b, (lazy_bool_or a b = lazy_bool_false) = (a = lazy_bool_false /\ b = lazy_bool_false);
  }.

Section K_Defs.

  Generalizable Variable K.

  Context `{klb : LazyBool K}.

  Definition lazy_bool_up : K -> Prop := fun b : K => b = lazy_bool_true.
  Definition lazy_bool_down : K -> Prop := fun b : K => b = lazy_bool_false.

  (* semideciability so that we can work on Prop directly, without mentioning K *)
  Definition semidec := fun P : Prop => {x : K | lazy_bool_up x = P}.

Lemma semidec_or P Q : semidec P -> semidec Q -> semidec (P \/ Q).
Proof.
  intros.
  destruct X as [k1 e1].
  destruct X0 as [k2 e2].
  exists (lazy_bool_or k1 k2).
  apply Prop_ext; intro p.
  unfold lazy_bool_up in p.
  rewrite lazy_bool_or_up in p.

  destruct p as [H | H].
  rewrite H in e1.
  left.
  rewrite <- e1.
  unfold lazy_bool_up; apply eq_refl.
  rewrite H in e2.
  right.
  rewrite <- e2.
  unfold lazy_bool_up; apply eq_refl.
  
  unfold lazy_bool_up.
  rewrite lazy_bool_or_up.
  destruct p as [H | H].
  left.
  rewrite <- e1 in H.
  unfold lazy_bool_up in H.
  exact H.
  right.
  rewrite <- e2 in H.
  unfold lazy_bool_up in H.
  exact H.
Defined.

Lemma semidec_and P Q : semidec P -> semidec Q -> semidec (P /\ Q).
Proof.
  intros.
  destruct X as [k1 e1].
  destruct X0 as [k2 e2].
  exists (lazy_bool_and k1 k2).
  apply Prop_ext; intro p.
  unfold lazy_bool_up in p.
  rewrite lazy_bool_and_up in p.
  destruct p as [H H1].
  split.
  rewrite H in e1.
  rewrite <- e1; unfold lazy_bool_up; auto.
  rewrite H1 in e2.
  rewrite <- e2; unfold lazy_bool_up; auto.
  
  unfold lazy_bool_up.
  rewrite lazy_bool_and_up.
  destruct p as [H H1].
  split.
  rewrite <- e1 in H.
  unfold lazy_bool_up in H.
  exact H.
  rewrite <- e2 in H1.
  unfold lazy_bool_up in H1.
  exact H1.
  
Defined.


End K_Defs.
