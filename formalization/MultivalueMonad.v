Require Import Base.
Require Import Kleene.

(** Multivalue monad **)
(* Functor structure: *)
Structure Monad : Type :=
  {
    (* monad is a functor *)
    Monad_obj_map : Type -> Type; 
    Monad_fun_map : forall A B, (A -> B) -> Monad_obj_map A -> Monad_obj_map B;
    Monad_functorial_comp : forall A B C (f : A -> B) (g : B -> C),
        Monad_fun_map _ _ (fun x => g (f x)) = fun x => (Monad_fun_map _ _ g) ((Monad_fun_map _ _ f) x);
    Monad_functorial_id :  forall A, (fun x : Monad_obj_map A => x) = Monad_fun_map A A (fun x => x);

    (* monad has unit and mult *)
    Monad_unit : forall A : Type, A -> Monad_obj_map A;
    Monad_mult : forall A : Type, Monad_obj_map (Monad_obj_map A) -> Monad_obj_map A;

    (* unit and mult are nat. trans.  *)
    Monad_unit_ntrans : forall A B (f : A -> B) x, (Monad_fun_map A B f) (Monad_unit A x) = Monad_unit B (f x);

    Monad_mult_ntrans : forall A B (f : A -> B) x, Monad_mult B ((Monad_fun_map (Monad_obj_map A) (Monad_obj_map B) (Monad_fun_map A B f)) x) = (Monad_fun_map A B f) (Monad_mult A x);  

    (* coherence conditions *)
    Monad_coh1 : forall A x, Monad_mult A (Monad_unit (Monad_obj_map A) x) = x;
    Monad_coh2 : forall A x, Monad_mult A (Monad_fun_map A (Monad_obj_map A) (Monad_unit A)  x) = x;
    Monad_coh3 : forall A x, Monad_mult A (Monad_mult (Monad_obj_map A) x) = Monad_mult A (Monad_fun_map (Monad_obj_map (Monad_obj_map A)) (Monad_obj_map A) (Monad_mult A) x);

  }.


Definition preserves_hprop (M : Monad) := forall A, is_hprop A -> is_hprop (Monad_obj_map M A). 


Definition lifted_projP1 (M : Monad) : forall A (P : A -> Prop), (Monad_obj_map M) {x : A | P x} -> (Monad_obj_map M) A.
Proof.
  intros.
  apply ((Monad_fun_map M) {x : A | P x}).
  intro.
  destruct X0.
  exact x.
  exact X.
Defined. 

Definition trace_lifts_to_fiber (M : Monad) :
  forall P : nat -> Type,
  forall R : (forall n, P n -> P (S n) -> Prop),
    (Monad_obj_map M) (P O) ->
    (forall n (x : P n), (Monad_obj_map M) {y : P (S n) | R n x y}) ->
    forall n, (Monad_obj_map M) (P n).
Proof.
  intros P R X f.
  apply nat_rect.
  exact X.
  intros.
  pose proof (f n).
  apply Monad_mult.
  apply (Monad_fun_map M (P n)).
  intro.
  exact (lifted_projP1 M _ _ (X1 X2)).
  exact X0.
Defined.


(* given a collection of sections, get the retraction. *)
Definition sections_to_fibers (M : Monad) : forall P : nat -> Type,
    (Monad_obj_map M) (forall n, P n) -> (forall n, (Monad_obj_map M) (P n)).
Proof.
  intros P X n.
  apply ((Monad_fun_map M) _ _ (fun f => f n) X).
Defined.



Definition lifts_lifted_trace (M : Monad) := 
  forall P : nat -> Type,
  forall R : (forall n, P n -> P (S n) -> Prop),
  forall X : (Monad_obj_map M) (P O),
  forall f : (forall n (x : P n), (Monad_obj_map M) {y : P (S n) | R n x y}),
    {F : (Monad_obj_map M) {f : forall n, (P n) | forall m, R m (f m) (f (S m))} |
     sections_to_fibers _ _ (lifted_projP1 _ _ _ F) = trace_lifts_to_fiber M P R X f}.


(* classical non-empty subset monad *)
Section NonEmptyPowerSet.
  Definition NEPS_obj_map : Type -> Type := fun A => {P : A ->  Prop | exists x, P x}.
  Definition NEPS_fun_map : forall A B (f : A -> B), NEPS_obj_map A -> NEPS_obj_map B.
  Proof.
    intros.
    destruct X.
    
    exists (fun b => exists a, x a /\ b = f a).
    
    destruct e.
    exists (f x0).
    exists x0.
    auto.
  Defined.
  Lemma sigma_eqP2 : forall (A : Type) (P : A -> Prop) (x y : A) (a : P x) (b : P y),  x = y ->  exist P x a = exist P y b.
  Proof.
    intros.
    apply (sigma_eqP A P x y a b H).
    apply irrl.
  Defined.

  Definition NEPS_functorial_comp : forall A B C (f : A -> B) (g : B -> C),
      NEPS_fun_map _ _ (fun x => g (f x)) = fun x => (NEPS_fun_map _ _ g) ((NEPS_fun_map _ _ f) x).
  Proof.
    intros.
    apply fun_ext.
    intro.
    unfold NEPS_fun_map.
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

  

    Definition NEPS_functorial_id :  forall A, (fun x : NEPS_obj_map A => x) = NEPS_fun_map A A (fun x => x).
    Proof.
      intros.
      apply fun_ext.
      intro.
      unfold NEPS_fun_map.
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
    Definition NEPS_unit : forall A : Type, A -> NEPS_obj_map A.
    Proof.
      intros.
      exists (fun a => a = X).
      exists X; auto.
    Defined.
      
    Definition NEPS_mult : forall A : Type, NEPS_obj_map (NEPS_obj_map A) -> NEPS_obj_map A.
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
    Definition NEPS_unit_ntrans : forall A B (f : A -> B) x, (NEPS_fun_map A B f) (NEPS_unit A x) = NEPS_unit B (f x).
    Proof.
      intros.
      unfold NEPS_unit.
      unfold NEPS_fun_map.
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
   
    Definition NEPS_mult_ntrans : forall A B (f : A -> B) x, NEPS_mult B ((NEPS_fun_map (NEPS_obj_map A) (NEPS_obj_map B) (NEPS_fun_map A B f)) x) = (NEPS_fun_map A B f) (NEPS_mult A x).
    Proof.
      intros.
      unfold NEPS_mult.
      unfold NEPS_fun_map.
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
      exists (NEPS_fun_map _ _ f x2).
      split.
      exists x2.
      split; auto.
      unfold NEPS_fun_map.
      destruct x2.
      simpl.
      exists x1; auto.
    Defined.
    
    (* coherence conditions *)
    Definition NEPS_coh1 : forall A x, NEPS_mult A (NEPS_unit (NEPS_obj_map A) x) = x.
    Proof.
      intros.
      destruct x.
      unfold NEPS_mult.
      unfold NEPS_unit.
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
    
    Definition NEPS_coh2 : forall A x, NEPS_mult A (NEPS_fun_map A (NEPS_obj_map A) (NEPS_unit A)  x) = x.
    Proof.
      intros.
      unfold NEPS_mult, NEPS_fun_map, NEPS_obj_map, NEPS_unit.
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
    
    Definition NEPS_coh3 : forall A x, NEPS_mult A (NEPS_mult (NEPS_obj_map A) x) = NEPS_mult A (NEPS_fun_map (NEPS_obj_map (NEPS_obj_map A)) (NEPS_obj_map A) (NEPS_mult A) x).
    Proof.
    Admitted.
End NonEmptyPowerSet.


Structure MultivalueMonad (K : LazyBool) : Type :=
  {
    base_monad : Monad;
    base_monad_hprop_elim : forall A, is_hprop A -> is_equiv (Monad_unit base_monad A);
    base_monad_unit_is_mono : forall A, is_mono (Monad_unit base_monad A);
    base_monad_traces_lift : lifts_lifted_trace base_monad;
    multivalued_choice : forall x y : lazy_bool K, x = lazy_bool_true K \/ y = lazy_bool_true K -> Monad_obj_map base_monad ({ x = lazy_bool_true K } + { (y = lazy_bool_true K) });
    to_subset : forall A, Monad_obj_map base_monad A -> A -> Prop;
    to_subset_non_empty : forall A (X : Monad_obj_map base_monad A), exists x : A, to_subset A X x;
    to_subset_unit : forall A (a : A), to_subset A (Monad_unit base_monad A a) = (fun b : A => a = b);
    
  }.


Parameter M_structure : MultivalueMonad kleenean_structure.

Definition M : Type -> Type := Monad_obj_map (base_monad _ M_structure).
Definition M_lift : forall A B, (A -> B) -> M A -> M B := Monad_fun_map (base_monad _ M_structure).
Definition M_functorial_comp : forall A B C (f : A -> B) (g : B -> C),
    M_lift _ _ (fun x => g (f x)) = fun x => (M_lift _ _ g) ((M_lift _ _ f) x)
  := Monad_functorial_comp (base_monad _ M_structure).
Definition M_functorial_id : forall A, (fun x : M A => x) = M_lift A A (fun x => x)
:= Monad_functorial_id (base_monad _ M_structure).

(* Monadic structure: *)
Definition M_unit : forall T : Type, T -> M T
  := Monad_unit (base_monad _ M_structure).
Definition M_mult : forall T : Type, M (M T) -> M T
  := Monad_mult (base_monad _ M_structure). 
Definition M_lift_dom : forall A B, (A -> M B) -> M A -> M B :=
  fun A B f => fun x => M_mult B ((M_lift A (M B) f) x).
Definition M_unit_ntrans : forall A B (f : A -> B) x, (M_lift A B f) (M_unit A x) = M_unit B (f x)
  := Monad_unit_ntrans (base_monad _ M_structure).
Definition M_mult_ntrans : forall A B (f : A -> B) x, M_mult B ((M_lift (M A) (M B) (M_lift A B f)) x) = (M_lift A B f) (M_mult A x)
  := Monad_mult_ntrans (base_monad _ M_structure).  

(* coherence conditions for the monadic structure: *)
Definition M_coh1 : forall A x, M_mult A (M_unit (M A) x) = x := Monad_coh1 (base_monad _ M_structure).
Definition M_coh2 : forall A x, M_mult A (M_lift A (M A) (M_unit A)  x) = x := Monad_coh2 (base_monad _ M_structure).
Definition M_coh3 : forall A x, M_mult A (M_mult (M A) x) = M_mult A (M_lift (M (M A)) (M A) (M_mult A) x) := Monad_coh3 (base_monad _ M_structure). 


Definition M_hprop_elim : forall A, is_hprop A -> is_equiv (M_unit A) :=  base_monad_hprop_elim _ M_structure.
Definition M_unit_is_mono : forall A, is_mono (M_unit A) := base_monad_unit_is_mono _ M_structure.
Definition M_traces_lift := base_monad_traces_lift _ M_structure.
Definition M_choice : forall x y, (kleenean_up x \/ kleenean_up y) -> M ({kleenean_up x} + {kleenean_up y}) := (multivalued_choice _ M_structure).


Opaque M M_lift M_functorial_comp M_functorial_id M_unit M_mult M_unit_ntrans M_mult_ntrans M_coh1 M_coh2 M_coh3 M_hprop_elim M_unit_is_mono M_traces_lift M_choice.

  
Definition M_hprop_elim_f : forall A, is_hprop A -> M A -> A.
Proof.
  intros.
  exact (projP1 _ _ (M_hprop_elim A H) X).
Defined.

(* M unit is singleton {M_unit unit tt} *)
Lemma M_preserves_singleton : forall a : M unit, a = M_unit _ tt.
Proof.
  intros.
  pose proof (M_hprop_elim unit).
  assert (forall x y : unit, x = y).
  intros.
  destruct x, y; auto.
  destruct (X H).
  destruct a0.
  unfold fc, id in H1.
  apply (lp _ _ (fun k => k a)) in H1.
  rewrite (H (x a) (tt)) in H1.
  auto.
Defined.

(* M unit is subsingleton, of course. *)
Lemma M_singleton_is_hprop : is_hprop (M unit).
Proof.
  intros x y; rewrite (M_preserves_singleton x), (M_preserves_singleton y); exact eq_refl.
Defined.

(* lifting of a constant function is constant. This is because unit is preserved by M. *)  
Lemma M_lift_const_is_const : forall {A B} b, M_lift A B (fun _  => b) = fun _ => M_unit _ b.
Proof.
  intros.
  pose proof (M_functorial_comp A unit B (fun _ => tt) (fun _ => b)).
  rewrite H.
  assert ((M_lift A unit (fun _ : A => tt)) = (fc  (M_unit unit) (fun _ : M A => tt))).
  apply fun_to_subsingleton_id.
  apply M_singleton_is_hprop.
  rewrite H0.
  pose proof (M_unit_ntrans unit B (fun _ => b) tt).
  unfold fc.
  rewrite H1.
  auto.
Defined.

Definition M_projP1 : forall A (P : A -> Prop), M {x : A | P x} -> M A.
Proof.
  intros.
  apply (M_lift {x : A | P x}).
  intro.
  destruct X0.
  exact x.
  exact X.
Defined.

  
  (* := lifted_projP1 (base_monad _ M_structure). *)
  
(* Proof. *)
(*   intros. *)
(*   apply (M_lift {x : A | P x}). *)
(*   intro. *)
(*   destruct X0. *)
(*   exact x. *)
(*   exact X. *)
(* Defined.   *)

(* we can get sections from repeated M-valued procedures. 
   In the simple case, intuitively, when we have x0 : T, 
   and  f : nat -> T -> M T such that
   for all y \in (f n) xn, (R n) xn y holds, by repeatedly applying f,
   we can get a set of pathes {x0, x1, ...} such that R n (xn) (xn+1) holds. *)
Definition M_paths :
  forall P : nat -> Type,
  forall R : (forall n, P n -> P (S n) -> Prop),
    M (P O) ->
    (forall n (x : P n), M {y : P (S n) | R n x y}) ->
    M {f : forall n, (P n) | forall m, R m (f m) (f (S m))}.
Proof.
  intros.
  exact (projP1 _ _ (M_traces_lift P R X X0)).
Defined.


(* similarly as above, when we have when we have x0 : T, and f : nat -> T -> M T,
   we can apply primitive recursion and get a sequence of M T. 
   Note that this does not contain any information of paths. *)
Definition M_sets :
  forall P : nat -> Type,
  forall R : (forall n, P n -> P (S n) -> Prop),
    M (P O) ->
    (forall n (x : P n), M {y : P (S n) | R n x y}) ->
    forall n, M (P n).
Proof.
  intros P R X f.
  apply nat_rect.
  exact X.
  intros.
  pose proof (f n).
  apply (M_lift_dom (P n)).
  intro.
  exact (M_projP1 _ _ (X1 X2)).
  exact X0.
Defined.

(* given a collection of sections, get the retraction. *)
Definition M_retraction : forall P : nat -> Type,
    M (forall n, P n) -> (forall n, M (P n)).
Proof.
  intros P X n.
  apply (M_lift _ _ (fun f => f n) X).
Defined.

(* the axiomatized property of pathsM. When we obtain a set of 
   paths from a procedure, when we get the retraction, make the sequences of sets, 
   it has to be identical to the one obtained by M_sets *)
Lemma M_paths_prop : forall P R X f, M_retraction _ (M_projP1 _ _ (M_paths P R X f)) = M_sets P R X f.
Proof.
  intros.
  unfold M_paths.
  destruct ((M_traces_lift P R X f)).
  simpl.
  exact e.
Qed.


(* A special use case of pathsM: when we have a sequence of sets f : forall n, M (P n), 
   we can get the set of sections M (forall n, P n) *)
Definition M_countable_lift : forall P : nat -> Type, (forall n, M (P n)) -> M (forall n, P n).
Proof.
  intros P f.
  pose proof (M_paths P (fun _ _ _ => True) (f O)).
  simpl in X.
  assert ((forall n : nat, P n -> M {_ : P (S n) | True})).
  intros.
  pose proof (f (S n)).
  apply (M_lift (P (S n))).
  intro.
  exists X2.
  exact I.
  exact X1.
  pose proof (X X0).
  exact (M_projP1 _ _ X1).
Defined.

(* The property of countable lifting. It is the section of the retraction. *)
Lemma M_countable_lift_prop : forall P : nat -> Type, forall f,
      M_retraction P  (M_countable_lift P f) = f.
Proof.
  intros P f.
  unfold M_countable_lift.
  rewrite (M_paths_prop _ _ (f 0) (fun n _ => M_lift _ _ (fun X2 => exist _ X2 I) (f (S n)))).
  apply dfun_ext.
  intro.
  unfold M_sets.
  induction x.
  simpl.
  auto.
  simpl.
  rewrite IHx.
  simpl.
  unfold M_projP1,lifted_projP1,  M_lift_dom.
  
  
  assert (M_lift _ _  (fun X0 : {_ : P (S x) | True} => let (x0, _) := X0 in x0)
                (M_lift _ _ (fun X0 : P (S x) => exist _ X0 I) (f (S x))) = f (S x)).
  pose proof (M_functorial_comp _ _ _
                           (fun X0  => exist _ X0 I)
                           (fun X0 : {_ : P (S x) | True} => let (x0, _) := X0 in x0)).
  apply (lp  _ _ (fun k => k (f (S x)))) in H.
  rewrite <- H, <- M_functorial_id.
  
  exact eq_refl.

  rewrite H.
  assert ((M_lift (P x) (M (P (S x))) (fun _ : P x => f (S x)) (f x)) = M_unit _ (f (S x))).
  rewrite M_lift_const_is_const.
  exact eq_refl.
  rewrite H0, M_coh1.
  exact eq_refl.
Defined.

(* when we have two kleenean_structures that at least one of are True classically, 
   we can nondeterministically decide which holds. *)
Definition select : forall x y : kleenean, kleenean_up x \/ kleenean_up y -> M ({ (kleenean_up x) } + { (kleenean_up y) }).
Proof.
  apply M_choice.
Defined.


(* when there is p -> T and q -> T, we can nondeterministically join them *)
Definition mjoin (p q : Prop) (T : Type) : ({p}+{q} -> T) ->  M ({p}+{q}) -> M T.
Proof.
  intros f x.
  exact (M_lift _ _ f x).
Defined.

(* semideciability so that we can work on Prop directly, without mentioning K *)
Definition semidec := fun P : Prop => {x : kleenean | kleenean_up x <-> P}.

Definition choose : forall p q, semidec p -> semidec q -> p \/ q -> M ({p}+{q}).
Proof.
  intros.
  destruct H.
  destruct H0.
  destruct i.
  destruct i0.
  apply (M_lift ({kleenean_up x} + {kleenean_up x0})).
  intro.
  destruct H4; auto.
  apply select.
  destruct H1; auto.
Defined.

Definition dec := fun P : Prop =>  {P} + {~ P}.
Lemma semidec_dec : forall P, semidec P -> semidec (~ P) -> dec P.
Proof.
  intros P p q.
  pose proof (choose _ _ p q (lem P)).
  apply M_hprop_elim_f.
  
  intros t1 t2.
  destruct t1, t2.
  induction (irrl _ p0 p1);
    auto.
  induction (n p0).
  induction (n p0).
  induction (irrl _ n n0); auto.
  exact X.
Defined.

Definition M_extension : forall A B, M (A -> B) -> (M A -> M B).
Proof.
  intros.
  apply (M_lift_dom A).
  intro.
  apply (M_lift (A ->B)).
  auto.
  auto.
  auto.
Defined.



Lemma semidec_or P Q : semidec P -> semidec Q -> semidec (P \/ Q).
Proof.
  intros.
  destruct H as [k1 e1].
  destruct H0 as [k2 e2].
  exists (kleenean_or k1 k2).
  split; intro p.
  rewrite kleenean_or_up in p.
  destruct p as [H | H].
  left; apply proj1 in e1; apply e1, H.
  right; apply proj1 in e2; apply e2, H.
  rewrite kleenean_or_up.
  destruct p as [H | H].
  left; apply proj2 in e1; apply e1, H.
  right; apply proj2 in e2; apply e2, H.
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

Notation "[ x | P ]" := (M {x | P}) : type_scope.
Notation "[ x : T | P ]" := (M {x : T | P}) : type_scope.
Notation "[ ( a , b ) | P ]" := (M (sigT (fun a => {b | P}))) : type_scope.

(* Lemma M_unit_is_mono : forall A x y, M_unit A x = M_unit A y -> x = y. *)
(* Proof. *)
(*   intros. *)
(*   pose (f := (fun a => a = x)). *)
(*   assert (f x <> f y). *)
(*   simpl. *)
(*   unfold f. *)
(*   Check f. *)
(*   destruct f. *)
(*   f. *)
  
  
Definition Mand : M Prop -> Prop.
Proof.
  intro.
  exact (X = M_unit _ True).
Defined.

Definition Mor : M Prop -> Prop.
Proof.
  intro.
  exact (~ (X = M_unit _ False)).
Defined.

Lemma Mor_is_retract : forall P : Prop, Mor (M_unit _ P) = P.
Proof.
  intro P.
  destruct (lem P).
  unfold Mor.
  assert (e : P = True) by (apply Prop_ext; auto).
  rewrite e.
  apply Prop_ext.
  intro; auto.
  intro.
  intro.
  apply M_unit_is_mono in H1.
  rewrite <- H1; auto.
  apply Prop_ext.
  intro; auto.
  unfold Mor in H0.
  assert (P = False).
  apply Prop_ext; intro; auto.
  contradict H1.
  rewrite H1 in H0.
  contradict H0; auto.
  intro.
  contradict (H H0).
Defined.
  
Lemma Mand_is_retract : forall P : Prop, Mand (M_unit _ P) = P.
Proof.
  intro P.
  destruct (lem P).
  unfold Mand.
  assert (e : P = True) by (apply Prop_ext; auto).
  rewrite e.
  apply Prop_ext; intro; auto; auto.
  assert (e : P = False); apply Prop_ext; intro ; auto.
  contradict H0.
  rewrite e in H0.
  unfold Mand in H0.
  pose proof(M_unit_is_mono _ _ _ H0).
  assert False by (rewrite H1; auto).
  contradict H2.
  rewrite e in H0; contradict H0.
Defined.

Definition M_all {A} (P : A -> Prop) : M A -> Prop := fun X => Mand (M_lift _ _ P X).
Definition M_some {A} (P : A -> Prop) : M A -> Prop := fun X => Mor (M_lift _ _ P X).
Definition M_in {A} (a : A) (X : M A) : Prop := M_some (fun b => a = b) X. 
  
(* Goal forall A (P : A -> Prop) (X : M A), M_all P X -> forall a, M_in a X -> P a. *)
(* Proof. *)
(*   intros. *)
(*   unfold M_all in H. *)
(*   unfold Mand in H. *)
(*   unfold M_in in H0. *)
(*   unfold M_some in H0. *)
(*   unfold Mor in H0. *)
  

(* Lemma M_existence_to_all : forall A (P : A -> Prop), M {x | P x} -> {x : M A | M_all P x}. *)
(* Proof. *)
(*   intros. *)
(*   exists (M_projP1 _ _  X). *)
(*   unfold M_all. *)
(*   unfold Mand. *)
(*   pose proof @M_lift_const_is_const A Prop True. *)
(*   apply *)
    
(*   unfold M_projP1. *)

(*   simpl. *)
  
(*   simpl. *)
  
  
(*       (*   simpl. *) *)
