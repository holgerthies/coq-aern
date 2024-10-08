Require Import Base.
Require Import Kleene.
Require Import Monad.
Require Import ClassicalMonads.

Section Monad_Defs.

(* Generalizable Variables types. *)

Context {types : RealTypes}.

#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).

Context {M_Monad : Monad ^M}.

(* Definition preserves_hprop (M : Monad) := forall A, is_hprop A -> is_hprop (Monad_obj_map M A).  *)

Definition lifted_projP1  : forall A (P : A -> Prop), ^M {x : A | P x} -> ^M A.
Proof.
  intros.
  apply (Monad_fun_map {x : A | P x}).
  intro.
  destruct X0.
  exact x.
  exact X.
Defined. 

Definition trace_lifts_to_fiber:
  forall P : nat -> Type,
  forall R : (forall n, P n -> P (S n) -> Prop),
    ^M (P O) ->
    (forall n (x : P n), ^M {y : P (S n) | R n x y}) ->
    forall n, ^M (P n).
Proof.
  intros P R X f.
  apply nat_rect.
  exact X.
  intros.
  pose proof (f n).
  apply Monad_mult.
  apply (Monad_fun_map (P n)).
  intro.
  exact (lifted_projP1 _ _ (X1 X2)).
  exact X0.
Defined.

(* given a collection of sections, get the retraction. *)
Definition sections_to_fibers : forall P : nat -> Type,
    ^M (forall n, P n) -> (forall n, ^M (P n)).
Proof.
  intros P X n.
  apply (Monad_fun_map _ _ (fun f => f n) X).
Defined.

Definition lifts_lifted_trace := 
  forall P : nat -> Type,
  forall R : (forall n, P n -> P (S n) -> Prop),
  forall X : M (P O),
  forall f : (forall n (x : P n), M {y : P (S n) | R n x y}),
    {F : M {f : forall n, (P n) | forall m, R m (f m) (f (S m))} |
     sections_to_fibers _ (lifted_projP1 _ _ F) = trace_lifts_to_fiber P R X f}.

End Monad_Defs.

Lemma NPset_unit_is_mono : forall A, is_mono (Monad_unit A : A -> NPset A).
Proof.
  intros.
  intros x y H.
  apply sigma_eqP_pr1 in H.
  apply (lp _ _ (fun g => g x)) in H.
  rewrite <- H; auto.
Defined.

Lemma Nabla_unit_is_mono : forall A, is_mono (Monad_unit A : A -> Nabla A).
Proof.
  intros.
  intros x y H.
  apply sigma_eqP_pr1 in H.
  apply (lp _ _ (fun g => g x)) in H.
  rewrite <- H; auto.
Defined.

Section M_Defs.

Class MultivalueMonad_M (types : RealTypes) :=
  {
    klb :> LazyBool_K types;
    M_Monad :> Monad (@M types);
    M_description_hom :> Monoid_hom M_Monad NPset_Monad;
    M_base_monad_hprop_elim : forall A, is_hprop A -> is_equiv (Monad_unit A);
    M_base_monad_traces_lift : lifts_lifted_trace;
    multivalued_choice : forall x y : K, x = lazy_bool_true \/ y = lazy_bool_true -> @M types ({ x = lazy_bool_true } + { (y = lazy_bool_true) });

    M_description_is_mono : Monoid_hom_is_mono _ _ M_description_hom;
    M_description_is_equiv : forall A, is_equiv (Monad_fun_map _ _ (Monoid_hom_nat_trans _ _ A));

    M_destruct : forall A (X : @M types A), @M types {x : A | projP1 _ _ (Monoid_hom_nat_trans _ _ A X) x};

     M_countable_selection :
      forall x : nat -> K,
        (exists n, x n = lazy_bool_true ) ->
        @M types {n | x n = lazy_bool_true };

    seq_subset_continuity :
      forall {X} (f : (nat -> X) -> K) (x : (nat -> X)), 
        (f x) = lazy_bool_true -> 
        @M types {m | forall y, (forall n, (n < m)%nat -> x n = y n) -> (f y )= lazy_bool_true};
    
    kleenean_to_nat_sequence : 
      forall (k : K), 
        @M types {f : nat -> nat | k = lazy_bool_true <-> exists n, (f n) = 1};

    M_baire_choice :
      let Mor := fun X : @M types Prop => X <> Monad_unit Prop False in
      let M_some := fun {A} (P : A -> Prop) X => (Mor (Monad_fun_map _ _ P X)) in
      let M_in := fun {A} (a : A) (X : M A) => M_some (fun b => a = b) X in
      forall (P : (nat -> nat) -> Type) (f : forall ϕ, @M types (P ϕ)),
        @M types {s : forall ϕ, P ϕ | forall ϕ, M_in (s ϕ) (f ϕ)}
  }.

Context {types : RealTypes} {mvmM : @MultivalueMonad_M types}.
#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).

Definition M_description A := @Monoid_hom_nat_trans _ _ _ _ M_description_hom A.

(* Definition M : Type -> Type := M. *)
Definition M_lift : forall A B, (A -> B) -> ^M A -> ^M B := Monad_fun_map.
Definition M_functorial_comp : forall A B C (f : A -> B) (g : B -> C),
    M_lift _ _ (fun x => g (f x)) = fun x => (M_lift _ _ g) ((M_lift _ _ f) x)
  := Monad_functorial_comp.
Definition M_functorial_id : forall A, (fun x : M A => x) = M_lift A A (fun x => x)
:= Monad_functorial_id.

(* Monadic structure: *)
Definition M_unit : forall T : Type, T -> ^M T
  := Monad_unit.
Definition M_mult : forall T : Type, ^M (^M T) -> ^M T
  := Monad_mult. 
Definition M_lift_dom : forall A B, (A -> ^M B) -> ^M A -> ^M B :=
  fun A B f => fun x => M_mult B ((M_lift A (M B) f) x).
Definition M_unit_ntrans : forall A B (f : A -> B) x, (M_lift A B f) (M_unit A x) = M_unit B (f x)
  := Monad_unit_ntrans.
Definition M_mult_ntrans : forall A B (f : A -> B) x, M_mult B ((M_lift (M A) (M B) (M_lift A B f)) x) = (M_lift A B f) (M_mult A x)
  := Monad_mult_ntrans.

(* coherence conditions for the monadic structure: *)
Definition M_coh1 : forall A x, M_mult A (M_unit (M A) x) = x := Monad_coh1.
Definition M_coh2 : forall A x, M_mult A (M_lift A (M A) (M_unit A)  x) = x := Monad_coh2.
Definition M_coh3 : forall A x, M_mult A (M_mult (M A) x) = M_mult A (M_lift (M (M A)) (M A) (M_mult A) x) := Monad_coh3. 


Definition M_hprop_elim : forall A, is_hprop A -> is_equiv (M_unit A) :=  M_base_monad_hprop_elim.
(* Definition M_unit_is_mono : forall A, is_mono (M_unit A) := MultivalueMonad_base_monad_unit_is_mono _ M_structure. *)
Definition M_traces_lift := M_base_monad_traces_lift.
Definition M_choice := multivalued_choice.

Definition M_picture : forall {A}, ^M A -> NPset A.
Proof.
  intros A X.
  exact (M_description A X).
Defined.

Definition M_picture_1 : forall {A}, ^M A -> A -> Prop.
Proof.
  intros A X.
  exact (projP1 _ _ (M_description A X)).
Defined.

Definition M_W_destruct : forall {A} (X : M A), exists x : A, M_picture_1 X x.
Proof.
  intros.
  unfold M_picture_1.
  destruct (M_description A X).
  exact e.
Defined.


Lemma M_unit_is_mono : forall A, is_mono (M_unit A).
Proof.
  intros A x y H.
  pose proof M_description_is_mono.
  unfold Monoid_hom_is_mono in H0.
  pose proof (Monoid_hom_unit _ _ A ).
  apply (lp _ _ (fun g => g x)) in H1.
  pose proof (Monoid_hom_unit _ _ A ).
  apply (lp _ _ (fun g => g y)) in H2.
  unfold M_unit in H.
  rewrite H in H1.
  rewrite H1 in H2.
  apply NPset_unit_is_mono in H2.
  exact H2.
Defined.  


Lemma M_fun_picture : forall {A B} (f : A -> B), NPset A -> NPset B.
Proof.
  intros A B f.
  exact (Monad_fun_map _ _ f).
Defined.

Lemma M_fun_cont : forall {A B} (f : A -> B) X b , M_picture_1 (M_lift _ _ f X) b = exists a, (M_picture_1 X) a /\ b = f a  .
Proof.
  intros.
  unfold M_picture_1.
  pose proof ((Monoid_hom_nat_trans_prop _ _ _ _ f)).
  apply (lp _ _ (fun g => g X)) in H.
  fold (M_description A) in H.
  fold (M_description B) in H.
  unfold M_lift.
  rewrite H.
  clear H.
  apply Prop_ext.
  intro.
  destruct (M_description A X).
  destruct e.
  simpl in H.
  destruct H.
  exists x2; auto.
  intro.
  destruct H.
  destruct (M_description A X).
  simpl.
  destruct e.
  exists x.
  simpl in H.
  auto.
Defined.

Lemma M_fun_cont_r : forall {A B} (f : A -> B), forall X x, M_picture_1 X x -> M_picture_1 (M_lift _ _ f X) (f x).
Proof.
  intros.
  pose proof ((Monoid_hom_nat_trans_prop _ _  A B f)).
  apply (lp _ _ (fun g => g X)) in H0.
  unfold M_picture_1.
  fold (M_description B) in H0.
  unfold M_lift.
  rewrite H0.
  unfold M_picture_1 in H.
  pose (j :=  (Monoid_hom_nat_trans _ _ A X)).
  fold j.
  unfold M_description in H.
  fold j in H.
  destruct j.
  simpl in H.
  simpl.
  exists x; auto.
Defined.

Lemma M_fun_cont_r_inv : forall {A B} (f : A -> B), forall X y, M_picture_1 (Monad_fun_map _ _ f X) y -> exists x, M_picture_1 X x /\ y = f x.
Proof.
 
  intros.
  pose proof ((Monoid_hom_nat_trans_prop _ _  A B f)).
  apply (lp _ _ (fun g => g X)) in H0.
  unfold M_picture_1, M_description in H.
  rewrite H0 in H.
  clear H0.
  unfold M_picture_1, M_description.
  
  
  pose (XP :=  (Monoid_hom_nat_trans _ _ A X)).
  fold XP.
  fold XP in H.
  destruct XP.
  simpl in H.
  destruct H.
  exists x0.
  simpl; auto.
Defined.

Definition M_hprop_elim_f : forall A, is_hprop A -> ^M A -> A.
Proof.
  intros.
  exact (projP1 _ _ (M_base_monad_hprop_elim A H) X).
Defined.

(* M unit is singleton {Monad_unit unit tt} *)
Lemma M_preserves_singleton : forall a : ^M unit, a = Monad_unit _ tt.
Proof.
  intros.
  pose proof (M_base_monad_hprop_elim unit).
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
Lemma M_singleton_is_hprop : is_hprop (^M unit).
Proof.
  intros x y; rewrite (M_preserves_singleton x), (M_preserves_singleton y); exact eq_refl.
Defined.

(* lifting of a constant function is constant. This is because unit is preserved by M. *)  
Lemma Monad_fun_map_const_is_const : forall {A B} b, Monad_fun_map A B (fun _  => b) = fun _ => M_unit _ b.
Proof.
  intros.
  pose proof (M_functorial_comp A unit B (fun _ => tt) (fun _ => b)).
  unfold M_lift in H.
  rewrite H.
  assert ((Monad_fun_map A unit (fun _ : A => tt)) = (fc  (M_unit unit) (fun _ : M A => tt))).
  apply fun_to_subsingleton_id.
  apply M_singleton_is_hprop.
  rewrite H0.
  pose proof (M_unit_ntrans unit B (fun _ => b) tt).
  unfold fc.
  fold M_lift.
  rewrite H1.
  auto.
Defined.

Definition M_projP1 : forall A (P : A -> Prop), ^M {x : A | P x} -> ^M A.
Proof.
  intros.
  apply (Monad_fun_map {x : A | P x}).
  intro.
  destruct X0.
  exact x.
  exact X.
Defined.

  
  (* := lifted_projP1 M. *)
  
(* Proof. *)
(*   intros. *)
(*   apply (Monad_fun_map {x : A | P x}). *)
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
    ^M (P O) ->
    (forall n (x : P n), ^M {y : P (S n) | R n x y}) ->
    ^M {f : forall n, (P n) | forall m, R m (f m) (f (S m))}.
Proof.
  intros.
  exact (projP1 _ _ (M_base_monad_traces_lift P R X X0)).
Defined.


(* similarly as above, when we have when we have x0 : T, and f : nat -> T -> M T,
   we can apply primitive recursion and get a sequence of M T. 
   Note that this does not contain any information of paths. *)
Definition M_sets :
  forall P : nat -> Type,
  forall R : (forall n, P n -> P (S n) -> Prop),
    ^M (P O) ->
    (forall n (x : P n), ^M {y : P (S n) | R n x y}) ->
    forall n, ^M (P n).
Proof.
  intros P R X f.
  apply nat_rect.
  exact X.
  intros.
  pose proof (f n).
  apply (Monad_fun_map_dom (P n)).
  intro.
  exact (M_projP1 _ _ (X1 X2)).
  exact X0.
Defined.

(* given a collection of sections, get the retraction. *)
Definition M_retraction : forall P : nat -> Type,
    ^M (forall n, P n) -> (forall n, ^M (P n)).
Proof.
  intros P X n.
  apply (Monad_fun_map _ _ (fun f => f n) X).
Defined.

(* the axiomatized property of pathsM. When we obtain a set of 
   paths from a procedure, when we get the retraction, make the sequences of sets, 
   it has to be identical to the one obtained by M_sets *)
Lemma M_paths_prop : forall P R X f, M_retraction _ (M_projP1 _ _ (M_paths P R X f)) = M_sets P R X f.
Proof.
  intros.
  unfold M_paths.
  destruct ((M_base_monad_traces_lift P R X f)).
  simpl.
  exact e.
Qed.


(* A special use case of pathsM: when we have a sequence of sets f : forall n, M (P n), 
   we can get the set of sections M (forall n, P n) *)
Definition M_countable_lift : forall P : nat -> Type, (forall n, ^M (P n)) -> ^M (forall n, P n).
Proof.
  intros P f.
  pose proof (M_paths P (fun _ _ _ => True) (f O)).
  simpl in X.
  assert ((forall n : nat, P n -> ^M {_ : P (S n) | True})).
  intros.
  pose proof (f (S n)).
  apply (Monad_fun_map (P (S n))).
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
  rewrite (M_paths_prop _ _ (f 0) (fun n _ => Monad_fun_map _ _ (fun X2 => exist _ X2 I) (f (S n)))).
  apply dfun_ext.
  intro.
  unfold M_sets.
  induction x.
  simpl.
  auto.
  simpl.
  rewrite IHx.
  simpl.
  unfold M_projP1,lifted_projP1,  Monad_fun_map_dom.
  
  
  assert (Monad_fun_map _ _  (fun X0 : {_ : P (S x) | True} => let (x0, _) := X0 in x0)
                (Monad_fun_map _ _ (fun X0 : P (S x) => exist _ X0 I) (f (S x))) = f (S x)).
  pose proof (M_functorial_comp _ _ _
                           (fun X0  => exist _ X0 I)
                           (fun X0 : {_ : P (S x) | True} => let (x0, _) := X0 in x0)).
  apply (lp  _ _ (fun k => k (f (S x)))) in H.
  unfold M_lift in H.
  rewrite <- H, <- Monad_functorial_id.
  
  exact eq_refl.

  rewrite H.
  assert ((Monad_fun_map (P x) (M (P (S x))) (fun _ : P x => f (S x)) (f x)) = Monad_unit _ (f (S x))).
  rewrite Monad_fun_map_const_is_const.
  exact eq_refl.
  rewrite H0, Monad_coh1.
  exact eq_refl.
Defined.

(* when we have two kleeneans that at least one of are True classically, 
   we can nondeterministically decide which holds. *)
Definition select : forall x y : K, lazy_bool_up _ x \/ lazy_bool_up _ y -> ^M ({ (lazy_bool_up _ x) } + { (lazy_bool_up _ y) }).
Proof.
  apply multivalued_choice.
Defined.


(* when there is p -> T and q -> T, we can nondeterministically join them *)
Definition mjoin (p q : Prop) (T : Type) : ({p}+{q} -> T) ->  ^M ({p}+{q}) -> ^M T.
Proof.
  intros f x.
  exact (M_lift _ _ f x).
Defined.

(* semideciability so that we can work on Prop directly, without mentioning K *)
Definition semidec := fun P : Prop => {x : K | lazy_bool_up _ x <-> P}.

Definition choose : forall p q, semidec p -> semidec q -> p \/ q -> ^M ({p}+{q}).
Proof.
  intros.
  destruct X.
  destruct X0.
  destruct i.
  destruct i0.
  apply (M_lift ({lazy_bool_up _ x} + {lazy_bool_up _ x0})).
  intro.
  destruct H4; auto.
  apply select.
  destruct H; auto.
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

Definition M_extension : forall A B, ^M (A -> B) -> (^M A -> ^M B).
Proof.
  intros.
  apply (Monad_fun_map_dom A).
  intro.
  apply (M_lift (A ->B)).
  auto.
  auto.
  auto.
Defined.



Lemma semidec_or P Q : semidec P -> semidec Q -> semidec (P \/ Q).
Proof.
  intros.
  destruct X as [k1 e1].
  destruct X0 as [k2 e2].
  exists (lazy_bool_or k1 k2).
  split; intro p.
  unfold lazy_bool_up in p.
  rewrite lazy_bool_or_up in p.
  destruct p as [H | H].
  left; apply proj1 in e1; apply e1, H.
  right; apply proj1 in e2; apply e2, H.
  unfold lazy_bool_up.
  rewrite lazy_bool_or_up.
  destruct p as [H | H].
  left; apply proj2 in e1; apply e1, H.
  right; apply proj2 in e2; apply e2, H.
Defined.

Lemma semidec_and P Q : semidec P -> semidec Q -> semidec (P /\ Q).
Proof.
  intros.
  destruct X as [k1 e1].
  destruct X0 as [k2 e2].
  exists (lazy_bool_and k1 k2).
  split; intro p.
  unfold lazy_bool_up in p.
  rewrite lazy_bool_and_up in p.
  destruct p as [H H1].
  split.
  apply proj1 in e1; apply e1, H.
  apply proj1 in e2; apply e2, H1.
  unfold lazy_bool_up.
  rewrite lazy_bool_and_up.
  destruct p as [H H1].
  split.
  apply proj2 in e1; apply e1, H.
  apply proj2 in e2; apply e2, H1.
Defined.

Notation "[ x | P ]" := (M {x | P}) : type_scope.
Notation "[ x : T | P ]" := (M {x : T | P}) : type_scope.
Notation "[ ( a , b ) | P ]" := (M (sigT (fun a => {b | P}))) : type_scope.

(* Lemma M_unit_is_mono : forall A x y, Monad_unit A x = Monad_unit A y -> x = y. *)
(* Proof. *)
(*   intros. *)
(*   pose (f := (fun a => a = x)). *)
(*   assert (f x <> f y). *)
(*   simpl. *)
(*   unfold f. *)
(*   Check f. *)
(*   destruct f. *)
(*   f. *)
  
  
Definition Mand : ^M Prop -> Prop.
Proof.
  intro.
  exact (X = Monad_unit _ True).
Defined.

Definition Mor : ^M Prop -> Prop.
Proof.
  intro.
  exact (~ (X = Monad_unit _ False)).
Defined.

Lemma Mor_is_retract : forall P : Prop, Mor (Monad_unit _ P) = P.
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
  
Lemma Mand_is_retract : forall P : Prop, Mand (Monad_unit _ P) = P.
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

Definition M_all {A} (P : A -> Prop) : M A -> Prop := fun X => Mand (Monad_fun_map _ _ P X).
Definition M_some {A} (P : A -> Prop) : M A -> Prop := fun X => Mor (Monad_fun_map _ _ P X).
Definition M_in {A} (a : A) (X : M A) : Prop := M_some (fun b => a = b) X. 

Lemma baire_choice :
  forall (P : (nat -> nat) -> Type) (f : forall ϕ, ^M (P ϕ)),
    ^M {s : forall ϕ, P ϕ | forall ϕ, M_in (s ϕ) (f ϕ)}.
Proof.
  exact M_baire_choice.
Qed.

Lemma sigma_eqP2_2 : forall (A : Type) (P : A -> Prop) (X Y : {a : A | P a}),  projP1 _ _ X = projP1 _ _  Y -> X = Y.
Proof.
  intros.
  destruct X, Y.
  apply (sigma_eqP A P _ _ _ _  H).
  apply irrl.
Defined.

Definition M_ext : forall A (X Y : M A), (M_picture_1 X = M_picture_1 Y) -> X = Y.
Proof.
  intros.
  apply (M_description_is_mono A X Y).
  unfold M_picture_1 in H.
  apply sigma_eqP2_2.
  auto.
Defined.


Definition M_in_destruct : forall A, forall X : ^M A, ^M {x : A | M_in x X}.
  intros.
  unfold M_in.
  unfold M_some.
  unfold Mor.
  pose proof (M_destruct _ X).
  fold (M_picture_1 X) in X0.
  apply (fun f => Monad_fun_map _ _ f X0). 
  intro.
  destruct X1.
  exists x.
  intro.
  pose proof (M_fun_cont_r (fun b : A => x = b) X x p).
  unfold M_lift in H0.
  rewrite H in H0.
  pose proof (@Monoid_hom_unit _ _ _ _ (M_description_hom) Prop).
  apply (lp _ _ (fun g => g False)) in H1.
  apply (lp _ _ (projP1 _ _ )) in H1.
  unfold M_picture_1, M_description in H0.
  rewrite H1 in H0.
  simpl in H0.
  rewrite <- H0; auto.
Defined.


Lemma M_picture_1_destruct : forall A a b, M_picture_1 (Monad_unit A a) b -> a = b.
Proof.
  intros.
  pose proof (@Monoid_hom_unit _ _ _ _ (M_description_hom) A).
  apply (lp _ _ (fun g => g a)) in H0.
  apply (lp _ _ (projP1 _ _ )) in H0.
  unfold M_picture_1, M_description in H.
  rewrite H0 in H.
  simpl in H.
  rewrite H; auto.
Defined.

Lemma M_picture_1_intro : forall A a b, a = b -> M_picture_1 (Monad_unit A a) b.
Proof.
  intros.
  rewrite H.
  pose proof (@Monoid_hom_unit _ _ _ _ (M_description_hom) A).
  apply (lp _ _ (fun g => g b)) in H0.
  apply (lp _ _ (projP1 _ _ )) in H0.
  unfold M_picture_1, M_description.
  rewrite H0.
  simpl.
  auto.
Defined.

Lemma M_in_picture_1 : forall {A} (a : A) (X : M A), M_in a X = M_picture_1 X a.
Proof.
  intros.
  apply Prop_ext; intro.
  unfold M_in, M_some, Mor in H.
  destruct (lem ( M_picture_1 X a)); auto.
  contradict H.
  apply M_ext.
  apply fun_ext; intro.
  destruct (lem x).
  assert (x = True) by (apply Prop_ext; intro; auto).
  induction (eq_sym H1).
  pose proof (M_fun_cont (fun b : A => a = b) X True).
  unfold M_lift in H2.
  rewrite H2.
  apply Prop_ext; intro.
  destruct H3.
  destruct H3.
  contradict H0.
  assert (j : a = x) by (rewrite <- H4; auto); rewrite j; auto.
  apply M_picture_1_destruct in H3.
  contradict H3; intro j; rewrite j; auto.
  assert (x = False).
  (apply Prop_ext; intro; auto).
  contradict H1.
  induction (eq_sym H1).
  clear H H1.
  pose proof (M_fun_cont (fun b : A => a = b) X False).
  unfold M_lift in H.
  rewrite H.
  apply Prop_ext; intro.
  apply M_picture_1_intro; auto.
  unfold M_picture_1 in H0.
  unfold M_picture_1.
  destruct (M_description A X).
  destruct e.

  exists x0.
  split; auto.
  simpl in H0.
  assert (a <> x0).
  intro.
  induction H2.
  exact (H0 x1).
  apply Prop_ext; intro; auto.
  contradict H3.

  unfold M_in, M_some, Mor.
  intro.
  pose proof (M_fun_cont (fun b : A => a = b) X True).
  unfold M_lift in H1.
  rewrite H0 in H1.
  assert ( (exists a0 : A, M_picture_1 X a0 /\ True = (a = a0))).
  exists a; split; auto.
  apply Prop_ext; intro; auto.
  rewrite <- H1 in H2.
  apply M_picture_1_destruct in H2.
  rewrite H2; auto.
Defined.

    
Lemma M_all_picture_1 : forall A (P : A -> Prop) (X : M A), M_all P X = forall a, M_picture_1 X a -> P a.
Proof.
  intros.
  unfold M_all, Mand.
  apply Prop_ext; intros.
  pose proof (M_fun_cont_r P X a H0).
  unfold M_lift in H1.
  rewrite H in H1.
  apply M_picture_1_destruct in H1.
  rewrite<- H1; auto.

  apply M_ext.
  apply fun_ext.
  intro; apply Prop_ext; intro.
  apply M_picture_1_intro.
  pose proof (M_fun_cont P X x).
  unfold M_lift in H1.
  rewrite H1 in H0.
  destruct H0.
  destruct H0.
  pose proof (H _ H0).
  assert (P x0 = True).
  apply Prop_ext; intro; auto.
  rewrite H4 in H2.
  auto.
  apply M_picture_1_destruct in H0.
  rewrite <- H0.
  
  pose proof (M_fun_cont P X True).
  unfold M_lift in H1.
  rewrite H1.
  apply M_hprop_elim_f.
  intros y z; apply irrl.
  apply (fun j => Monad_fun_map _ _ j (M_destruct _ X)).
  fold (M_picture_1 X).
  intro.
  destruct X0.
  exists x0; auto.
  split; auto.
  pose proof (H _ p).
  apply Prop_ext; intro; auto.
Defined.

Lemma classical_tautology_neg_and : forall P Q, (~(P /\ Q)) = ((~ P) \/ (~ Q)).
Proof.
  intros.
  apply Prop_ext.
  intro.
  destruct (lem P).
  destruct (lem Q).
  contradict H; auto.
  right; auto.
  left; auto.
  intro.
  destruct H.
  contradict H.
  destruct H; auto.
  contradict H.
  destruct H; auto.
Defined.

Lemma classical_tautology_neg_or : forall P Q, (~(P \/ Q)) = ((~ P) /\ (~ Q)).
Proof.
  intros.
  apply Prop_ext.
  intro.
  destruct (lem P).
  contradict H; auto.
  destruct (lem Q).
  contradict H; auto.
  auto.
  intro.
  destruct H.
  intro.
  destruct H1.
  contradiction (H H1).
  contradiction (H0 H1).
Defined.

Lemma classical_tautology_dneg : forall P : Prop, (~ ~ P) = P.
Proof.
  intros.
  apply Prop_ext.
  intro.
  destruct (lem (P)); auto.
  contradiction (H H0).
  intro.
  auto.
Defined.

Lemma classical_tautology_contra : forall P Q : Prop, (P -> Q) = ((~ Q) -> (~ P)).
Proof.
  intros.
  apply Prop_ext.
  intros.
  destruct (lem (P)); auto.
  intros.
  destruct (lem (Q)); auto.
  contradiction (H H1 H0).
Defined.


Lemma classical_tautology_neg_all : forall A (P : A -> Prop), (~ (forall x : A, P x)) = (exists x : A, ~ P x).
Proof.
  intros.
  apply Prop_ext.
  rewrite classical_tautology_contra.
  rewrite classical_tautology_dneg.
  intros.
  destruct (lem (P x)); auto.
  contradict H.
  exists x; auto.
  intros.
  destruct H.
  intro.
  contradiction (H (H0 x)).  
Defined.

Lemma classical_tautology_neg_some : forall A (P : A -> Prop), (~ (exists x : A, P x)) = (forall x : A, ~ P x).
Proof.
  intros.
  apply Prop_ext.
  (* rewrite classical_tautology_contra. *)
  (* rewrite classical_tautology_dneg. *)
  intros.
  destruct (lem (P x)); auto.
  contradict H.
  exists x; auto.
  intros.
  intro.
  destruct H0.  
  contradiction ((H x) H0).  
Defined.

Lemma classical_tautology_False : forall P : Prop, (~ P) -> P = False.
Proof.
  intros.
  apply Prop_ext; intro; auto.
  contradiction H0.
Defined.

Lemma classical_tautology_True : forall P : Prop, P -> P = True.
Proof.
  intros.
  apply Prop_ext; intro; auto.
Defined.  
  
Lemma M_some_picture_1 : forall A (P : A -> Prop) (X : M A), M_some P X = exists a, M_picture_1 X a /\ P a.
Proof.
  intros.
  unfold M_some, Mor.
  apply Prop_ext.
  rewrite classical_tautology_contra.
  intros.
  rewrite classical_tautology_neg_some in H.
  intro.
  contradict H0.
  apply M_ext.
  apply fun_ext; intro.
  apply Prop_ext; intro.
  fold M_lift in H0.
  rewrite (M_fun_cont P X x) in H0.
  destruct H0.
  destruct H0.
  pose proof (H x0).
  rewrite (classical_tautology_neg_and) in H2.
  destruct H2.
  contradiction (H2 H0).
  rewrite (classical_tautology_False _ H2) in H1.
  rewrite H1.
  apply  (M_picture_1_intro); auto.
  
  apply (M_picture_1_destruct) in H0.
  rewrite <- H0.
  fold M_lift.
  rewrite (M_fun_cont P X False).
  destruct (M_W_destruct X).
  pose proof (H x0).
  exists x0.
  split; auto.
  rewrite (classical_tautology_neg_and) in H2.
  destruct H2.
  contradiction (H2 H1).
  apply eq_sym, classical_tautology_False; auto.

  intro.
  intro.
  apply (lp _ _ M_picture_1) in H0.
  pose proof (M_fun_cont P X True).
  fold M_lift in H0.
  rewrite H0 in H1.
  assert ((exists a : A, M_picture_1 X a /\ True = P a)).
  destruct H.
  exists x.
  destruct H ; split; auto.
  apply eq_sym, classical_tautology_True; auto.
  rewrite <- H1 in H2.
  apply M_picture_1_destruct in H2.
  rewrite H2; auto.
Defined.


    
Definition M_retraction_T : forall A (P : A -> Type),
    ^M (forall n, P n) -> (forall n, ^M (P n)).
Proof.
  intros A P X n.
  apply (Monad_fun_map _ _ (fun f => f n) X).
Defined.

Lemma M_existence_to_all : forall A (P : A -> Prop), ^M {x | P x} -> {x : ^M A | M_all P x}.
Proof.
  intros.
  exists (M_projP1 _ _  X).
  unfold M_all.
  unfold Mand.
  unfold M_projP1.
  pose proof (M_functorial_comp _ _ _ ((fun X0 : {x : A | P x} => let (x, _) := X0 in x)) P ).
  apply (lp _ _ (fun g => g X)) in H.
  unfold M_lift in H.
  rewrite <- H.
  assert ((fun x : {x : A | P x} => P (let (x0, _) := x in x0)) = fun _ : {x : A | P x} => True).
  apply fun_ext; intro x; destruct x;  simpl; auto.
  apply Prop_ext; intro; auto.
  rewrite H0.
  rewrite (@Monad_fun_map_const_is_const ).
  auto.
Defined.


Lemma M_all_to_existence : forall A (P : A -> Prop), {x : ^M A | M_all P x} ->  ^M {x | P x}.
Proof.
  intros.
  destruct X.
  unfold M_all in m.
  unfold Mand in m.
  pose proof (M_destruct _ x).
  fold (M_picture_1 x) in X.
  apply (fun f => Monad_fun_map _ _ f X).
  intro.
  destruct X0.
  exists x0.
  pose proof (M_fun_cont_r P x _ p).
  fold M_lift in m.
  rewrite m in H.
  apply M_picture_1_destruct in H.
  rewrite <- H; auto.
Defined.

Definition M_all_destruct : forall {A} {P : A -> Prop} {X x}, M_all P X -> M_in x X -> P x.
Proof.
  intros.
  rewrite (M_all_picture_1 A P X) in H.
  rewrite M_in_picture_1 in H0.
  exact (H _ H0).
Defined.

Definition M_all_destruct_2 : forall {A B} {P : A -> B -> Prop} {X Y x y},
    M_all (fun a => M_all (fun b => P a b) Y) X -> M_in x X -> M_in y Y -> P x y.
Proof.
  intros.
  rewrite (M_all_picture_1 A _ X) in H.
  rewrite M_in_picture_1 in H0.
  pose proof (H _ H0).
  rewrite (M_all_picture_1 B _ Y) in H2.
  rewrite M_in_picture_1 in H1.
  pose proof (H2 _ H1).
  exact H3.
Defined.

  
  
  

Definition countable_selection (P : nat -> Type) (f : forall n, ^M (P n)) : ^M {s : forall n, P n | forall n, M_in (s n) (f n)}.
Proof.

  pose proof (M_paths P (fun n _ y => M_in y (f (S n))) (f 0)).
  simpl in X.
  assert ((forall n : nat, P n -> ^M {y : P (S n) | M_in y (f (S n))}) ).
  intros.
  pose proof (M_destruct _(f (S n))).
  fold (M_picture_1 (f (S (n)))) in X1.
  apply (fun j => Monad_fun_map _ _ j X1).
  intro.
  destruct X2.
  exists x.
  rewrite M_in_picture_1.
  exact p.
  apply X in X0.
  
  pose proof (M_destruct _ (f O)).
  fold (M_picture_1 (f 0)) in X1.
  apply (fun j => Monad_fun_map_dom _ _ j X0).
  intro.
  apply (fun j => Monad_fun_map _ _ j X1).
  intro.
  destruct X2, X3.
  
  
  exists (fun n => match n with O => x0 | S m => x (S m) end).
  intro.
  destruct n.
  rewrite M_in_picture_1; auto.
  exact (m n).
Defined.

End M_Defs.
