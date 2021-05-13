(* Extensionality Axioms for our type theory *)
Axiom lem : forall P : Prop, P \/ ~P.
Axiom Prop_ext : forall P Q : Prop, (P -> Q) -> (Q -> P) -> P = Q.
Axiom fun_ext : forall A B (f g: A -> B), (forall x, f x = g x) -> f = g.
Definition classic : Type -> Prop := fun A => exists x : A, True.

Notation "[ A ]" := (classic A) : type_scope.

(* Proof irrelevence derived from axioms *)
Lemma irrl : forall P : Prop, forall x y : P, x = y.
Proof.
  intros P x.
  assert (P = True).
  apply Prop_ext; intro; auto.
  
  induction (eq_sym H).
  destruct x.
  intro.
  destruct y.
  apply eq_refl.
Qed.

(* Auxiliary functions *)
Definition lp : forall S T (f : S -> T) (a b : S), a = b -> f a = f b.
Proof.
  intros.
  rewrite H.
  exact (eq_refl _).
Defined.


(* transporting path *)
Definition tpp : forall A : Type, forall P : A -> Type, forall x y : A, forall e : x = y, P x -> P y.
Proof.
  intros.
  induction e.
  exact X.
Defined.

(* path of sigma types *)
Lemma sewonsewon : forall (A : Type) (P : A -> Type) (x y : A) (a : P x) (b : P y), forall e : x = y,
      tpp A P x y e a = b -> existT P x a = existT P y b.
Proof.
  intros.
  induction H.
  unfold tpp.
  unfold eq_rect.

  destruct e.
  exact eq_refl.
Defined.

(* path of sigma types *)
Lemma sewonsewonp : forall (A : Type) (P : A -> Prop) (x y : A) (a : P x) (b : P y), forall e : x = y,
      tpp A P x y e a = b -> exist P x a = exist P y b.
Proof.
  intros.
  induction H.
  unfold tpp.
  unfold eq_rect.

  destruct e.
  exact eq_refl.
Defined.


Definition sewon_sewon : forall A P (a c : A) b d, existT P a b = existT P c d -> a = c.
Proof.
  intros.
  auto.
  apply (@lp {x : A & P x} A (@projT1 A P  ) (existT P a b) (existT P c d)) in H.
  simpl in H.
  exact H.
Defined.

Definition projP1 : forall A (P : A -> Prop) (x : {x : A | P x}), A.
Proof.
  intros.
  destruct x.
  exact x.
Defined.


Definition pr1 : forall A (P : A -> Prop) (a : {x | P x}), A.
Proof.
  intros.
  destruct a.
  exact x.
Defined.

Definition sewon_sewonp : forall A P (a c : A) b d, exist P a b = exist P c d -> a = c.
Proof.
  intros.
  apply (@lp {x : A | P x} A (@projP1 A P  ) (exist P a b) (exist P c d)) in H.
  simpl in H.
  exact H.
Defined.
  
(* equivalence in extensional type theory *)
Definition id (A : Type) : A -> A := fun x => x.
Definition fc {A B C : Type} (f : B -> C) (g : A -> B) : A -> C := fun x => f (g x).
Definition is_equiv {A B : Type} (f : A -> B) := {g : B -> A | fc g f = id _ /\ fc f g = id _}.
