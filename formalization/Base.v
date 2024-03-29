(* Extensionality Axioms for our type theory *)
Axiom lem : forall P : Prop, P \/ ~P.
Axiom Prop_ext : forall P Q : Prop, (P -> Q) -> (Q -> P) -> P = Q.
Axiom dfun_ext : forall A (P : A -> Type) (f g: forall a : A, P a), (forall x, f x = g x) -> f = g.
Axiom countable_choice : forall A (P : nat -> A -> Prop), (forall n, exists x, P n x) -> exists f : nat -> A , forall n, P n (f n).
Axiom dependent_choice : forall A (R : A -> A -> Prop),
    (forall x, exists y, R x y) -> forall x0,
      (exists f : nat -> A, f 0 = x0 /\ forall n, R (f n) (f (S n))).



Record RealTypes : Type := mkRealTypes
{
  K : Type;
  M : Type -> Type;
  Real : Type;
}.
Arguments K {types} : rename.
Arguments M [types] type : rename.
Arguments Real {types} : rename.

Lemma fun_ext : forall A B (f g: A -> B), (forall x, f x = g x) -> f = g.
Proof.
  intros.
  apply dfun_ext.
  exact H.
Defined.

Definition isSubsingleton := fun P : Type => forall x y : P, x = y.
Definition is_hprop (A : Type) := forall x y : A, x = y.
Definition is_mono {A B} (f : A -> B) := forall x y, f x = f y -> x = y.


Lemma fun_to_subsingleton_id : forall {A B} (f g : A -> B), isSubsingleton B -> f = g.
Proof.
  intros.
  apply fun_ext.
  intros.
  apply H.
Defined.

  
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

(* equivalence in extensional type theory *)
Definition id (A : Type) : A -> A := fun x => x.
Definition fc {A B C : Type} (f : B -> C) (g : A -> B) : A -> C := fun x => f (g x).
Definition is_equiv {A B : Type} (f : A -> B) := {g : B -> A | fc g f = id _ /\ fc f g = id _}.



(* transporting path *)
Definition tpp : forall A : Type, forall P : A -> Type, forall x y : A, forall e : x = y, P x -> P y.
Proof.
  intros.
  induction e.
  exact X.
Defined.

(* path of sigma types *)
Lemma sigma_eqT : forall (A : Type) (P : A -> Type) (x y : A) (a : P x) (b : P y), forall e : x = y,
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
Lemma sigma_eqP : forall (A : Type) (P : A -> Prop) (x y : A) (a : P x) (b : P y), forall e : x = y,
      tpp A P x y e a = b -> exist P x a = exist P y b.
Proof.
  intros.
  induction H.
  unfold tpp.
  unfold eq_rect.

  destruct e.
  exact eq_refl.
Defined.


Definition sigma_eqT_pr1 : forall A P (a c : A) b d, existT P a b = existT P c d -> a = c.
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

Definition sigma_eqP_pr1 : forall A P (a c : A) b d, exist P a b = exist P c d -> a = c.
Proof.
  intros.
  apply (@lp {x : A | P x} A (@projP1 A P  ) (exist P a b) (exist P c d)) in H.
  simpl in H.
  exact H.
Defined.

Lemma sigma_eqP2 : forall (A : Type) (P : A -> Prop) (x y : A) (a : P x) (b : P y),  x = y ->  exist P x a = exist P y b.
Proof.
  intros.
  apply (sigma_eqP A P x y a b H).
  apply irrl.
Defined.

(* Use the following instead of direct integers to get integer literals when extracting code *)

Definition n1 := (1)%nat.
Definition n2 := (2)%nat.
Definition n3 := (3)%nat.
Definition n4 := (4)%nat.

Require Export ZArith_base.

Definition z0 := (0)%Z.
Definition z1 := (1)%Z.
Definition z2 := (2)%Z.
Definition z3 := (3)%Z.
Definition z4 := (4)%Z.
Definition z5 := (5)%Z.
Definition z6 := (6)%Z.
Definition z7 := (7)%Z.
Definition z8 := (8)%Z.
Definition z9 := (9)%Z.
Definition z10 := (10)%Z.
Definition z11 := (11)%Z.
Definition z12 := (12)%Z.

