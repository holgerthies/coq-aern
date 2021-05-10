Axiom irrl : forall P : Prop, forall x y : P, x = y.
Axiom lem : forall P : Prop, P \/ ~P.
Axiom Prop_ext : forall P Q : Prop, (P -> Q) -> (Q -> P) -> P = Q.
Axiom fun_ext : forall A B (f g: A -> B), (forall x, f x = g x) -> f = g.
  
  
Definition lp : forall S T (f : S -> T) (a b : S), a = b -> f a = f b.
Proof.
  intros.
  rewrite H.
  exact (eq_refl _).
Defined.
