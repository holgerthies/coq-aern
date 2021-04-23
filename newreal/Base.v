Axiom irrl : forall P : Prop, forall x y : P, x = y.
Axiom lem : forall P : Prop, P \/ ~P.



Definition lp : forall S T (f : S -> T) (a b : S), a = b -> f a = f b.
Proof.
  intros.
  rewrite H.
  exact (eq_refl _).
Defined.
