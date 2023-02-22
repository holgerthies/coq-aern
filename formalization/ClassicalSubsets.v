Section ClassicalSubsets.
  Context (X : Type).
  Definition csubset := X -> Prop.
  Definition union (A B : csubset) : csubset := fun x => A x \/ B x.
  Definition intersection (A B : csubset) : csubset := fun x => A x /\ B x.
  Definition intersects (A B : csubset) := exists x, intersection A B x.
  Definition is_subset (A B : csubset) := forall x, A x -> B x.
End ClassicalSubsets.
