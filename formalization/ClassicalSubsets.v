Section ClassicalSubsets.
  Context (X : Type).
  Definition csubset := X -> Prop.

  Definition union (A B : csubset) : csubset := fun x => A x \/ B x.
  Definition intersection (A B : csubset) : csubset := fun x => A x /\ B x.
End ClassicalSubsets.
