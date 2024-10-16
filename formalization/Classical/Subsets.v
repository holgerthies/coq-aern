(* This file defines classical subsets on some operations on them *)
Section ClassicalSubsets.
  Context {X : Type}.
  Definition csubset := X -> Prop.
  Definition union (A B : csubset) : csubset := fun x => A x \/ B x.
  Definition countable_union (A : nat -> csubset) : csubset := fun x => exists n, A n x.
  Definition intersection (A B : csubset) : csubset := fun x => A x /\ B x.
  Definition countable_intersection (A : nat -> csubset) : csubset := fun x => forall n, A n x.
  Definition complement (A: csubset) : csubset := fun x => not (A x).
  Definition intersects (A B : csubset) := exists x, intersection A B x.
  Definition is_subset (A B : csubset) := forall x, A x -> B x.
  Definition singleton (x : X) : csubset := fun y => x = y. 

  Lemma intersects_union A B b: intersects b (union A B) <-> intersects b A \/ intersects b B. 
Proof.
    split; intros.
    destruct H.
    destruct H.
    destruct H0; [left | right]; exists x; split;auto.
    destruct H;destruct H;exists x;split; [|left| | right];apply H.
Defined.

  Lemma union_subset A B C : is_subset (union A B) C <-> is_subset A C /\ is_subset B C.
Proof.
    split; intros.
    split; intros x H';apply H; [left | right]; auto.
    intros x H'.
    destruct H.
    destruct H';[apply H | apply H0];auto.
Defined.    
End ClassicalSubsets.
