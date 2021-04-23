Parameter K : Set.
Parameter trueK : K.
Parameter falseK : K.

Definition upK : K -> Prop := fun b : K => b = trueK.
Definition downK : K -> Prop := fun b : K => b = falseK.

Parameter M : Type -> Type.
Parameter unitM : forall T : Type, T -> M T.
Parameter lift_domM : forall A B, (A -> M B) -> M A -> M B.
Definition liftM : forall A B, (A -> B) -> M A -> M B :=
  fun A B f => lift_domM A B (fun x => unitM B (f x)). 

Parameter select : forall x y : K, upK x \/ upK y -> M ({ (upK x) } + { (upK y) }).

Notation "[ x | P ]" := (M {x | P}) : type_scope.
Notation "[ x : T | P ]" := (M {x : T | P}) : type_scope.
Notation "[ ( a , b ) | P ]" := (M (sigT (fun a => {b | P}))) : type_scope.

