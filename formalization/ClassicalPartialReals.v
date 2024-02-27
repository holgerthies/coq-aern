Require Import Base Real ClassicalMonads ClassicalPartiality.


Declare Scope pcreal_scope.

Notation pcReal := (pc Real).

Notation "x + y" := (pc_lift2 (fun a b => a + b)%Real x y) : pcreal_scope.
Notation "x - y" := (pc_lift2 (fun a b => a - b)%Real x y) : pcreal_scope.
Notation "x * y" := (pc_lift2 (fun a b => a * b)%Real x y) : pcreal_scope.

Delimit Scope pcreal_scope with pcreal.
