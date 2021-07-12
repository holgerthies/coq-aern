Require Import Real.
Require Import Euclidean.

Definition RealPoly (n : nat) := {x : euclidean (S n) | euclidean_head x <> Real0 }.
