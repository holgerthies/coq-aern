Require Import AbBool.
Require Import BasicAxioms.
Require Import BasicArith.
Open Scope T_scope.


  
(** weak split: does not have any computational content **)
Lemma W_split : forall x y ε, ε > T0 -> x>y-ε \/ y>x-ε.
Proof.
  intros x y ε p.
  destruct (Ttotal_order x y) as [H|[H|H]].
  + apply (Tlt_plus_lt (-ε + x) T0 ε) in p.
    ring_simplify in p.
    apply (Tlt_lt_lt (-ε + x) x y p) in H.
    replace (-ε+x) with (x-ε) in H by ring; right; exact H.
  + rewrite H.
    left.
    apply (Tlt_plus_lt (y-ε) T0 ε) in p.
    ring_simplify in p.
    exact p.
  + apply (Tlt_plus_lt (-ε + y) T0 ε) in p.
    ring_simplify in p.
    apply (Tlt_lt_lt (-ε + y) y x p) in H.
    replace (-ε+y) with (y-ε) in H by ring; left; exact H.
Defined.

(** string but multivalued split **)
Lemma M_split : forall x y ε, ε > T0 -> mdown ({x>y-ε} + {y>x-ε}).
Proof.
  intros x y ε p.
  apply (choose (x >? y-ε) (y >? x-ε)).
  + exact (Tltb_lt_t (y-ε) x).
  + exact (Tltb_lt_t (x-ε) y).
  + apply W_split.
    exact p.
Defined.



Lemma not_bounded : forall x, [ y | y > x ].
Proof.
  intro x.
  apply (mjoin (x>T0-T1) (T0>x-T1)).
  + intros [c1|c2].
    ++ exists (x+T1).
       pose proof (T1_gt_T0).
       apply (Tlt_plus_lt x T0 T1) in H.
       ring_simplify in H.
       exact H.
    ++ exists (x+T2).
       pose proof (T2_pos).
       apply (Tlt_plus_lt x T0 T2) in H.
       ring_simplify in H.
       exact H.
  + apply M_split .
    exact T1_gt_T0.
Defined.

(*
Lemma not_bounded2 : forall x, x > T0 -> [k | x < NT k < x + T2].
Proof.
  intros.

Lemma not_bounded2 : forall x, [ y | x < IZT y < x + T2].
Proof.
  intros.
  apply (mjoin (x>T0-T1) (T0>x-T1)).
  + intros [c1|c2].

  induction y.
*)