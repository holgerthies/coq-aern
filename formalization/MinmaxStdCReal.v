From mathcomp Require Import all_ssreflect.
Require Import Base.
Require Import Coq.Reals.Abstract.ConstructiveReals.
Require Import QArith.

(* Auxiliary lemmas, simple consequences of lem *)
Lemma and_or_distr_r P Q R : (P \/ R) /\ (Q \/ R) -> (P /\ Q) \/ R.
Proof.
  intros [HP HQ].
  have [r|nr] := (lem R).
  auto.
  left.
  destruct HP.
  destruct HQ. auto.
  absurd R; auto.
  absurd R; auto.
Qed.

Lemma and_or_distr_3_mid P Q R S :
(P \/ Q \/ S) /\ (P \/ R \/ S) -> P \/ (Q /\ R) \/ S.
Proof.
  intros [HQ HR].
  have [p|np] := (lem P). auto.
  destruct HQ. absurd P; auto.
  destruct HR. absurd P; auto.
  right.
  by apply and_or_distr_r.
Qed.

Local Open Scope ConstructiveReals.
Axiom cr : ConstructiveReals.

(* Compatibility with coq-aern: *)

Definition Real := CRcarrier cr.

Definition Real0 : Real := 0.
Definition Real1 : Real := 1.
Definition Realplus x y : Real := x + y.
Definition Realmult x y : Real := x * y.
Definition Realopp x : Real := - x.

(* Definition Realinv : forall {z}, z <> Real0 -> Real := TODO. *)

Notation "x > y" := (CRlt _ y x) : ConstructiveReals.
Notation "x >= y" := (CRle _ y x) : ConstructiveReals.

Lemma CRlt_antisym (x y : Real) : y > x -> x > y -> False.
Proof.
  have L := CRltLinear cr.
  unfold isLinearOrder in L.
  destruct L as [[L' _] _].
  apply L'.
Qed.

Notation "x <@ y" := (CRltProp _ x y) (at level 70, no associativity) : ConstructiveReals.
Notation "x <=@ y" := ((CRltProp _ y x) -> False) (at level 70, no associativity) : ConstructiveReals.
Notation "x >@ y" := (CRltProp _ y x) (at level 70, no associativity) : ConstructiveReals.
Notation "x >=@ y" := ((CRltProp _ x y) -> False) (at level 70, no associativity) : ConstructiveReals.
Notation "x =@ y" := ((x <=@ y)/\(x >=@ y)) (at level 70, right associativity) : ConstructiveReals.

Definition Reallt : Real -> Real -> Prop := CRltProp cr.

Lemma Realeq_refl (x : Real) : x =@ x.
Proof.
  suff lt: x <=@ x by auto.
  intros.
  apply (CRltEpsilon cr) in H.
  by apply (CRlt_antisym x x); auto.
Qed.

Lemma Realeq_sym (x y : Real) : x =@ y -> y =@ x.
Proof.
  intros [H1 H2].
  split; auto.
Qed.

Lemma Realtotal_order : forall r1 r2 : Real, r1 <@ r2 \/ r1 =@ r2 \/ r1 >@ r2.
Proof.
  intros.
  apply and_or_distr_3_mid.
  split.
  have [gt|ngt] := (lem (r1 >@ r2)).
  right. right. auto.
  right. left. auto.
  have [gt|ngt] := (lem (r2 >@ r1)).
  left. auto.
  right. left. auto.
Qed.

Lemma Reallt_nlt : forall r1 r2 : Real, r1 <@ r2 -> ~ r2 <@ r1.
Proof.
  intros.
  have L := CRltLinear cr.
  unfold isLinearOrder in L.
  destruct L as [[L' _] _].
  have L := L' r1 r2. clear L'.
  apply (CRltEpsilon cr) in H.
  have L2 := (L H).
  have [gt|ngt] := (lem (r1 >@ r2)).
  apply (CRltEpsilon cr) in gt.
  auto. auto.
Qed.

Lemma Reallt_le : forall x y : Real, x <@ y -> x <=@ y.
Proof.
  intros.
  have L := CRltLinear cr.
  unfold isLinearOrder in L.
  destruct L as [[L' _] _].
  have L := L' x y. clear L'.
  destruct L.
  by apply (CRltEpsilon cr).
  by apply (CRltEpsilon cr).
Qed.

Definition W_M (x y z : Real)
  := (x >@ y -> z =@ x) /\ (x =@ y -> z =@ x) /\ (x <@ y -> z =@ y).

Lemma W_M_or : forall x y z, W_M x y z -> (z =@ x) \/ (z =@ y).
Proof.
  intros x y z m.
  destruct m as [a [b c]].
  destruct (Realtotal_order x y) as [p1 | [p2 | p3]].
  right. auto.
  left. auto.
  left. auto.
Qed. 

Lemma W_M_Or : forall x y z, W_M x y z -> (z=@x /\ x>=@y) \/ (z=@y /\ y>=@x).
Proof.
  intros x y z m.
  destruct m as [a [b c]].
  destruct (Realtotal_order x y) as [p1 | [p2 | p3]].
  right. split. auto.
  by apply Reallt_le.
  left. split. auto.
  destruct p2. auto.
  left. split. auto.
  by apply Reallt_le.
Qed.

Lemma W_max : forall x y, (exists z, W_M x y z).
Proof.
  intros x y.
  destruct (Realtotal_order x y) as [c1 | [c2 | c3]]; unfold W_M.

  exists y.
  split; auto.
  intro H; contradict H; apply Reallt_nlt; auto.
  split. apply Realeq_sym.
  intros. apply Realeq_refl.

  exists x.
  split; split;auto.
  apply Realeq_refl.
  apply Realeq_refl.
  intro. apply Realeq_refl.

  exists x.
  split; split; auto.
  apply Realeq_refl.
  apply Realeq_refl.
  intro. apply Realeq_refl.
  intro H; contradict c3; apply Reallt_nlt; auto.
Qed.

Lemma Realmax : forall x y, {z | W_M x y z}.
Proof.
  intros.

(* TODO *)
Admitted.
(* 
  apply Real_mslimit_P_lt.
  + (* max is single valued predicate *)
    unfold unique.
    pose proof (W_max x y).
    destruct H as [m H].
    exists m.
    split; auto.
    intros m' H'.
    destruct (W_M_Or x y m H) as [[H11 H12]|[H11 H12]];
      destruct (W_M_Or x y m' H') as [[H11' H12']|[H11' H12']];
      try rewrite <- H11; try rewrite <- H11'; auto with Realiny.   
  + (* construct limit *)
    intros.
    apply (mjoin (x>y - prec n) (y > x - prec n)).
    ++ intros [c1|c2].
       +++ (* when x>y-2ⁿ *)
         exists x.
         destruct (W_max x y).
         exists x0.
         constructor; auto.
         destruct (W_M_Or x y x0 H) as [[H1 _]|[H1 H2]].
         ++++ rewrite H1.
              destruct (dist_zero x0 x0) as [o t]; rewrite (t eq_refl).
                apply prec_pos.
                
         ++++ rewrite <- H1.
              pose proof (prec_pos n) as P.
              apply (Reallt_plus_lt y Real0 (prec n)) in P; ring_simplify in P.
              apply (Realge_le) in H2.
              apply (Realle_lt_lt x y (y+prec n) H2) in P.
              assert (y-prec n < x < y+prec n) by auto.
              pose proof (prec_pos n) as Q.
              rewrite (dist_symm).
              apply (Realmetric_gtgt_sand y x (prec n) Q H0).
              
       +++ (* when x<y-2ⁿ *)
         exists y.
         destruct (W_max x y).
         exists x0.
         constructor; auto.
         destruct (W_M_Or x y x0 H) as [[H1 H2]|[H1 _]].
         ++++ rewrite <- H1.
              pose proof (prec_pos n) as P.
              apply (Reallt_plus_lt x Real0 (prec n)) in P; ring_simplify in P.
              apply (Realge_le) in H2.
              apply (Realle_lt_lt y x (x+prec n) H2) in P.
              assert (x-prec n < y < x+prec n) by auto.
              pose proof (prec_pos n) as Q.
              rewrite (dist_symm).
              apply (Realmetric_gtgt_sand x y (prec n) Q H0).
           ++++ rewrite H1.
                destruct (dist_zero x0 x0) as [o t]; rewrite (t eq_refl).
                apply prec_pos.
                
    ++ apply M_split.
       apply prec_pos.       
Defined. *)