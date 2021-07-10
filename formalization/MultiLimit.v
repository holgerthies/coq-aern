Require Import Real.
(* computing a multivalued function using limit; e.g., complex sqrt *)


(* for a classical description of real numbers [P : Real -> Prop],
   [x : Real] approximates it by [prec n] *)
Definition w_approx (P : Real -> Prop) (n : nat) (x : Real) : Prop
  := exists y, P y /\ dist x y <= prec n.

(* a predicate [P : Real -> Prop] is complete if for any converging seqeunce
   [f : nat -> Real] such that [w_approx P n (f n)] holds for all [n : nat],
   the limit point satisfies [P x]. For example, [Real \ {0}] is not complete. *)
Definition closed_predicate (P : Real -> Prop) :=
  forall f : nat -> Real,
    is_fast_cauchy f -> (forall n, w_approx P n (f n)) -> (forall x, is_fast_limit x f -> P x).
                          
(* from a multivalued procedure apporximating, we get approximating sequences *)
Lemma consecutive_converging_fast_cauchy : forall f : nat -> Real,
    (forall n, dist (f n) (f (S n)) <= prec n) -> is_fast_cauchy f.
Proof.
  intros f H n m.
Admitted.


(* for a complete predicate [P : Real -> Prop], when we give an initial searching point
   [ M {x : Real | w_approx P O x}] and a procedure that refines it,
   [f : forall n x, w_approx P n x -> M {y : Real | w_approx P (S n) y /\ dist x y <= prec n}],
   (see that f is a function that [ (f n) x p] is roughly a multivalued real number [y]
   such that (1) [y] approximates [P] by [prec (n + 1)] and (2) [|x-y| <= prec n] when 
   [x] is [prec n] approximation of [P]) it gives us a multivalued real numbers 
   that are in [P] *)
Definition multivalued_limit : forall P : Real -> Prop,
    closed_predicate P ->
    M {x : Real | w_approx P O x} ->
    (forall n x, w_approx P n x ->
                 M {y : Real | w_approx P (S n) y /\ dist x y <= prec n}) ->
    M {x : Real | P x}. 
Proof.
  intros P c X f.
  assert ((forall n (x : {x : Real | w_approx P n x}),
              M {y : { y : Real | w_approx P (S n) y} | dist (projP1 _ _ x) (projP1 _ _ y) <= prec n})).
  intros.
  destruct x.
  pose proof (f n x w).
  apply (liftM {y : Real | w_approx P (S n) y /\ dist x y <= prec n}).
  intro.
  destruct H.
  destruct a.
  exists (exist _ x0 H).
  simpl.
  exact H0.
  exact X0.
  pose proof (pathsM _ _ X X0).
  simpl in X1.
  apply (lift_domM {x | w_approx P 0 x}).
  intro.
  apply (liftM {f : forall n : nat, {x : Real | w_approx P n x}
               | forall m : nat,
                   dist (projP1 Real (fun x : Real => w_approx P m x) (f m))
                        (projP1 Real (fun y : Real => w_approx P (S m) y) (f (S m))) <= prec m}).
  intro.
  destruct H.
  destruct H0.
  simpl in r.
  assert (is_fast_cauchy (fun n => projP1 _ _ (x0 n))).
  apply consecutive_converging_fast_cauchy.
  exact r.
  pose proof (C_limit _ H).
  destruct H0.
  exists x1.
  pose proof (c (fun n => projP1 _ _ (x0 n)) H).
  assert (forall n : nat, w_approx P n ((fun n0 : nat => projP1 Real (w_approx P n0) (x0 n0)) n)).
  intro.
  destruct (x0 n).
  simpl.
  exact w0.
  apply (H0 H1).
  exact i.
  exact X1.
  exact X.
Defined.

Set Warnings "-parsing".
From mathcomp Require Import all_ssreflect.
Require Import Real Reals RealCoqReal RealHelpers RealMetric Psatz.
Set Warnings "parsing".

Lemma consecutive_converging_fast_cauchy' : forall f : nat -> Real,  (forall n, dist (f n) (f (S n)) <= prec n.+1) -> is_fast_cauchy f.
Proof.
  move => f H.         
  have prec_pos n m :  - prec n - prec m <= dist (f n) (f m).
  - apply /Realle_le_le/dist_pos_t.
    rewrite <-Realplus_unit.
    rewrite /Realminus.
    apply Reallt_le.
    have -> : Real0 = -Real0 by rewrite -{1}(Realplus_inv Real0) Realplus_unit.
    by apply Reallt_lt_plus_lt;apply Reallt_anti;apply prec_pos.
  suff D  : forall n m, dist (f n) (f m) <= prec n + prec m.
  - move => n m.
    case (Realmetric_Or (f n) (f m)) => [[<- B] | [P B]].
    by split => //.
    suff [H0 H0']: - prec n - prec m <= f m - f n <= prec n + prec m.
    + have precR1 := (relate_prec m).
      have precR2 := (relate_prec n).
      have precR2' := relate_subtraction _ _ (relate_prec n).
      Holger H0.
      Holger H0'.
      split; classical;relate;by lra.
    rewrite -P.
    by split => //.
   suff P n k : dist (f (n + k)%coq_nat) (f n)  <= prec n + prec (n+k)%coq_nat.
  - move => n m.
    case (Nat.le_ge_cases n m) => le.
    have -> : (m = n + (m-n)%coq_nat)%coq_nat by lia.
    rewrite dist_symm.
    by apply P.
    have -> : (n = m + (n-m)%coq_nat)%coq_nat by lia.
    rewrite Realplus_comm.
    by apply P.
  suff P' : dist (f (n+k)%coq_nat) (f n) <= prec n - prec (n+k )%coq_nat.
  - have precR1 := (relate_prec n).
    have precR3 := (relate_prec (n+k)%coq_nat).
    have B1 := (tpmn_lt n).
    have B2 := (tpmn_lt (n+k)%coq_nat).
    Holger P'.
    classical.
    relate.
    by lra.
  elim k => [ | k' IH].
  - rewrite !Nat.add_0_r.
    rewrite (dist_zero (f n) (f n)).2 => //.
    rewrite /Realminus.
    rewrite Realplus_inv.
    by apply Realle_triv.
  have tri : dist (f (n+k'.+1)%coq_nat) (f n) <= dist (f (n+k')%coq_nat) (f (n+k'.+1)%coq_nat) + dist (f (n+k')%coq_nat) (f n) by apply Realge_le;rewrite dist_symm;apply dist_tri.
  apply /Realle_le_le.
  apply tri.
  have -> : ((n+k'.+1)%coq_nat = (n+k')%coq_nat.+1) by lia.
  apply /Realle_le_le.
  apply Realle_le_plus_le.
  apply H.
  apply IH.
  rewrite <- (prec_twice (n+k')%coq_nat).
  rewrite Nat.add_1_r.
  classical.
  relate.
  by lra.
Qed.
