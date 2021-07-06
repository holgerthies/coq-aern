From mathcomp Require Import all_ssreflect.
Require Import ConstructiveEpsilon.
Require Import PeanoNat.

(* ******************************************** *)
(* search for nat with decidable precidate P *)
(* ******************************************** *)

(* Adapted code from https://softwarefoundations.cis.upenn.edu/current/lf-current/Logic.html *)
Theorem restricted_excluded_middle : forall P b,
(P <-> b = true) -> {P} + {~ P}.
Proof.
intros P [] H.
- left. rewrite H. reflexivity.
- right. rewrite H. intros contra. discriminate contra.
Defined.

Theorem lem_nat_eq : forall (n m : nat),
  {n = m} + {n <> m}.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply Nat.eqb_eq.
Defined.
(* End of adapted code *)

Definition testLPO1 : { n:nat |  n = 10%N }.
Proof.
  apply constructive_indefinite_ground_description_nat.
  move => n.
  apply lem_nat_eq.
  by exists 10%N.
Defined.

Compute let (a,_) := testLPO1 in a.
(* 
	 = 10
     : nat
*)

Require Import Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellNatInteger.
Extraction Language Haskell.

(* Extraction "Main" testLPO1. *)

Require Import Kleene.
Require Import Psatz.
Require Import Nat.
Require Import Reals.

Require Import Real RealCoqReal RealHelpers.

(* results about (/ 2 ^ n) adapted  from incone *)
Lemma tpmn_lt n: (0 < /2^n)%R.
Proof. apply/Rinv_0_lt_compat/pow_lt; lra. Qed.

Lemma pwr2gtz m: exists n, (2^n > m)%nat.
Proof.
  elim: m => [ | m [n /leP ih]]; first by exists 0%nat; apply /leP => /=; lia.
  by exists n.+1; apply /leP => /=; lia.
Qed.

Lemma dns0_tpmn: forall eps, (0 < eps)%R -> exists n, (/2^n < eps)%R.
Proof.
  move => eps epsprp.
  pose z := Z.to_nat (up (/eps)).
  have [n /leP nprp]:= pwr2gtz z; have g0: (0 < 2^n)%R by apply pow_lt; lra.
  exists n.
  rewrite -[eps]Rinv_involutive; try lra.
  apply Rinv_lt_contravar; first by rewrite Rmult_comm; apply Rdiv_lt_0_compat;  try lra.
  have ->: (2 = INR 2)%R by trivial.
  rewrite -pow_INR.
  apply /Rlt_le_trans/(le_INR _ _ nprp).
  suff : (INR z.+1 > (/ eps))%R by lra.
  apply /Rgt_trans/(archimed (/ eps)).1.
  rewrite S_INR.
  rewrite INR_IZR_INZ.
  unfold z.
  rewrite Z2Nat.id; first by lra.
  apply le_IZR.
  have epsprp' : (0 < / eps)%R by apply Rinv_0_lt_compat.
  suff: ((IZR (up (/ eps))) > (/ eps))%R by lra.
  by apply archimed.
Qed.


(* ******************************************** *)
(* search for n with P n for a non-deterministically 
                         "choosable" precidate P *)
(* ******************************************** *)

Definition mjoinM (p q : Prop) (T : Type) : ({p}+{q} -> M T) ->  M ({p}+{q}) -> M T.
Proof.
  intros f x.
  exact (lift_domM _ _ f x).
Defined.


Definition linear_search_choose 
  (P : nat -> Prop)
  (P_decM : (forall n : nat, M ({P n.+1} + {~ P n}))) 
  := 
fix linear_search (m : nat) (b : before_witness P m) {struct b} :
	M {n : nat | P n} := 
  mjoinM _ _ _ 
    (fun P_dec =>
      match P_dec with
      | left yes_next => unitM _ (exist [eta P] m.+1 yes_next)
      | right no => linear_search m.+1 (inv_before_witness P m b no)
      end)
    (P_decM m).

Definition constructive_search_choose_nat
  : forall P : nat -> Prop,
      (forall n : nat, M ({P n.+1} + {~ P n}) ) ->
      (exists n : nat, P n) -> 
      M {n : nat | P n}
  :=
    fun 
    (P : nat -> Prop) 
    (P_decM : forall n : nat, M ({P n.+1} + {~ P n}))
    (e : exists n : nat, P n) =>
  linear_search_choose P P_decM 0 (let (n, p) := e in O_witness P n (stop P n p)).

(* ******************************************** *)
(* search for the minimal n with P n for a 
  "non-deterministically choosable" precidate P  *)
(* ******************************************** *)

Definition linear_search_min_choose 
  (P : nat -> Prop)
  (P_decM : (forall n : nat, M ({P n.+1} + {~ P n}))) 
  := 
fix linear_search (m : nat) (not_Pm : ~P m) (not_Pm1 : ~P m.+1) (b : before_witness P m.+2) {struct b} :
	M {n : nat | P (n.+2) /\ ~ P n} := 
  mjoinM _ _ _ 
    (fun P_dec =>
      match P_dec with
      | left yes_next => 
          unitM _ (exist [eta (fun n => P (n.+2) /\ ~ P n)] m.+1 (conj yes_next not_Pm1))
      | right no => linear_search m.+1 not_Pm1 no (inv_before_witness P m.+2 b no)
      end)
    (P_decM m.+2).

Definition constructive_search_min_choose_nat
  : forall P : nat -> Prop,
      (forall n : nat, M ({P n.+1} + {~ P n}) ) ->
      (exists n : nat, P n) -> 
      ~P O ->
      ~P (S(O)) ->
      M {n : nat | P (n.+2) /\ ~ P n}
  :=
    fun 
    (P : nat -> Prop) 
    (P_decM : forall n : nat, M ({P n.+1} + {~ P n}))
    (e : exists n : nat, P n) 
    not_P0 not_P1 =>
  linear_search_min_choose P P_decM 0 not_P0 not_P1 
    (let (n, p) := e in 
    (inv_before_witness P _ 
      (inv_before_witness P _ 
        (O_witness P n (stop P n p))
        not_P0)
      not_P1))
.


Definition lt_prec x n := prec n < x.

Definition is_magnitude1 x n := 
  lt_prec x n.+2 /\ not (lt_prec x n)
.
    (* prec n.+2 < x < prec n. *)

Lemma weaken_orM_r : forall P Q Q': Prop, (Q -> Q') -> M ({P}+{Q}) -> M ({P}+{Q'}).
Proof.
  intros P Q Q' QQ'.
  apply liftM.
  move => [iP|iQ].
  left. by auto.
  right. exact (QQ' iQ).
Qed.

Lemma half_lt_one : Real1 / Real2_neq_Real0 < Real1.
Proof.
classical.
relate.
suff -> : (y = 2)%R by lra.
by apply relate_IZReal.
Qed.

Definition magnitude1 x : (Real0 < x < Real1 / Real2_neq_Real0) 
  -> M { n | is_magnitude1 x n }.
Proof.
  move => [pos lt2].
  unfold is_magnitude1.
  apply constructive_search_min_choose_nat.
  unfold lt_prec.
  intros.
  apply (weaken_orM_r _ (x < prec n) _).
  intros.
  auto with Realiny.
  apply choose.
  auto with Realiny.
  auto with Realiny.

  (* prec n.+1 < x \/ x < prec n *)
  destruct (Realtotal_order x (prec n)) as [H|[H|H]].
  right. exact H.
  left. rewrite H. apply prec_S.
  left. unfold Realgt in H. apply (Reallt_lt_lt _ (prec n) _).
  apply prec_S. exact H.

  (* ~ lt_prec x 0 *)
  Focus 2. unfold lt_prec. apply Realgt_ngt. unfold prec. unfold Realgt. 
  have h := half_lt_one.
  apply (Reallt_lt_lt _ (Real1 / Real2_neq_Real0) _); auto.

  (* ~ lt_prec x 1 *)
  Focus 2. unfold lt_prec. unfold prec. apply Realgt_ngt. unfold Realgt. auto.
  unfold lt_prec.
  case (ana1 x) => xr [R1 R2].
  suff : exists n,  (/ 2 ^ n < xr)%R.
  - case => n nprp.
    exists n.
    have P := (relate_prec n).
    classical.
    by relate.
  apply dns0_tpmn.
  by apply /transport_lt_inv/pos/R1/relate_constant0.
Qed.

(* ******************************************** *)
(* Code exracted from ConstructiveEpsilon. 
             Included here only for reference.  *)
(* ******************************************** *)

(* 

Inductive before_witness (P : nat -> Prop) (n : nat) : Prop :=
	stop : P n -> before_witness P n
  | next : before_witness P n.+1 -> before_witness P n.

Definition inv_before_witness
  : forall (P : nat -> Prop) (n : nat),
  before_witness P n -> ~ P n -> before_witness P n.+1
  :=
fun (P : nat -> Prop) (n : nat) (b : before_witness P n) =>
match b with
| @stop _ _ p =>
	fun not_p : ~ P n =>
    match not_p p return (before_witness P n.+1) with
    end
| @next _ _ b0 => fun=> b0
end.

Definition constructive_indefinite_ground_description_nat
  : forall P : nat -> Prop,
      (forall n : nat, {P n} + {~ P n}) ->
      (exists n : nat, P n) -> {n : nat | P n}
  :=
fun (P : nat -> Prop) 
  (P_dec : forall n : nat, {P n} + {~ P n})
  (e : exists n : nat, P n) =>
linear_search P P_dec 0 (let (n, p) := e in O_witness P n (stop P n p)).
      
      
Definition constructive_indefinite_ground_description_nat
  : forall P : nat -> Prop,
  (forall n : nat, {P n} + {~ P n}) ->
  (exists n : nat, P n) -> {n : nat | P n}
  :=
fun (P : nat -> Prop) 
    (P_dec : forall n : nat, {P n} + {~ P n})
    (e : exists n : nat, P n) =>
  linear_search P P_dec 0 (let (n, p) := e in O_witness P n (stop P n p)).

Definition O_witness
  : forall (P : nat -> Prop) (n : nat),
  before_witness P n -> before_witness P 0
:=
fun P : nat -> Prop =>
  fix O_witness (n : nat) : before_witness P n -> before_witness P 0 :=
    match n as n0 return (before_witness P n0 -> before_witness P 0) with
    | 0 => id
    | n0.+1 => fun b : before_witness P n0.+1 => O_witness n0 (next P n0 b)
    end.

Definition linear_search
  : forall P : nat -> Prop,
  (forall n : nat, {P n} + {~ P n}) ->
  forall m : nat, before_witness P m -> {n : nat | P n}
  :=
fun (P : nat -> Prop) (P_dec : forall n : nat, {P n} + {~ P n}) =>
    fix linear_search (m : nat) (b : before_witness P m) {struct b} :
	  {n : nat | P n} :=
      match P_dec m with
      | left yes => exist [eta P] m yes
      | right no => linear_search m.+1 (inv_before_witness P m b no)
      end.

Definition constructive_indefinite_ground_description_nat
  : forall P : nat -> Prop,
  (forall n : nat, {P n} + {~ P n}) ->
  (exists n : nat, P n) -> {n : nat | P n}  
  :=
  fun (P : nat -> Prop) (P_dec : forall n : nat, {P n} + {~ P n})
    (e : exists n : nat, P n) =>
  linear_search P P_dec 0 (let (n, p) := e in O_witness P n (stop P n p))
     : forall P : nat -> Prop,
         (forall n : nat, {P n} + {~ P n}) ->
  (exists n : nat, P n) -> {n : nat | P n}. 
  
  *)
