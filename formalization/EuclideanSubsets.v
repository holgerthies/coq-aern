(* this file proves various properties of subsets of real numbers *)
Require Import Lia.
Require Import Real Euclidean List Minmax ClassicalSubsets Sierpinski testsearch Dyadic Subsets.
Check multivalued_countable_choice.
Section EuclideanBalls.

Context {d : nat}.
Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).
#[local] Definition sofReal := @sofReal types casofReal.
#[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).
#[local] Notation "^euclidean" := (@euclidean types) (at level 0).


  Ltac IZReal_tac t :=
    match t with
    | real_0 => constr:(0%Z)
    | real_1 => constr:(1%Z)
    | IZreal ?u =>
      match isZcst u with
      | true => u
      | _ => constr:(InitialRing.NotConstant)
      end
    | _ => constr:(InitialRing.NotConstant)
    end.

  Add Ring realRing : (realTheory ) (constants [IZReal_tac]).
  

(** Define classical euclidean subsets and operations on them **)
Definition euclidean_subset :=  (@csubset (^euclidean d)).

Definition union (A B : euclidean_subset) : euclidean_subset := fun x => A x \/ B x.
Definition intersection (A B : euclidean_subset) : euclidean_subset:= fun x => A x /\ B x.

Definition translation (A : euclidean_subset) (a : euclidean d ): euclidean_subset := fun x => A (euclidean_minus x a).

Definition scaling (l : Real )(A : euclidean_subset) : euclidean_subset := fun x => exists y, x = (euclidean_scalar_mult l y) /\ A y.


(** Basic subsets are the empty set and balls in max norm **)
Definition empty_set : euclidean_subset := fun x => False.

(** open and closed balls are encoded as pairs of midpoint and radius.
As the radius is not required to be positive, the empty set is included **)
Definition ball := ((^euclidean d) * ^Real)%type.

(** emebedding of open balls **)
Definition ball_to_subset (b : ball)  : euclidean_subset := (fun x => (euclidean_max_dist x (fst b)) < (snd b)).  

(** emebedding of closed balls **)
Definition closed_ball_to_subset (b : ball)  : euclidean_subset := (fun x => (euclidean_max_dist x (fst b)) <= (snd b)).  

(** It is semidecidable if a point is cointained in an open ball *)
Lemma contained_in_ball_semidec b x : {s : sierp | sierp_up s <-> (ball_to_subset b) x}.
  Proof.
    unfold ball_to_subset.
    destruct (sierp_from_semidec (real_lt_semidec (euclidean_max_dist x (fst b)) (snd b))) as [s P].
    exists s.
    apply P.
Defined.



Lemma ball_max_dist x y b: ball_to_subset b x -> ball_to_subset b y -> euclidean_max_dist x y < real_2*(snd b). 
Proof.
  intros H1 H2.
  apply (real_le_lt_lt _ _ _ (euclidean_max_dist_tri x (fst b) y)).
  assert (real_2 = real_1 + real_1) as -> by auto.
  assert ((real_1 + real_1) * snd b = snd b + snd b ) as -> by ring.
  apply real_lt_lt_plus_lt;auto.
  rewrite euclidean_max_dist_sym;auto.
Defined.

Lemma empty_ball_subset A x : is_subset (ball_to_subset (x,real_0)) A.
Proof.
  unfold is_subset, ball_to_subset.
  simpl.
  intros y P.
  apply real_gt_nle in P.
  contradict P.
  apply euclidean_max_dist_pos.
Defined.

(** Some basic properties  **)

Definition rad (L : list ball) := (fold_right (fun b1 r => (real_max (snd b1) r)) real_0 L).

Lemma ball_to_subset_scalar_mult s c1 r1 p1:
    s > real_0 ->
    ball_to_subset (c1, r1) p1 ->
    ball_to_subset (euclidean_scalar_mult s c1, s * r1) (euclidean_scalar_mult s p1).
  Proof.
    unfold ball_to_subset; simpl.
    intros.
    rewrite euclidean_max_dist_scalar_mult.
    apply real_lt_mult_pos_lt; auto.
    apply real_lt_le;auto.
Defined.

Lemma ball_to_subset_plus c1 r1 p1 c2 r2 p2 :
    ball_to_subset (c1, r1) p1 ->
    ball_to_subset (c2, r2) p2 ->
    ball_to_subset (euclidean_plus c1 c2, r1 + r2) (euclidean_plus p1 p2).
Proof.
    unfold ball_to_subset; simpl.
    intros.
    apply (real_le_lt_lt _ (euclidean_max_dist p1 c1 + euclidean_max_dist p2 c2)).
    apply euclidean_max_dist_plus_le.
    apply real_lt_lt_plus_lt; auto.
Defined.
End EuclideanBalls.

Section BallOperations.
(** Operations on lists of balls **)

  Context {d : nat}.
  Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

  #[local] Notation "^K" := (@K types) (at level 0).
  #[local] Notation "^M" := (@M types) (at level 0).
  #[local] Notation "^Real" := (@Real types) (at level 0).
  #[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).
  #[local] Notation "^euclidean" := (@euclidean types) (at level 0).
  Add Ring realRing : (realTheory ).


  Fixpoint change_rad (L : list (@ball d types)) (p : nat) :=
    match L with
     | nil => nil
    | a :: L' => (fst a, prec p) :: change_rad L' p
   end.

  Lemma change_rad_spec L p : forall b, In b (change_rad L p) <-> snd b = prec p /\ exists r, In (fst b, r) L.
  Proof.
    intros b.
    induction L as [ | b' L' [IH1 IH2]].
    split;simpl;intros;[contradict H | destruct H; destruct H0;auto].
    split.
    - simpl.
      intros.
      destruct H.
      destruct b as [cb rb].
      destruct b' as [cb' rb'].
      simpl.
      apply pair_equal_spec in H.
      destruct H.
      split; simpl; auto.
      exists rb'.
      left.
      f_equal.
      apply H.
      pose proof (IH1 H) as [IHl IHr].
      split;auto.
      destruct IHr.
      exists x.
      right;auto.
   - simpl.
     intros [H1 H2].
     destruct H2.
     destruct H.
     destruct b.
     destruct b'.
     simpl.
     apply pair_equal_spec in H.
     destruct H.
     left.
     f_equal;auto.

     right.
     apply IH2.
     split;auto.
     destruct b.
     exists x.
     apply H.
  Defined.

  Lemma change_rad_rad L p: rad (change_rad L p) <= prec p.
  Proof.
    induction L as [ | b L' IH].
    simpl.
    apply real_lt_le.
    apply prec_pos.
    simpl.
    apply real_max_le_le_le.
    apply real_eq_le; auto.
    apply IH.
  Defined.

  Lemma rad_forall L b : In b L -> snd b <= (rad (d:=d) L).
  Proof.
    induction L.
    simpl;intros; contradict H.
    simpl.
    intros.
    destruct H.
    rewrite H.
    apply real_ge_le.
    apply real_max_fst_ge.
    apply (real_le_le_le _ (rad L)).
    apply IHL; auto.
    apply real_ge_le.
    apply real_max_snd_ge.
  Defined.

  Lemma rad_le L r : r >= real_0 -> (forall b, In b L -> snd b <= r) <-> rad (d := d) L <= r.
  Proof.
    intro rpos.
    split.
    - intro.      
      induction L.
      auto.
      apply real_max_le_le_le.
      apply H.
      unfold In; left; auto.
      apply IHL.
      intros.
      apply H.
      unfold In; right; auto.
    - intros.
      induction L.
      contradict H0.
      destruct H0.
      rewrite <- H0.
      apply real_max_le_fst_le in H; auto.
      apply IHL; auto.
      apply real_max_le_snd_le in H; auto.
  Defined.

  Lemma rad_prec_spec L p : rad (d := d) L <= prec p <-> forall b, In b L -> (snd b <= prec p).
  Proof.
    split.
    intros.
    apply (real_le_le_le _ (rad L));auto.
    apply rad_forall;auto.
    intros.
    induction L.
    simpl.
    apply real_lt_le.
    apply prec_pos.
    simpl.
    apply real_max_le_le_le.
    apply H.
    left;auto.
    apply IHL.
    intros b inb.
    apply H.
    right;auto.
  Defined.

  Fixpoint scale_list (L : list ball) l := match L with
                               nil => nil
                             | b :: L' => (euclidean_scalar_mult (n := d) l (fst b), l * (snd b)) :: scale_list L' l
                            end.


  Lemma scale_rad L l: (real_0 <= l) -> rad (scale_list L l) = l * rad L.
  Proof.  
    intros H.
    induction L as [| b L' IH].
    simpl;ring.
    simpl;rewrite IH.
    rewrite real_max_hom;auto.
  Qed.

  Lemma scale_list_in L l b: l <> real_0 -> In b L <-> In ((euclidean_scalar_mult l (fst b)),(l * snd b)) (scale_list L l).
  Proof.
    intros l0.
    induction L.
    split;auto.
    simpl.
    split; intros.
    destruct H.
    rewrite H.
    left;auto.
    right.
    apply IHL;auto.
    destruct H.
    - left.
      injection H.
      intros.
      destruct a;destruct b.
      simpl in H0.
      f_equal.
      apply (euclidean_eq_scalar_mult_cancel l);auto.
      apply (real_eq_mult_cancel _ r r0 l0);rewrite !(real_mult_comm _ l);auto.
   - right.
     apply IHL.
     apply H.
  Qed.

  Lemma scale_list_in_rev L l b (lneq0 : l <> real_0) : In b (scale_list L l) <-> In ((euclidean_scalar_mult (/ lneq0) (fst b)),((/ lneq0) * snd b)) L.
  Proof.

    pose proof (scale_list_in L l ((euclidean_scalar_mult (/ lneq0) (fst b)),((/ lneq0) * snd b)) lneq0).
    simpl in H.
    assert (l * (/ lneq0 * snd b) = snd b) by (rewrite <-real_mult_assoc,(real_mult_comm l), real_mult_inv, real_mult_unit;auto).
    assert (euclidean_scalar_mult l (euclidean_scalar_mult (/ lneq0) (fst b)) = fst b) by apply euclidean_scalar_mult_inv.
    rewrite H0,H1 in H.
    destruct b.
    split;apply H.
  Defined.

  Lemma scale_intersects M L l  : (real_0 < l) -> Forall (fun b : ball => intersects (closed_ball_to_subset b) M) L -> Forall (fun b : ball => intersects (closed_ball_to_subset b) (scaling l M)) (scale_list L l).
  Proof.
    intros lgt0 H.
    pose proof (real_gt_neq _ _ lgt0) as lneq0.
    apply Forall_forall.
    rewrite Forall_forall in H.
    intros b inb.
    pose proof (scale_list_in_rev L l b lneq0).
    destruct (H (euclidean_scalar_mult (/ lneq0) (fst b), / lneq0 * snd b)) as [x [P1 P2]].
    apply H0;auto.
    exists (euclidean_scalar_mult l x).
    split.
    - unfold ball_to_subset in P1.
      simpl in P1.
      unfold ball_to_subset.
      pose proof (euclidean_max_dist_scalar_mult (euclidean_scalar_mult l x) (fst b) (/ lneq0)).
      assert (/ lneq0 > real_0) by  (apply real_pos_inv_pos;auto).
      apply (real_le_mult_pos_cancel (/ lneq0));auto.
      rewrite real_mult_comm.
      rewrite <-H1;auto.
      pose proof (real_gt_neq _ _ H2) as dlneq0.
      assert (l = / dlneq0 ).
      {
        apply (real_eq_mult_cancel _ _ _ dlneq0).
        rewrite real_mult_inv, real_mult_comm, real_mult_inv.
        auto.
      }
      replace (euclidean_scalar_mult l x) with (euclidean_scalar_mult (/ dlneq0) x) by (rewrite <-H3;auto).
      rewrite euclidean_scalar_mult_inv.
      rewrite real_mult_comm;auto.
      left. auto.
   - exists x;auto.
  Defined.
End BallOperations.

Section EuclideanOpen.
(** This section defines an alternative encoding for open sets of euclidean space and shows the equivalence to the more general definition **)
Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.
 Context {d : nat}.

#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).
#[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).
#[local] Notation "^euclidean" := (@euclidean types) (at level 0).


  Add Ring realRing : (realTheory ).
  

  Definition euclidean_open (M : euclidean_subset) := {c : nat -> (ball (d := d)) | (forall n, is_subset (ball_to_subset (c n)) M) /\ forall x, M x -> exists n, (ball_to_subset (c n)) x}.


  Lemma euclidean_open_is_open M : euclidean_open M -> open M.
  Proof.
    unfold open.
    intros OM x.
    destruct OM as [c P].
    pose ((fun n=> projP1 _ _ (contained_in_ball_semidec (c n) x)) : nat -> sierp).
    assert (forall n, sierp_up (s n) <-> (ball_to_subset (c n)) x).
    {
      intros.
      unfold s.
      destruct (contained_in_ball_semidec  (c n)).
      auto.
    }
    assert (M x <-> exists n, ball_to_subset (c n) x).
    {
      split.
      apply P.
      intros.
      destruct H0.
      destruct P.
      apply (H1 x0);auto.
    }
    destruct (eventually_true s) as [k' [H1 H2]].
    exists k'.
    rewrite H0.
    split; intros.
    destruct (H1 H3) as [n nprp].
    exists n.
    apply H;auto.
    destruct H3 as [n nprp].
    apply H2.
    exists n.
    apply H.
    exact nprp.
  Defined.

  (* Lemma enumerate_dyadic_elements A : open A -> ^M {f : nat -> option (@DyadicVector d) | forall v, A (to_euclidean v) <-> exists n, (f n) = Some v}. *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct (open_cf_exists X) as [f P]. *)
  (*   destruct (enumerable_dyadic_vector d) as [e E]. *)
  (*   pose proof (multivalued_choice_sequence_sierp (fun n => (f (to_euclidean (e n))))). *)
  (*   revert X0. *)
  (*   apply M_lift. *)
  (*   intros [c [cprp1 cprp2]]. *)
  (*   exists (fun n => if (c n) =? 0 then None else Some (e (pred (c n)))). *)
  (*   intros. *)
  (*   rewrite <-P. *)
  (*   destruct (E v) as [m <-]. *)
  (*   split. *)
  (*   - intros. *)
  (*     destruct (cprp2 _ H) as [n [H' <-]]. *)
  (*     exists n. *)
  (*     rewrite <-Nat.eqb_neq in H'. *)
  (*     rewrite H';reflexivity. *)
  (*  - intros H. *)
  (*    destruct H as [n N]. *)
  (*    specialize (cprp1 n). *)
  (*    destruct (c n);simpl in N. *)
  (*    contradict N; discriminate. *)
  (*    rewrite Nat.pred_succ in cprp1. *)
  (*    injection N; intros <-. *)
  (*    destruct cprp1;[contradict H |];auto. *)
  (* Defined. *)


  Lemma open_is_euclidean_open A : open A -> ^M (euclidean_open A).
  Proof.
    intros.
    destruct (open_cf_exists X) as [f P].
    pose proof (interval_extension_sierp f) as I.
    revert I.
    apply M_lift.
    intros [F [I1 I2]].
    destruct (enumerable_pair _ _ (enumerable_dyadic_vector d) enumerable_nat) as [e E].
    exists (fun n => if (F (fst (e n)) (snd (e n))) then (to_euclidean (fst (e n)), prec (snd (e n))) else ((euclidean_zero d), real_0)).
    split.
    - unfold is_subset;simpl.
      intros.
      rewrite <-P.
      destruct (F (fst (e n)) (snd (e n))) eqn : B.

      apply (I1 _ _ B).
      exact H.

      pose proof (euclidean_max_dist_pos x (euclidean_zero d)).
      contradict H0.
      apply real_gt_nge.
      exact H.
   - intros.
     destruct (I2 x ((proj2 (P x)) H)) as [v [n [N1 N2]]].
     destruct (E (v,n)) as [m M].
     exists m.
     rewrite M;simpl; rewrite N2.
     exact N1.
   Defined.

  (** Operations on Euclidean open sets **)

  Lemma euclidean_open_union (M1 M2 : euclidean_subset) : euclidean_open M1 -> euclidean_open M2 -> euclidean_open (union M1 M2).
  Proof.
    intros H1 H2.
    destruct H1 as [c1 [P1 P2]].
    destruct H2 as [c2 [Q1 Q2]].
    exists (fun n => if Nat.even n then (c1 (n/2)%nat) else (c2 ((n-1)/2)%nat)). 
    split; intros.
    - intros x.
      destruct (Nat.even n); [left;apply (P1 (n /2) %nat x) | right; apply (Q1 ((n-1) /2)%nat x)];auto.
    - destruct H.

      destruct (P2 x H) as [n P2'].
      exists (2*n)%nat.
      rewrite Nat.even_mul.
      replace ((2*n) /2)%nat with n by (rewrite Nat.mul_comm, Nat.div_mul;auto).
      apply P2'.

      destruct (Q2 x H) as [n Q2'].
      exists (2*n+1)%nat.
      rewrite Nat.add_comm, Nat.even_add_mul_2.
      replace ((1 + 2*n - 1) /2)%nat with n by (rewrite Nat.add_comm, Nat.add_sub, Nat.mul_comm, Nat.div_mul;auto).
      apply Q2'.
  Defined.

End EuclideanOpen.

Section EuclideanLocated.
  Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

  #[local] Notation "^K" := (@K types) (at level 0).
  #[local] Notation "^M" := (@M types) (at level 0).
  #[local] Notation "^Real" := (@Real types) (at level 0).
  #[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).
  #[local] Notation "^euclidean" := (@euclidean types) (at level 0).

  Add Ring realRing : (realTheory ).
  Context {d : nat}.

  Definition located (M : euclidean_subset) := 
    forall n, {Ln : list (ball (d := d)) |
                rad Ln <= prec n /\
                Forall (fun b => intersects (closed_ball_to_subset b) M) Ln /\
                forall x,  M x ->  Exists (fun b => (closed_ball_to_subset b) x) Ln
      }.

  Definition dist A (x : euclidean d) r := (exists y, A y /\ euclidean_max_dist x y <= r) /\ forall y, A y -> euclidean_max_dist x y >= r.

  Lemma min_dist_point (c : euclidean d) r x :  (r >= real_0) -> (euclidean_max_dist x c) >= r -> exists y, euclidean_max_dist c y = r /\ euclidean_max_dist x y = (euclidean_max_dist c x) - r.
  Proof.
    intros.
    destruct H0.
    2 : {
      exists x.
      rewrite euclidean_max_dist_sym;split;auto.
      rewrite <- H0.
      assert (euclidean_max_dist x x = real_0) as -> by (apply euclidean_max_dist_id;auto).
      ring.
    }
    assert ((euclidean_max_dist x c) <> real_0) by (apply dg0;apply (real_le_lt_lt _ _ _ H);auto).
    exists ((r * (/ H1))%Real * (x - c) + c )%euclidean.
    split.
    - rewrite <-(euclidean_plus_zero c) at 1.
      rewrite euclidean_plus_comm.
      rewrite euclidean_max_dist_plus_cancel.
      assert ((euclidean_zero d) = ((r * / H1)%Real * (euclidean_zero d))%euclidean) as ->.
      {
        rewrite <- (euclidean_scalar_mult_zero (euclidean_zero d)) at 2.
        rewrite euclidean_scalar_mult_mult.
        assert (r * / H1 * real_0 = real_0) as -> by ring.
        rewrite euclidean_scalar_mult_zero;auto.
      }
      rewrite euclidean_max_dist_scalar_mult.
      rewrite euclidean_max_dist_minus_plus.
      rewrite euclidean_plus_comm.
      rewrite euclidean_plus_zero.
      rewrite (euclidean_max_dist_sym c x).
      rewrite real_mult_assoc.
      rewrite real_mult_inv;ring.
      apply real_le_pos_mult_pos_pos;auto.
      apply real_lt_le.
      apply real_pos_inv_pos.
      apply (real_le_lt_lt _ r);auto.
    -
      rewrite euclidean_max_dist_sym.
      rewrite <-euclidean_max_dist_minus_plus.
      rewrite euclidean_max_dist_sym.
      rewrite euclidean_max_dist_scaled.
      rewrite (euclidean_max_dist_sym (x-c)%euclidean), euclidean_max_dist_minus_plus.
      rewrite euclidean_plus_comm, euclidean_plus_zero.
      rewrite real_mult_comm.
      unfold real_minus.
      rewrite real_mult_plus_distr.
      rewrite real_mult_comm,real_mult_unit.
      rewrite real_plus_comm, (real_plus_comm _ (-r)).
      apply real_eq_plus_eq.
      assert ((euclidean_max_dist c x) * - (r * (/ H1)) = (((/ H1) * euclidean_max_dist x c) * (-r))) as -> by (rewrite euclidean_max_dist_sym;ring).
      rewrite real_mult_inv.
      ring.
      apply (real_le_mult_pos_cancel (euclidean_max_dist x c)).
      apply (real_le_lt_lt _ r);auto.
      rewrite real_mult_assoc.
      rewrite real_mult_inv.
      rewrite real_mult_comm, !real_mult_unit.
      apply real_lt_le;auto.
  Defined.

  Lemma closed_ball_dist_exists b x : (snd b)  >= real_0 -> {r | dist (closed_ball_to_subset b) x r}.
  Proof.
    intros R.
    destruct b as [c r].
    exists (real_max real_0 ((euclidean_max_dist c x)- r)).
    split.
    - destruct (real_max_cand real_0 (euclidean_max_dist x c -r)).
      + assert (r >= euclidean_max_dist x c).
        { add_both_side_by (-r).
          assert ((-r + euclidean_max_dist x c) = euclidean_max_dist x c - r) as -> by ring.
          apply (real_max_eq_snd_le _ _ _ H).
        }
        exists x.
        rewrite (euclidean_max_dist_sym  c).
        rewrite H.
        split;auto.
        rewrite (proj2 (euclidean_max_dist_id x x) eq_refl). 
        apply real_le_triv.
      + assert (r <= euclidean_max_dist x c).
        { add_both_side_by (-r).
          assert ((-r + euclidean_max_dist x c) = euclidean_max_dist x c - r) as -> by ring.
          apply (real_max_eq_fst_le _ _ _ H).
        }
        destruct (min_dist_point c r x) as [y [P1 P2]]; auto.
        exists y.
        split;unfold closed_ball_to_subset;[simpl;rewrite euclidean_max_dist_sym, P1; apply real_le_triv | ].
        rewrite (euclidean_max_dist_sym c), H, (euclidean_max_dist_sym _ c), P2.
        apply real_le_triv.
    - intros.
      destruct (real_max_cand real_0 (euclidean_max_dist x c -r)); rewrite (euclidean_max_dist_sym c), H0;[apply euclidean_max_dist_pos | ].
      add_both_side_by r.
      apply (real_le_le_le _ _ _ (euclidean_max_dist_tri x y c)).
      apply real_le_plus_le.
      apply H.
  Defined.

  Lemma located_dist_exists M x : (exists y, M y) -> (located M) -> {r | forall y, M y -> euclidean_max_dist x y >= r /\ exists y, M y /\ euclidean_max_dist x y = r}.
  Proof.
    intros nonempty H.
    apply real_limit_P.
  Admitted.

  Lemma located_union K1 K2 : located K1 -> located K2 -> located (union K1 K2).
  Proof.
    intros H1 H2 n.
    destruct (H1 n) as [L1 [D1 [int1 cov1]]].
    destruct (H2 n) as [L2 [D2 [int2 cov2]]].
    exists (L1 ++ L2).
    split; [| split].
    - apply rad_prec_spec.
      intros b inb.
      apply in_app_or in inb.
      destruct inb;[apply (rad_prec_spec L1 n) | apply (rad_prec_spec L2 n)];auto.
  - apply Forall_app.
    rewrite Forall_forall in int1.
    rewrite Forall_forall in int2.
    assert (forall b, intersects (closed_ball_to_subset b) K1 \/ intersects (closed_ball_to_subset b) K2 -> intersects (closed_ball_to_subset b) (union K1 K2)) by (intros; apply intersects_union;auto).
    split;apply (Forall_impl _ H);apply Forall_forall;intros b inb; [left;apply int1 | right;apply int2];auto.
 - intros x cx.
   apply Exists_app.
   destruct cx; [left;apply cov1 | right;apply cov2];auto.
  Defined.

  Lemma located_translation K a : located K -> located (translation K a).
  Proof.
    intros H n.
    destruct (H n) as [L [D [int cov]]].
    exists (map (fun (b : ball) => ((euclidean_plus (fst b) a),(snd b))) L).
    split; [|split].
    - apply rad_prec_spec.
      intros b inb.
      apply in_map_iff in inb.
      destruct inb as [x [Hx Hx']].
      destruct b.
      simpl.
      injection Hx.
      intros <- _.
      apply (real_le_le_le _ (rad L));auto.
      apply rad_forall;auto.
  -  apply Forall_forall.
     intros b inb.
     rewrite Forall_forall in int.
     assert (In ((euclidean_minus (fst b) a), snd b) L).
     {
       rewrite in_map_iff in inb.
       destruct inb as [x [P1 P2]].
       destruct b.
       injection P1; intros <- <-;simpl.
       rewrite euclidean_minus_plus.
       destruct x; auto.
     }
     destruct (int _ H0) as [x [xp1 xp2]].
     exists (euclidean_plus x a).
     split.
     destruct b.
     unfold closed_ball_to_subset.
     unfold closed_ball_to_subset in xp1.
     simpl in xp1;simpl.
     rewrite <-euclidean_max_dist_minus_plus;auto.
     unfold translation;rewrite euclidean_minus_plus;auto.
 - intros x Tx.
   apply Exists_exists.
   pose proof (cov _ Tx).
   rewrite Exists_exists in H0.
   destruct H0 as [b [inb P]].
   destruct b as [cb rb].
   exists ((euclidean_plus cb a, rb)).
   split.
   apply in_map_iff.
   exists (cb, rb).
   split; auto.
   unfold closed_ball_to_subset.
   rewrite euclidean_max_dist_sym.
   simpl.
   rewrite <-euclidean_max_dist_minus_plus.
   rewrite euclidean_max_dist_sym.
   apply P.
  Defined.

  Lemma located_scale_down M k : located M -> located (scaling (prec k) M).
  Proof.
    intros Mc n.
    destruct (Mc (n-k)%nat) as [L [Lp1 [Lp2 Lp3]]].
    exists (scale_list L (prec k)).
    split; [|split].
    - rewrite scale_rad; [|left;apply prec_pos].
      apply (real_le_le_le _ ((prec k) * prec (n - k))).
      apply real_le_mult_pos_le; [left;apply prec_pos | auto].
      rewrite <- prec_hom.
      destruct (Nat.lt_ge_cases n k).
      pose proof (Nat.sub_0_le n k) as [H1 H2].
      rewrite H2; [|lia].
      apply real_lt_le.
      apply prec_monotone.
      lia.
      rewrite le_plus_minus_r; [apply real_eq_le;auto|lia].
  - apply scale_intersects;auto.
    apply prec_pos.
  - intros x H.
    assert (M (euclidean_scalar_mult (Nreal (Npow2 k)) x)) as My.
    {
      destruct H as [y [P1 P2]].
      rewrite P1.
      rewrite euclidean_scalar_mult_mult.
      rewrite real_mult_comm.
      rewrite prec_Npow2_unit.
      rewrite euclidean_scalar_mult_unit;auto.
    }
    pose proof (Lp3 (euclidean_scalar_mult (Nreal (Npow2 k)) x) My) as Lp3'.
    rewrite Exists_exists in Lp3'.
    destruct Lp3' as [b [inb B]].
    apply Exists_exists.
    exists (((euclidean_scalar_mult (prec k) (fst b))), (prec k * snd b)).
    split.
    apply scale_list_in;auto.
    apply real_gt_neq.
    apply prec_pos.
    unfold closed_ball_to_subset;simpl.
    replace x with (euclidean_scalar_mult (prec k) (euclidean_scalar_mult (Nreal (Npow2 k)) x)).
    rewrite euclidean_max_dist_scalar_mult; [|left;apply prec_pos].
    apply real_le_mult_pos_le;auto;left;apply prec_pos.
    rewrite euclidean_scalar_mult_mult.
    rewrite prec_Npow2_unit.
    apply euclidean_scalar_mult_unit.
 Defined.


  Lemma located_scale_up M k : located M -> located (scaling (Nreal (Npow2 k)) M).
  Proof.
    intros Mc n.
    destruct (Mc (n+k)%nat) as [L [Lp1 [Lp2 Lp3]]].
    exists (scale_list L (Nreal (Npow2 k))).
    split; [|split].
    - rewrite scale_rad; [|left;apply Nreal_Npow2_pos].
      apply (real_le_le_le _ (Nreal (Npow2 k) * prec (n + k))).
      apply real_le_mult_pos_le; [left;apply Nreal_Npow2_pos | auto].
      rewrite prec_hom.
      rewrite (real_mult_comm (prec n)), <-real_mult_assoc, (real_mult_comm _ (prec k)).
      rewrite prec_Npow2_unit, real_mult_unit.
      apply real_eq_le;auto.
  - apply scale_intersects;auto.
    apply Nreal_Npow2_pos.
  - intros x H.
    assert (M (euclidean_scalar_mult (prec k) x)) as My.
    {
      destruct H as [y [P1 P2]].
      rewrite P1.
      rewrite euclidean_scalar_mult_mult.
      rewrite prec_Npow2_unit.
      rewrite euclidean_scalar_mult_unit;auto.
    }
    pose proof (Lp3 (euclidean_scalar_mult (prec k) x) My) as Lp3'.
    rewrite Exists_exists in Lp3'.
    destruct Lp3' as [b [inb B]].
    apply Exists_exists.
    exists (((euclidean_scalar_mult (Nreal (Npow2 k)) (fst b))), ((Nreal (Npow2 k)) * snd b)).
    split.
    apply scale_list_in;auto.
    apply real_gt_neq.
    apply Nreal_Npow2_pos.
    unfold closed_ball_to_subset;simpl.
    replace x with (euclidean_scalar_mult (Nreal (Npow2 k)) (euclidean_scalar_mult (prec k) x)).
    rewrite euclidean_max_dist_scalar_mult; [|left;apply Nreal_Npow2_pos].
    apply real_le_mult_pos_le;auto;left;apply Nreal_Npow2_pos.
    rewrite euclidean_scalar_mult_mult.
    rewrite real_mult_comm.
    rewrite prec_Npow2_unit.
    apply euclidean_scalar_mult_unit.
  Defined.

  Definition Hausdorff_dist_bound (S T : (euclidean_subset (d := d))) n :=
    (forall x, S x -> exists y, T y /\ euclidean_max_dist x y <= n) /\
      (forall y, T y -> exists x, S x /\ euclidean_max_dist x y <= n).

  (* Lemma Hausdorff_dist_bound_approx M L n: (rad L <= prec n /\ Forall (fun b : ball => intersects (ball_to_subset b) M) L  /\ (forall x, M x -> Exists (fun b : ball => ball_to_subset b x) L)) -> Hausdorff_dist_bound M (fun x => Exists (fun b  => ball_to_subset b x) L) (real_2 * prec n). *)
  (* Proof. *)
  (*   intros [H1 [H2 H3]]. *)
  (*   unfold Hausdorff_dist_bound. *)
  (*   split. *)
  (*   - intros. *)
  (*     exists x. *)
  (*     split;[apply H3;auto|]. *)
  (*     rewrite ((proj2 (euclidean_max_dist_id x x)) (eq_refl x)). *)
  (*     assert (real_0 = real_2 * real_0) as -> by ring. *)
  (*     apply real_le_mult_pos_le; [apply real_lt_0_2|apply prec_pos]. *)
  (*  - intros. *)
  (*    apply Exists_exists in H. *)
  (*    destruct H as [b [B1 B2]]. *)
  (*    rewrite Forall_forall in H2. *)
  (*    destruct (H2 _ B1) as [x [I1 I2]]. *)
  (*    exists x;split;auto. *)
  (*    apply (real_lt_le_lt _ (real_2 * snd b)). *)
  (*    apply ball_max_dist;auto. *)
  (*    apply real_le_mult_pos_le. *)
  (*    apply real_lt_le;apply real_lt_0_2. *)
  (*    apply (real_le_le_le _ (rad L));auto. *)
  (*    apply (rad_forall _ _ B1). *)
  (* Defined. *)
  Lemma located_lim :
    forall K : euclidean_subset,
      (forall n : nat, {X :  euclidean_subset & prod (located X) (Hausdorff_dist_bound X K (prec n))})
      -> located K.
  Proof.
    intros.
    intro p.
    destruct (X (S p)) as [A [CA HD]].
    destruct (CA (S p)) as [L [dL [int cov]]].
    exists (change_rad L p).
    pose proof (change_rad_spec L p) as P.
    split.
    apply change_rad_rad.
    split.
    apply Forall_forall.
    intros b inb.
    pose proof (P b) as [P1 P2].
    specialize (P1 inb) as [P1' P1''].
    destruct P1'' as [r P1''].
    assert (forall b', (intersects (closed_ball_to_subset b') A /\ snd b' <= prec (S p)) -> intersects (closed_ball_to_subset ((fst b', prec p))) K).
    {
      intros b' [H1 H2].
      destruct H1 as [y [yp1 yp2]].
      destruct HD as [HD1 _].
      destruct (HD1 _ yp2) as [y' [y'p1 y'p2]].
      exists y'.
      split;auto.
      unfold closed_ball_to_subset;simpl.
      pose proof (euclidean_max_dist_tri y' y (fst b')).
      apply (real_le_le_le _ _ _ H).
      rewrite <-prec_twice.
      replace (p + 1)%nat with (S p) by lia.
      apply real_le_le_plus_le.
      rewrite euclidean_max_dist_sym;auto.
      apply (real_le_le_le _ (snd b'));auto.

    }
    specialize (H (fst b, r)).
    destruct b.
    simpl in H.
    simpl in P1'.
    rewrite P1'.
    apply H.
    split.
    rewrite Forall_forall in int.
    apply int.
    apply P1''.
    apply (real_le_le_le _ (snd (e, r))).
    apply real_eq_le;auto.
    apply (real_le_le_le _ (rad L)); auto.
    apply (rad_forall L (fst (e, r0), r)); auto.
    intros x Kx.
    assert (exists y, A y /\ euclidean_max_dist x y <= prec (S p)) as [y [yp1 yp2]].
    {
      destruct HD.
      destruct (H0 _ Kx).
      exists x0.
      rewrite euclidean_max_dist_sym.
      apply H1.
    } 
    specialize (cov _ yp1).
    rewrite Exists_exists in cov.
    destruct cov as [b' [bP' bP'']].
    rewrite Exists_exists.
    exists (fst b', prec p).
    specialize (P  (fst b', prec p)) as [_ P].
    split.
    apply P.
    simpl; split;auto.
    exists (snd b').
    destruct b';simpl;auto.
    unfold ball_to_subset.
    simpl.
    pose proof (euclidean_max_dist_tri x y (fst b')).
    apply (real_le_le_le _ _ _ H).
    rewrite <-prec_twice.
    replace (p+1)%nat with (S p) by lia.
    apply real_le_le_plus_le;auto.
    apply (real_le_le_le _ (snd b')).
    apply bP''.
    apply (real_le_le_le _ (rad L)); auto.
    apply rad_forall; auto.
  Defined.

End EuclideanLocated.

Section SubsetsR2.

Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.
#[local] Notation "^Real" := (@Real types) (at level 0).

  Definition make_ball2 (x y r : ^Real) : (ball (d:=n2)) := ((make_euclidean2 x y), r).

 Lemma split_ball_to_subset2 (b_x b_y r x y : ^Real) : 
    closed_ball_to_subset (Euclidean.cons b_x (Euclidean.cons b_y Euclidean.nil), r) (Euclidean.cons x (Euclidean.cons y Euclidean.nil)) -> 
    abs(x + - b_x) <= r /\
    abs(y + - b_y) <= r.
  Proof.
    intro HX.
    pose proof HX as HY.
    apply real_max_le_fst_le in HX.
    apply real_max_le_snd_le, real_max_le_fst_le in HY.
    split; auto. 
  Defined.  
End SubsetsR2.

 
