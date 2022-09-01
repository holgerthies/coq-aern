(* this file proves various properties of subsets of real numbers *)
Require Import Lia.
Require Import Real Euclidean List Minmax.
Section Subsets.

Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).
#[local] Definition sofReal := @sofReal types casofReal.
#[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).
#[local] Notation "^euclidean" := (@euclidean types) (at level 0).

  Add Ring realRing : (realTheory ).
  
  Context (d : nat).

  Definition euclidean_subset :=  (^euclidean d) -> Prop.

  Definition union (A B : euclidean_subset) := fun x => A x \/ B x.
  Definition intersection (A B : euclidean_subset) := fun x => A x /\ B x.
  Definition intersects (A B : euclidean_subset) := exists x, intersection A B x.
  Definition is_subset (A B : euclidean_subset) := forall x, A x -> B x.

  Definition empty_set : euclidean_subset := fun x => False.

  Definition ball := ((^euclidean d) * ^Real)%type.


  Definition ball_to_subset (b : ball)  : euclidean_subset := (fun x => (euclidean_max_dist x (fst b)) <= (snd b)).  

  Definition diam (L : list ball) := (fold_right (fun b1 r => (real_max (snd b1) r)) real_0 L).

  Definition Hausdorff_dist_bound (S T : euclidean_subset) n :=
    (forall x, S x -> exists y, T y /\ euclidean_max_dist x y <= n) /\
      (forall y, T y -> exists x, S x /\ euclidean_max_dist x y <= n).

  Definition is_compact (M : euclidean_subset) := 
    forall n, {Ln : list ball |
                diam Ln <= prec n /\
                Forall (fun b => intersects (ball_to_subset b) M) Ln /\
                forall x,  M x ->  Exists (fun b => (ball_to_subset b) x) Ln
              }.
  Fixpoint change_diam (L : list ball) (p : nat) :=
    match L with
     | nil => nil
    | a :: L' => (fst a, prec p) :: change_diam L' p
   end.

  (* Lemma change_diam_prop (L : list ball) (p : nat) : {L' : list ball | (forall b, In b L -> (In ((fst b), prec p) L')) /\ (forall b, In b L' -> (exists r, In ((fst b), r) L) /\ (snd b = prec p))}. *)
  (* Proof. *)
  (*   induction L. *)
  (*   - exists nil. *)
  (*     simpl. *)
  (*     split; intros;auto. *)
  (*     contradict H. *)
  (*   - destruct IHL. *)
  (*     exists ((fst a, prec p) :: x). *)
  (*     intros. *)
  (*     simpl. *)
  (*     split. *)
  (*     + intros. *)
  (*       destruct H. *)
  (*       left. *)
  (*       f_equal. *)
  (*       f_equal. *)
  (*       apply H. *)
  (*       right. *)
  (*       apply a0. *)
  (*       apply H. *)
  (*    + intros [c r]. *)
  (*      split. *)
  (*      destruct H. *)
  (*      exists (snd a). *)
  (*      apply pair_equal_spec in H. *)
  (*      left. *)
  (*      simpl. *)
  (*      rewrite (surjective_pairing a). *)
  (*      f_equal. *)
  (*      apply H. *)
  (*      destruct a0. *)
  (*      destruct (H1 _ H). *)
  (*      destruct H2. *)
  (*      exists x0. *)
  (*      right. *)
  (*      apply H2. *)
  (*      destruct H. *)
  (*      simpl. *)
  (*      apply pair_equal_spec in H. *)
  (*      destruct H; auto. *)
  (*      destruct a0. *)
  (*      apply H1. *)
  (*      apply H. *)
  (* Defined. *)

  (* Definition change_diam  (L : list ball) (p : nat) : list ball. *)
  (* Proof. *)
  (*   destruct (change_diam_prop L p). *)
  (*   apply x. *)
  (* Defined. *)

  Lemma change_diam_prop L p: diam (change_diam L p) <= prec p /\ (forall b, In b L -> (In ((fst b), prec p) (change_diam L p))) /\ (forall b, In b  (change_diam L p) -> (exists r, In ((fst b), r) L)).
  Proof.
    induction L as [ | b L' [D [L R]]].
    simpl.
    split; [ | split]; intros;auto.
    apply real_lt_le.
    apply prec_pos.
    contradict H.

    split; [| split].
    - simpl.
      apply real_max_le_le_le.
      apply real_eq_le; auto.
      apply D.
   - intros.
     destruct H.
     left.
     f_equal.
     f_equal.
     exact H.
     right.
     apply L.
     exact H.
  - intros [c r].
    simpl.
    intros H.
    destruct H.
    exists (snd b).
    apply pair_equal_spec in H.
    left.
    rewrite (surjective_pairing b).
    f_equal.
    apply H.
    destruct (R _ H).
    exists x.
    right.
    apply H0.
  Qed.
  Lemma change_diam_spec L p : forall b, In b (change_diam L p) <-> snd b = prec p /\ exists r, In (fst b, r) L.
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
  Qed.

  Lemma change_diam_diam L p: diam (change_diam L p) <= prec p.
  Proof.
    induction L as [ | b L' IH].
    simpl.
    apply real_lt_le.
    apply prec_pos.
    simpl.
    apply real_max_le_le_le.
    apply real_eq_le; auto.
    apply IH.
  Qed.

  Lemma diam_forall L b : In b L -> snd b <= diam L.
  Proof.
    induction L.
    simpl;intros; contradict H.
    simpl.
    intros.
    destruct H.
    rewrite H.
    apply real_ge_le.
    apply real_max_fst_ge.
    apply (real_le_le_le _ (diam L)).
    apply IHL; auto.
    apply real_ge_le.
    apply real_max_snd_ge.
  Qed.

  Lemma is_compact_lim :
    forall K : euclidean_subset,
      (forall n : nat, {X :  euclidean_subset & prod (is_compact X) (Hausdorff_dist_bound X K (prec n))})
      -> is_compact K.
  Proof.
    intros.
    intro p.
    destruct (X (S p)) as [A [CA HD]].
    destruct (CA (S p)) as [L [dL [int cov]]].
    exists (change_diam L p).
    pose proof (change_diam_spec L p) as P.
    split.
    apply change_diam_diam.
    split.
    apply Forall_forall.
    intros b inb.
    pose proof (P b) as [P1 P2].
    specialize (P1 inb) as [P1' P1''].
    destruct P1'' as [r P1''].
    assert (forall b', (intersects (ball_to_subset b') A /\ snd b' <= prec (S p)) -> intersects (ball_to_subset ((fst b', prec p))) K).
    {
      intros b' [H1 H2].
      destruct H1 as [y [yp1 yp2]].
      destruct HD as [HD1 _].
      destruct (HD1 _ yp2) as [y' [y'p1 y'p2]].
      exists y'.
      split;auto.
      unfold ball_to_subset;simpl.
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
    apply (real_le_le_le _ (diam L)); auto.
    apply (diam_forall L (fst (e, r0), r)); auto.
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
    apply (real_le_le_le _ (diam L)); auto.
    apply diam_forall; auto.
  Defined.
End Subsets.

 
