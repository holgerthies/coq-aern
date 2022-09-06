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

  Definition union (A B : euclidean_subset) : euclidean_subset := fun x => A x \/ B x.
  Definition intersection (A B : euclidean_subset) : euclidean_subset:= fun x => A x /\ B x.
  Definition intersects (A B : euclidean_subset) := exists x, intersection A B x.

  Definition translation (A : euclidean_subset) (a : euclidean d ): euclidean_subset := fun x => A (euclidean_minus x a).
  Definition scaling (l : Real )(A : euclidean_subset) : euclidean_subset := fun x => exists y, x = (euclidean_scalar_mult l y) /\ A y.

  Definition is_subset (A B : euclidean_subset) := forall x, A x -> B x.

  Definition empty_set : euclidean_subset := fun x => False.

  Definition ball := ((^euclidean d) * ^Real)%type.


  Definition ball_to_subset (b : ball)  : euclidean_subset := (fun x => (euclidean_max_dist x (fst b)) <= (snd b)).  

  Definition diam (L : list ball) := (fold_right (fun b1 r => (real_max (snd b1) r)) real_0 L).

  Definition Hausdorff_dist_bound (S T : euclidean_subset) n :=
    (forall x, S x -> exists y, T y /\ euclidean_max_dist x y <= n) /\
      (forall y, T y -> exists x, S x /\ euclidean_max_dist x y <= n).

  Definition is_covert (M : euclidean_subset) := 
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

  Lemma diam_prec_spec L p : diam L <= prec p <-> forall b, In b L -> (snd b <= prec p).
  Proof.
    split.
    intros.
    apply (real_le_le_le _ (diam L));auto.
    apply diam_forall;auto.
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
  Qed.
  Lemma is_covert_lim :
    forall K : euclidean_subset,
      (forall n : nat, {X :  euclidean_subset & prod (is_covert X) (Hausdorff_dist_bound X K (prec n))})
      -> is_covert K.
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
  Lemma intersects_union A B b: intersects b (union A B) <-> intersects b A \/ intersects b B. 
  Proof.
    split; intros.
    destruct H.
    destruct H.
    destruct H0; [left | right]; exists x; split;auto.
    destruct H;destruct H;exists x;split; [|left| | right];apply H.
  Qed.

  Lemma is_covert_union K1 K2 : is_covert K1 -> is_covert K2 -> is_covert (union K1 K2).
  Proof.
    intros H1 H2 n.
    destruct (H1 n) as [L1 [D1 [int1 cov1]]].
    destruct (H2 n) as [L2 [D2 [int2 cov2]]].
    exists (L1 ++ L2).
    split; [| split].
    - apply diam_prec_spec.
      intros b inb.
      apply in_app_or in inb.
      destruct inb;[apply (diam_prec_spec L1 n) | apply (diam_prec_spec L2 n)];auto.
  - apply Forall_app.
    rewrite Forall_forall in int1.
    rewrite Forall_forall in int2.
    assert (forall b, intersects (ball_to_subset b) K1 \/ intersects (ball_to_subset b) K2 -> intersects (ball_to_subset b) (union K1 K2)) by (intros; apply intersects_union;auto).
    split;apply (Forall_impl _ H);apply Forall_forall;intros b inb; [left;apply int1 | right;apply int2];auto.
 - intros x cx.
   apply Exists_app.
   destruct cx; [left;apply cov1 | right;apply cov2];auto.
  Defined.


  Lemma is_covert_translation K a : is_covert K -> is_covert (translation K a).
  Proof.
    intros H n.
    destruct (H n) as [L [D [int cov]]].
    exists (map (fun (b : ball) => ((euclidean_plus (fst b) a),(snd b))) L).
    split; [|split].
    - apply diam_prec_spec.
      intros b inb.
      apply in_map_iff in inb.
      destruct inb as [x [Hx Hx']].
      destruct b.
      simpl.
      injection Hx.
      intros <- _.
      apply (real_le_le_le _ (diam L));auto.
      apply diam_forall;auto.
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
     unfold ball_to_subset.
     unfold ball_to_subset in xp1.
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
   unfold ball_to_subset.
   rewrite euclidean_max_dist_sym.
   simpl.
   rewrite <-euclidean_max_dist_minus_plus.
   rewrite euclidean_max_dist_sym.
   apply P.
  Defined.

  Fixpoint scale_list (L : list ball) l := match L with
                               nil => nil
                             | b :: L' => (euclidean_scalar_mult l (fst b), l * (snd b)) :: scale_list L' l
                            end.


  Lemma scale_diam L l: (real_0 < l) -> diam (scale_list L l) = l * diam L.
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
  Qed.

  Lemma real_inv_neq0 (x : Real) (xneq0 : x <> real_0) : (/ xneq0) <> real_0.
  Proof.
     intros H.
     apply (real_eq_mult_eq_r x) in H.
     rewrite real_mult_inv in H.
     ring_simplify in H.
     apply real_1_neq_0.
     apply H.
  Qed.
     
  Lemma real_le_mult_pos_cancel z z1 z2 : z > real_0 -> z1*z <= z2*z ->  z1 <= z2.
  Proof.
    intros.
    destruct H0.
    apply real_lt_le.
    apply (real_lt_mult_pos_cancel z);auto.
    apply real_eq_le.
    apply (real_eq_mult_cancel z);auto.
    apply real_gt_neq;auto.
  Qed.

  Lemma scale_intersects M L l  : (real_0 < l) -> Forall (fun b : ball => intersects (ball_to_subset b) M) L -> Forall (fun b : ball => intersects (ball_to_subset b) (scaling l M)) (scale_list L l).
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
   - exists x;auto.
  Qed.


  Lemma is_covert_scale_down M k : is_covert M -> is_covert (scaling (prec k) M).
  Proof.
    intros Mc n.
    destruct (Mc (n-k)%nat) as [L [Lp1 [Lp2 Lp3]]].
    exists (scale_list L (prec k)).
    split; [|split].
    - rewrite scale_diam; [|apply prec_pos].
      apply (real_le_le_le _ ((prec k) * prec (n - k))).
      apply real_le_mult_pos_le; [apply prec_pos | auto].
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
    unfold ball_to_subset;simpl.
    replace x with (euclidean_scalar_mult (prec k) (euclidean_scalar_mult (Nreal (Npow2 k)) x)).
    rewrite euclidean_max_dist_scalar_mult; [|apply prec_pos].
    apply real_le_mult_pos_le;auto;apply prec_pos.
    rewrite euclidean_scalar_mult_mult.
    rewrite prec_Npow2_unit.
    apply euclidean_scalar_mult_unit.
 Defined.


  Lemma is_covert_scale_up M k : is_covert M -> is_covert (scaling (Nreal (Npow2 k)) M).
  Proof.
    intros Mc n.
    destruct (Mc (n+k)%nat) as [L [Lp1 [Lp2 Lp3]]].
    exists (scale_list L (Nreal (Npow2 k))).
    split; [|split].
    - rewrite scale_diam; [|apply Nreal_Npow2_pos].
      apply (real_le_le_le _ (Nreal (Npow2 k) * prec (n + k))).
      apply real_le_mult_pos_le; [apply Nreal_Npow2_pos | auto].
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
    unfold ball_to_subset;simpl.
    replace x with (euclidean_scalar_mult (Nreal (Npow2 k)) (euclidean_scalar_mult (prec k) x)).
    rewrite euclidean_max_dist_scalar_mult; [|apply Nreal_Npow2_pos].
    apply real_le_mult_pos_le;auto;apply Nreal_Npow2_pos.
    rewrite euclidean_scalar_mult_mult.
    rewrite real_mult_comm.
    rewrite prec_Npow2_unit.
    apply euclidean_scalar_mult_unit.
Defined.
End Subsets.

Section SubsetsR2.

Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.
#[local] Notation "^Real" := (@Real types) (at level 0).

  Definition make_ball2 (x y r : ^Real) : ball 2 := ((make_euclidean2 x y), r).
  
  Lemma split_ball_to_subset2 (b_x b_y r x y : ^Real) : 
    ball_to_subset 2 (Euclidean.cons b_x (Euclidean.cons b_y Euclidean.nil), r) (Euclidean.cons x (Euclidean.cons y Euclidean.nil)) -> 
    abs(x + - b_x) <= r /\
    abs(y + - b_y) <= r.
  Proof.
    intro HX.
    pose proof HX as HY.
    apply real_max_le_fst_le in HX.
    apply real_max_le_snd_le, real_max_le_fst_le in HY.
    split; auto. 
  Qed.  
End SubsetsR2.

 
