(* this file proves various properties of subsets of real numbers *)
Require Import Lia.
Require Import Real Euclidean List Minmax ClassicalSubsets Sierpinski testsearch.

Section GeneralSubsets.
Context (X : Type).
Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.
#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).

Definition open (A : (csubset X)) := forall x, {s : sierp | (sierp_up s)  <-> A x}. 

Definition overt (A : (csubset X)) := forall B, open B -> {k : ^K | (k = lazy_bool_true) <-> (@intersects X A B)}. 

Definition compact (A : (csubset X)) := forall B, open B -> {k : ^K | (k = lazy_bool_true) <-> (@is_subset X A B)}. 
End GeneralSubsets.


Section RealSubsets.

Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.

#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).
#[local] Definition sofReal := @sofReal types casofReal.
#[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).
#[local] Notation "^euclidean" := (@euclidean types) (at level 0).


  Add Ring realRing : (realTheory ).
  
  Context (d : nat).

 (* TODO: Move to appropriate place *)
  Axiom eventually_true :forall (c : forall (n :nat), sierp), {k | sierp_up k <-> exists n, sierp_up(c n)}.
  (* continuity principle for functions to Sierpisnki*)

  Definition euclidean_subset :=  csubset (^euclidean d).

  Definition ball := ((^euclidean d) * ^Real)%type.


  Definition ball_to_subset (b : ball)  : euclidean_subset := (fun x => (euclidean_max_dist x (fst b)) < (snd b)).  

  Lemma dyadic_ball_cover : {c : forall (z :Z) (p : nat), ball | forall x, exists z p, ball_to_subset (c z p) x}.
  Definition euclidean_open (M : euclidean_subset) := {c : nat -> ball | (forall n, is_subset (^euclidean d) (ball_to_subset (c n)) M) /\ forall x, M x -> exists n, (ball_to_subset (c n)) x}.

  Lemma contained_in_ball_semidec b x : {s : sierp | sierp_up s <-> (ball_to_subset b) x}.
  Proof.
    unfold ball_to_subset.
    destruct (real_lt_semidec (euclidean_max_dist x (fst b)) (snd b)) as [k P].
    exists (sierp_from_kleenean k).
    apply P.
  Defined.

  Lemma euclidean_open_is_open M : euclidean_open M -> open (^euclidean d) M.
  Proof.
    unfold open.
    intros OM x.
    destruct OM as [c P].
    pose ((fun n=> projP1 _ _ (contained_in_ball_semidec (c n) x)) : nat -> K).
    assert (forall n, (k n) = lazy_bool_true <-> (ball_to_subset (c n)) x).
    {
      intros.
      unfold k.
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
    destruct (eventually_true k) as [k' [H1 H2]].
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

  Lemma open_is_euclidean_open M : open (^euclidean d) M -> euclidean_open M. 
  Proof.
    
  (* is this still needed? *)
  Lemma open_open A x : is_open A -> (CRelationClasses.iffT (A x) (^M {r | r > real_0 /\ is_subset (ball_to_subset (x, r)) A})).
  Proof.
    intros.
    destruct X as [c [P1 P2]].
    split; intros.
    - assert (exists n, (projP1 _ _ (contained_in_ball_semidec (c n) x)) = lazy_bool_true) as C.
      destruct (P2 _ H).
      exists x0.
      destruct (contained_in_ball_semidec (c x0) x);simpl.
      apply i;auto.
    pose proof (multivalued_countable_choice _ C).
    revert X.
    apply M_lift.
    intros [n nprp].
    destruct (contained_in_ball_semidec (c n) x).
    simpl in nprp.
    exists ((snd (c n) - (euclidean_max_dist x (fst (c n)))) / real_2_neq_0).
    split;destruct i as [I _].
    apply real_half_gt_zero.
    apply real_gt_minus_gt_zero.
    apply (I nprp).
    intros p.
    unfold ball_to_subset;simpl; intros Hp.
    apply (P1 n).
    apply (real_le_lt_lt _ (euclidean_max_dist p x + euclidean_max_dist x (fst (c n)))).
    apply euclidean_max_dist_tri.
    apply (real_lt_add_r (- euclidean_max_dist x (fst (c n)))).
    ring_simplify.
    apply (real_le_lt_lt _ _ _ Hp).
    unfold real_minus.
    rewrite real_plus_comm.
    apply real_gt_half.
    rewrite real_plus_comm.
    apply real_gt_minus_gt_zero.
    apply I;auto.
  - apply M_hprop_elim;[intros p1 p2;apply irrl | ].
    revert X.
    apply M_lift.
    intros [r [rprp1 rprp2]].
    apply rprp2.
    unfold ball_to_subset;simpl.
    apply real_lt_le.
    apply (real_le_lt_lt _ real_0).
    apply real_eq_le.
    apply euclidean_max_dist_id;auto.
    exact rprp1.
  Defined.

  Definition union (A B : euclidean_subset) : euclidean_subset := fun x => A x \/ B x.
  Definition intersection (A B : euclidean_subset) : euclidean_subset:= fun x => A x /\ B x.

  Definition translation (A : euclidean_subset) (a : euclidean d ): euclidean_subset := fun x => A (euclidean_minus x a).
  Definition scaling (l : Real )(A : euclidean_subset) : euclidean_subset := fun x => exists y, x = (euclidean_scalar_mult l y) /\ A y.


  Definition empty_set : euclidean_subset := fun x => False.


  Definition open_ball_to_subset (b : ball)  : euclidean_subset := (fun x => (euclidean_max_dist x (fst b)) < (snd b)).  
  Definition rad (L : list ball) := (fold_right (fun b1 r => (real_max (snd b1) r)) real_0 L).

  Lemma ball_to_subset_scalar_mult s c1 r1 p1:
    s >= real_0 ->
    ball_to_subset (c1, r1) p1 ->
    ball_to_subset (euclidean_scalar_mult s c1, s * r1) (euclidean_scalar_mult s p1).
  Proof.
    unfold ball_to_subset; simpl.
    intros.
    rewrite euclidean_max_dist_scalar_mult.
    apply real_le_mult_pos_le; auto. auto.
  Qed.

  Lemma ball_to_subset_plus c1 r1 p1 c2 r2 p2 :
    ball_to_subset (c1, r1) p1 ->
    ball_to_subset (c2, r2) p2 ->
    ball_to_subset (euclidean_plus c1 c2, r1 + r2) (euclidean_plus p1 p2).
  Proof.
    unfold ball_to_subset; simpl.
    intros.
    apply (real_le_le_le _ (euclidean_max_dist p1 c1 + euclidean_max_dist p2 c2)).
    apply euclidean_max_dist_plus_le.
    apply real_le_le_plus_le; auto.
  Qed.

  Definition Hausdorff_dist_bound (S T : euclidean_subset) n :=
    (forall x, S x -> exists y, T y /\ euclidean_max_dist x y <= n) /\
      (forall y, T y -> exists x, S x /\ euclidean_max_dist x y <= n).

  Definition is_covert (M : euclidean_subset) := 
    forall n, {Ln : list ball |
                rad Ln <= prec n /\
                Forall (fun b => intersects (ball_to_subset b) M) Ln /\
                forall x,  M x ->  Exists (fun b => (ball_to_subset b) x) Ln
              }.
  Fixpoint change_rad (L : list ball) (p : nat) :=
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
  Qed.

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
  Qed.

  Lemma rad_forall L b : In b L -> snd b <= rad L.
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
  Qed.

  Lemma rad_le L r : r >= real_0 -> (forall b, In b L -> snd b <= r) <-> rad L <= r.
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
  Qed.

  Lemma rad_prec_spec L p : rad L <= prec p <-> forall b, In b L -> (snd b <= prec p).
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
    - apply rad_prec_spec.
      intros b inb.
      apply in_app_or in inb.
      destruct inb;[apply (rad_prec_spec L1 n) | apply (rad_prec_spec L2 n)];auto.
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
      left. auto.
   - exists x;auto.
  Qed.

  Lemma is_covert_scale_down M k : is_covert M -> is_covert (scaling (prec k) M).
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
    unfold ball_to_subset;simpl.
    replace x with (euclidean_scalar_mult (prec k) (euclidean_scalar_mult (Nreal (Npow2 k)) x)).
    rewrite euclidean_max_dist_scalar_mult; [|left;apply prec_pos].
    apply real_le_mult_pos_le;auto;left;apply prec_pos.
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
    unfold ball_to_subset;simpl.
    replace x with (euclidean_scalar_mult (Nreal (Npow2 k)) (euclidean_scalar_mult (prec k) x)).
    rewrite euclidean_max_dist_scalar_mult; [|left;apply Nreal_Npow2_pos].
    apply real_le_mult_pos_le;auto;left;apply Nreal_Npow2_pos.
    rewrite euclidean_scalar_mult_mult.
    rewrite real_mult_comm.
    rewrite prec_Npow2_unit.
    apply euclidean_scalar_mult_unit.
  Defined.

  Definition is_open' (M : euclidean_subset) := forall x, {k : K | k = lazy_bool_true <-> M x}.



  Definition open_ball_list_to_subset (L : list ball) : euclidean_subset := fun x => exists A, In A L /\ (open_ball_to_subset A) x.


  Fixpoint real_to_euclidean (x : ^Real ) (m : nat) (n : nat) :=
    match m with
      0 => Euclidean.nil
    | (S m') => if (m =? n) then 
                Euclidean.cons x (euclidean_zero m')
               else Euclidean.cons real_0 (real_to_euclidean x m' n)
    end.

  Definition double_open_ball (b : ball) n := (((euclidean_plus (fst b) (real_to_euclidean ((-snd b) / real_2_neq_0) d n)), snd b) :: b :: ((euclidean_plus (fst b) (real_to_euclidean ((-snd b) / real_2_neq_0) d n)), snd b) :: nil).
  
  Fixpoint euclidean_nth {m} n (x : euclidean (S m)) : Real :=
    match m with
      0 => (euclidean_head x)
    | (S m') =>
       match n with
         0 => (euclidean_head x)
        | (S n') => euclidean_nth n' (euclidean_tail x)
       end
     end.
  Lemma double_open_ball_spec b : forall x, open_ball_list_to_subset (double_open_ball b) x <-> 
  (* make copy of each element shifted in a certain direction *)
  Fixpoint make_copy (L : (list ball)) (n : nat) :=
    match L with
      nil => nil
    | (b :: L') => (b :: ((euclidean_plus (fst b) (real_to_euclidean (snd b) d n)), snd b) :: (make_copy L' n))
    end.

  Fixpoint make_copies (L : (list ball)) (n : nat) :=
    match n with
      0 => L
    | (S n') => make_copy (make_copies L n') n
   end.

  (* split ball into 2^d smaller balls *)
  Definition split_ball (b : ball) := scale_list (make_copies (b :: nil) d) (prec 1).

  (* Lemma split_ball_contains x b : ball_to_subset b x -> exists b', In b' (split_ball b) /\ ball_to_subset b' x. *)
  (* Proof. *)
  (*   intros. *)
  (* Lemma ball_refinement x b : ball_to_subset b x -> {b' | ball_to_subset b' x /\ (snd b') <= (snd b) / real_2_neq_0  }. *)
  (* Proof. *)
  (*   intros. *)
    
  Definition is_compact (M : euclidean_subset) := forall A, is_open A -> {k : K | k = lazy_bool_true <-> is_subset M A}.

  Definition is_overt (M : euclidean_subset) := forall A, is_open A -> {k : K | k = lazy_bool_true <-> exists x, (intersection M A) x}.

  Lemma is_open_union (M1 M2 : euclidean_subset) : is_open M1 -> is_open M2 -> is_open (union M1 M2).
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


    
  Lemma is_open_intersection (M1 M2 : euclidean_subset) : is_open M1 -> is_open M2 -> is_open (intersection M1 M2).
  Proof.
    intros H1 H2.
    destruct H1 as [c1 [P1 P2]].
    destruct H2 as [c2 [Q1 Q2]].
    unfold is_open, intersection.
    exists (lazy_bool_and k1 k2).
    split; intros.
    rewrite lazy_bool_and_up in H.
    split; [apply P1 | apply P2];apply H.
    rewrite lazy_bool_and_up.
    split; [apply P1 | apply P2]; apply H.
 Defined.

  Lemma union_subset A B C : is_subset (union A B) C <-> is_subset A C /\ is_subset B C.
  Proof.
    split; intros.
    split; intros x H';apply H; [left | right]; auto.
    intros x H'.
    destruct H.
    destruct H';[apply H | apply H0];auto.
  Qed.    

  Lemma is_compact_union M1 M2 : is_compact M1 -> is_compact M2 -> is_compact (union M1 M2).
  Proof.
    intros H1 H2 A Aopen.
    destruct (H1 A Aopen) as [k1 P1].
    destruct (H2 A Aopen) as [k2 P2].
    exists (lazy_bool_and k1 k2).
    split; intros.
    rewrite lazy_bool_and_up in H.
    intros x P.
    destruct P; [apply P1| apply P2];auto;apply H;auto.
    rewrite lazy_bool_and_up.
    rewrite union_subset in H.
    split;[apply P1 | apply P2];apply H.
  Defined.

  Lemma is_overt_union M1 M2 : is_overt M1 -> is_overt M2 -> is_overt (union M1 M2).
  Proof.
  unfold is_overt.
End Subsets.
Section Overt.

Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.
#[local] Notation "^Real" := (@Real types) (at level 0).

  Lemma in_ball_reduct d c0 c r x0 (x : euclidean d) :  ball_to_subset (S d) ((Euclidean.cons c0 c),r) (Euclidean.cons x0 x) <-> ball_to_subset d (c, r) x /\ dist x0 c0 <= r. 
  Proof.
    split; intros.
    unfold ball_to_subset in H.   
    simpl in H.
    rewrite euclidean_max_dist_cons in H.
    split.
    unfold ball_to_subset;simpl.
    apply (real_max_le_snd_le (dist x0 c0));auto.
    apply (real_max_le_fst_le _ (euclidean_max_dist x c));auto.
    unfold ball_to_subset.
    simpl.
    rewrite euclidean_max_dist_cons.
    apply real_max_le_le_le;apply H.
  Defined.
  Search (list _ -> list _ -> _).
  Lemma make_copy_monotone d L L' n: incl L L' -> incl (make_copy d L n) (make_copy d L' n).
  Proof.
   intros.
   induction L'.
   apply incl_l_nil in H.
   rewrite H.
   apply incl_nil_l.
   simpl.
  Defined.
  Lemma make_copies_monotone d a L b n: In b (make_copies d L n) -> In b (make_copies d (a :: L) n).
  Proof.
    destruct n.
    simpl.
    intros.
    right;auto.
    simpl.
    intros.
    induction L.
    apply make_copy_monotone.
    unfold make_copies.
    simpl.
    unfold make_copies.
    simpl.
  Lemma make_copies_contains d L (b : ball d)  : In b L -> forall x, euclidean_max_dist (fst b) x <= real_2 * (snd b) -> exists b', In b' (make_copies d L d) /\ ball_to_subset d b' x. 
  Proof.
    induction d.
    intros.
    exists b.
    simpl.
    split;auto.
    revert H0.
    rewrite (dim_zero_destruct x).
    rewrite (dim_zero_destruct (fst b)).
    unfold ball_to_subset, euclidean_max_dist.
    simpl.
    admit.
    intros.
    induction L.
    contradict H.
    destruct (in_inv H).
    admit.
    destruct (IHL H1).
    exists x0.
    destruct ()
    apply real_le_pos_mult
  
End Overt.
Section SubsetsR2.

Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.
#[local] Notation "^Real" := (@Real types) (at level 0).

  
  Definition make_ball2 (x y r : ^Real) : ball n2 := ((make_euclidean2 x y), r).
  
  Lemma split_ball_to_subset2 (b_x b_y r x y : ^Real) : 
    ball_to_subset n2 (Euclidean.cons b_x (Euclidean.cons b_y Euclidean.nil), r) (Euclidean.cons x (Euclidean.cons y Euclidean.nil)) -> 
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

 
