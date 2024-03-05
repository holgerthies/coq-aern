Require Import Real.
Require Import ClassicalMonads.
Require Import Minmax.
Require Import Subsets.


Require Import RealAssumption.
Require Import ClassicalPartiality.
Require Import ClassicalPartialReals.
Require Import ClassicalContinuity.
Require Import ClassicalContinuousPartialRealFunctions.

(* Structure cinterval := { *)
(*     u : ^Real ; *)
(*     b : ^Real ; *)
(*     b_below_u : b <= u *)
(*   }. *)

(* Definition cinterval_in x i := b i <= x /\ x <= u i. *)

(* (* Definition pc_fun_at_cinterval f i : *) *)


(* Definition cinterval_as_csubset i  := fun x => cinterval_in x i. *)



Definition W_is_upper_unbounded (P : Real -> Prop) := forall x, exists x', P x' /\ x < x'.



Lemma W_is_not_bounded_above_is_upper_unbounded P :
  ~ W_is_bounded_above P -> W_is_upper_unbounded P.
Proof.
  intros.
  unfold W_is_bounded_above in H.
  intro.
  destruct (lem ( exists x' : ^Real, P x' /\ x < x')); auto.
  assert (forall x', ~ P x' \/ x' <= x).
  intro.
  destruct (lem (P x')); auto.
  right.
  destruct (lem (x' <= x)); auto.
  
  contradict H0.
  exists x'; auto.
  split; auto.
  apply real_nle_ge in H2.
  auto.
  contradict H.
  exists x.
  intro.
  intro.
  pose proof (H1 z).
  destruct H2.
  contradict H2; auto.
  auto.
Defined.

Lemma le_sandwich a b : a <= b <= a -> a = b.
Proof.
  intros.
  destruct H. 
  destruct H; auto.
  destruct H0; auto.
  contradict H; apply real_lt_nlt; auto.
Defined.

Lemma ge_rhs_plus_2_ge a b : a <= b -> a <= b + (real_1 + real_1).
Proof.
  intros.
  assert (real_0 < real_1 + real_1).
  pose proof (real_lt_lt_plus_lt _ _ _ _ real_1_gt_0 real_1_gt_0).
  replace (real_0 + real_0) with real_0 in H0 by ring.
  exact H0.
  destruct H.
  left.
  
  pose proof (real_lt_lt_plus_lt _ _ _ _ H H0).
  replace (a + real_0) with a in H1 by ring.
  exact H1.

  induction H.
  left.
  apply (real_lt_plus_lt a) in H0.
  replace (a + real_0) with a in H0 by ring.
  exact H0.
Defined.  

Lemma le_dist_le_add_le a b c d : a <= b -> dist a c <= d -> c <= b + d.
Proof.
  intros.
  destruct (lem (a < c)).
  rewrite (lt_metric _ _ H1) in H0.
  pose proof (real_le_le_plus_le _ _ _ _ H H0).
  replace (a + (c - a) ) with c in H2 by ring.
  exact H2.
  
  apply real_nge_le in H1.
  rewrite dist_symm in H0.
  rewrite (le_metric _ _ H1) in H0.
  assert (j : c <= a) by auto.
  apply (real_le_plus_le c) in H0.
  replace (c + (a - c)) with a in H0 by ring.
  apply (real_le_plus_le d) in H1.
  replace (d + c) with (c + d) in H1 by ring.
  pose proof (real_le_le_le _ _ _ H0 H1).
  pose proof (real_le_le_plus_le _ _ _ _ H H2).
  
  apply (real_le_plus_le (-a)) in H3.
  replace (- a + (a + a)) with a in H3 by ring.
  replace (- a + (b + (d + a))) with (b + d) in H3 by ring.
  exact (real_le_le_le _ _ _ j H3). 
Defined.

Lemma add_pos_rhs_gt {a b} : real_0 < b -> a < a + b.
Proof.
  intro.
  apply (real_lt_plus_lt a) in H.
  replace (a + real_0) with a in H by ring.
  exact H.
Defined.

Lemma dist_from_l_le a b c d : a <= b <= c -> dist a c <= d -> dist a b <= d.
Proof.
  intros.
  destruct H.
  rewrite (le_metric _ _ H).
  rewrite (le_metric _ _ (real_le_le_le _ _ _ H H1)) in H0.
  pose proof (real_le_le_plus_le _ _ _ _ H1 H0).
  apply (real_le_plus_le (-c)) in H2.
  replace (- c + (b + (c - a))) with (b -a ) in H2 by ring.
  replace (-c + (c + d)) with d in H2 by ring.
  exact H2.
Defined.

Lemma refine_interval {a b c d} : a <= b <= c -> a <= d <= c -> a <= b <= d \/ d <= b <= c.
Proof.
  intros.
  destruct (lem (b <d )).
  left.
  destruct H.
  split; auto; left; auto.
  apply real_nge_le in H1.
  destruct H.
  right.
  split; auto.
Defined.

Lemma dist_in_interval {a b c d} : a <= b <= c -> a <= d <= c -> dist b d <= dist b a \/ dist b d <= dist b c.
Proof.
  intros.
  destruct H, H0.
  rewrite (dist_symm b a).
  rewrite (le_metric _ _ H).
  rewrite (le_metric _ _ H1).
  destruct (lem (b < d)).
  assert (b <= d).
  left; auto.
  clear H3.
  
  rewrite (le_metric _ _ H4).
  right.
  apply (real_le_plus_le (-b)) in H2.
  replace (-b + d) with (d - b) in H2 by ring.
  replace (-b + c) with (c - b) in H2 by ring.
  exact H2.
  apply real_nge_le in H3.
  left.
  rewrite (dist_symm).
  rewrite (le_metric _ _ H3).
  apply (real_le_plus_le (-a-d+b)) in H0.
  replace (- a - d + b + a) with (b - d) in H0 by ring.
  replace (-a -d +b +d) with (b - a) in H0 by ring.
  exact H0.
Defined.  

Lemma not_in_above_is_upper_bound P x :
  (forall y, x <= y -> ~ P y) -> W_is_upper_bound P x.
Proof.
  intros.
  intro.
  intro.
  destruct (lem (z <= x)); auto.
  apply real_nle_ge in H1.
  assert (x <= z).
  left; auto.
  pose proof (H _ H2).
  contradict H3; auto.
Defined.

Lemma pc_cont_fun_on_closed_interval_is_bounded_above :
  forall (f : ^Real -> pc ^Real) l u,
    l <= u ->
    (forall x, l <= x <= u -> cont_at f x) ->
    W_is_bounded_above (fun y => exists x, l <= x <= u /\ defined_to (f x) y).
Proof.
  intros.
  destruct H.
  (* when l < u *)
  {
    assert (forall x, l <= x <= u -> defined (f x)) as f_is_total.
    intros.
    destruct (H0 x H1); auto.
    pose (B := fun p => l <= p <= u /\ W_is_bounded_above (fun y => exists x, l <= x <= p /\ defined_to (f x) y)).
    assert (B l) as Bl.
    assert (l <= l <= u) as ord.
    split; [right | left ]; auto.
    split.
    auto.
    destruct (f_is_total _ ord) as [fl h].
    exists fl.
    intro.
    intro.
    destruct H1.
    destruct H1.
    apply le_sandwich in H1.
    induction H1.
    rewrite H2 in h.
    apply pc_unit_mono in h.
    right; auto.
    assert (B_is_non_empty : W_is_non_empty B) by (exists l; auto).
    assert (u_is_B_upper_bound : W_is_upper_bound B u).
    intro.
    intro.
    destruct H1.
    destruct H1; auto.
    assert (B_is_bounded_above : W_is_bounded_above B) by (exists u; auto).
    
    pose proof (W_complete B B_is_non_empty B_is_bounded_above) as [s h].

    (* prove the sup s is nontrivially larger than l *)
    assert (l < s) as lgts.
    {
      assert (l <= l <= u) as l_ord.
      split; auto.
      right; auto.
      destruct (f_is_total l l_ord) as [fl lfl].
      destruct (H0 l l_ord) as [_ p].
      pose proof (p real_1 real_1_gt_0) as [del [del_pos q]].
      pose (u' := real_min u (l + del)).
      assert (l <= u' <= u) as u'interval.
      split.
      destruct (real_min_cand u (l + del)).
      unfold u'; rewrite H1.
      auto.
      unfold u'; rewrite H1.
      left.
      pose proof (real_lt_plus_r_lt l _ _ del_pos).
      rewrite real_plus_comm.
      replace (real_0 + l) with l in H2 by ring.
      auto.
      unfold u'.
      apply real_min_fst_le.

      assert (l < u') as sltu'.
      unfold u'.
      destruct (real_min_cand u (l + del)); rewrite H1; auto.
      apply add_pos_rhs_gt.
      auto.
      assert (B u').
      split.
      auto.
      exists (fl + real_1).
      intros fx [x [x_ord xfx]].
      assert (metric l x <= del).
      assert (metric l u' <= del).
      unfold metric; simpl.
      destruct u'interval.
      rewrite (le_metric _ _ H1).
      unfold u'.
      pose proof (real_min_snd_le u (l + del)).
      apply (real_le_plus_le (-l)) in H3.
      replace (- l + real_min u (l + del)) with ( real_min u (l + del) - l) in H3 by ring.
      replace (- l + (l + del)) with del in H3 by ring.
      auto.
      exact (dist_from_l_le _ _ _ _ x_ord H1).
      pose proof (q x fl fx H1 lfl xfx).
      assert (fl <= fl) by (right; auto).
      pose proof (le_dist_le_add_le _ _ _ _ H3 H2).
      auto.
      destruct h.
      pose proof (H2 _ H1).
      exact (real_lt_le_lt _ _ _ sltu' H4).
    }

    
    assert (s = u) as sequ.
    +
      destruct h.
      pose proof (H2 _ u_is_B_upper_bound) as s_le_u.
      destruct s_le_u; auto.
      assert (l <= s <= u).
      split.
      pose proof (H1 l Bl); auto.
      auto.
      destruct (H0 _ H4) as [_ p].
      pose proof (p _ real_1_gt_0) as [del q].

      pose (l' := real_max l (s - del)).
      assert (B l') as Bl'.
      {
        destruct (lem (B l')); auto.
        assert (W_is_upper_bound B l').
        apply not_in_above_is_upper_bound.
        intros.
        intro.
        contradict H5.
        split.
        split.
        exact (real_max_fst_ge l (s - del)).
        destruct H7.
        destruct H5.
        exact (real_le_le_le _ _ _ H6 H8).
        destruct H7.
        destruct H7.
        exists x.
        intro fz.
        intros [z [z_ord zfz]].
        assert (l <= z <= y).
        split.
        destruct z_ord; auto.
        destruct z_ord.
        exact (real_le_le_le _ _ _ H9 H6).
        exact (H7 fz (ex_intro _ z (conj H8 zfz))).
        pose proof (H2 l' H6).
        destruct (real_max_cand l (s - del));
          unfold l' in H7;
          rewrite H8 in H7.
        pose proof (real_gt_nle _ _ lgts).
        contradict (H9 H7).
        apply (real_le_plus_le (-s +del)) in H7.
        replace (- s + del + s ) with del in H7 by ring.
        replace (- s + del + (s - del)) with real_0 in H7 by ring.
        destruct q.
        pose proof (real_gt_nle _ _ H9).
        contradict (H11 H7).
      }
      

      pose (u' := real_min u (s + del)).
      assert (l <= u' <= u) as u'interval.
      split.
      destruct (real_min_cand u (s + del)).
      unfold u'; rewrite H5.
      auto.
      unfold u'; rewrite H5.
      destruct q.
      left.
      destruct H4.
      pose proof (real_le_lt_plus_lt _ _ _ _ H4 H6).
      replace (l + real_0) with l in H9 by ring.
      auto.
      unfold u'.
      apply real_min_fst_le.

      assert (s < u') as sltu'.
      unfold u'.
      destruct (real_min_cand u (s + del)); rewrite H5; auto.
      destruct q.
      pose proof (real_lt_plus_r_lt s _ _ H6).
      replace (real_0 + s) with s in H8 by ring.
      replace (del + s) with (s + del) in H8 by ring.
      auto.
      
      assert (metric s u' <= del) as u'dist.
      unfold metric; simpl.
      rewrite (lt_metric _ _ sltu').
      
      unfold u'.
      pose proof (real_min_snd_le u (s + del)).
      Search (_ + _ <= _ + _).
      pose proof (real_le_plus_le (- s) _ _ H5).
      replace (- s + real_min u (s + del) ) with (real_min u (s + del) - s ) in H6 by ring.
      replace (- s + (s + del)) with del in H6 by ring.
      auto.

      assert (B u').
      split; auto.

      destruct (Bl') as [l'_ord [l'upb l'upb_spec]].
      exists (l'upb + (real_1 + real_1)).
      intros fx [x [x_ord xfx]].
      assert (l <= l' <= u') as l'leu'.
      destruct l'_ord, u'interval.
      split; auto.
      assert (l' <= s).
      destruct (real_max_cand l (s - del)).
      unfold l'; rewrite H9.
      auto.
      unfold l'; rewrite H9.
      destruct q.
      left.
      apply (real_lt_plus_lt (s -del)) in H10.
      replace (s - del + real_0) with (s - del) in H10 by ring.
      replace (s - del + del) with s in H10 by ring.
      exact H10.
      left.
      apply (real_le_lt_lt _ _ _ H9 sltu').

      (* cases *)
      destruct (refine_interval x_ord l'leu') as [x_ord' | x_ord'].
      (* destruct (lem (l <= x <= l')) as [x_ord' | x_ord']. *)
      unfold W_is_upper_bound in   l'upb_spec.
      pose proof (  l'upb_spec fx (ex_intro _ x (conj x_ord' xfx))).
      apply ge_rhs_plus_2_ge.
      auto.
      assert (l' <= s <= u') as j.
      split; auto.
      left; auto.

      assert (metric s l' <= del) as dist_s_l'.
      unfold metric; simpl.
      destruct j.
      pose proof (le_metric _ _ H5).
      rewrite dist_symm.
      rewrite H7.
      pose proof (real_max_snd_ge l (s - del)).
      unfold l'.
      apply (real_le_plus_le (del - real_max l (s - del))) in H8.
      replace (del - real_max l (s - del) + (s - del)) with (s - real_max l (s - del)) in H8 by ring.
      replace (del - real_max l (s - del) + real_max l (s - del)) with del in H8 by ring.
      exact H8.

      assert (metric s u' <= del) as dist_s_u'.
      unfold metric; simpl.
      destruct j.
      pose proof (le_metric _ _ H6).
      rewrite H7.
      pose proof (real_min_snd_le u (s + del)).
      unfold u'.
      apply (real_le_plus_le (-s)) in H8.
      replace (- s + real_min u (s + del)) with (real_min u (s + del) - s) in H8 by ring.
      replace (- s + (s + del)) with del in H8 by ring.
      exact H8.
      
      assert (metric s x <= del) as dist_s_x.
      destruct (dist_in_interval j x_ord').
      unfold metric in dist_s_l'; simpl in dist_s_l'.
      unfold metric; simpl.
      exact (real_le_le_le _ _ _ H5 dist_s_l').
      unfold metric in dist_s_u'; simpl in dist_s_u'.
      unfold metric; simpl.
      exact (real_le_le_le _ _ _ H5 dist_s_u').
 
      destruct (f_is_total l' l'_ord) as [fl' l'fl'].
      assert (l <= l' <= l') as l'_ord_temp.
      split.
      destruct l'_ord; auto.
      right; auto.
      pose proof (l'upb_spec fl' (ex_intro _ l' (conj l'_ord_temp l'fl'))). 
      destruct q as [q1 q2].
      destruct (f_is_total s H4) as [fs sfs].

      pose proof (q2 l' fs fl' dist_s_l' sfs l'fl').
      pose proof (q2 x fs fx dist_s_x sfs xfx).
      unfold metric in H6, H7.
      simpl in H6, H7.
      pose proof (dist_tri fl' fs fx).
      pose proof (real_le_le_plus_le _ _ _ _ H6 H7).
      
      rewrite (dist_symm fl' fs) in H8. 
      pose proof (real_le_le_le _ _ _ H8 H9).
      pose proof (le_dist_le_add_le _ _ _ _ H5 H10).
      exact H11.
      pose proof (H1 _ H5).
      contradict H6.
      apply real_gt_nle.
      auto.

    +
      destruct sequ.
      (* now prove B s holds *)
      assert (B s).
      split.
      split; auto.
      right; auto.
      {
        assert (l <= s <= s).
        split; auto.
        right; auto.
        destruct (H0 _ H1) as [[fs sfs] q].
        pose proof (q real_1 real_1_gt_0) as [del [del_pos qq]].
        clear q.
        pose (l' := real_max l (s - del)).
        assert (B l') as Bl'.
        {
          destruct (lem (B l')); auto.
          assert (W_is_upper_bound B l').
          apply not_in_above_is_upper_bound.
          intros.
          intro.
          contradict H2.
          split.
          split.
          exact (real_max_fst_ge l (s - del)).
          destruct H4.
          destruct H2.
          exact (real_le_le_le _ _ _ H3 H5).
          destruct H4.
          destruct H4.
          exists x.
          intro fz.
          intros [z [z_ord zfz]].
          assert (l <= z <= y).
          split.
          destruct z_ord; auto.
          destruct z_ord.
          exact (real_le_le_le _ _ _ H6 H3).
          exact (H4 fz (ex_intro _ z (conj H5 zfz))).
          destruct h.
          pose proof (H5 l' H3).
          destruct (real_max_cand l (s - del)).
          unfold l' in H6.
          rewrite H7 in H6.
          pose proof (real_gt_nle _ _ lgts).
          contradict (H8 H6).
          unfold l' in H6.
          rewrite H7 in H6.
          
          apply (real_le_plus_le (-s +del)) in H6.
          replace (- s + del + s ) with del in H6 by ring.
          replace (- s + del + (s - del)) with real_0 in H6 by ring.
          
          pose proof (real_gt_nle _ _ del_pos).
          contradict (H8 H6).
        }

        destruct Bl'.
        destruct H3.
        exists (x + (real_1 + real_1)).
        intros fz [z [z_ord zfz]].
        destruct (refine_interval z_ord H2) as [z_ord' | z_ord'].
        (* destruct (lem (l <= x <= l')) as [x_ord' | x_ord']. *)
        unfold W_is_upper_bound in H3.
        pose proof (H3 fz (ex_intro _ z (conj z_ord' zfz))).
        apply ge_rhs_plus_2_ge.
        auto.

        assert (metric s l' <= del) as dist_s_l'.
        {
          unfold metric; simpl.
          destruct H2.
          pose proof (le_metric _ _ H4).
          rewrite dist_symm.
          rewrite H5.
          pose proof (real_max_snd_ge l (s - del)).
          unfold l'.
          apply (real_le_plus_le (del - real_max l (s - del))) in H6.
          replace (del - real_max l (s - del) + (s - del)) with (s - real_max l (s - del)) in H6 by ring.
          replace (del - real_max l (s - del) + real_max l (s - del)) with del in H6 by ring.
          exact H6.
        }

        assert (metric s z <= del) as dist_s_z.
        {
          unfold metric; simpl.
          destruct z_ord'.
          pose proof (le_metric _ _ H5).
          rewrite dist_symm.
          rewrite H6.
          apply (real_le_plus_le (-z - l' + s)) in H4.
          replace (- z - l' + s + l') with (s - z) in H4 by ring.
          replace ( - z - l' + s + z) with (s - l') in H4 by ring.
          assert (s - l' <= del).
          destruct H2.
          pose proof (le_metric _ _ H7).
          unfold metric in dist_s_l'; simpl in dist_s_l'.
          rewrite dist_symm in H8.
          rewrite H8 in dist_s_l'.
          auto.
          exact (real_le_le_le _ _ _ H4 H7).
        }

        pose proof (qq z fs fz dist_s_z sfs zfz).

        pose proof (f_is_total l' H2) as [fl' l'fl'].
        assert (l <= l' <= l').
        split; auto.
        destruct H2; auto.
        right; auto.
        pose proof (H3 fl' (ex_intro _ l' (conj H5 l'fl'))).

        pose proof (qq l' fs fl' dist_s_l' sfs l'fl').

        unfold metric in H4, H7.
        simpl in H4, H7.
        pose proof (dist_tri fl' fs fz).
        pose proof (real_le_le_plus_le _ _ _ _ H7 H4).
        
        rewrite (dist_symm fl' fs) in H8. 
        pose proof (real_le_le_le _ _ _ H8 H9).
        pose proof (le_dist_le_add_le _ _ _ _ H6 H10).
        exact H11.


      }

      
      

      
      unfold B in H1.
      destruct H1.
      exact H2.
  }

  {
    (* easy case when l = u *)
    induction H.
    assert (l <= l <= l) by (split; right; auto).
    destruct (H0 _ H) as [[fx xfx] _].
    exists fx.
    intros fy [y [y_ord yfy]].
    induction (le_sandwich _ _ y_ord).
    rewrite yfy in xfx.
    apply pc_unit_mono in xfx.
    rewrite xfx; right; auto.
  }
  
Defined.

(* Lemma pc_extreme_value_theorem :  *)
(*   forall (f : ^Real -> pc ^Real) l u, *)
(*     l <= u -> *)
(*     (forall x, l <= x <= u -> cont_at f x) -> *)
(*     exists M, *)
(*       (exists x, l <= x <= u /\  *)
(*                 (forall x, l <= x <= u -> cont_at f x) -> *)
(*     W_is_bounded_above (fun y => exists x, l <= x <= u /\ defined_to (f x) y). *)

   
(* Lemma pc_cont_fun_on_closed_interval_is_bounded_above : *)
(*   forall (f : ^Real -> pc ^Real) l u, *)
(*     l <= u -> *)
(*     (forall x, l <= x <= u -> cont_at f x) -> *)
(*     W_is_bounded_above (fun y => exists x, l <= x <= u /\ defined_to (f x) y). *)
