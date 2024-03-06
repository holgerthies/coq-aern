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

Require Import RealSubsets.
Require Import List.
  
Section ClassicallyCompact.

  Lemma closed_interval_is_closed x y : x <= y -> is_closed (fun a => x <= a <= y).
  Proof.
    intros h z H.
    assert (z < x \/ y < z).
    destruct (lem (z < x \/ y < z)); auto.
    contradict H.
    unfold complement.
    apply dn_unit.
    split.
    destruct (lem (x <= z)); auto.
    apply real_nle_ge in H.
    contradict H0.
    auto.
    destruct (lem (z <= y)); auto.
    apply real_nle_ge in H.
    contradict H0.
    auto.
    destruct H0.
    assert (real_0 < x - z).
    apply (real_lt_plus_lt (-z)) in H0.
    replace (-z + z) with real_0 in H0 by ring.
    replace (-z + x) with (x - z) in H0 by ring.
    auto.
    pose proof (real_Archimedean _ H1) as [n p].
    exists n.
    intros.
    intro.
    assert (y0 < x).
    pose proof (dist_lt_prop z y0 (prec n)) as [i _].
    pose proof (i H2) as [j _].
    apply (real_lt_plus_lt (y0 + prec n)) in j.
    replace (y0 + prec n + - prec n) with y0 in j by ring.
    replace (y0 + prec n + (z - y0)) with (z + prec n) in j by ring.
    apply (real_lt_plus_lt z) in p.
    replace (z + (x - z)) with x in p by ring.
    apply (real_lt_lt_lt _ _ _ j p).
    destruct H3.
    contradict (real_gt_nle _ _ H4 H3).

    assert (real_0 < z - y).
    apply (real_lt_plus_lt (-y)) in H0.
    replace (-y + y) with real_0 in H0 by ring.
    replace (-y + z) with (z - y) in H0 by ring.
    auto.
    pose proof (real_Archimedean _ H1) as [n p].
    exists n.
    intros.
    intro.
    assert (y < y0).
    pose proof (dist_lt_prop z y0 (prec n)) as [i _].
    pose proof (i H2) as [_ j].
    apply (real_lt_plus_lt (y0 - prec n)) in j.
    replace (y0 - prec n + prec n) with y0 in j by ring.
    replace (y0 - prec n + (z - y0)) with (z - prec n) in j by ring.
    apply (real_lt_plus_lt (y - prec n)) in p.
    replace (y - prec n + prec n) with y in p by ring.
    replace (y - prec n + (z - y)) with (z - prec n) in p by ring.
    apply (real_lt_lt_lt _ _ _ p j).
    destruct H3.
    contradict (real_gt_nle _ _ H4 H5).
  Defined.

  Definition open_ball := (^Real * {r : Real | real_0 < r})%type.

  Definition center (o : open_ball) := fst o.

  Definition radius (o : open_ball) := projP1 _ _  (snd o).

  Definition radius_is_positive (o : open_ball) : real_0 < radius o.
  Proof.
    destruct o.
    destruct s.
    auto.
  Defined.

  Definition open_ball_in x o :=
    dist x (center o) < radius o.
  
  Definition open_ball_inclusion a b :=
    forall x, open_ball_in x a -> open_ball_in x b.

  Lemma open_ball_finer_open_ball x : forall o : open_ball,
      open_ball_in x o ->
      exists o', center o' = x /\ open_ball_inclusion o' o.
  Proof.
    intros.
    destruct o as [c [r p]].
     
    destruct (real_le_or_le c x).
    unfold open_ball_in in H.
    simpl in H.
    simpl in H.
    unfold radius in H.
    simpl in H.
    rewrite dist_symm in H.
    rewrite (le_metric _ _ H0) in H.
    assert (real_0 < r - x + c).
    apply (real_lt_plus_lt (-x + c)) in H.
    replace ( - x + c + (x - c)) with real_0 in H by ring.
    replace ( - x + c + r) with (r - x + c) in H by ring.
    auto.
    exists (x, exist _ _ H1).
    simpl.
    split; auto.
    intro.
    unfold open_ball_in.
    simpl.
    unfold radius; simpl.
    intro.
    pose proof (le_metric _ _ H0).
    pose proof (dist_tri x0 x c).
    rewrite (dist_symm c x) in H3.
    apply (real_lt_plus_lt (dist x c)) in H2.
    rewrite real_plus_comm in H2.
    pose proof (real_le_lt_lt _ _ _ H4 H2).
    rewrite H3 in H5.
    replace (x - c + (r - x + c)) with r in H5 by ring.
    exact H5.

    unfold open_ball_in in H.
    simpl in H.
    simpl in H.
    unfold radius in H.
    simpl in H.
    rewrite (le_metric _ _ H0) in H.
    assert (real_0 < r - c + x).
    apply (real_lt_plus_lt (-c + x)) in H.
    replace ( - c + x + (c - x)) with real_0 in H by ring.
    replace ( - c + x + r) with (r - c + x) in H by ring.
    auto.
    exists (x, exist _ _ H1).
    simpl.
    split; auto.
    intro.
    unfold open_ball_in.
    simpl.
    unfold radius; simpl.
    intro.
    pose proof (le_metric _ _ H0).
    pose proof (dist_tri x0 x c).
    apply (real_lt_plus_lt (dist x c)) in H2.
    rewrite real_plus_comm in H2.
    pose proof (real_le_lt_lt _ _ _ H4 H2).
    rewrite H3 in H5.
    replace ( c - x + (r - c + x)) with r in H5 by ring.
    exact H5.
  Defined.
  
  Lemma mid_point_le_le x y : x <= y -> x <= (x + y)/d2 <= y.
  Proof.
  Admitted.

  Lemma mid_point_left_or_right x y z : x <= y <= z -> (x <= y <= (x + z)/d2) \/ ((x + z)/d2 <= y <= z).
  Admitted.

  Lemma dist_form_l_to_mid_point x y : x <= y -> dist x ((x + y)/d2) = (dist x y) /d2.
  Admitted.

  Lemma dist_form_l_to_mid_point' x y : x <= y -> ((x + y)/d2) - x = (y - x) /d2.
  Admitted.
  
  Lemma dist_form_u_to_mid_point' x y : x <= y -> y - ((x + y)/d2) = (y - x) /d2.
  Admitted.

  
  Definition is_open_cover {A} (o : A -> open_ball) S :=
    forall x, S x -> exists a, dist x (center (o a)) < radius (o a). 
  
  Definition is_finite_sub_cover {A} (c : list A) (o : A -> open_ball) S := 
    forall x, S x -> Exists (fun b => dist x (center (o b)) < radius (o b)) c.

  Definition is_compact S := forall A (o : A -> open_ball),
      is_open_cover o S ->   
      exists l : list A, is_finite_sub_cover l o S.

  Definition is_left_or_right_half a b :=
    (fst a = fst b /\ snd a = (fst b + snd b)/d2) \/
    (snd a = snd b /\ fst a = (fst b + snd b)/d2).
      
    Lemma closed_unit_interval_is_compact : forall x y,
      x <= y -> x = real_0 -> y = real_1 -> 
      is_compact (fun a => x <= a <= y).
  Proof.
    intros x y H jjjx jjjy.
    intros A o ho.
    apply Prop_dn_elim.
    intro.
    assert (exists f : nat -> {i : Real * Real | fst i <= snd i /\ neg (exists l : list A, is_finite_sub_cover l o (fun a : ^Real => fst i <= a <= snd i))},
               f O = exist _ (x, y) (conj H H0) /\
                 forall n, is_left_or_right_half (projP1 _ _ (f (S n))) (projP1 _ _ (f n))).

    apply (dependent_choice
             {i : Real * Real | fst i <= snd i /\ neg (exists l : list A, is_finite_sub_cover l o (fun a : ^Real => fst i <= a <= snd i))}
             (fun i j => is_left_or_right_half (projP1 _ _ j) (projP1 _ _ i))
          ).
    intros [[a b] [ord_ab ab_no_cover]].
    simpl in ord_ab, ab_no_cover.
    simpl.
    pose (c := (a + b)/d2).
    assert (a <= c <= b).
    apply mid_point_le_le.
    auto.
    
    destruct (lem (exists l : list A, is_finite_sub_cover l o (fun a0 : ^Real => a <= a0 <= c))).
    destruct (lem (exists l : list A, is_finite_sub_cover l o (fun a0 : ^Real => c <= a0 <= b))).
    {
      (* then contradiction *)
      contradict ab_no_cover.
      apply dn_unit.
      destruct H2.
      destruct H3.
      exists (x0 ++ x1).
      intro.
      intro.
      destruct (mid_point_left_or_right _ _ _ H4).
      apply Exists_app.
      left.
      auto.
      apply Exists_app.
      right.
      auto.
    }
    {
      (* refine right *)
      destruct H1.   
      exists (exist _ (c, b) (conj H4 H3)).
      right.
      simpl.
      split; auto.
    }
    {
      (* refine left *)
      destruct H1.   
      exists (exist _ (a, c) (conj H1 H2)).
      left.
      simpl.
      split; auto.
    }
    destruct H1 as [f [h1 h2]].
    simpl in h1.

    assert (exists l, x <= l <= y /\ forall n, exists m, dist (fst (projP1 _ _ (f m))) l <= prec n /\
                                                           (snd (projP1 _ _ (f m))) - (fst (projP1 _ _ (f m))) = prec n)
      as
      [l [l_ord m]].
    {

      assert (forall n, x <= (fst (projP1 _ _ (f n))) /\ (snd (projP1 _ _ (f n))) <= y) as j.
      {
        intros.
        induction n.
        rewrite h1.
        simpl.
        split; right; auto.
        
        destruct (h2 n).
        destruct (f n).
        destruct (f (S n)).
        simpl.
        destruct x0, x1.
        simpl in a, a0.
        simpl in H1.
        simpl in IHn.
        simpl.
        destruct H1.
        induction H1.
        destruct IHn.
        split; auto.
        destruct a0.
        destruct (mid_point_le_le _ _ H4).
        rewrite H2.
        destruct a.
        destruct (mid_point_le_le _ _ H8).
        apply (real_le_le_le _ _ _ H11 H3).

        destruct (f n).
        destruct (f (S n)).
        simpl.
        destruct x0, x1.
        simpl in a, a0.
        simpl in H1.
        simpl in IHn.
        simpl.
        destruct H1.
        split; auto.
        destruct a.
        destruct (mid_point_le_le _ _ H3).
        rewrite H2.
        destruct IHn.
        apply (real_le_le_le _ _ _ H7 H5).
        destruct IHn.
        induction H1.
        auto.
      }
      

      
      assert (forall n, (snd (projP1 _ _ (f n))) - (fst (projP1 _ _ (f n))) = prec n) as jj.
      {
        intros.
        induction n.
        simpl.
        rewrite h1.
        simpl.
        rewrite jjjx, jjjy.
        ring.

        destruct (h2 n).
        destruct (f n).
        destruct (f (S n)).
        simpl.
        destruct x0, x1.
        simpl in a, a0.
        simpl in H1.
        simpl in IHn.
        simpl.
        destruct H1.
        rewrite H2.
        destruct H1.
        destruct a.
        rewrite dist_form_l_to_mid_point'.
        rewrite IHn.
        auto.
        auto.
        

        
        destruct (f n).
        destruct (f (S n)).
        simpl.
        destruct x0, x1.
        simpl in a, a0.
        simpl in H1.
        simpl in IHn.
        simpl.
        destruct H1.
        rewrite H1, H2.
        auto.
        rewrite dist_form_u_to_mid_point'; auto.
        rewrite IHn; auto.
        destruct a; auto.
      }
      
      assert (is_fast_cauchy (fun n => fst (projP1 _ _ (f n)))) as jjj.
      {
        
        apply MultiLimit.consecutive_converging_fast_cauchy.
        intros.
        destruct (h2 n).
        destruct (f n).
        destruct (f (S n)).
        simpl.
        destruct x0, x1.
        simpl in a, a0.
        simpl in H1.
        simpl.
        destruct H1.
        rewrite H1.
        rewrite dist_axiom_identity.
        assert (real_0 <= prec (S n)).
        left.
        apply prec_pos.
        simpl in H3; auto.

        pose proof (jj n).
        destruct (f n).
        destruct (f (S n)).
        simpl.
        destruct x0, x1.
        simpl in a, a0.
        simpl in H1, H2.
        simpl.
        destruct H1.
        rewrite H3.
        
        destruct a.
        pose proof (mid_point_le_le _ _ H4).
        destruct H6.
        
        rewrite (dist_form_l_to_mid_point _ _ H4).
        pose proof (le_metric _ _ H4).
        rewrite H8.
        rewrite H2.
        right; auto.
      }

      (* apply is_fast_cauchy_iff_p in jjj. *)
      pose proof (real_limit _  jjj) as [l p].
      exists l.
      split.
      pose proof (is_closed_is_seq_complete _ (closed_interval_is_closed x y H)).
      apply (H1 _ jjj).
      intros.
      unfold w_approx.
      exists  (fst
         (projP1 (^Real * ^Real)
            (fun i : ^Real * ^Real =>
             fst i <= snd i /\
             neg (exists l0 : list A, is_finite_sub_cover l0 o (fun a : ^Real => fst i <= a <= snd i))) 
            (f n))).
      split.
      split.
      destruct (j n); auto.
      destruct (j n).
      destruct (f n).
      simpl.
      simpl in H2, H3, a.
      destruct a.
      apply (real_le_le_le _ _ _ H4 H3).
      
      rewrite dist_axiom_identity.
      left; apply prec_pos.
      exact p.

      intros.
      exists n.
      pose proof (p n).
      destruct (jj n).
      simpl.
      simpl in H1.
      
      destruct (f n).
      simpl.
      simpl in  H1.
      rewrite dist_symm.
      auto.      
    }
    

    pose proof (ho l l_ord) as [a al_dist].
    pose proof (open_ball_finer_open_ball _ _ al_dist) as [o' [p1 p2]].
    
    pose proof (real_Archimedean _ (radius_is_positive (o'))) as [p p_ord].
    pose proof (m (S (S p))) as [i [q1 q2]].
    destruct (f i).
    simpl in a0.
    simpl in q1, q2.
    destruct a0.
    assert False; apply H2.
    exists (cons a nil).
    unfold is_finite_sub_cover.
    intros.
    apply Exists_exists.
    exists a.
    split; auto.
    simpl.
    left; auto.
    assert (open_ball_in x1 o').
    {
      unfold open_ball_in.
      rewrite p1.
      assert (dist x1 l < prec p).
      assert (dist x1 (fst x0) < prec (S p)).
      destruct H3.
      rewrite dist_symm.
      rewrite (le_metric _ _ H3).
      assert (snd x0 - fst x0 <= prec p / real_2_neq_0 / real_2_neq_0) by (right; auto).

      pose proof (real_le_le_plus_le _ _ _ _ H4 H5).
      apply (real_le_plus_le (- snd x0)) in H6.
      replace  (- snd x0 + (x1 + (snd x0 - fst x0))) with (x1 - fst x0) in H6 by ring.
      simpl.
      replace (- snd x0 + (snd x0 + prec p / real_2_neq_0/ real_2_neq_0)) with (prec p / real_2_neq_0 / real_2_neq_0) in H6 by ring.
      assert (prec (S (S p)) < prec (S p)).
      apply prec_monotone.
      auto.
      simpl in H7.
      apply (real_le_lt_lt _ _ _ H6 H7).

      assert (prec (S (S p)) < prec (S p)) as k.
      apply prec_monotone.
      auto.
      pose proof (real_le_lt_lt _ _ _ q1 k) as k1.
        
      pose proof (real_lt_lt_plus_lt _ _ _ _ k1 H4).
      pose proof (dist_tri x1 (fst x0) l).
      rewrite real_plus_comm in H6.
      pose proof (real_le_lt_lt _ _ _ H6 H5).
      simpl in H7.
      pose proof (prec_twice p).
      replace (p + 1)%nat with (1 + p)%nat in H8 by (apply Nat.add_comm).
      simpl in H8.
      rewrite H8 in H7.
      exact H7.
      apply (real_lt_lt_lt _ _ _ H4 p_ord).
    }
    apply p2.
    exact H4.
    contradict H3.
  Defined.
  
End ClassicallyCompact.
