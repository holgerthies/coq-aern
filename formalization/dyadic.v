(* this file proves various properties of subsets of real numbers *)
Require Import Lia.
Require Import Real Euclidean List Minmax ClassicalSubsets Sierpinski testsearch.

Require Import Vector.
Section Dyadic.
Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.
#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).
#[local] Definition sofReal := @sofReal types casofReal.
#[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).
#[local] Notation "^euclidean" := (@euclidean types) (at level 0).

  Add Ring realRing : (realTheory ).
  Definition Dyadic := (Z * nat)%type. 
  Definition to_real (d : Dyadic) := (IZreal (fst d)) * prec (snd d).
  Lemma pos_approx x : x > real_0 -> ^M {n : nat |  dist x (Nreal n) <= real_1}.
  Proof.
    intros.
    assert  (forall n : nat, ^M ({(fun n0 : nat => x < Nreal n0) (S n)} + {~ (fun n0 : nat => x < Nreal n0) n})).
    {
      intros.
      apply (M_lift ({x < Nreal (S n)} + {Nreal n < x})).
      - intros.
        destruct H0.
        + left.
          exact r.
        + right.
          apply real_lt_nlt.
          exact r.
      - apply choose.
        apply real_lt_semidec.
        apply real_lt_semidec.
        destruct (real_total_order x (Nreal (S n))) as [H1 | [H1 | H1]].
        left.
        exact H1.
        right.
        rewrite H1.
        apply Nreal_strict_monotone.
        lia.
        right.
        apply (real_lt_lt_lt _ (Nreal (S n))).
        apply Nreal_strict_monotone;lia.
        exact H1.
    }

    pose proof (epsilon_smallest_choose_M (fun n => (x < (Nreal n))) X (nat_bound_above _ H)).
    revert X0.
    apply M_lift.
    intros.
    destruct H0 as [n [H1 H2]].
    exists n.
    apply dist_le_prop.
    split.
    add_both_side_by (Nreal n).
    destruct n.
    apply real_lt_le.
    apply (real_lt_lt_lt _ real_0).
    add_both_side_by real_1.
    apply real_1_gt_0.
    exact H.
    apply (real_le_le_le _ (Nreal n)).
    simpl.
    add_both_side_by real_1.
    apply real_eq_le;auto.
    apply real_nge_le.
    apply H2.
    lia.
    add_both_side_by (Nreal n).
    apply real_lt_le.
    simpl in H1.
    rewrite real_plus_comm.
    exact H1.
  Defined.

  Lemma real_round x : ^M {z : Z |  dist x (IZreal z) <= real_1}.
  Proof.
    apply (M_lift_dom ({x > real_0} + {x < real_1} )).
    - intros.
      destruct H.
      pose proof (pos_approx _ r).
      revert X.
      apply M_lift.
      intros.
      destruct H.
      exists (Z.of_nat x0).
      rewrite <-IZreal_Nreal.
      exact r0.
      apply (M_lift_dom ({x < real_0} + {x > - real_1} )).
      + intros.
        destruct H.
        apply real_lt_anti in r0.
        ring_simplify in r0.
        pose proof (pos_approx _ r0).
        revert X;apply M_lift;intros.
        destruct H.
        exists (- (Z.of_nat x0))%Z.
        rewrite IZ_asym.
        rewrite <-IZreal_Nreal.
        rewrite dist_symm.
        unfold dist.
        assert (- Nreal x0 - x = - x - Nreal x0) as -> by ring.
        exact r1.

        apply M_unit.
        exists 0%Z.
        simpl;apply dist_le_prop.
        split.
        apply real_lt_le.
        ring_simplify.
        exact r0.

        apply real_lt_le.
        ring_simplify.
        exact r.
      + apply choose; repeat apply real_lt_semidec.
        destruct (real_total_order x real_0) as [H | [H | H]].

        left;auto.
        right.
        rewrite H.
        apply real_lt_anti_anti.
        ring_simplify.
        apply real_1_gt_0.

        right.
        apply (real_lt_lt_lt _ real_0);auto.
        add_both_side_by real_1.
        apply real_1_gt_0.
    - apply choose; repeat apply real_lt_semidec.
        destruct (real_total_order x real_1) as [H | [H | H]].
        right.
        exact H.
        left.
        rewrite H.
        apply real_1_gt_0.
        left.
        apply (real_lt_lt_lt _ real_1).
        apply real_1_gt_0.
        exact H.
    Defined.

  Lemma real_approx x p : ^M { d : Dyadic  | dist x (to_real d) <= prec p}.
  Proof.
    unfold to_real.
    pose proof (real_round (x * Nreal (Npow2 p))).
    revert X;apply M_lift; intros.
    destruct H.
    exists (x0, p).
    simpl.
    apply (real_le_mult_pos_le (prec p)) in r; [| apply real_lt_le;apply prec_pos].
    ring_simplify in r.
    rewrite dist_scale in r; [| apply real_lt_le;apply prec_pos].
    rewrite real_mult_comm,real_mult_assoc in r.
    rewrite (real_mult_comm _ (prec p)), prec_Npow2_unit, real_mult_comm, real_mult_unit, real_mult_comm in r.
    exact r.
  Defined.
End Dyadic.

Section DyadicVector.
Context {types : RealTypes} { casofReal : ComplArchiSemiDecOrderedField_Real types }.
#[local] Notation "^K" := (@K types) (at level 0).
#[local] Notation "^M" := (@M types) (at level 0).
#[local] Notation "^Real" := (@Real types) (at level 0).
#[local] Notation "^IZreal" := (@IZreal types sofReal) (at level 0).
#[local] Notation "^euclidean" := (@euclidean types) (at level 0).
Definition DyadicVector {d : nat}:= t Dyadic d. 
Definition to_euclidean {d} (x : (@DyadicVector d)) : (^euclidean d).
Proof.
  induction x.
  apply Euclidean.nil.
  apply Euclidean.cons.
  apply (to_real h).
  apply IHx.
Defined.

Lemma euclidean_approx {d} x p : ^M { y : (@DyadicVector d)  | euclidean_max_dist x (to_euclidean y) <= prec p}.
  induction d.
  - apply M_unit.
    exists (nil Dyadic).
    rewrite (dim_zero_destruct x).
    rewrite (proj2 (euclidean_max_dist_id _ _) eq_refl). 
    apply real_lt_le;apply prec_pos.
  - destruct (dim_succ_destruct x) as [hx [tx H]].
    specialize (IHd tx).
    revert IHd.
    apply M_lift_dom.
    intros.
    destruct H0 as [y P].
    pose proof (real_approx hx p). 
    revert X.
    apply M_lift.
    intros.
    destruct H0 as [y0 H'].
    exists (cons _ y0 _ y).
    rewrite H.
    simpl.
    rewrite euclidean_max_dist_cons.
    apply real_max_le_le_le;auto.
Defined.

Definition enumerable (X : Type) := {f : nat ->X | forall x, exists n, (f n) = x}.

Lemma enumerable_pos X : {f : positive ->X | forall x, exists n, (f n) = x} -> enumerable X.
Proof.
  intros.
  destruct X0 as [f P].
  exists (fun n => (f (Pos.of_nat n))).
  intros.
  destruct (P x) as [n N].
  exists (Pos.to_nat n).
  rewrite Pos2Nat.id;auto.
Defined.

Fixpoint pos_to_pospair_fst (p : positive) :=
  match p with
  | xO (xO p') => xO (pos_to_pospair_fst p') 
  | xI (xO p') => xO (pos_to_pospair_fst p') 
  | xO (xI p') => xI (pos_to_pospair_fst p')  
  | xI (xI p') => xI (pos_to_pospair_fst p')  
  | _ => xH
  end.
    
Fixpoint pos_to_pospair_snd (p : positive) :=
  match p with
  | xO (xO p') => xO (pos_to_pospair_snd p') 
  | xI (xO p') => xI (pos_to_pospair_snd p') 
  | xO (xI p') => xO (pos_to_pospair_snd p')  
  | xI (xI p') => xI (pos_to_pospair_snd p')  
  | _ => xH
  end.

Fixpoint pospair_to_pos_fst p :=
  match p with
  | (xO p') => (xO (xO (pospair_to_pos_fst p')))
  | (xI p') => (xO (xI (pospair_to_pos_fst p'))) 
  | xH => (xO xH)
 end.
Fixpoint pospair_to_pos_snd q :=
  match q with
  | (xO q') => (xO (xO (pospair_to_pos_snd q')))
  | (xI q') => (xI (xO (pospair_to_pos_snd q'))) 
  | xH => (xI xH) 
 end.
Fixpoint pospair_to_pos p q :=
  match p, q with
  | (xO p'), (xO q') => (xO (xO (pospair_to_pos p' q')))
  | (xO p'), (xI q') => (xI (xO (pospair_to_pos p' q')))
  | (xI p'), (xO q') => (xO (xI (pospair_to_pos p' q')))
  | (xI p'), (xI q') => (xI (xI (pospair_to_pos p' q')))
  | (xO p'), xH =>  (pospair_to_pos_fst p')
  | (xI p'), xH => (pospair_to_pos_fst (xI p'))
  | xH, (xO q') => (xO (xO (pospair_to_pos_snd q')))
  | xH, (xI q') => (xI (xO (pospair_to_pos_snd q')))
  | xH, xH => 1%positive
 end.


Lemma pos_to_pospair_fst_inj p : (pos_to_pospair_fst (pospair_to_pos_fst p )) = p.
Proof.
  induction p;simpl; try rewrite IHp;auto.
Defined.

Lemma pos_to_pospair_snd_inj q : (pos_to_pospair_snd (pospair_to_pos_snd q )) = q.
Proof.
  induction q;simpl; try rewrite IHq;auto.
Defined.

Lemma pos_to_pospair_surj pq : exists p, (pos_to_pospair_fst p) = (fst pq) /\ (pos_to_pospair_snd p) = (snd pq).  
Proof.
  destruct pq as [p q].
  exists (pospair_to_pos p q).
  revert q.
  induction p;intros;destruct q;simpl;try (destruct (IHp q) as [-> ->]);auto.

  rewrite pos_to_pospair_fst_inj.
 simpl. 
  destruct (IHp 1%positive) as [-> ->].
  simpl.
  destruct q.
  destruct (IHp q).
  rewrite H.
  rewrite H0.
  simpl.
  rewrite H1,H2.
  auto.
  simpl.
Lemma enumerable_pair X Y : enumerable X -> enumerable Y -> enumerable (X * Y).
Proof.
  intros.
  apply enumerable_pos.
  destruct X0 as [fx Px].
  destruct X1 as [fy Py].
  exists (fun n => ((fx n), (fy n))).
  intros.
  destruct x.
 
