Require Import BasicAxioms.
Require Import BasicArith.
Require Import BasicSplit.


Open Scope T_scope.


Definition convex (x y w1 w2 : T) : x < y -> w1 > T0 -> w2 > T0 -> T.
Proof.
  intros p p1 p2.
  pose proof (Tlt_lt_plus_lt T0 w1 T0 w2 p1 p2).
  rewrite Tplus_unit in H.
  exact ((x*w1+y*w2)/(Tgt_neq (w1+w2) T0 H)).
Defined.


Lemma convexity : forall x y w1 w2,
    forall (p:x < y) (q:w1 > T0) (r:w2 > T0),
      x < convex x y w1 w2 p q r < y.
Proof.
  intros.
  split.
  + unfold convex.
    apply (Tlt_mult_r_pos_lt x y w2 r) in p.
    apply (Tlt_plus_lt  (w1*x) (x*w2) (y*w2)) in p.
    assert (w1+w2 <> T0) as Path by auto with Tiny.
    rewrite <- (neq_path (w1+w2) T0 Path (Tgt_neq (w1 + w2) T0
    (eq_ind (T0 + T0) (fun t : T => t < w1 + w2) (Tlt_lt_plus_lt T0 w1 T0 w2 q r) T0
            (Tplus_unit T0)))).
    
    apply (Tlt_plus_lt  w2 T0 w1) in q.
    replace (w2+T0) with w2 in q by ring.
    replace (w2+w1) with (w1+w2) in q by ring.
    pose proof (Tlt_lt_lt T0 w2 (w1+w2) r q).
    replace (w1 * x + x * w2) with (x*(w1  + w2)) in p by ring.
    assert (/Path > T0) by auto with Tiny.
    apply (Tlt_mult_r_pos_lt (x*(w1+w2)) (w1*x+y*w2) (/Path) H0) in p.
    rewrite Tmult_assoc, (Tmult_comm (w1+w2) (/Path)) in p.
    rewrite (Tmult_inv (w1 + w2) Path), Tmult_comm, Tmult_unit in p.
    replace (w1*x) with (x*w1) in p by ring.
    exact p.

  + unfold convex.
    apply (Tlt_mult_r_pos_lt x y w1 q) in p.
    apply (Tlt_plus_lt  (w2*y) (x*w1) (y*w1)) in p.
    assert (w1+w2 <> T0) as Path by auto with Tiny.
    rewrite <- (neq_path (w1+w2) T0 Path (Tgt_neq (w1 + w2) T0
    (eq_ind (T0 + T0) (fun t : T => t < w1 + w2) (Tlt_lt_plus_lt T0 w1 T0 w2 q r) T0
            (Tplus_unit T0)))).


    apply (Tlt_plus_lt  w1 T0 w2) in r.
    replace (w1+T0) with w1 in r by ring.
    pose proof (Tlt_lt_lt T0 w1 (w1+w2) q r).
    replace (w2 * y + y * w1) with (y * (w1  + w2)) in p by ring.
    assert (/Path > T0) by auto with Tiny.
    apply (Tlt_mult_r_pos_lt  (w2*y+x*w1) (y*(w1+w2)) (/Path) H0) in p.
    rewrite Tmult_assoc in p at 1.
    replace ((w1 + w2) * / Path) with (/Path*(w1+w2)) in p by auto with Tiny.
    rewrite (Tmult_inv (w1 + w2) Path) in p.
    replace (y*T1) with y in p by ring.
    replace  (w2 * y + x * w1) with (x * w1 + y * w2) in p by ring.
    exact p.
Qed.
    

  


(*
Lemma NT_hom : forall n m, NT (n+m) = NT n + NT m.
Proof.
  intros n m.
  induction n.
  simpl.
  auto with Tiny.
  assert (S n + m = S (n+m))%nat as H by intuition.
  rewrite H.
  assert (forall n, NT (S n) = T1 + NT n) by (intro; simpl; exact eq_refl).
  rewrite (H0 n). rewrite (H0 ((n+m)%nat)).
  rewrite IHn; ring.
Qed.
Hint Resolve NT_hom: Tiny.

Lemma NT_pos : forall n, (n>0)%nat -> NT n > T0.
Proof.
  intros n p.
  induction n.
  contradict p; exact (gt_irrefl 0).
  assert (S n = 1+n)%nat as q; intuition.
  rewrite q.
  rewrite (NT_hom 1%nat n).
  pose proof (T1_gt_T0) as gtg.
  destruct n.
  simpl; ring_simplify; auto with Tiny.

  Search (forall n, S n > 0)%nat.
  pose proof (IHn (gt_Sn_O n)).
  pose proof (Tlt_lt_plus_lt T0 T1 T0 (NT (S n)) gtg H) as H1; ring_simplify in H1.
  replace (NT (S n) + T1) with (T1 + NT (S n)) in H1 by ring.
  assert (NT 1 = T1). simpl. ring.
  rewrite H0; exact H1.
Qed.
Hint Resolve NT_pos: Tiny.


Lemma IZT_hom : forall n m, IZT (n+m) = IZT n + IZT m.
Proof.
  intros n m.
  induction n; simpl.
  auto with Tiny.
  unfold IZT at 2.1 

Lemma convexity : forall z1 z2 a b,
    (z1>0)%Z -> (z2>0)%Z -> a<b ->
    a < ((IZT z1)*a + (NT z2) * b) / (NT (z1 + z2)) < b.
Proof.
  intros.
  split.
  + replace a with (a * T1) at 1 by ring.
    assert (NT (z1+z2) > T0).
    ++ assert (z1+z2 > 0)%nat as t by intuition.
       auto with Tiny.
    ++ 
       
      replace T1 with (/(NT (z1+z2)) * (NT (z1+z2))) at 1 by auto with Tiny.
      replace (  a * (/ NT (z1 + z2) * NT (z1 + z2))) with
          (  a * (NT (z1 + z2) */ NT (z1 + z2))) by ring.
      replace (  a * (NT (z1 + z2) */ NT (z1 + z2))) with
          (a * (NT (z1 + z2)) */ NT (z1 + z2)) by ring.

      assert (/ (NT (z1+z2)) > T0);  auto with Tiny.

      replace ((NT z1 * a + NT z2 * b) / NT (z1 + z2)) with
          ((NT z1 * a + NT z2 * b) */ NT (z1 + z2)) by auto.

      replace (  a * NT (z1 + z2) * / NT (z1 + z2)) with
          ( / NT (z1+z2) * (a * NT (z1 + z2))) by ring.
      replace ((NT z1 * a + NT z2 * b) * / NT (z1 + z2)) with
          ( / NT (z1 + z2) * (NT z1 * a + NT z2 * b)) by ring.
      apply Tlt_mult_pos_lt.
      exact H3.
    replace (NT (z1+z2)) with (NT z1 + NT z2) by auto with Tiny.
    replace (a * (NT z1 + NT z2)) with (a* NT z1 + a * NT z2) by ring.
    replace ( (a* NT z1 + a * NT z2)) with ( (NT z1 * a + NT z2 * a)) by ring.
    apply (Tlt_plus_lt).
    apply (Tlt_mult_pos_lt).
    apply (NT_pos z2 H0).
    exact H1.

  + assert (NT (z1+z2) > T0).
    ++ assert (z1+z2>0)%nat as t by intuition.
       auto with Tiny.
    ++ replace b with (b * T1) at 2 by ring.
       replace T1 with (/(NT (z1+z2)) *NT (z1+z2)) by auto with Tiny.
       replace (/ NT (z1+z2) * NT(z1+z2)) with (NT (z1+z2) * /(NT (z1+z2))) by auto with Tiny.
       replace (b * (NT (z1 + z2) * / NT (z1 + z2))) with
           ((b * NT (z1 + z2)) * / NT (z1 + z2)) by ring.
       replace ( (NT z1 * a + NT z2 * b) / NT (z1 + z2)) with
           ( (NT z1 * a + NT z2 * b) * / NT (z1 + z2)) by auto.
       assert (/ NT (z1+z2) > T0) by auto with Tiny.
       replace ( (NT z1 * a + NT z2 * b) * / NT (z1 + z2)) with
           ( / NT (z1 + z2)* (NT z1 * a + NT z2 * b)) by ring.
       replace ( b * NT (z1 + z2) * / NT (z1 + z2)) with
           ( / NT (z1 + z2) *(b * NT (z1 + z2))) by ring.
       apply Tlt_mult_pos_lt.
       +++ exact H3.
       +++
         replace (NT (z1+z2)) with (NT z1 + NT z2) by auto with Tiny.
         replace (b * (NT z1 + NT z2)) with (b* NT z1 + b * NT z2) by ring.
         replace ( (b* NT z1 + b * NT z2)) with ( (NT z1 * b + NT z2 * b)) by ring.
         apply (Tlt_plus_r_lt).
         apply (Tlt_mult_pos_lt).
         apply (NT_pos z1 H).
         exact H1.
Qed.

Definition convex (z1 z2 : T) (n m : Z)
  : z1 < z2 -> (n > 0)%Z -> (m >0)%Z -> T.
Proof.
  intros.
  exact ((NT n * z1 + NT m * z2) / NT (n+m)).
Defined.

Lemma convex_loc_r : forall (z1 z2 : T) (n m : nat)
    (p: z1 < z2)  (q : (n > 0)%nat)  (r: (m >0)%nat),
    (z2 - convex z1 z2 n m p q r = (z2-z1) * (NT n) / (NT (n+m))).
Proof.
  intros.
  unfold convex.
  pose proof (eq_refl ((z2 - z1) * NT m / NT (n + m))) as H0.
  assert (NT (n+m) <> T0);  assert (n+m>0)%nat by intuition; auto with Tiny.
  replace z2 with (z2*T1) at 1 by ring.
  replace T1 with (/NT (n + m) * NT (n + m)) at 1 by auto with Tiny.
  replace (/NT (n+m) * NT (n+m)) with (NT(n+m)*/NT(n+m)) at 1 by ring.
  replace (z2 * (NT (n + m) * / NT (n + m))) with
      ((z2 * (NT (n + m))) * / NT (n + m)) by ring.
  replace ((NT n * z1 + NT m * z2) / NT (n + m)) with
      ((NT n * z1 + NT m * z2) */ NT (n + m)) by auto.
  replace (z2 * NT (n + m) * / NT (n + m) - (NT n * z1 + NT m * z2) * / NT (n + m)) with
      ((z2 * NT (n + m)  - (NT n * z1 + NT m * z2)) * / NT (n + m)) by ring.
  rewrite (NT_hom n m) at 1.
  
  
  replace (z2 * (NT n + NT m) - (NT n * z1 + NT m * z2)) with 
      ((z2 - z1)*NT n) by ring.
  replace ((z2 - z1) * NT m / NT (n + m)) with ((z2 - z1) * NT m */ NT (n + m)) by auto.
  exact eq_refl.
Qed.

Lemma convex_loc_l : forall (z1 z2 : T) (n m : nat)
    (p: z1 < z2)  (q : (n > 0)%nat)  (r: (m >0)%nat),
    (convex z1 z2 n m p q r - z1 = (z2-z1) * (NT m) / (NT (n+m))).
Proof.
  intros.
  unfold convex.
  pose proof (eq_refl ((z2 - z1) * NT n / NT (n + m))) as H0.
  assert (NT (n+m) <> T0);  assert (n+m>0)%nat by intuition; auto with Tiny.
  replace z1 with (z1*T1) at 2 by ring.
  replace T1 with (/NT (n + m) * NT (n + m)) at 1 by auto with Tiny.
  replace (/NT (n+m) * NT (n+m)) with (NT(n+m)*/NT(n+m)) at 1 by ring.
  replace (z1 * (NT (n + m) * / NT (n + m))) with
      ((z1 * (NT (n + m))) * / NT (n + m)) by ring.
  replace ((NT n * z1 + NT m * z2) / NT (n + m)) with
      ((NT n * z1 + NT m * z2) */ NT (n + m)) by auto.
  replace ((NT n * z1 + NT m * z2) * / NT (n + m) - z1 * NT (n + m) * / NT (n + m)) with
      (((NT n * z1 + NT m * z2) - z1 * NT (n + m)) * / NT (n + m)) by ring.
  rewrite (NT_hom n m) at 1.
  replace ((z2 - z1) * NT m / NT (n + m)) with
      ((z2 - z1) * NT m * / NT (n + m)) by auto.
  ring.
Qed.


Lemma lt_cancel : forall n m, (n > m)%nat -> (m -n > 0)%nat.
Proof.
  intros n m p.
  auto with arith.
  case_eq (m-n)%nat; intros.

  admit.
  
  Check Nat.lt_plus_minus.
  auto with arith.
  induction m.
  auto with arith.
  contradict p; apply (Nat.nlt_0_r).
  
  induction n.
  simpl.
  auto.

  Check lt_minus.

Lemma NT_gt : forall n m, (n > m)%nat -> NT n > NT m.
Proof.
  intros.
  assert (NT n = NT (m + (n-m))).
  intuition.
  replace (NT (m + (n-m))) with (NT m + NT (n-m)) in H0 by auto with Tiny.
  rewrite H0.
  replace (NT m) with (NT m + T0) at 2 by ring.
  apply (Tlt_plus_lt).
  assert (n-m > 0)%nat.
  
  Search (0 < _ - _ )%nat.
  Check lt_minus_lt_0.
  auto.
  trivial.
  intuition.
  
  ring_simplify.
  induction n.
  +  contradict H;  apply (Nat.nlt_0_r m).
     Search ( _ = _ + _)%nat.
  +  

     Search (~  _ < 0)%nat.
  
Lemma convex_order : forall (z1 z2 : T) (n m : nat)
    (p: z1 < z2)  (q : (n > 0)%nat)  (r: (m >0)%nat),
    (m>n)%nat -> convex z1 z2 n m p q r > convex z1 z2 m n p r q.
Proof.
  intros; unfold convex.
  assert ((n+m>0)%nat) as H1 by intuition.
  assert (/NT (n+m) > T0) as H2 by auto with Tiny.
  replace ((NT n * z1 + NT m * z2) / NT (n + m)) with
      ((NT n * z1 + NT m * z2) */ NT (n + m)) by auto;
    replace ((NT m * z1 + NT n * z2) / NT (m + n)) with
        ((NT m * z1 + NT n * z2) */ NT (m + n)) by auto.
  replace ((m+n)%nat) with ((n+m)%nat) by intuition.
  apply Tlt_mult_r_pos_lt; auto with Tiny.
  assert (m-n > 
  apply (Tlt_mult_
  
Definition NT2 := NT 2.
Definition NT3 := NT 3.
*)
