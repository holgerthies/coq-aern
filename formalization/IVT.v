Require Import Real.
Require Import Minmax.

Local Open Scope Real_scope.

Section IVT.
  Context {T : ComplArchiSemiDecOrderedField}.
  Notation R := (CarrierField T).
  
  Ltac IZReal_tac t :=
    match t with
    | @real_0 R => constr:(0%Z)
    | @real_1 R => constr:(1%Z)
    | @IZreal R ?u =>
      match isZcst u with
      | true => u
      | _ => constr:(InitialRing.NotConstant)
      end
    | _ => constr:(InitialRing.NotConstant)
    end.

  Add Ring realRing : (realTheory R) (constants [IZReal_tac]).
  
  Notation real_ := (real R).
  Notation real_0_ := (@real_0 R).
  Notation real_1_ := (@real_1 R).
  Notation prec_ := (@prec R).
  Notation dist_ := (@dist T).

  Arguments d2 {_}.
  Lemma sandwich : forall a b, (forall ε, ε > real_0_ -> a-ε < b < a+ε) -> b = a.
  Proof.
    intros a b e.
    destruct (real_total_order a b) as [c1|[c2|c3]].
    pose proof (@padding _ b a c1) as H.
    destruct H as [eps [p1 p2]].
    pose proof (e (eps / d2) (@real_half_gt_zero _  eps p1)).
    rewrite p2 in H.
    destruct H.
    replace (a+eps/d2) with (eps/d2+a) in H0 by ring.
    apply (real_lt_plus_lt (-a)) in H0.
    replace ( - a + (eps + a)) with eps in H0 by ring.
    replace ( - a + (eps / d2 + a)) with (eps / d2) in H0 by ring.
    contradict H0.
    pose proof (@real_gt_half _ eps p1).
    auto with real.

    auto.
    
    pose proof (@padding _ a b c3) as H.
    destruct H as [eps [p1 p2]].
    pose proof (e (eps / d2) (@real_half_gt_zero _  eps p1)).
    rewrite p2 in H.
    destruct H.
    apply (real_lt_plus_lt (-b)) in H.
    apply (real_lt_plus_lt (eps/d2)) in H.
    replace (b+eps/d2) with (eps/d2+b) in H by ring.
    apply (real_lt_plus_lt (-b)) in H0.
    replace (eps / d2 + (- b + b)) with (eps/d2) in H by ring.
    replace ( eps / d2 + (- b + (eps + b - eps / d2))) with (eps) in H by ring.
    contradict H.
    pose proof (@real_gt_half _ eps p1).
    auto with real.
  Qed.  

  

  Definition continuous_at (f : real_ -> real_) (z : real_) : Prop
    := forall ε, ε > real_0_ ->
                 exists δ, δ > real_0_ /\
                           (forall z', dist_ z z' < δ -> dist_ (f z) (f z') < ε).

  Definition continuous (f : real_ -> real_) : Prop := forall z, continuous_at f z.

  (* proved by Dongseong and written by Sewon *)
  Theorem W_IVT_l : forall f : real_ -> real_,
      continuous f ->
      forall a b, a < b -> 
                  forall c, f a < c < f b -> exists z', a < z' < b /\ f z' = c.
  Proof.
    intros f cont a b o c p.
    assert (@W_is_non_empty _ (fun z => a<=z<=b /\ f z < c)) as nepty.
    exists a; constructor 1; auto with real.
    destruct p as [t1 t2]; exact t1.
    assert (@W_is_bounded_above _ (fun z => a<=z<=b /\ f z < c)) as upbd.
    exists b.
    unfold W_is_bounded_above; intros b' p'; destruct p' as [[p1 p2] p3]; exact p2.
    (* u := sup { z | f z < c } *)
    destruct (@W_complete _ (fun z => a<=z<=b /\ f z < c) nepty upbd) as [u q].

    (* prove a<=u<=b *)
    assert (mem : a <= u <= b).
    destruct (real_total_order a u) as [t1 | [t2 | t3]].
    split; auto with real.
    destruct (real_total_order u b) as [tt1 | [tt2 | tt3]]; auto with real.
    (** when u>b => contradict sup *)
    assert (upb_alt : W_is_upper_bound (fun z => a<=z<=b /\ f z < c) b).
    unfold W_is_upper_bound.
    intros z [[mem1 mem2] cond]; auto with real.
    contradict q.
    unfold W_is_sup.
    intuition.
    pose proof (H3 b upb_alt) as contra.
    contradict contra.
    auto with real.

    split; auto with real.
    rewrite <- t2; auto with real.

    (** when u < a => contradict sup *)

    contradict q.
    unfold W_is_sup; intuition.
    unfold W_is_upper_bound in H2.  
    destruct nepty as [t1 t2].
    pose proof (H2 t1 t2).
    destruct t2 as [[qq1 pp2] qq2].
    pose proof (real_le_le_le a t1 u qq1 H).
    contradict H4; auto with real.


    
    (* Casing on f u >? 0 *)
    destruct (real_total_order (f u) c) as [l | [m | r]].
    (** when f u < c, pick small u + e such that f u+e < c => contradict *)
    (** because u+e is in the set while u is the supremum of the set     *)
    assert (mem2 : u < b).
    destruct mem as [e [k | v]].
    exact k.
    rewrite v in l; destruct p as [p1 p2].
    contradict l; auto with real.
    
    destruct (@padding _ c (f u) l) as [eps [o1 o2]].
    assert (t1 : eps / d2 > real_0_) by auto with real.
    destruct (cont u (eps/d2) t1) as [δ [o3 o4]].
    destruct (real_W_min_prop (u+δ/d2) b) as [x  H].
    
    assert (dis : dist_ u x < δ).
    (**)
    destruct (real_total_order (u+δ/d2) b) as [l1 |[ l2 | l3]];
      destruct H as [r1 [r2 r3]].
    
    apply r3 in l1.
    rewrite l1.
    replace u with (real_0_+u) at 1 by ring;
      replace (u+δ/d2) with (δ/d2+u) by ring.
    rewrite <- (real_metric_inv real_0_ (δ/d2) u).

    destruct (@dist_prop _ real_0_ (δ/d2)) as [_[_ u3]];
      rewrite (u3 (@real_half_gt_zero _  δ o3)).
    ring_simplify; apply @real_gt_half ; exact o3.

    apply r2 in l2.
    rewrite l2.
    replace u with (u+real_0_) at 1 by ring.
    rewrite <- (real_metric_plus_inv real_0_ (δ/d2) u).
    destruct (@dist_prop _ real_0_ (δ/d2)) as [_[_ u3]];
      rewrite (u3 (@real_half_gt_zero _  δ o3)).
    ring_simplify; apply @real_gt_half; exact o3.

    pose proof (r1 l3) as H.
    rewrite H.
    pose proof (@real_metric_inv _ real_0_ (b-u) u) as H1.
    replace (real_0_+u) with u in H1 by ring.
    replace (b-u+u) with b in H1 by ring.
    rewrite <- H1.
    assert (b-u > real_0_) as H2 by auto with real.
    destruct (@dist_prop _ real_0_ (b-u)) as [_[_ u3]].
    apply u3 in H2.
    rewrite H2.
    assert ((u+δ/d2) +-u > b+-u).
    apply real_lt_plus_r_lt.
    exact l3.
    replace ( u + δ / d2 + - u) with (δ/d2) in H0 by ring.
    replace (b+-u) with (b-u) in H0 by ring.
    ring_simplify.
    pose proof (@real_gt_half _ δ o3).
    exact (real_lt_lt_lt (b-u) (δ/d2) δ H0 H3).
    (**)

    pose proof (o4 x dis).
    (* prove a<=x<=b and f x < c then contradicts sup *)
    (**)
    assert (memx : a<=x<=b).
    destruct mem as [mem _].
    destruct H as [l1 [l2 l3]].
    destruct (real_total_order (u+δ/d2) b) as [r1 | [r2 | r3]].
    (*** when u+δ/2 <b *)
    split.
    apply l3 in r1.
    rewrite r1.
    pose proof (@real_half_gt_zero _  δ o3).
    assert (u+δ/d2 > u+real_0_).
    apply (real_lt_plus_lt); auto.
    replace (u+real_0_) with u in H1 by ring.
    pose proof (@real_le_lt_lt _ a u (u+δ/d2) mem H1); auto with real.

    pose proof (l3 r1) as H1; rewrite H1.
    auto with real.

    (*** when u+δ/2 =b *)
    pose proof (l2 r2) as H; rewrite H.
    split.
    pose proof (@real_half_gt_zero _  δ o3).
    assert (u+δ/d2 > u+real_0_).
    apply (real_lt_plus_lt); auto.
    replace (u+real_0_) with u in H2 by ring.
    pose proof (@real_le_lt_lt _ a u (u+δ/d2) mem H2); auto with real.
    rewrite <- r2; right; exact eq_refl.

    (*** when u+δ/2 > b *)
    pose proof (l1 r3) as H; rewrite H.
    split; auto with real.
    (**)

    assert (f x < c).
    destruct (real_total_order (f u) (f x)) as [l1 | [l2 | l3]].
    destruct (@dist_prop _ (f u) (f x)) as [_ [_ r3]];
      pose proof (r3 l1).
    rewrite H1 in H0.
    rewrite o2.
    pose proof (real_lt_plus_lt  (f u) (f x - f u) (eps/d2) H0).
    ring_simplify in H2.
    pose proof (@real_gt_half _ eps o1).
    assert (f u + eps > f u + eps / d2).
    apply (real_lt_plus_lt); auto.
    replace (eps + f u) with (f u + eps) by ring.
    apply (real_lt_lt_lt (f x) (f u + eps / d2) (f u + eps)).
    exact H2.
    exact H4.

    rewrite <- l2; exact l.

    exact (real_lt_lt_lt (f x) (f u) c l3 l).

    (** finally....  x is the counter example of sup *)
    contradict q.
    unfold W_is_sup.
    unfold not; intros.
    destruct H2 as [H2 _].
    unfold W_is_upper_bound in H2.
    pose proof (H2 x (conj memx H1)).
    destruct (real_is_min_or (u+δ/d2) b x H) as [p1 | p2].
    rewrite <- p1 in H3.
    destruct H3.
    apply (real_lt_plus_lt (-u) (u+δ/d2) u) in H3.
    ring_simplify in H3.
    pose proof (@real_half_gt_zero _  δ o3).
    contradict H4.
    exact (real_lt_nlt (δ/d2) real_0_ H3).
    apply (real_eq_plus_eq (u+δ/d2) u (-u)) in H3.
    ring_simplify in H3.
    pose proof (@real_half_gt_zero _  δ o3).
    rewrite H3 in H4.
    contradict H4.
    exact (real_ngt_triv real_0_).
    rewrite <- p2 in H3.
    contradict H3; auto with real.

    (** when f u = c *)
    exists u.
    split.
    destruct mem as [[o1|o1] [o2|o2]].
    exact (conj o1 o2).
    destruct p.
    rewrite o2 in m.
    contradict m.
    auto with real.
    rewrite <- o1 in m.
    contradict m.
    destruct p.
    auto with real.
    rewrite o1 in o; rewrite <- o2 in o.
    contradict o; auto with real.
    exact m.

    (** when f u > c *)
    assert (mem2 : a < u).
    destruct mem as [[k| v] _].
    exact k.
    rewrite <-v in r; destruct p as [p1 p2].
    contradict r; auto with real.
    
    destruct (@padding _ (f u) c r) as [eps [o1 o2]].
    assert (t1 : eps / d2 > real_0_) by auto with real.
    destruct (cont u (eps/d2) t1) as [δ [o3 o4]].
    destruct (real_W_max_prop (u-δ/d2) a) as [x  H].
    
    assert (dis : dist_ u x < δ).
    (**)
    destruct (real_is_max_Or (u-δ/d2) a x H) as [[c1 p1] | [c2 p2]].
    (* case where Max is u-δ/d2 *)
    rewrite <- c1.
    rewrite  (@real_metric_inv _ u (u-δ/d2) (δ/d2)).
    replace (u - δ / d2 + δ / d2) with u by ring.
    rewrite (@real_metric_inv _ (u+δ/d2) u (-u)).
    replace (u + δ / d2 + - u) with (δ/d2) by ring;
      replace (u+-u) with real_0_ by ring.
    destruct (@dist_prop _ real_0_ (δ/d2)) as [_[_ u3]].
    rewrite dist_symm.
    rewrite (u3 (@real_half_gt_zero _  δ o3)).
    ring_simplify; apply @real_gt_half; exact o3.

    (* case where Max is a *)
    pose proof (@real_half_gt_zero _  δ o3).
    apply (real_lt_plus_lt u (real_0_) (δ/d2)) in H0.
    ring_simplify in H0.
    pose proof (real_lt_le a (u+δ/d2)  (real_lt_lt_lt a u (u+δ/d2) mem2 H0)) as R.
    assert (u - δ / d2 <= a <= u + δ / d2).
    split; auto with real.
    pose proof (real_metric_sand u a (δ/d2) H1).
    pose proof (@real_gt_half _ δ o3).
    rewrite<- c2.
    exact (@real_le_lt_lt _ (dist_ u a) (δ/d2) δ H2 H3).
    (**)

    pose proof (o4 x dis).
    (* prove a<=x<=b and f x > c then contradicts sup *)
    (** a<=x<=b *)
    assert (memx : a<=x<=b).

    destruct (real_is_max_Or (u - δ/d2) a x H) as [[l1 l2 ] | [r1 r2]].
    rewrite <- l1.
    split; auto with real.
    pose proof (@real_half_gt_zero _  δ o3).

    apply (real_lt_plus_lt (u-δ/d2) real_0_ (δ/d2)) in H1.
    ring_simplify in H1.
    destruct mem.
    pose proof (real_lt_le_lt (u-δ/d2) u b H1 H3). 
    auto with real.
    rewrite <-r1. split; auto with real.
    (** prove f x > c *)
    assert (f x > c).
    destruct (real_metric_Or (f u) (f x)) as [[H1 _] | [_ H1]].
    (*** when |f u - f x| = f u - x f *)
    rewrite H1 in H0.
    apply (real_lt_plus_r_lt (f x - eps/d2) (f u - f x) (eps/d2)) in H0.
    ring_simplify in H0.
    rewrite o2 in H0.
    replace (eps + c - eps/d2) with (c + (eps -eps/d2)) in H0 by ring.
    replace (eps - eps / d2) with (eps / d2) in H0 by auto with real.
    apply (real_lt_plus_r_lt c real_0_ (eps/d2)) in t1.
    ring_simplify in t1.
    exact (real_lt_lt_lt c (c+ eps/d2) (f x) t1 H0).
    (*** when |f u - f x| = f x - f u *)
    assert (f u <= f x) as H2 by auto with real.
    exact (real_lt_le_lt c (f u) (f x) r H2).


    (** finally....  x is the counter example of sup *)
    (*** prove x < u *)
    assert (x < u) as ord.
    destruct (real_is_max_Or (u-δ/d2) a x H) as [[l1 r1]|[l2 r2]].
    assert (u-δ/d2 +δ/d2 = x + δ/d2) as H2 by auto with real.
    ring_simplify in H2.
    rewrite H2.
    replace (δ/d2+x) with (x+δ/d2) by ring;
      replace x with (x+real_0_) at 1 by ring.
    apply real_lt_plus_lt; exact (@real_half_gt_zero _  δ o3).
    rewrite <- l2; exact mem2.

    (*** prove that x is an upperbound *)
    assert (W_is_upper_bound (fun z : real_ => a<=z<=b /\ f z < c) x).
    unfold W_is_upper_bound.
    intros z [q1 q2].

    destruct (real_total_order z x) as [to1 | [to2|to3]]; auto with real.
    destruct (real_total_order z u) as [tp1 | [tp2|tp3]]; auto with real.
    (**** when x < z < u, z is not in set *)
    assert (dist_ u z < δ).
    destruct (real_metric_Or u z) as [[cs11 cs12] | [_ cs2]].
    rewrite cs11.
    apply (real_lt_plus_lt (u-x-z) x z) in to3. 
    ring_simplify in to3.
    destruct (real_metric_Or u x) as [[cp11 cp12] | [_ cp2]].
    rewrite cp11 in dis.
    exact (real_lt_lt_lt (u-z) (u-x) δ to3 dis).
    contradict cp2; auto with real.
    contradict cs2; auto with real.
    
    
    pose proof (o4 z H2).
    (***** when x < z < u then f z > c thus not in set *)
    assert (f z > c) as noway.
    destruct (real_metric_Or (f u) (f z)) as [[H4 _]|[_ H4]].
    rewrite H4 in H3.
    apply (real_lt_plus_lt (f z - (eps / d2)) (f u - f z) (eps/d2)) in H3.
    ring_simplify in H3.
    rewrite o2 in H3.
    replace (-(eps/d2)+(eps+c)) with (eps - (eps/d2) + c) in H3 by ring.
    replace (eps - (eps/d2) + c) with (eps/d2 + c) in H3 by auto with real.
    replace (eps/d2+c) with (c+eps/d2) in H3 by ring.
    apply (real_lt_plus_lt c real_0_ (eps/d2)) in t1.
    ring_simplify in t1.
    exact (real_lt_lt_lt c (c+eps/d2) (f z) t1 H3).
    assert (f u <= f z) as H5 by auto with real.
    exact (real_lt_le_lt c (f u) (f z) r H5).

    contradict q2.
    auto with real.

    (**** when u = z *)
    rewrite <- tp2 in r; contradict r; auto with real.

    (**** when u < z *)
    contradict q.
    unfold W_is_sup.
    unfold W_is_upper_bound.
    red; intros.
    destruct H2 as [H2 _].
    pose proof (H2 z (conj q1 q2 )).
    contradict H3; auto with real.
    

    (*** as x < u is a upperbound, contradicts u to be sup *)
    contradict q.
    unfold W_is_sup.
    unfold W_is_upper_bound.
    red; intros.
    destruct H3 as [_ H3].
    pose proof (H3 x H2).
    contradict H4; auto with real.
  Qed.


  Definition opp_fun (f : real_ -> real_) : (real_ -> real_)
    := fun x => - f x.

  Lemma opp_fun_inv : forall f : real_ -> real_,
      forall x y, dist_ (f x) (f y) = dist_ (opp_fun f x) (opp_fun f y).
  Proof.
    intros.
    unfold opp_fun.
    pose proof (@real_metric_inv _ (- f x) (- f y) (f x + f y)) as A.
    replace (- f x + (f x + f y)) with (f y) in A  by ring.
    replace (- f y + (f x + f y)) with (f x) in A by ring.
    rewrite A.
    apply dist_symm.
  Qed.
  
  Lemma opp_fun_cont : forall f : real_ -> real_, continuous f -> continuous (opp_fun f).
  Proof.
    intros f cont.
    intros z ε p.
    unfold continuous in cont.
    pose proof (cont z ε p).
    destruct H as [δ [b c]].
    exists δ.
    split; auto.
    intros z' q; apply c in q.
    rewrite <- (opp_fun_inv f z z'); exact q.
  Qed.  

  Theorem W_IVT_r : forall f : real_ -> real_,
      continuous f ->
      forall a b, a < b -> 
                  forall c, f b < c < f a -> exists z', a<z'<b /\ f z' = c.
  Proof.
    intros.
    pose proof (opp_fun f) as g.
    pose proof (opp_fun_cont f H) as cont.
    assert (opp_fun f a < - c < opp_fun f b).
    destruct H1 as [o1 o2];  unfold opp_fun; split; auto with real.
    pose proof (W_IVT_l (opp_fun f) cont a b H0 (- c) H2).
    destruct H3.
    exists x.
    unfold opp_fun in H3.
    destruct H3.
    assert (- f x + f x + c = - c + f x + c) by auto with real.
    ring_simplify in H5.
    rewrite <- H5; auto.
  Qed.

  Theorem W_IVT : forall f : real_ -> real_,
      continuous f ->
      forall a b, a < b ->
                  forall c, (f a < c < f b \/ f b < c < f a) -> exists z', a<z'<b/\ f z' = c. 
  Proof.
    intros f H a b H0 c [l|r].
    exact (W_IVT_l f H a b H0 c l).
    exact (W_IVT_r f H a b H0 c r).
  Qed.

  (**********************************************************)
  (* PROOF OF CONSreal_RUCreal_IVE IVT                              *)
  (**********************************************************)
  Definition uniq (f : real_ -> real_) (a b : real_)
    := a<b /\ f a < real_0_ < f b /\ exists! z, (a<z<b) /\ f z = real_0_.

  Lemma uniq_pick : forall (f : real_ -> real_) (a b c d : real_), continuous f ->
                                                                uniq f a d ->
                                                                b < c -> a < b -> c < d  -> (f b < real_0_) \/ (real_0_ < f c).
  Proof.
    intros.
    destruct H0 as [o0 [[o1 o2] o3]].
    destruct (real_total_order (f b) real_0_) as [p|[p|p]];
      destruct (real_total_order (f c) real_0_) as [q|[q|q]].
    + (* f(b) < 0*)
      left; exact p.
    + (* f(b) < 0 *)
      left; exact p.
    +
      left; exact p.
      
    + (* f(b) = 0 and f(c) < 0: show that is a root in [c,d] 
     and that the root r is equal to b *)
      pose proof (W_IVT_l f H c d H3 real_0_ (conj q o2)) as [r [c1 c2]].
      destruct o3 as [x [[P1 P2] Q]].
      assert (a<r<d) as Xo.
      ++ split.
         +++ 
           destruct c1 as [l _].
           exact (real_lt_lt_lt a c r (real_lt_lt_lt a b c H2 H1) l).
         +++
           destruct c1 as [_ l].
           exact l.
           
           
      ++
        pose proof (Q r (conj Xo c2)) as H10.
        pose proof (Q b (conj (conj H2 (real_lt_lt_lt b c d H1 H3)) p)) as H11.
        destruct c1 as [c1 _].
        pose proof (real_lt_lt_lt b c r H1 c1) as C.
        rewrite <- H10 in C; rewrite <- H11 in C.
        contradict C; auto with real.

    + (* f b = 0, f c = 0 *)
      assert ( a < b < d).
      ++ split; auto.
         exact (real_lt_lt_lt b c d H1 H3).
      ++ assert (a < c < d).
         +++ split; auto.
             exact (real_lt_lt_lt a b c H2 H1).

         +++ destruct o3 as [p1 [[p2 p3] p4]].
             pose proof (p4 b (conj H0 p)) as X.
             pose proof (p4 c (conj H4 q)) as Y.
             rewrite <- X in H1; rewrite <- Y in H1; contradict H1; auto with real.

    + (* f(c) > 0 *)
      right; exact q.
      
    + (* f(b) > 0 and f(c) < 0 *)
      pose proof (W_IVT_l f H a b H2 real_0_ (conj o1 p)) as X.
      pose proof (W_IVT_l f H c d H3 real_0_ (conj q o2)) as Y.
      destruct X as [x1 [x2 x3]].
      destruct Y as [y1 [y2 y3]].
      assert (a<x1<d) as orx.
      ++ destruct x2; split; auto.
         exact (real_lt_lt_lt x1 b d H4 (real_lt_lt_lt b c d H1 H3)).
      ++ assert (a<y1<d) as ory.
         destruct y2; split; auto.
         exact (real_lt_lt_lt a c y1 (real_lt_lt_lt a b c H2 H1) H0).
         destruct o3 as [x [[P1 P2] Q]].
         pose proof (Q x1 (conj orx x3)) as xr.
         pose proof (Q y1 (conj ory y3)) as yr.
         assert (x1<y1) as or.
         +++
           destruct x2; destruct y2.
           apply (real_lt_lt_lt_lt x1 b c y1); auto with real.

         +++
           rewrite <- xr in or; rewrite <- yr in or; contradict or; auto with real.
    + (* f(c) = 0 *)
      pose proof (W_IVT_l f H a b H2 real_0_ (conj o1 p)) as X.
      destruct X as [x1 [x2 x3]].
      assert (a<x1<d) as orx.
      ++
        destruct x2; split; auto.
        exact (real_lt_lt_lt x1 b d H4 (real_lt_lt_lt b c d H1 H3)).
      ++


        destruct o3 as [x [[P1 P2] Q]].
        pose proof (Q x1 (conj orx x3)) as xr.
        pose proof (Q c (conj (conj (real_lt_lt_lt a b c H2 H1) H3) q)) as yr.
        destruct x2 as [_ x2].
        pose proof (real_lt_lt_lt x1 b c x2 H1) as C.
        rewrite <- xr in C; rewrite <- yr in C; contradict C; auto with real.

    + right; exact q.
  Qed.

  
  Lemma M_uniq_pick : forall (f : real_ -> real_) (a b c d : real_), continuous f ->
                                                                  uniq f a d ->
                                                                  b < c -> a < b -> c < d  -> M ({f b < real_0_}+{real_0_ < f c}).
  Proof.
    intros.
    apply (choose (f b < real_0_)  (real_0_ < f c)); auto with real.
    apply (uniq_pick f a b c d H H0 H1 H2 H3).
  Defined.


  Definition real_3 := @IZreal R 3.
  Definition dreal_3 : real_3 <> real_0_.
  Proof.
    assert (3>0)%Z.
    intuition.
    exact (real_gt_neq real_3 real_0_ (IZreal_pos 3 H)).
  Defined.

  Definition talve (a b c d : real_)
    := a <= b /\ b < c /\ c <= d /\ dist_ b c =(real_2 * dist_ a d) / dreal_3.
  Definition halve (a b c d : real_)
    := a <= b /\ b < c /\ c <= d /\ dist_ b c < ( dist_ a d) * (prec 1).
  Definition refining (a b c d : real_) (n:nat)
    := a <= b /\ b < c /\ c <= d /\ dist_ b c <= ( dist_ a d) * (prec n).

  Lemma real_le_mult_r_pos_le : forall c a b, c > real_0_ -> a <= b -> a*c <= b*c.
  Proof.
    intros c a b p q.
    destruct q as [q|q].
    apply (real_lt_mult_r_pos_lt a b c p) in q.
    left; exact q.
    right; auto with real.
  Qed.
  
  Lemma refining_S : forall a b c d e f n,
      refining a b e f n-> halve b c d e -> refining a c d f (S n).
  Proof.
    unfold refining.
    intros a b c d e f n r h.
    unfold halve in h.
    split.
    destruct r as [p _].
    destruct h as [q _].
    exact (real_le_le_le a b c p q).
    split.
    destruct r as [_ [p _]].
    destruct h as [_ [q _]].
    auto with real.
    split.
    destruct r as [_[_ [p _]]].
    destruct h as [_[_ [q _]]].
    exact (real_le_le_le d e f q p).
    
    destruct r as [_[_ [_ p]]].
    destruct h as [_[_ [_ q]]].

    pose proof (@prec_pos T 1).
    apply (real_le_mult_r_pos_le (prec 1)) in p; auto.
    pose proof
         (real_lt_le_lt (dist_ c d) (dist_ b e * prec 1) (dist_ a f * prec n * prec 1) q p).
    replace (dist_ a f * prec n * prec 1) with
        (dist_ a f * (prec n * prec 1))  in H0 by ring.
    rewrite <- (prec_hom n 1) in H0.
    rewrite (Nat.add_1_r n) in H0.  
    left; exact H0.
  Qed.
  (* Global Hint Resolve refining_S : real. *)


  
  Lemma talve_twice : forall a b c d e f, talve a b e f -> talve b c d e -> halve a c d f.
  Proof.
    unfold talve.
    intros a b c d e f p q.
    unfold halve.

    split.
    destruct p as [p _].
    destruct q as [q _].
    exact (real_le_le_le a b c p q).

    split.
    destruct q as [_ [q _]].
    exact q.

    split.
    destruct p as [_[_ [p _]]].
    destruct q as [_[_ [q _]]].
    exact (real_le_le_le d e f q p).

    assert (a < f) as QQ.
    destruct p as [p1[p2 [p3 _]]].
    pose proof (@real_le_lt_lt _ a b e p1 p2).
    exact (real_lt_le_lt a e f H p3).
    
    destruct p as [_[_ [_ p]]].
    destruct q as [_[qr [_ q]]].
    rewrite p in q.
    rewrite q.
    simpl.
    
    replace (real_2 * (real_2 * dist_ a f / dreal_3) / dreal_3) with
        (real_2 * (real_2 * dist_ a f */ dreal_3)*/dreal_3) by auto.
    
    replace (real_2 * (real_2 * dist_ a f */ dreal_3)*/dreal_3) with
        (dist_ a f * (real_2 * real_2  */ dreal_3 */dreal_3)) by ring.

    apply (real_lt_mult_pos_lt).

    + rewrite (lt_metric a f QQ).
      apply (real_lt_plus_lt (-a) a f) in QQ.
      ring_simplify in QQ.
      replace (f-a) with (-a+f) by ring; exact QQ.

    + assert (3 > 0)%Z as Q1 by intuition.
      apply (@IZreal_pos T 3) in Q1.
      replace (IZreal 3) with real_3 in Q1; auto.
      pose proof (@real_2_pos T) as Q2.
      apply (real_lt_mult_pos_move_rr_n real_2); auto with real.
      replace (real_2*real_2*/dreal_3*/dreal_3*real_2) with
          (real_2*real_2*real_2*/dreal_3*/dreal_3) by ring.
      replace  (real_2*real_2*real_2*/dreal_3*/dreal_3) with
          (real_2*real_2*real_2/dreal_3/dreal_3) by auto.
      apply (real_gt_mult_pos_move_rl real_3); auto with real.
      apply (real_gt_mult_pos_move_rl real_3); auto with real.

      replace (real_3*(real_3*real_1)) with (real_3*real_3) by ring.
      replace real_3 with (@IZreal R 3) by auto.
      replace real_2 with (@IZreal R 2) by auto.
      unfold IZreal.
      unfold IPreal.
      unfold IPreal_2.
      apply (real_lt_add_r ( - (real_1_ + real_1_) * (real_1_ + real_1_) * (real_1_ + real_1_))).
      replace ((real_1_ + real_1_) * (real_1_ + real_1_) * (real_1_ + real_1_) +
               - (real_1_ + real_1_) * (real_1_ + real_1_) * (real_1_ + real_1_)) with real_0_ by ring.
      replace ((real_1_ + (real_1_ + real_1_)) * (real_1_ + (real_1_ + real_1_)) +
  - (real_1_ + real_1_) * (real_1_ + real_1_) * (real_1_ + real_1_)) with real_1_ by ring.
      exact real_1_gt_0.
  Qed.

  Lemma inv_unif : forall a b (c : a <> real_0_) (d : b <> real_0_), a = b -> @real_inv _ a c = @real_inv _ b d.
  Proof.
    intros.
    induction H.
    assert (k : c = d) by apply irrl.
    induction k; auto.
  Qed.

  
  Definition trisect (f : real_ -> real_) (a b : real_)
    : continuous f -> uniq f a b -> [(a',b') | uniq f a' b' /\ talve a a' b' b  ].
  Proof.
    intros cont [t1 [ord H]].
    apply (mjoin (f ((real_2*a+b)/dreal_3) < real_0_) (real_0_ <(f ((a+real_2*b)/dreal_3)))).

    + intros [c|c].
      ++ exists ((real_2*a+b)/dreal_3); exists b.
         assert (a< ((real_2 * a + b) / dreal_3) < b).
         +++
           assert (3>0)%Z by intuition.
           apply (@IZreal_pos T 3) in H0.
           pose proof (@real_2_pos T).
           pose proof (@real_1_gt_0 R).
           
           pose proof (convexity a b (real_2) (real_1) t1 (H1) H2) as H3.
           unfold convex in H3.
           replace (b*real_1) with b in H3 by ring.
           replace (a*real_2) with (real_2*a) in H3 by ring.
           replace (real_2+real_1_) with (real_3 ) in H3.

           (* path on neq *)
           assert (real_2 + real_1 = real_3) as path by (unfold real_2, real_3; unfold IZreal;  unfold IPreal; unfold IPreal_2; ring).
           assert (real_2 + real_1 <> real_0_) as Path.
           rewrite path.
           auto with real.         
           rewrite <- (irrl _ Path (real_gt_neq (real_2 + real_1) real_0_
                                               (eq_ind (real_0_ + real_0_) (fun t : real_ => t < real_2 + real_1) (real_lt_lt_plus_lt real_0_ real_2 real_0_ real_1 (H1) H2) real_0_
                                                       (real_plus_unit real_0_)))) in H3.
           assert (/dreal_3 = /Path).
           apply inv_unif.
           (unfold real_2, real_3; unfold IZreal;  unfold IPreal; unfold IPreal_2; ring).
           unfold real_div; rewrite H4; unfold real_div in H3; exact H3.
           (unfold real_2, real_3; unfold IZreal;  unfold IPreal; unfold IPreal_2; ring).
           
         +++
           split. 
           ++++
             destruct H0.
             destruct ord.
             
             pose proof (W_IVT_l f cont ((real_2*a+b)/dreal_3) b H1 real_0_ (conj c H3)).
             destruct H4 as [x [[Q0 Q1] Q2]].

             unfold uniq.
             split; auto.
             split; auto.
             exists x.
             unfold unique.
             split; auto.
             intros x' [[P0 P1] P2].
             destruct H as [y [_ u2]].
             pose proof (u2 x (conj (conj (real_lt_lt_lt a ((real_2*a+b)/dreal_3) x H0 Q0) Q1) Q2)).
             pose proof (u2 x' (conj (conj (real_lt_lt_lt a ((real_2*a+b)/dreal_3) x' H0 P0) P1) P2)).
             rewrite<-H;rewrite<-H4; exact eq_refl.
           ++++
             unfold talve.
             destruct H0.
             split.
             left; exact H0.
             split.
             exact H1.
             split.
             right; exact eq_refl.
             rewrite (lt_metric ((real_2 * a + b) / dreal_3) b H1).
             rewrite (lt_metric a b t1).
             assert (3>0)%Z as H3 by intuition.
             apply (@IZreal_pos T 3) in H3.
             replace (b) with (b*real_1) at 1 by ring.
             replace real_1 with (/dreal_3*real_3) at 1 by auto with real.
             replace (  b * (/ dreal_3 * real_3)) with ((real_3*b)*/dreal_3) by ring.
             unfold real_div.
             unfold real_3.
             unfold real_2.
             unfold IZreal. 
             unfold IPreal.
             unfold IPreal_2.
             ring.


      ++ exists a.
         exists ((a+real_2*b)/dreal_3).

         assert (a< ((a +real_2* b) / dreal_3) < b).
         +++
           assert (3>0)%Z by intuition.
           apply (@IZreal_pos T 3) in H0.
           pose proof (@real_2_pos T).
           pose proof (@real_1_gt_0 R).
           
           pose proof (convexity a b (real_1) (real_2) t1 H2 (H1 )) as H3.
           unfold convex in H3.
           replace (a*real_1) with a in H3 by ring.
           replace (b*real_2) with (real_2*b) in H3 by ring.
           
           assert (real_1 + real_2 = real_3) as path by (unfold real_2, real_3; unfold IZreal;  unfold IPreal; unfold IPreal_2; ring).
           assert (real_1 + real_2 <> real_0_) as Path.
           rewrite path.
           auto with real.         
           rewrite <- (irrl _ Path (real_gt_neq (real_1 + real_2) real_0_
                                               (eq_ind (real_0_ + real_0_) (fun t : real_ => t < real_1 + real_2) (real_lt_lt_plus_lt real_0_ real_1 real_0_ real_2 H2 (H1 )) real_0_
                                                       (real_plus_unit real_0_)))) in H3.
           assert (/dreal_3 = /Path).
           apply inv_unif.
           (unfold real_2, real_3; unfold IZreal; unfold IPreal; unfold IPreal_2; ring).
           unfold real_div; rewrite H4; unfold real_div in H3; exact H3.
           
         +++
           split. 
           ++++
             destruct H0.
             destruct ord.
             
             pose proof (W_IVT_l f cont a ((a+real_2*b)/dreal_3) H0 real_0_ (conj H2 c)).
             destruct H4 as [x [[Q0 Q1] Q2]].

             unfold uniq.
             split; auto.
             split; auto.
             exists x.
             unfold unique.
             split; auto.
             intros x' [[P0 P1] P2].
             destruct H as [y [_ u2]].
             pose proof (u2 x (conj (conj Q0 (real_lt_lt_lt x ((a+real_2*b)/dreal_3) b Q1 H1)) Q2)) as H.
             pose proof (u2 x' (conj (conj P0 (real_lt_lt_lt x' ((a+real_2*b)/dreal_3) b P1 H1)) P2)) as H4.
             rewrite<-H;rewrite<-H4; exact eq_refl.
           ++++
             unfold talve.
             destruct H0.
             split.
             right; exact eq_refl.
             split.
             exact H0.
             split.
             left; exact H1.
             rewrite (lt_metric a ((a + real_2*b) / dreal_3) H0).
             rewrite (lt_metric a b t1).
             assert (3>0)%Z as H3 by intuition.
             apply (@IZreal_pos T 3) in H3.

             replace a with (a*real_1) at 2 by ring.
             replace real_1 with (/dreal_3*real_3) at 1 by auto with real.
             replace (  a * (/ dreal_3 * real_3)) with ((real_3*a)*/dreal_3) by ring.
             unfold real_div.
             unfold real_3.
             unfold real_2.
             unfold IZreal.
             unfold IPreal.
             unfold IPreal_2.
             ring.

    +
      apply (M_uniq_pick f a ((real_2*a+b)/dreal_3) ((a+real_2*b)/dreal_3) b cont (conj t1 (conj ord H))).
      
      ++
        apply (real_lt_plus_lt (a+b) a b) in t1.
        replace (a + b + a) with ((real_1 + real_1) * a + b) in t1 by ring.
        replace (a + b + b) with (a + (real_1 + real_1) * b) in t1 by ring.
        replace (real_1_+real_1) with (@real_2 R) in t1 by auto.
        assert (3>0)%Z by intuition.
        apply (@IZreal_pos T 3) in H0.
        assert (/dreal_3 > real_0_) by apply  real_pos_inv_pos2.


        apply (real_lt_mult_r_pos_lt) ; auto.

      ++
        assert (3>0)%Z by intuition.
        apply (@IZreal_pos T 3) in H0.
        pose proof (@real_2_pos T).
        pose proof (@real_1_gt_0 R).

        pose proof (convexity a b (real_2) (real_1) t1 (H1) H2) as H3.
        unfold convex in H3.

        assert (real_2 + real_1 = real_3) as path by (unfold real_2, real_3; unfold IZreal;  unfold IPreal; unfold IPreal_2; ring).
        assert (real_2 + real_1 <> real_0_) as Path.
        rewrite path.
        auto with real.         
        rewrite <- (irrl _  Path (real_gt_neq (real_2 + real_1) real_0_
                                             (eq_ind (real_0_ + real_0_) (fun t : real_ => t < real_2 + real_1) (real_lt_lt_plus_lt real_0_ real_2 real_0_ real_1 (H1) H2) real_0_
                                                     (real_plus_unit real_0_)))) in H3.
        assert (/dreal_3 = /Path).
        apply inv_unif.
        (unfold real_2, real_3; unfold IZreal;  unfold IPreal; unfold IPreal_2; ring).
        unfold real_div.
        rewrite H4.
        
        
        
        replace (b*real_1) with b in H3 by ring.
        replace (a*real_2) with (real_2*a) in H3 by ring.
        replace (real_2+real_1) with real_3 in H3.
        destruct H3; auto.
        
      ++
        assert (3>0)%Z by intuition.
        apply (@IZreal_pos T 3) in H0.
        pose proof (@real_2_pos T).
        pose proof (@real_1_gt_0 R).
        
        pose proof (convexity a b (real_1) (real_2) t1 H2 (H1)) as H3.
        unfold convex in H3.

        assert (real_1 + real_2 = real_3) as path by (unfold real_2, real_3; unfold IZreal;  unfold IPreal; unfold IPreal_2; ring).
        assert (real_1 + real_2 <> real_0_) as Path.
        rewrite path.
        auto with real.         
        rewrite <- (irrl _  Path (real_gt_neq (real_1 + real_2) real_0_
                                             (eq_ind (real_0_ + real_0_) (fun t : real_ => t < real_1 + real_2) (real_lt_lt_plus_lt real_0_ real_1 real_0_ real_2 H2 (H1)) real_0_
                                                     (real_plus_unit real_0_)))) in H3.
        assert (/dreal_3 = /Path).
        apply inv_unif.
        (unfold real_2, real_3; unfold IZreal;  unfold IPreal; unfold IPreal_2; ring).
        unfold real_div.
        rewrite H4.

        
        replace (a*real_1) with a in H3 by ring.
        replace (b*real_2) with (real_2*b) in H3 by ring.
        replace (real_2+real_1_) with real_3 in H3.
        destruct H3; auto.
        unfold real_3.
        unfold real_2.
        unfold IZreal.
        unfold IPreal.
        unfold IPreal_2.
        ring.
  Defined.


  Definition halving (f : real_ -> real_) (a b : real_)
    : continuous f -> uniq f a b -> [(a',b') | uniq f a' b' /\ halve a a' b' b  ].
  Proof.
    intros.
    pose proof (trisect f a b H H0) as one.
    apply (M_lift_dom ({a' : real_ & {b' : real_ | uniq f a' b' /\ talve a a' b' b}})); auto.
    intro Q.
    destruct Q as [x [y [P1 P2]]].
    
    pose proof (trisect f x y H P1) as X.
    apply (M_lift ({a' : real_  & ({ b' | uniq f a' b' /\ talve x a' b' y }) } )); auto.
    intros [x' [y' [P1' P2']]].
    exists x'.
    exists y'.
    split; auto.
    exact (talve_twice a x x' y' y b P2 P2').
  Defined.    
  Notation "{ ( a , b ) | P }" := (sigT (fun a => {b | P})) : type_scope.



  Local Hint Resolve @real_1_gt_0 : real.
  Lemma root_approx  (f : real_ -> real_)
        (cont : continuous f) (uni : uniq f real_0_ real_1)  (n : nat)
    : [(a,b)| uniq f a b /\ refining real_0_ a b real_1 n].
  Proof.
    induction n.
    + apply M_unit.
      exists real_0_; exists real_1.
      split; auto.
      unfold refining.
      split; auto with real.
      split.
      exact real_1_gt_0.
      split; auto with real.
      simpl.
      ring_simplify; right; exact eq_refl.

    + apply (M_lift_dom {a : real_ & {b : real_ | uniq f a b /\ refining real_0_ a b real_1 n} }); auto.
      intro X.
      destruct X as [x [y [p q]]].
      pose proof (halving f x y cont p).
      apply (M_lift ({ (a', b')| uniq f a' b' /\ halve x a' b' y})); auto.
      intros [x' [y' [p' q']]].
      exists x'; exists y'.
      split; auto.
      exact (refining_S real_0_ x x' y' y real_1 n q q').
  Defined. 


  Lemma CIVT : forall (f : real_ -> real_),
      continuous f -> uniq f real_0_ real_1 -> {z | real_0_<z<real_1 /\ f z = real_0_}.
  Proof.
    intros f cont u.
    apply real_mslimit_P.
    + (* root is unique that is uniq *)
      destruct u as [_ [_ un]]; exact un.
    + (* construct limit *)
      intro n.
      pose proof (root_approx f cont u (S n)).
      apply (M_lift ({(a, b)| uniq f a b /\ refining real_0_ a b real_1 (S n)})); auto.
      intros [x [y [p q]]].
      exists x.
      unfold uniq in p.
      destruct p as [u1 [u2 u3]].
      destruct u3 as [z un].
      exists z.
      unfold unique in un.
      destruct un as [ord uni].
      split.
      ++ split.
         +++ unfold refining in q.
             destruct q as [Q1 [Q2 [Q3 Q4]]].
             destruct ord as [[H1 H2] H3].
             pose proof (@real_le_lt_lt _ real_0_ x z Q1 H1) as P.
             pose proof (real_lt_le_lt z y real_1 H2 Q3) as Q.
             exact (conj P Q).

         +++ destruct ord as [_ H]; exact H.


      ++ unfold refining in q.
         destruct q as [Q1 [Q2 [Q3 Q4]]].
         rewrite dist_0_1 in Q4.
         ring_simplify in Q4.
         assert (dist_ x z <= dist_ x y ) as F.
         +++ pose proof (lt_metric x y Q2) as r1.
             destruct ord as [[p1 p2] _].
             pose proof (lt_metric x z p1) as r2.
             rewrite r1; rewrite r2.
             apply (real_lt_plus_r_lt (-x) z y) in p2.
             replace (z+-x) with (z-x) in p2 by ring.
             replace (y+-x) with (y-x) in p2 by ring.
             left; exact p2.
         +++ pose proof (real_le_le_le (dist_ x z) (dist_ x y) (prec (S n)) F Q4) as H.
             left; exact (@real_le_lt_lt _ (dist_ x z) (prec (S n)) (prec n) H (prec_S n)).

  Defined.
End IVT.

Global Hint Resolve @real_1_gt_0: real.
