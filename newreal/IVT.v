Require Import Base.
Require Import Kleene.
Require Import RealAxioms.
Require Import RealRing.
Require Import RealSimpleLemmas.
Require Import Minmax.

Local Open Scope Real_scope.


Lemma sandwich : forall a b, (forall ε, ε > Real0 -> a-ε < b < a+ε) -> b = a.
Proof.
  intros a b e.
  destruct (Realtotal_order a b) as [c1|[c2|c3]].
  pose proof (padding b a c1) as H.
  destruct H as [eps [p1 p2]].
  pose proof (e (eps / dReal2) (Realhalf_gt_zero eps p1)).
  rewrite p2 in H.
  destruct H.
  replace (a+eps/dReal2) with (eps/dReal2+a) in H0 by ring.
  apply (Reallt_plus_lt (-a)) in H0.
  replace ( - a + (eps + a)) with eps in H0 by ring.
  replace ( - a + (eps / dReal2 + a)) with (eps / dReal2) in H0 by ring.
  contradict H0.
  pose proof (Realgt_half eps p1).
  auto with Realiny.

  auto.
  
  pose proof (padding a b c3) as H.
  destruct H as [eps [p1 p2]].
  pose proof (e (eps / dReal2) (Realhalf_gt_zero eps p1)).
  rewrite p2 in H.
  destruct H.
  apply (Reallt_plus_lt (-b)) in H.
  apply (Reallt_plus_lt (eps/dReal2)) in H.
  replace (b+eps/dReal2) with (eps/dReal2+b) in H by ring.
  apply (Reallt_plus_lt (-b)) in H0.
  replace (eps / dReal2 + (- b + b)) with (eps/dReal2) in H by ring.
  replace ( eps / dReal2 + (- b + (eps + b - eps / dReal2))) with (eps) in H by ring.
  contradict H.
  pose proof (Realgt_half eps p1).
  auto with Realiny.
Qed.  

  

Definition continuous_at (f : Real -> Real) (z : Real) : Prop
  := forall ε, ε > Real0 ->
               exists δ, δ > Real0 /\
                         (forall z', dist z z' < δ -> dist (f z) (f z') < ε).

Definition continuous (f : Real -> Real) : Prop := forall z, continuous_at f z.

(* proved by Dongseong and written by Sewon *)
Theorem W_IVT_l : forall f : Real -> Real,
  continuous f ->
  forall a b, a < b -> 
              forall c, f a < c < f b -> exists z', a < z' < b /\ f z' = c.
Proof.
  intros f cont a b o c p.
  assert (W_nemp (fun z => a<=z<=b /\ f z < c)) as nepty.
  exists a; constructor 1; auto with Realiny.
  destruct p as [t1 t2]; exact t1.
  assert (W_upbd (fun z => a<=z<=b /\ f z < c)) as upbd.
  exists b.
  unfold W_upb; intros b' p'; destruct p' as [[p1 p2] p3]; exact p2.
  (* u := sup { z | f z < c } *)
  destruct (W_complete (fun z => a<=z<=b /\ f z < c) nepty upbd) as [u q].

  (* prove a<=u<=b *)
  assert (mem : a <= u <= b).
  destruct (Realtotal_order a u) as [t1 | [t2 | t3]].
  split; auto with Realiny.
  destruct (Realtotal_order u b) as [tt1 | [tt2 | tt3]]; auto with Realiny.
  (** when u>b => contradict sup *)
  assert (upb_alt : W_upb (fun z => a<=z<=b /\ f z < c) b).
  unfold W_upb.
  intros z [[mem1 mem2] cond]; auto with Realiny.
  contradict q.
  unfold W_sup.
  intuition.
  pose proof (H3 b upb_alt) as contra.
  contradict contra.
  auto with Realiny.

  split; auto with Realiny.
  rewrite <- t2; auto with Realiny.

  (** when u < a => contradict sup *)

  contradict q.
  unfold W_sup; intuition.
  unfold W_upb in H2.  
  destruct nepty as [t1 t2].
  pose proof (H2 t1 t2).
  destruct t2 as [[qq1 pp2] qq2].
  pose proof (Realle_le_le a t1 u qq1 H).
  contradict H4; auto with Realiny.


  
  (* Casing on f u >? 0 *)
  destruct (Realtotal_order (f u) c) as [l | [m | r]].
  (** when f u < c, pick small u + e such that f u+e < c => contradict *)
  (** because u+e is in the set while u is the supremum of the set     *)
  assert (mem2 : u < b).
  destruct mem as [e [k | v]].
  exact k.
  rewrite v in l; destruct p as [p1 p2].
  contradict l; auto with Realiny.
  
  destruct (padding c (f u) l) as [eps [o1 o2]].
  assert (t1 : eps / dReal2 > Real0) by auto with Realiny.
  destruct (cont u (eps/dReal2) t1) as [δ [o3 o4]].
  destruct (W_min (u+δ/dReal2) b) as [x  H].
  
  assert (dis : dist u x < δ).
  (**)
  destruct (Realtotal_order (u+δ/dReal2) b) as [l1 |[ l2 | l3]];
    destruct H as [r1 [r2 r3]].
  
  apply r3 in l1.
  rewrite l1.
  replace u with (Real0+u) at 1 by ring;
    replace (u+δ/dReal2) with (δ/dReal2+u) by ring.
  rewrite <- (Realmetric_inv Real0 (δ/dReal2) u).

  destruct (dist_prop Real0 (δ/dReal2)) as [_[_ u3]];
    rewrite (u3 (Realhalf_gt_zero δ o3)).
  ring_simplify; apply Realgt_half; exact o3.

  apply r2 in l2.
  rewrite l2.
  replace u with (u+Real0) at 1 by ring.
  rewrite <- (Realmetric_plus_inv Real0 (δ/dReal2) u).
  destruct (dist_prop Real0 (δ/dReal2)) as [_[_ u3]];
    rewrite (u3 (Realhalf_gt_zero δ o3)).
  ring_simplify; apply Realgt_half; exact o3.

  pose proof (r1 l3) as H.
  rewrite H.
  pose proof (Realmetric_inv Real0 (b-u) u) as H1.
  replace (Real0+u) with u in H1 by ring.
  replace (b-u+u) with b in H1 by ring.
  rewrite <- H1.
  assert (b-u > Real0) as H2 by auto with Realiny.
  destruct (dist_prop Real0 (b-u)) as [_[_ u3]].
  apply u3 in H2.
  rewrite H2.
  assert ((u+δ/dReal2) +-u > b+-u).
  apply Reallt_plus_r_lt.
  exact l3.
  replace ( u + δ / dReal2 + - u) with (δ/dReal2) in H0 by ring.
  replace (b+-u) with (b-u) in H0 by ring.
  ring_simplify.
  pose proof (Realgt_half δ o3).
  exact (Reallt_lt_lt (b-u) (δ/dReal2) δ H0 H3).
  (**)

  pose proof (o4 x dis).
  (* prove a<=x<=b and f x < c then contradicts sup *)
  (**)
  assert (memx : a<=x<=b).
  destruct mem as [mem _].
  destruct H as [l1 [l2 l3]].
  destruct (Realtotal_order (u+δ/dReal2) b) as [r1 | [r2 | r3]].
  (*** when u+δ/2 <b *)
  split.
  apply l3 in r1.
  rewrite r1.
  pose proof (Realhalf_gt_zero δ o3).
  assert (u+δ/dReal2 > u+Real0).
  apply (Reallt_plus_lt); auto.
  replace (u+Real0) with u in H1 by ring.
  pose proof (Realle_lt_lt a u (u+δ/dReal2) mem H1); auto with Realiny.

  pose proof (l3 r1) as H1; rewrite H1.
  auto with Realiny.

  (*** when u+δ/2 =b *)
  pose proof (l2 r2) as H; rewrite H.
  split.
  pose proof (Realhalf_gt_zero δ o3).
  assert (u+δ/dReal2 > u+Real0).
  apply (Reallt_plus_lt); auto.
  replace (u+Real0) with u in H2 by ring.
  pose proof (Realle_lt_lt a u (u+δ/dReal2) mem H2); auto with Realiny.
  rewrite <- r2; right; exact eq_refl.

  (*** when u+δ/2 > b *)
  pose proof (l1 r3) as H; rewrite H.
  split; auto with Realiny.
  (**)

  assert (f x < c).
  destruct (Realtotal_order (f u) (f x)) as [l1 | [l2 | l3]].
  destruct (dist_prop (f u) (f x)) as [_ [_ r3]];
    pose proof (r3 l1).
  rewrite H1 in H0.
  rewrite o2.
  pose proof (Reallt_plus_lt  (f u) (f x - f u) (eps/dReal2) H0).
  ring_simplify in H2.
  pose proof (Realgt_half eps o1).
  assert (f u + eps > f u + eps / dReal2).
  apply (Reallt_plus_lt); auto.
  replace (eps + f u) with (f u + eps) by ring.
  apply (Reallt_lt_lt (f x) (f u + eps / dReal2) (f u + eps)).
  exact H2.
  exact H4.

  rewrite <- l2; exact l.

  exact (Reallt_lt_lt (f x) (f u) c l3 l).

  (** finally....  x is the counter example of sup *)
  contradict q.
  unfold W_sup.
  unfold not; intros.
  destruct H2 as [H2 _].
  unfold W_upb in H2.
  pose proof (H2 x (conj memx H1)).
  destruct (W_m_or (u+δ/dReal2) b x H) as [p1 | p2].
  rewrite <- p1 in H3.
  destruct H3.
  apply (Reallt_plus_lt (-u) (u+δ/dReal2) u) in H3.
  ring_simplify in H3.
  pose proof (Realhalf_gt_zero δ o3).
  contradict H4.
  exact (Reallt_nlt (δ/dReal2) Real0 H3).
  apply (Realeq_plus_eq (u+δ/dReal2) u (-u)) in H3.
  ring_simplify in H3.
  pose proof (Realhalf_gt_zero δ o3).
  rewrite H3 in H4.
  contradict H4.
  exact (Realngt_triv Real0).
  rewrite <- p2 in H3.
  contradict H3; auto with Realiny.

  (** when f u = c *)
  exists u.
  split.
  destruct mem as [[o1|o1] [o2|o2]].
  exact (conj o1 o2).
  destruct p.
  rewrite o2 in m.
  contradict m.
  auto with Realiny.
  rewrite <- o1 in m.
  contradict m.
  destruct p.
  auto with Realiny.
  rewrite o1 in o; rewrite <- o2 in o.
  contradict o; auto with Realiny.
  exact m.

  (** when f u > c *)
  assert (mem2 : a < u).
  destruct mem as [[k| v] _].
  exact k.
  rewrite <-v in r; destruct p as [p1 p2].
  contradict r; auto with Realiny.
  
  destruct (padding (f u) c r) as [eps [o1 o2]].
  assert (t1 : eps / dReal2 > Real0) by auto with Realiny.
  destruct (cont u (eps/dReal2) t1) as [δ [o3 o4]].
  destruct (W_max (u-δ/dReal2) a) as [x  H].
  
  assert (dis : dist u x < δ).
  (**)
  destruct (W_M_Or (u-δ/dReal2) a x H) as [[c1 p1] | [c2 p2]].
  (* case where Max is u-δ/dReal2 *)
  rewrite <- c1.
  rewrite  (Realmetric_inv u (u-δ/dReal2) (δ/dReal2)).
  replace (u - δ / dReal2 + δ / dReal2) with u by ring.
  rewrite (Realmetric_inv (u+δ/dReal2) u (-u)).
  replace (u + δ / dReal2 + - u) with (δ/dReal2) by ring;
    replace (u+-u) with Real0 by ring.
  destruct (dist_prop Real0 (δ/dReal2)) as [_[_ u3]].
  rewrite dist_symm.
    rewrite (u3 (Realhalf_gt_zero δ o3)).
  ring_simplify; apply Realgt_half; exact o3.

  (* case where Max is a *)
  pose proof (Realhalf_gt_zero δ o3).
  apply (Reallt_plus_lt u (Real0) (δ/dReal2)) in H0.
  ring_simplify in H0.
  pose proof (Reallt_le a (u+δ/dReal2)  (Reallt_lt_lt a u (u+δ/dReal2) mem2 H0)) as R.
  assert (u - δ / dReal2 <= a <= u + δ / dReal2).
  split; auto with Realiny.
  pose proof (Realmetric_sand u a (δ/dReal2) H1).
  pose proof (Realgt_half δ o3).
  rewrite<- c2.
  exact (Realle_lt_lt (dist u a) (δ/dReal2) δ H2 H3).
  (**)

  pose proof (o4 x dis).
  (* prove a<=x<=b and f x > c then contradicts sup *)
  (** a<=x<=b *)
  assert (memx : a<=x<=b).

  destruct (W_M_Or (u - δ/dReal2) a x H) as [[l1 l2 ] | [r1 r2]].
  rewrite <- l1.
  split; auto with Realiny.
  pose proof (Realhalf_gt_zero δ o3).

  apply (Reallt_plus_lt (u-δ/dReal2) Real0 (δ/dReal2)) in H1.
  ring_simplify in H1.
  destruct mem.
  pose proof (Reallt_le_lt (u-δ/dReal2) u b H1 H3). 
  auto with Realiny.
  rewrite <-r1. split; auto with Realiny.
  (** prove f x > c *)
  assert (f x > c).
  destruct (Realmetric_Or (f u) (f x)) as [[H1 _] | [_ H1]].
  (*** when |f u - f x| = f u - x f *)
  rewrite H1 in H0.
  apply (Reallt_plus_r_lt (f x - eps/dReal2) (f u - f x) (eps/dReal2)) in H0.
  ring_simplify in H0.
  rewrite o2 in H0.
  replace (eps + c - eps/dReal2) with (c + (eps -eps/dReal2)) in H0 by ring.
  replace (eps - eps / dReal2) with (eps / dReal2) in H0 by auto with Realiny.
  apply (Reallt_plus_r_lt c Real0 (eps/dReal2)) in t1.
  ring_simplify in t1.
  exact (Reallt_lt_lt c (c+ eps/dReal2) (f x) t1 H0).
  (*** when |f u - f x| = f x - f u *)
  assert (f u <= f x) as H2 by auto with Realiny.
  exact (Reallt_le_lt c (f u) (f x) r H2).


  (** finally....  x is the counter example of sup *)
  (*** prove x < u *)
  assert (x < u) as ord.
  destruct (W_M_Or (u-δ/dReal2) a x H) as [[l1 r1]|[l2 r2]].
  assert (u-δ/dReal2 +δ/dReal2 = x + δ/dReal2) as H2 by auto with Realiny.
  ring_simplify in H2.
  rewrite H2.
  replace (δ/dReal2+x) with (x+δ/dReal2) by ring;
    replace x with (x+Real0) at 1 by ring.
  apply Reallt_plus_lt; exact (Realhalf_gt_zero δ o3).
  rewrite <- l2; exact mem2.

  (*** prove that x is an upperbound *)
  assert (W_upb (fun z : Real => a<=z<=b /\ f z < c) x).
  unfold W_upb.
  intros z [q1 q2].

  destruct (Realtotal_order z x) as [to1 | [to2|to3]]; auto with Realiny.
  destruct (Realtotal_order z u) as [tp1 | [tp2|tp3]]; auto with Realiny.
  (**** when x < z < u, z is not in set *)
  assert (dist u z < δ).
  destruct (Realmetric_Or u z) as [[cs11 cs12] | [_ cs2]].
  rewrite cs11.
  apply (Reallt_plus_lt (u-x-z) x z) in to3. 
  ring_simplify in to3.
  destruct (Realmetric_Or u x) as [[cp11 cp12] | [_ cp2]].
  rewrite cp11 in dis.
  exact (Reallt_lt_lt (u-z) (u-x) δ to3 dis).
  contradict cp2; auto with Realiny.
  contradict cs2; auto with Realiny.
  
  
  pose proof (o4 z H2).
  (***** when x < z < u then f z > c thus not in set *)
  assert (f z > c) as noway.
  destruct (Realmetric_Or (f u) (f z)) as [[H4 _]|[_ H4]].
  rewrite H4 in H3.
  apply (Reallt_plus_lt (f z - (eps / dReal2)) (f u - f z) (eps/dReal2)) in H3.
  ring_simplify in H3.
  rewrite o2 in H3.
  replace (-(eps/dReal2)+(eps+c)) with (eps - (eps/dReal2) + c) in H3 by ring.
  replace (eps - (eps/dReal2) + c) with (eps/dReal2 + c) in H3 by auto with Realiny.
  replace (eps/dReal2+c) with (c+eps/dReal2) in H3 by ring.
  apply (Reallt_plus_lt c Real0 (eps/dReal2)) in t1.
  ring_simplify in t1.
  exact (Reallt_lt_lt c (c+eps/dReal2) (f z) t1 H3).
  assert (f u <= f z) as H5 by auto with Realiny.
  exact (Reallt_le_lt c (f u) (f z) r H5).

  contradict q2.
  auto with Realiny.

  (**** when u = z *)
  rewrite <- tp2 in r; contradict r; auto with Realiny.

  (**** when u < z *)
  contradict q.
  unfold W_sup.
  unfold W_upb.
  red; intros.
  destruct H2 as [H2 _].
  pose proof (H2 z (conj q1 q2 )).
  contradict H3; auto with Realiny.
  

  (*** as x < u is a upperbound, contradicts u to be sup *)
  contradict q.
  unfold W_sup.
  unfold W_upb.
  red; intros.
  destruct H3 as [_ H3].
  pose proof (H3 x H2).
  contradict H4; auto with Realiny.
Qed.


Definition opp_fun (f : Real -> Real) : (Real -> Real)
  := fun x => - f x.

Lemma opp_fun_inv : forall f : Real -> Real,
    forall x y, dist (f x) (f y) = dist (opp_fun f x) (opp_fun f y).
Proof.
  intros.
  unfold opp_fun.
  pose proof (Realmetric_inv (- f x) (- f y) (f x + f y)) as A.
  replace (- f x + (f x + f y)) with (f y) in A  by ring.
  replace (- f y + (f x + f y)) with (f x) in A by ring.
  rewrite A.
  apply dist_symm.
Qed.
  
Lemma opp_fun_cont : forall f : Real -> Real, continuous f -> continuous (opp_fun f).
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

Theorem W_IVT_r : forall f : Real -> Real,
  continuous f ->
  forall a b, a < b -> 
              forall c, f b < c < f a -> exists z', a<z'<b /\ f z' = c.
Proof.
  intros.
  pose proof (opp_fun f) as g.
  pose proof (opp_fun_cont f H) as cont.
  assert (opp_fun f a < - c < opp_fun f b).
  destruct H1 as [o1 o2];  unfold opp_fun; split; auto with Realiny.
  pose proof (W_IVT_l (opp_fun f) cont a b H0 (- c) H2).
  destruct H3.
  exists x.
  unfold opp_fun in H3.
  destruct H3.
  assert (- f x + f x + c = - c + f x + c) by auto with Realiny.
  ring_simplify in H5.
  rewrite <- H5; auto.
Qed.

Theorem W_IVT : forall f : Real -> Real,
    continuous f ->
    forall a b, a < b ->
                forall c, (f a < c < f b \/ f b < c < f a) -> exists z', a<z'<b/\ f z' = c. 
Proof.
  intros f H a b H0 c [l|r].
  exact (W_IVT_l f H a b H0 c l).
  exact (W_IVT_r f H a b H0 c r).
Qed.

(**********************************************************)
(* PROOF OF CONSRealRUCRealIVE IVT                              *)
(**********************************************************)
Definition uniq (f : Real -> Real) (a b : Real)
  := a<b /\ f a < Real0 < f b /\ exists! z, (a<z<b) /\ f z = Real0.

Lemma uniq_pick : forall (f : Real -> Real) (a b c d : Real), continuous f ->
    uniq f a d ->
    b < c -> a < b -> c < d  -> (f b < Real0) \/ (Real0 < f c).
Proof.
  intros.
  destruct H0 as [o0 [[o1 o2] o3]].
  destruct (Realtotal_order (f b) Real0) as [p|[p|p]];
    destruct (Realtotal_order (f c) Real0) as [q|[q|q]].
  + (* f(b) < 0*)
    left; exact p.
  + (* f(b) < 0 *)
    left; exact p.
  +
    left; exact p.
    
  + (* f(b) = 0 and f(c) < 0: show that is a root in [c,d] 
     and that the root r is equal to b *)
    pose proof (W_IVT_l f H c d H3 Real0 (conj q o2)) as [r [c1 c2]].
    destruct o3 as [x [[P1 P2] Q]].
    assert (a<r<d) as Xo.
    ++ split.
       +++ 
         destruct c1 as [l _].
         exact (Reallt_lt_lt a c r (Reallt_lt_lt a b c H2 H1) l).
       +++
         destruct c1 as [_ l].
         exact l.
         
         
    ++
      pose proof (Q r (conj Xo c2)) as H10.
      pose proof (Q b (conj (conj H2 (Reallt_lt_lt b c d H1 H3)) p)) as H11.
      destruct c1 as [c1 _].
      pose proof (Reallt_lt_lt b c r H1 c1) as C.
      rewrite <- H10 in C; rewrite <- H11 in C.
      contradict C; auto with Realiny.

  + (* f b = 0, f c = 0 *)
    assert ( a < b < d).
    ++ split; auto.
       exact (Reallt_lt_lt b c d H1 H3).
    ++ assert (a < c < d).
       +++ split; auto.
           exact (Reallt_lt_lt a b c H2 H1).

       +++ destruct o3 as [p1 [[p2 p3] p4]].
           pose proof (p4 b (conj H0 p)) as X.
           pose proof (p4 c (conj H4 q)) as Y.
           rewrite <- X in H1; rewrite <- Y in H1; contradict H1; auto with Realiny.

  + (* f(c) > 0 *)
    right; exact q.
   
  + (* f(b) > 0 and f(c) < 0 *)
    pose proof (W_IVT_l f H a b H2 Real0 (conj o1 p)) as X.
    pose proof (W_IVT_l f H c d H3 Real0 (conj q o2)) as Y.
    destruct X as [x1 [x2 x3]].
    destruct Y as [y1 [y2 y3]].
    assert (a<x1<d) as orx.
    ++ destruct x2; split; auto.
       exact (Reallt_lt_lt x1 b d H4 (Reallt_lt_lt b c d H1 H3)).
    ++ assert (a<y1<d) as ory.
       destruct y2; split; auto.
       exact (Reallt_lt_lt a c y1 (Reallt_lt_lt a b c H2 H1) H0).
       destruct o3 as [x [[P1 P2] Q]].
       pose proof (Q x1 (conj orx x3)) as xr.
       pose proof (Q y1 (conj ory y3)) as yr.
       assert (x1<y1) as or.
       +++
         destruct x2; destruct y2.
         apply (Reallt_lt_lt_lt x1 b c y1); auto with Realiny.

       +++
         rewrite <- xr in or; rewrite <- yr in or; contradict or; auto with Realiny.
  + (* f(c) = 0 *)
    pose proof (W_IVT_l f H a b H2 Real0 (conj o1 p)) as X.
    destruct X as [x1 [x2 x3]].
    assert (a<x1<d) as orx.
    ++
      destruct x2; split; auto.
      exact (Reallt_lt_lt x1 b d H4 (Reallt_lt_lt b c d H1 H3)).
    ++


      destruct o3 as [x [[P1 P2] Q]].
      pose proof (Q x1 (conj orx x3)) as xr.
      pose proof (Q c (conj (conj (Reallt_lt_lt a b c H2 H1) H3) q)) as yr.
      destruct x2 as [_ x2].
      pose proof (Reallt_lt_lt x1 b c x2 H1) as C.
      rewrite <- xr in C; rewrite <- yr in C; contradict C; auto with Realiny.

  + right; exact q.
Qed.

    
Lemma M_uniq_pick : forall (f : Real -> Real) (a b c d : Real), continuous f ->
    uniq f a d ->
    b < c -> a < b -> c < d  -> M ({f b < Real0}+{Real0 < f c}).
Proof.
  intros.
  apply (choose (f b < Real0)  (Real0 < f c)); auto with Realiny.
  apply (uniq_pick f a b c d H H0 H1 H2 H3).
Defined.


Definition Real3 := IZReal 3.
Definition dReal3 : Real3 <> Real0.
Proof.
  assert (3>0)%Z.
  intuition.
  exact (Realgt_neq Real3 Real0 (IZReal_pos 3 H)).
Defined.

Definition talve (a b c d : Real)
  := a <= b /\ b < c /\ c <= d /\ dist b c =(Real2 * dist a d) / dReal3.
Definition halve (a b c d : Real)
  := a <= b /\ b < c /\ c <= d /\ dist b c < ( dist a d) * (prec 1).
Definition refining (a b c d : Real) (n:nat)
  := a <= b /\ b < c /\ c <= d /\ dist b c <= ( dist a d) * (prec n).

Lemma Realle_mult_r_pos_le : forall c a b, c > Real0 -> a <= b -> a*c <= b*c.
Proof.
  intros c a b p q.
  destruct q as [q|q].
  apply (Reallt_mult_r_pos_lt a b c p) in q.
  left; exact q.
  right; auto with Realiny.
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
  exact (Realle_le_le a b c p q).
  split.
  destruct r as [_ [p _]].
  destruct h as [_ [q _]].
  auto with Realiny.
  split.
  destruct r as [_[_ [p _]]].
  destruct h as [_[_ [q _]]].
  exact (Realle_le_le d e f q p).
  
  destruct r as [_[_ [_ p]]].
  destruct h as [_[_ [_ q]]].

  pose proof (prec_pos 1).
  apply (Realle_mult_r_pos_le (prec 1)) in p; auto.
  pose proof
       (Reallt_le_lt (dist c d) (dist b e * prec 1) (dist a f * prec n * prec 1) q p).
  replace (dist a f * prec n * prec 1) with
      (dist a f * (prec n * prec 1))  in H0 by ring.
  rewrite <- (prec_hom n 1) in H0.
  rewrite (Nat.add_1_r n) in H0.  
  left; exact H0.
Qed.
Hint Resolve refining_S : Realiny.


  
Lemma talve_twice : forall a b c d e f, talve a b e f -> talve b c d e -> halve a c d f.
Proof.
  unfold talve.
  intros a b c d e f p q.
  unfold halve.

  split.
  destruct p as [p _].
  destruct q as [q _].
  exact (Realle_le_le a b c p q).

  split.
  destruct q as [_ [q _]].
  exact q.

  split.
  destruct p as [_[_ [p _]]].
  destruct q as [_[_ [q _]]].
  exact (Realle_le_le d e f q p).

  assert (a < f) as QQ.
  destruct p as [p1[p2 [p3 _]]].
  pose proof (Realle_lt_lt a b e p1 p2).
  exact (Reallt_le_lt a e f H p3).
  
  destruct p as [_[_ [_ p]]].
  destruct q as [_[qr [_ q]]].
  rewrite p in q.
  rewrite q.
  simpl.
  
  replace (Real2 * (Real2 * dist a f / dReal3) / dReal3) with
      (Real2 * (Real2 * dist a f */ dReal3)*/dReal3) by auto.
  
  replace (Real2 * (Real2 * dist a f */ dReal3)*/dReal3) with
      (dist a f * (Real2 * Real2  */ dReal3 */dReal3)) by ring.

  apply (Reallt_mult_pos_lt).

  + rewrite (lt_metric a f QQ).
    apply (Reallt_plus_lt (-a) a f) in QQ.
    ring_simplify in QQ.
    replace (f-a) with (-a+f) by ring; exact QQ.

  + assert (3 > 0)%Z as Q1 by intuition.
    apply (IZReal_pos 3) in Q1.
    replace (IZReal 3) with Real3 in Q1; auto.
    pose proof Real2_pos as Q2.
    apply (Reallt_mult_pos_move_rr_n Real2); auto with Realiny.
    replace (Real2*Real2*/dReal3*/dReal3*Real2) with
        (Real2*Real2*Real2*/dReal3*/dReal3) by ring.
    replace  (Real2*Real2*Real2*/dReal3*/dReal3) with
        (Real2*Real2*Real2/dReal3/dReal3) by auto.
    apply (Realgt_mult_pos_move_rl Real3); auto with Realiny.
    apply (Realgt_mult_pos_move_rl Real3); auto with Realiny.

    replace (Real3*(Real3*Real1)) with (Real3*Real3) by ring.
    replace Real3 with (IZReal 3) by auto.
    replace Real2 with (IZReal 2) by auto.
    unfold IZReal.
    unfold IPReal.
    unfold IPReal_2.
    ring_simplify.
    replace ((Real1 + Real1) * ((Real1 + Real1) * (Real1 + Real1))) with
        (Real0 + ((Real1 + Real1) * ((Real1 + Real1) * (Real1 + Real1)))) at 2  by ring.
    apply Reallt_plus_r_lt; exact Real1_gt_Real0.
Qed.



Definition trisect (f : Real -> Real) (a b : Real)
  : continuous f -> uniq f a b -> [(a',b') | uniq f a' b' /\ talve a a' b' b  ].
Proof.
  intros cont [t1 [ord H]].
  apply (mjoin (f ((Real2*a+b)/dReal3) < Real0) (Real0 <(f ((a+Real2*b)/dReal3)))).

  + intros [c|c].
    ++ exists ((Real2*a+b)/dReal3); exists b.
       assert (a< ((Real2 * a + b) / dReal3) < b).
       +++
         assert (3>0)%Z by intuition.
         apply (IZReal_pos 3) in H0.
         pose proof (Real2_pos).
         pose proof (Real1_gt_Real0).
         
         pose proof (convexity a b (Real2) (Real1) t1 H1 H2) as H3.
         unfold convex in H3.
         replace (b*Real1) with b in H3 by ring.
         replace (a*Real2) with (Real2*a) in H3 by ring.
         replace (Real2+Real1) with Real3 in H3.

         (* path on neq *)
         assert (Real2 + Real1 = Real3) as path by (unfold Real2, Real3; unfold IZReal; unfold IPReal; unfold IPReal_2; ring).
         assert (Real2 + Real1 <> Real0) as Path.
         rewrite path.
         auto with Realiny.         
         rewrite <- (neq_path (Real2+Real1) Real0 Path (Realgt_neq (Real2 + Real1) Real0
         (eq_ind (Real0 + Real0) (fun t : Real => t < Real2 + Real1) (Reallt_lt_plus_lt Real0 Real2 Real0 Real1 H1 H2) Real0
                 (Realplus_unit Real0)))) in H3.
         assert (/dReal3 = /Path).
         apply inv_unif.
         (unfold Real2, Real3; unfold IZReal; unfold IPReal; unfold IPReal_2; ring).
         unfold Realdiv; rewrite H4; unfold Realdiv in H3; exact H3.
         (unfold Real2, Real3; unfold IZReal; unfold IPReal; unfold IPReal_2; ring).
     
       +++
         split. 
           ++++
             destruct H0.
             destruct ord.
             
             pose proof (W_IVT_l f cont ((Real2*a+b)/dReal3) b H1 Real0 (conj c H3)).
             destruct H4 as [x [[Q0 Q1] Q2]].

             unfold uniq.
             split; auto.
             split; auto.
             exists x.
             unfold unique.
             split; auto.
             intros x' [[P0 P1] P2].
             destruct H as [y [_ u2]].
             pose proof (u2 x (conj (conj (Reallt_lt_lt a ((Real2*a+b)/dReal3) x H0 Q0) Q1) Q2)).
             pose proof (u2 x' (conj (conj (Reallt_lt_lt a ((Real2*a+b)/dReal3) x' H0 P0) P1) P2)).
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
             rewrite (lt_metric ((Real2 * a + b) / dReal3) b H1).
             rewrite (lt_metric a b t1).
             assert (3>0)%Z as H3 by intuition.
             apply (IZReal_pos 3) in H3.
             replace (b) with (b*Real1) at 1 by ring.
             replace Real1 with (/dReal3*Real3) at 1 by auto with Realiny.
             replace (  b * (/ dReal3 * Real3)) with ((Real3*b)*/dReal3) by ring.
             unfold Realdiv.
             unfold Real3.
             unfold Real2.
             unfold IZReal.
             unfold IPReal.
             unfold IPReal_2.
             ring_simplify.
             ring.


    ++ exists a.
       exists ((a+Real2*b)/dReal3).

       assert (a< ((a +Real2* b) / dReal3) < b).
       +++
         assert (3>0)%Z by intuition.
         apply (IZReal_pos 3) in H0.
         pose proof (Real2_pos).
         pose proof (Real1_gt_Real0).
         
         pose proof (convexity a b (Real1) (Real2) t1 H2 H1) as H3.
         unfold convex in H3.
         replace (a*Real1) with a in H3 by ring.
         replace (b*Real2) with (Real2*b) in H3 by ring.
         
         assert (Real1 + Real2 = Real3) as path by (unfold Real2, Real3; unfold IZReal; unfold IPReal; unfold IPReal_2; ring).
         assert (Real1 + Real2 <> Real0) as Path.
         rewrite path.
         auto with Realiny.         
         rewrite <- (neq_path (Real1+Real2) Real0 Path (Realgt_neq (Real1 + Real2) Real0
         (eq_ind (Real0 + Real0) (fun t : Real => t < Real1 + Real2) (Reallt_lt_plus_lt Real0 Real1 Real0 Real2 H2 H1) Real0
            (Realplus_unit Real0)))) in H3.
         assert (/dReal3 = /Path).
         apply inv_unif.
         (unfold Real2, Real3; unfold IZReal; unfold IPReal; unfold IPReal_2; ring).
         unfold Realdiv; rewrite H4; unfold Realdiv in H3; exact H3.
         
       +++
         split. 
           ++++
             destruct H0.
             destruct ord.
             
             pose proof (W_IVT_l f cont a ((a+Real2*b)/dReal3) H0 Real0 (conj H2 c)).
             destruct H4 as [x [[Q0 Q1] Q2]].

             unfold uniq.
             split; auto.
             split; auto.
             exists x.
             unfold unique.
             split; auto.
             intros x' [[P0 P1] P2].
             destruct H as [y [_ u2]].
             pose proof (u2 x (conj (conj Q0 (Reallt_lt_lt x ((a+Real2*b)/dReal3) b Q1 H1)) Q2)) as H.
             pose proof (u2 x' (conj (conj P0 (Reallt_lt_lt x' ((a+Real2*b)/dReal3) b P1 H1)) P2)) as H4.
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
             rewrite (lt_metric a ((a + Real2*b) / dReal3) H0).
             rewrite (lt_metric a b t1).
             assert (3>0)%Z as H3 by intuition.
             apply (IZReal_pos 3) in H3.

             replace a with (a*Real1) at 2 by ring.
             replace Real1 with (/dReal3*Real3) at 1 by auto with Realiny.
             replace (  a * (/ dReal3 * Real3)) with ((Real3*a)*/dReal3) by ring.
             unfold Realdiv.
             unfold Real3.
             unfold Real2.
             unfold IZReal.
             unfold IPReal.
             unfold IPReal_2.
             ring_simplify.
             ring.

  +
    apply (M_uniq_pick f a ((Real2*a+b)/dReal3) ((a+Real2*b)/dReal3) b cont (conj t1 (conj ord H))).
    
    ++
      apply (Reallt_plus_lt (a+b) a b) in t1.
      ring_simplify in t1.
      replace (Real1+Real1) with Real2 in t1 by auto.
      assert (3>0)%Z by intuition.
      apply (IZReal_pos 3) in H0.
      assert (/dReal3 > Real0) as H1 by auto with Realiny.
      apply (Reallt_mult_r_pos_lt); auto.

    ++
         assert (3>0)%Z by intuition.
         apply (IZReal_pos 3) in H0.
         pose proof (Real2_pos).
         pose proof (Real1_gt_Real0).

         pose proof (convexity a b (Real2) (Real1) t1 H1 H2) as H3.
         unfold convex in H3.

         assert (Real2 + Real1 = Real3) as path by (unfold Real2, Real3; unfold IZReal; unfold IPReal; unfold IPReal_2; ring).
         assert (Real2 + Real1 <> Real0) as Path.
         rewrite path.
         auto with Realiny.         
         rewrite <- (neq_path (Real2+Real1) Real0 Path (Realgt_neq (Real2 + Real1) Real0
         (eq_ind (Real0 + Real0) (fun t : Real => t < Real2 + Real1) (Reallt_lt_plus_lt Real0 Real2 Real0 Real1 H1 H2) Real0
            (Realplus_unit Real0)))) in H3.
         assert (/dReal3 = /Path).
         apply inv_unif.
         (unfold Real2, Real3; unfold IZReal; unfold IPReal; unfold IPReal_2; ring).
         unfold Realdiv.
         rewrite H4.
         
         
         
         replace (b*Real1) with b in H3 by ring.
         replace (a*Real2) with (Real2*a) in H3 by ring.
         replace (Real2+Real1) with Real3 in H3.
         destruct H3; auto.
         
    ++
      assert (3>0)%Z by intuition.
      apply (IZReal_pos 3) in H0.
      pose proof (Real2_pos).
      pose proof (Real1_gt_Real0).
      
      pose proof (convexity a b (Real1) (Real2) t1 H2 H1) as H3.
      unfold convex in H3.

         assert (Real1 + Real2 = Real3) as path by (unfold Real2, Real3; unfold IZReal; unfold IPReal; unfold IPReal_2; ring).
         assert (Real1 + Real2 <> Real0) as Path.
         rewrite path.
         auto with Realiny.         
         rewrite <- (neq_path (Real1+Real2) Real0 Path (Realgt_neq (Real1 + Real2) Real0
         (eq_ind (Real0 + Real0) (fun t : Real => t < Real1 + Real2) (Reallt_lt_plus_lt Real0 Real1 Real0 Real2 H2 H1) Real0
            (Realplus_unit Real0)))) in H3.
         assert (/dReal3 = /Path).
         apply inv_unif.
         (unfold Real2, Real3; unfold IZReal; unfold IPReal; unfold IPReal_2; ring).
         unfold Realdiv.
         rewrite H4.

      
      replace (a*Real1) with a in H3 by ring.
      replace (b*Real2) with (Real2*b) in H3 by ring.
      replace (Real2+Real1) with Real3 in H3.
      destruct H3; auto.
      unfold Real3.
      unfold Real2.
      unfold IZReal.
      unfold IPReal.
      unfold IPReal_2.
      ring.
Defined.


Definition halving (f : Real -> Real) (a b : Real)
  : continuous f -> uniq f a b -> [(a',b') | uniq f a' b' /\ halve a a' b' b  ].
Proof.
  intros.
  pose proof (trisect f a b H H0) as one.
  apply (lift_domM ({a' : Real & {b' : Real | uniq f a' b' /\ talve a a' b' b}})); auto.
  intro Q.
  destruct Q as [x [y [P1 P2]]].
  
  pose proof (trisect f x y H P1) as X.
  apply (liftM ({a' : Real  & ({ b' | uniq f a' b' /\ talve x a' b' y }) } )); auto.
  intros [x' [y' [P1' P2']]].
  exists x'.
  exists y'.
  split; auto.
  exact (talve_twice a x x' y' y b P2 P2').
Defined.    
Notation "{ ( a , b ) | P }" := (sigT (fun a => {b | P})) : type_scope.



Hint Resolve Real1_gt_Real0: Realiny.
Lemma root_approx  (f : Real -> Real)
         (cont : continuous f) (uni : uniq f Real0 Real1)  (n : nat)
  : [(a,b)| uniq f a b /\ refining Real0 a b Real1 n].
Proof.
  induction n.
  + apply unitM.
    exists Real0; exists Real1.
    split; auto.
    unfold refining.
    split; auto with Realiny.
    split.
    exact Real1_gt_Real0.
    split; auto with Realiny.
    simpl.
    ring_simplify; right; exact eq_refl.

  + apply (lift_domM {a : Real & {b : Real | uniq f a b /\ refining Real0 a b Real1 n} }); auto.
    intro X.
    destruct X as [x [y [p q]]].
    pose proof (halving f x y cont p).
    apply (liftM ({ (a', b')| uniq f a' b' /\ halve x a' b' y})); auto.
    intros [x' [y' [p' q']]].
    exists x'; exists y'.
    split; auto.
    exact (refining_S Real0 x x' y' y Real1 n q q').
Defined. 


Lemma CIVT : forall (f : Real -> Real),
    continuous f -> uniq f Real0 Real1 -> {z | Real0<z<Real1 /\ f z = Real0}.
Proof.
  intros f cont u.
  apply mslimit.
  + (* root is unique that is uniq *)
    destruct u as [_ [_ un]]; exact un.
  + (* construct limit *)
    intro n.
    pose proof (root_approx f cont u (S n)).
    apply (liftM ({(a, b)| uniq f a b /\ refining Real0 a b Real1 (S n)})); auto.
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
           pose proof (Realle_lt_lt Real0 x z Q1 H1) as P.
           pose proof (Reallt_le_lt z y Real1 H2 Q3) as Q.
           exact (conj P Q).

       +++ destruct ord as [_ H]; exact H.


    ++ unfold refining in q.
       destruct q as [Q1 [Q2 [Q3 Q4]]].
       rewrite dist_0_1 in Q4.
       ring_simplify in Q4.
       assert (dist x z <= dist x y ) as F.
       +++ pose proof (lt_metric x y Q2) as r1.
           destruct ord as [[p1 p2] _].
           pose proof (lt_metric x z p1) as r2.
           rewrite r1; rewrite r2.
           apply (Reallt_plus_r_lt (-x) z y) in p2.
           replace (z+-x) with (z-x) in p2 by ring.
           replace (y+-x) with (y-x) in p2 by ring.
           left; exact p2.
       +++ pose proof (Realle_le_le (dist x z) (dist x y) (prec (S n)) F Q4) as H.
           exact (Realle_lt_lt (dist x z) (prec (S n)) (prec n) H (prec_S n)).

Defined.
