Require Import Base.
Require Import Kleene.
Require Import RealAxioms.
Require Import RealRing.
Require Import RealSimpleLemmas.
Require Import Minmax.

Local Open Scope T_scope.


Lemma sandwich : forall a b, (forall ε, ε > T0 -> a-ε < b < a+ε) -> b = a.
Proof.
  intros a b e.
  destruct (Ttotal_order a b) as [c1|[c2|c3]].
  pose proof (padding b a c1) as H.
  destruct H as [eps [p1 p2]].
  pose proof (e (eps / dT2) (Thalf_gt_zero eps p1)).
  rewrite p2 in H.
  destruct H.
  replace (a+eps/dT2) with (eps/dT2+a) in H0 by ring.
  apply (Tlt_plus_lt (-a)) in H0.
  replace ( - a + (eps + a)) with eps in H0 by ring.
  replace ( - a + (eps / dT2 + a)) with (eps / dT2) in H0 by ring.
  contradict H0.
  pose proof (Tgt_half eps p1).
  auto with Tiny.

  auto.
  
  pose proof (padding a b c3) as H.
  destruct H as [eps [p1 p2]].
  pose proof (e (eps / dT2) (Thalf_gt_zero eps p1)).
  rewrite p2 in H.
  destruct H.
  apply (Tlt_plus_lt (-b)) in H.
  apply (Tlt_plus_lt (eps/dT2)) in H.
  replace (b+eps/dT2) with (eps/dT2+b) in H by ring.
  apply (Tlt_plus_lt (-b)) in H0.
  replace (eps / dT2 + (- b + b)) with (eps/dT2) in H by ring.
  replace ( eps / dT2 + (- b + (eps + b - eps / dT2))) with (eps) in H by ring.
  contradict H.
  pose proof (Tgt_half eps p1).
  auto with Tiny.
Qed.  

  

Definition continuous_at (f : T -> T) (z : T) : Prop
  := forall ε, ε > T0 ->
               exists δ, δ > T0 /\
                         (forall z', dist z z' < δ -> dist (f z) (f z') < ε).

Definition continuous (f : T -> T) : Prop := forall z, continuous_at f z.

(* proved by Dongseong and written by Sewon *)
Theorem W_IVT_l : forall f : T -> T,
  continuous f ->
  forall a b, a < b -> 
              forall c, f a < c < f b -> exists z', a < z' < b /\ f z' = c.
Proof.
  intros f cont a b o c p.
  assert (W_nemp (fun z => a<=z<=b /\ f z < c)) as nepty.
  exists a; constructor 1; auto with Tiny.
  destruct p as [t1 t2]; exact t1.
  assert (W_upbd (fun z => a<=z<=b /\ f z < c)) as upbd.
  exists b.
  unfold W_upb; intros b' p'; destruct p' as [[p1 p2] p3]; exact p2.
  (* u := sup { z | f z < c } *)
  destruct (W_complete (fun z => a<=z<=b /\ f z < c) nepty upbd) as [u q].

  (* prove a<=u<=b *)
  assert (mem : a <= u <= b).
  destruct (Ttotal_order a u) as [t1 | [t2 | t3]].
  split; auto with Tiny.
  destruct (Ttotal_order u b) as [tt1 | [tt2 | tt3]]; auto with Tiny.
  (** when u>b => contradict sup *)
  assert (upb_alt : W_upb (fun z => a<=z<=b /\ f z < c) b).
  unfold W_upb.
  intros z [[mem1 mem2] cond]; auto with Tiny.
  contradict q.
  unfold W_sup.
  intuition.
  pose proof (H3 b upb_alt) as contra.
  contradict contra.
  auto with Tiny.

  split; auto with Tiny.
  rewrite <- t2; auto with Tiny.

  (** when u < a => contradict sup *)

  contradict q.
  unfold W_sup; intuition.
  unfold W_upb in H2.  
  destruct nepty as [t1 t2].
  pose proof (H2 t1 t2).
  destruct t2 as [[qq1 pp2] qq2].
  pose proof (Tle_le_le a t1 u qq1 H).
  contradict H4; auto with Tiny.


  
  (* Casing on f u >? 0 *)
  destruct (Ttotal_order (f u) c) as [l | [m | r]].
  (** when f u < c, pick small u + e such that f u+e < c => contradict *)
  (** because u+e is in the set while u is the supremum of the set     *)
  assert (mem2 : u < b).
  destruct mem as [e [k | v]].
  exact k.
  rewrite v in l; destruct p as [p1 p2].
  contradict l; auto with Tiny.
  
  destruct (padding c (f u) l) as [eps [o1 o2]].
  assert (t1 : eps / dT2 > T0) by auto with Tiny.
  destruct (cont u (eps/dT2) t1) as [δ [o3 o4]].
  destruct (W_min (u+δ/dT2) b) as [x  H].
  
  assert (dis : dist u x < δ).
  (**)
  destruct (Ttotal_order (u+δ/dT2) b) as [l1 |[ l2 | l3]];
    destruct H as [r1 [r2 r3]].
  
  apply r3 in l1.
  rewrite l1.
  replace u with (T0+u) at 1 by ring;
    replace (u+δ/dT2) with (δ/dT2+u) by ring.
  rewrite <- (Tmetric_inv T0 (δ/dT2) u).

  destruct (dist_prop T0 (δ/dT2)) as [_[_ u3]];
    rewrite (u3 (Thalf_gt_zero δ o3)).
  ring_simplify; apply Tgt_half; exact o3.

  apply r2 in l2.
  rewrite l2.
  replace u with (u+T0) at 1 by ring.
  rewrite <- (Tmetric_plus_inv T0 (δ/dT2) u).
  destruct (dist_prop T0 (δ/dT2)) as [_[_ u3]];
    rewrite (u3 (Thalf_gt_zero δ o3)).
  ring_simplify; apply Tgt_half; exact o3.

  pose proof (r1 l3) as H.
  rewrite H.
  pose proof (Tmetric_inv T0 (b-u) u) as H1.
  replace (T0+u) with u in H1 by ring.
  replace (b-u+u) with b in H1 by ring.
  rewrite <- H1.
  assert (b-u > T0) as H2 by auto with Tiny.
  destruct (dist_prop T0 (b-u)) as [_[_ u3]].
  apply u3 in H2.
  rewrite H2.
  assert ((u+δ/dT2) +-u > b+-u).
  apply Tlt_plus_r_lt.
  exact l3.
  replace ( u + δ / dT2 + - u) with (δ/dT2) in H0 by ring.
  replace (b+-u) with (b-u) in H0 by ring.
  ring_simplify.
  pose proof (Tgt_half δ o3).
  exact (Tlt_lt_lt (b-u) (δ/dT2) δ H0 H3).
  (**)

  pose proof (o4 x dis).
  (* prove a<=x<=b and f x < c then contradicts sup *)
  (**)
  assert (memx : a<=x<=b).
  destruct mem as [mem _].
  destruct H as [l1 [l2 l3]].
  destruct (Ttotal_order (u+δ/dT2) b) as [r1 | [r2 | r3]].
  (*** when u+δ/2 <b *)
  split.
  apply l3 in r1.
  rewrite r1.
  pose proof (Thalf_gt_zero δ o3).
  assert (u+δ/dT2 > u+T0).
  apply (Tlt_plus_lt); auto.
  replace (u+T0) with u in H1 by ring.
  pose proof (Tle_lt_lt a u (u+δ/dT2) mem H1); auto with Tiny.

  pose proof (l3 r1) as H1; rewrite H1.
  auto with Tiny.

  (*** when u+δ/2 =b *)
  pose proof (l2 r2) as H; rewrite H.
  split.
  pose proof (Thalf_gt_zero δ o3).
  assert (u+δ/dT2 > u+T0).
  apply (Tlt_plus_lt); auto.
  replace (u+T0) with u in H2 by ring.
  pose proof (Tle_lt_lt a u (u+δ/dT2) mem H2); auto with Tiny.
  rewrite <- r2; right; exact eq_refl.

  (*** when u+δ/2 > b *)
  pose proof (l1 r3) as H; rewrite H.
  split; auto with Tiny.
  (**)

  assert (f x < c).
  destruct (Ttotal_order (f u) (f x)) as [l1 | [l2 | l3]].
  destruct (dist_prop (f u) (f x)) as [_ [_ r3]];
    pose proof (r3 l1).
  rewrite H1 in H0.
  rewrite o2.
  pose proof (Tlt_plus_lt  (f u) (f x - f u) (eps/dT2) H0).
  ring_simplify in H2.
  pose proof (Tgt_half eps o1).
  assert (f u + eps > f u + eps / dT2).
  apply (Tlt_plus_lt); auto.
  replace (eps + f u) with (f u + eps) by ring.
  apply (Tlt_lt_lt (f x) (f u + eps / dT2) (f u + eps)).
  exact H2.
  exact H4.

  rewrite <- l2; exact l.

  exact (Tlt_lt_lt (f x) (f u) c l3 l).

  (** finally....  x is the counter example of sup *)
  contradict q.
  unfold W_sup.
  unfold not; intros.
  destruct H2 as [H2 _].
  unfold W_upb in H2.
  pose proof (H2 x (conj memx H1)).
  destruct (W_m_or (u+δ/dT2) b x H) as [p1 | p2].
  rewrite <- p1 in H3.
  destruct H3.
  apply (Tlt_plus_lt (-u) (u+δ/dT2) u) in H3.
  ring_simplify in H3.
  pose proof (Thalf_gt_zero δ o3).
  contradict H4.
  exact (Tlt_nlt (δ/dT2) T0 H3).
  apply (Teq_plus_eq (u+δ/dT2) u (-u)) in H3.
  ring_simplify in H3.
  pose proof (Thalf_gt_zero δ o3).
  rewrite H3 in H4.
  contradict H4.
  exact (Tngt_triv T0).
  rewrite <- p2 in H3.
  contradict H3; auto with Tiny.

  (** when f u = c *)
  exists u.
  split.
  destruct mem as [[o1|o1] [o2|o2]].
  exact (conj o1 o2).
  destruct p.
  rewrite o2 in m.
  contradict m.
  auto with Tiny.
  rewrite <- o1 in m.
  contradict m.
  destruct p.
  auto with Tiny.
  rewrite o1 in o; rewrite <- o2 in o.
  contradict o; auto with Tiny.
  exact m.

  (** when f u > c *)
  assert (mem2 : a < u).
  destruct mem as [[k| v] _].
  exact k.
  rewrite <-v in r; destruct p as [p1 p2].
  contradict r; auto with Tiny.
  
  destruct (padding (f u) c r) as [eps [o1 o2]].
  assert (t1 : eps / dT2 > T0) by auto with Tiny.
  destruct (cont u (eps/dT2) t1) as [δ [o3 o4]].
  destruct (W_max (u-δ/dT2) a) as [x  H].
  
  assert (dis : dist u x < δ).
  (**)
  destruct (W_M_Or (u-δ/dT2) a x H) as [[c1 p1] | [c2 p2]].
  (* case where Max is u-δ/dT2 *)
  rewrite <- c1.
  rewrite  (Tmetric_inv u (u-δ/dT2) (δ/dT2)).
  replace (u - δ / dT2 + δ / dT2) with u by ring.
  rewrite (Tmetric_inv (u+δ/dT2) u (-u)).
  replace (u + δ / dT2 + - u) with (δ/dT2) by ring;
    replace (u+-u) with T0 by ring.
  destruct (dist_prop T0 (δ/dT2)) as [_[_ u3]].
  rewrite dist_symm.
    rewrite (u3 (Thalf_gt_zero δ o3)).
  ring_simplify; apply Tgt_half; exact o3.

  (* case where Max is a *)
  pose proof (Thalf_gt_zero δ o3).
  apply (Tlt_plus_lt u (T0) (δ/dT2)) in H0.
  ring_simplify in H0.
  pose proof (Tlt_le a (u+δ/dT2)  (Tlt_lt_lt a u (u+δ/dT2) mem2 H0)) as R.
  assert (u - δ / dT2 <= a <= u + δ / dT2).
  split; auto with Tiny.
  pose proof (Tmetric_sand u a (δ/dT2) H1).
  pose proof (Tgt_half δ o3).
  rewrite<- c2.
  exact (Tle_lt_lt (dist u a) (δ/dT2) δ H2 H3).
  (**)

  pose proof (o4 x dis).
  (* prove a<=x<=b and f x > c then contradicts sup *)
  (** a<=x<=b *)
  assert (memx : a<=x<=b).

  destruct (W_M_Or (u - δ/dT2) a x H) as [[l1 l2 ] | [r1 r2]].
  rewrite <- l1.
  split; auto with Tiny.
  pose proof (Thalf_gt_zero δ o3).

  apply (Tlt_plus_lt (u-δ/dT2) T0 (δ/dT2)) in H1.
  ring_simplify in H1.
  destruct mem.
  pose proof (Tlt_le_lt (u-δ/dT2) u b H1 H3). 
  auto with Tiny.
  rewrite <-r1. split; auto with Tiny.
  (** prove f x > c *)
  assert (f x > c).
  destruct (Tmetric_Or (f u) (f x)) as [[H1 _] | [_ H1]].
  (*** when |f u - f x| = f u - x f *)
  rewrite H1 in H0.
  apply (Tlt_plus_r_lt (f x - eps/dT2) (f u - f x) (eps/dT2)) in H0.
  ring_simplify in H0.
  rewrite o2 in H0.
  replace (eps + c - eps/dT2) with (c + (eps -eps/dT2)) in H0 by ring.
  replace (eps - eps / dT2) with (eps / dT2) in H0 by auto with Tiny.
  apply (Tlt_plus_r_lt c T0 (eps/dT2)) in t1.
  ring_simplify in t1.
  exact (Tlt_lt_lt c (c+ eps/dT2) (f x) t1 H0).
  (*** when |f u - f x| = f x - f u *)
  assert (f u <= f x) as H2 by auto with Tiny.
  exact (Tlt_le_lt c (f u) (f x) r H2).


  (** finally....  x is the counter example of sup *)
  (*** prove x < u *)
  assert (x < u) as ord.
  destruct (W_M_Or (u-δ/dT2) a x H) as [[l1 r1]|[l2 r2]].
  assert (u-δ/dT2 +δ/dT2 = x + δ/dT2) as H2 by auto with Tiny.
  ring_simplify in H2.
  rewrite H2.
  replace (δ/dT2+x) with (x+δ/dT2) by ring;
    replace x with (x+T0) at 1 by ring.
  apply Tlt_plus_lt; exact (Thalf_gt_zero δ o3).
  rewrite <- l2; exact mem2.

  (*** prove that x is an upperbound *)
  assert (W_upb (fun z : T => a<=z<=b /\ f z < c) x).
  unfold W_upb.
  intros z [q1 q2].

  destruct (Ttotal_order z x) as [to1 | [to2|to3]]; auto with Tiny.
  destruct (Ttotal_order z u) as [tp1 | [tp2|tp3]]; auto with Tiny.
  (**** when x < z < u, z is not in set *)
  assert (dist u z < δ).
  destruct (Tmetric_Or u z) as [[cs11 cs12] | [_ cs2]].
  rewrite cs11.
  apply (Tlt_plus_lt (u-x-z) x z) in to3. 
  ring_simplify in to3.
  destruct (Tmetric_Or u x) as [[cp11 cp12] | [_ cp2]].
  rewrite cp11 in dis.
  exact (Tlt_lt_lt (u-z) (u-x) δ to3 dis).
  contradict cp2; auto with Tiny.
  contradict cs2; auto with Tiny.
  
  
  pose proof (o4 z H2).
  (***** when x < z < u then f z > c thus not in set *)
  assert (f z > c) as noway.
  destruct (Tmetric_Or (f u) (f z)) as [[H4 _]|[_ H4]].
  rewrite H4 in H3.
  apply (Tlt_plus_lt (f z - (eps / dT2)) (f u - f z) (eps/dT2)) in H3.
  ring_simplify in H3.
  rewrite o2 in H3.
  replace (-(eps/dT2)+(eps+c)) with (eps - (eps/dT2) + c) in H3 by ring.
  replace (eps - (eps/dT2) + c) with (eps/dT2 + c) in H3 by auto with Tiny.
  replace (eps/dT2+c) with (c+eps/dT2) in H3 by ring.
  apply (Tlt_plus_lt c T0 (eps/dT2)) in t1.
  ring_simplify in t1.
  exact (Tlt_lt_lt c (c+eps/dT2) (f z) t1 H3).
  assert (f u <= f z) as H5 by auto with Tiny.
  exact (Tlt_le_lt c (f u) (f z) r H5).

  contradict q2.
  auto with Tiny.

  (**** when u = z *)
  rewrite <- tp2 in r; contradict r; auto with Tiny.

  (**** when u < z *)
  contradict q.
  unfold W_sup.
  unfold W_upb.
  red; intros.
  destruct H2 as [H2 _].
  pose proof (H2 z (conj q1 q2 )).
  contradict H3; auto with Tiny.
  

  (*** as x < u is a upperbound, contradicts u to be sup *)
  contradict q.
  unfold W_sup.
  unfold W_upb.
  red; intros.
  destruct H3 as [_ H3].
  pose proof (H3 x H2).
  contradict H4; auto with Tiny.
Qed.


Definition opp_fun (f : T -> T) : (T -> T)
  := fun x => - f x.

Lemma opp_fun_inv : forall f : T -> T,
    forall x y, dist (f x) (f y) = dist (opp_fun f x) (opp_fun f y).
Proof.
  intros.
  unfold opp_fun.
  pose proof (Tmetric_inv (- f x) (- f y) (f x + f y)) as A.
  replace (- f x + (f x + f y)) with (f y) in A  by ring.
  replace (- f y + (f x + f y)) with (f x) in A by ring.
  rewrite A.
  apply dist_symm.
Qed.
  
Lemma opp_fun_cont : forall f : T -> T, continuous f -> continuous (opp_fun f).
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

Theorem W_IVT_r : forall f : T -> T,
  continuous f ->
  forall a b, a < b -> 
              forall c, f b < c < f a -> exists z', a<z'<b /\ f z' = c.
Proof.
  intros.
  pose proof (opp_fun f) as g.
  pose proof (opp_fun_cont f H) as cont.
  assert (opp_fun f a < - c < opp_fun f b).
  destruct H1 as [o1 o2];  unfold opp_fun; split; auto with Tiny.
  pose proof (W_IVT_l (opp_fun f) cont a b H0 (- c) H2).
  destruct H3.
  exists x.
  unfold opp_fun in H3.
  destruct H3.
  assert (- f x + f x + c = - c + f x + c) by auto with Tiny.
  ring_simplify in H5.
  rewrite <- H5; auto.
Qed.

Theorem W_IVT : forall f : T -> T,
    continuous f ->
    forall a b, a < b ->
                forall c, (f a < c < f b \/ f b < c < f a) -> exists z', a<z'<b/\ f z' = c. 
Proof.
  intros f H a b H0 c [l|r].
  exact (W_IVT_l f H a b H0 c l).
  exact (W_IVT_r f H a b H0 c r).
Qed.

(**********************************************************)
(* PROOF OF CONSTRUCTIVE IVT                              *)
(**********************************************************)
Definition uniq (f : T -> T) (a b : T)
  := a<b /\ f a < T0 < f b /\ exists! z, (a<z<b) /\ f z = T0.

Lemma uniq_pick : forall (f : T -> T) (a b c d : T), continuous f ->
    uniq f a d ->
    b < c -> a < b -> c < d  -> (f b < T0) \/ (T0 < f c).
Proof.
  intros.
  destruct H0 as [o0 [[o1 o2] o3]].
  destruct (Ttotal_order (f b) T0) as [p|[p|p]];
    destruct (Ttotal_order (f c) T0) as [q|[q|q]].
  + (* f(b) < 0*)
    left; exact p.
  + (* f(b) < 0 *)
    left; exact p.
  +
    left; exact p.
    
  + (* f(b) = 0 and f(c) < 0: show that is a root in [c,d] 
     and that the root r is equal to b *)
    pose proof (W_IVT_l f H c d H3 T0 (conj q o2)) as [r [c1 c2]].
    destruct o3 as [x [[P1 P2] Q]].
    assert (a<r<d) as Xo.
    ++ split.
       +++ 
         destruct c1 as [l _].
         exact (Tlt_lt_lt a c r (Tlt_lt_lt a b c H2 H1) l).
       +++
         destruct c1 as [_ l].
         exact l.
         
         
    ++
      pose proof (Q r (conj Xo c2)) as H10.
      pose proof (Q b (conj (conj H2 (Tlt_lt_lt b c d H1 H3)) p)) as H11.
      destruct c1 as [c1 _].
      pose proof (Tlt_lt_lt b c r H1 c1) as C.
      rewrite <- H10 in C; rewrite <- H11 in C.
      contradict C; auto with Tiny.

  + (* f b = 0, f c = 0 *)
    assert ( a < b < d).
    ++ split; auto.
       exact (Tlt_lt_lt b c d H1 H3).
    ++ assert (a < c < d).
       +++ split; auto.
           exact (Tlt_lt_lt a b c H2 H1).

       +++ destruct o3 as [p1 [[p2 p3] p4]].
           pose proof (p4 b (conj H0 p)) as X.
           pose proof (p4 c (conj H4 q)) as Y.
           rewrite <- X in H1; rewrite <- Y in H1; contradict H1; auto with Tiny.

  + (* f(c) > 0 *)
    right; exact q.
   
  + (* f(b) > 0 and f(c) < 0 *)
    pose proof (W_IVT_l f H a b H2 T0 (conj o1 p)) as X.
    pose proof (W_IVT_l f H c d H3 T0 (conj q o2)) as Y.
    destruct X as [x1 [x2 x3]].
    destruct Y as [y1 [y2 y3]].
    assert (a<x1<d) as orx.
    ++ destruct x2; split; auto.
       exact (Tlt_lt_lt x1 b d H4 (Tlt_lt_lt b c d H1 H3)).
    ++ assert (a<y1<d) as ory.
       destruct y2; split; auto.
       exact (Tlt_lt_lt a c y1 (Tlt_lt_lt a b c H2 H1) H0).
       destruct o3 as [x [[P1 P2] Q]].
       pose proof (Q x1 (conj orx x3)) as xr.
       pose proof (Q y1 (conj ory y3)) as yr.
       assert (x1<y1) as or.
       +++
         destruct x2; destruct y2.
         apply (Tlt_lt_lt_lt x1 b c y1); auto with Tiny.

       +++
         rewrite <- xr in or; rewrite <- yr in or; contradict or; auto with Tiny.
  + (* f(c) = 0 *)
    pose proof (W_IVT_l f H a b H2 T0 (conj o1 p)) as X.
    destruct X as [x1 [x2 x3]].
    assert (a<x1<d) as orx.
    ++
      destruct x2; split; auto.
      exact (Tlt_lt_lt x1 b d H4 (Tlt_lt_lt b c d H1 H3)).
    ++


      destruct o3 as [x [[P1 P2] Q]].
      pose proof (Q x1 (conj orx x3)) as xr.
      pose proof (Q c (conj (conj (Tlt_lt_lt a b c H2 H1) H3) q)) as yr.
      destruct x2 as [_ x2].
      pose proof (Tlt_lt_lt x1 b c x2 H1) as C.
      rewrite <- xr in C; rewrite <- yr in C; contradict C; auto with Tiny.

  + right; exact q.
Qed.

    
Lemma M_uniq_pick : forall (f : T -> T) (a b c d : T), continuous f ->
    uniq f a d ->
    b < c -> a < b -> c < d  -> M ({f b < T0}+{T0 < f c}).
Proof.
  intros.
  apply (choose (f b < T0)  (T0 < f c)); auto with Tiny.
  apply (uniq_pick f a b c d H H0 H1 H2 H3).
Defined.


Definition T3 := IZT 3.
Definition dT3 : T3 <> T0.
Proof.
  assert (3>0)%Z.
  intuition.
  exact (Tgt_neq T3 T0 (IZT_pos 3 H)).
Defined.

Definition talve (a b c d : T)
  := a <= b /\ b < c /\ c <= d /\ dist b c =(T2 * dist a d) / dT3.
Definition halve (a b c d : T)
  := a <= b /\ b < c /\ c <= d /\ dist b c < ( dist a d) * (prec 1).
Definition refining (a b c d : T) (n:nat)
  := a <= b /\ b < c /\ c <= d /\ dist b c <= ( dist a d) * (prec n).

Lemma Tle_mult_r_pos_le : forall c a b, c > T0 -> a <= b -> a*c <= b*c.
Proof.
  intros c a b p q.
  destruct q as [q|q].
  apply (Tlt_mult_r_pos_lt a b c p) in q.
  left; exact q.
  right; auto with Tiny.
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
  exact (Tle_le_le a b c p q).
  split.
  destruct r as [_ [p _]].
  destruct h as [_ [q _]].
  auto with Tiny.
  split.
  destruct r as [_[_ [p _]]].
  destruct h as [_[_ [q _]]].
  exact (Tle_le_le d e f q p).
  
  destruct r as [_[_ [_ p]]].
  destruct h as [_[_ [_ q]]].

  pose proof (prec_pos 1).
  apply (Tle_mult_r_pos_le (prec 1)) in p; auto.
  pose proof
       (Tlt_le_lt (dist c d) (dist b e * prec 1) (dist a f * prec n * prec 1) q p).
  replace (dist a f * prec n * prec 1) with
      (dist a f * (prec n * prec 1))  in H0 by ring.
  rewrite <- (prec_hom n 1) in H0.
  rewrite (Nat.add_1_r n) in H0.  
  left; exact H0.
Qed.
Hint Resolve refining_S : Tiny.


  
Lemma talve_twice : forall a b c d e f, talve a b e f -> talve b c d e -> halve a c d f.
Proof.
  unfold talve.
  intros a b c d e f p q.
  unfold halve.

  split.
  destruct p as [p _].
  destruct q as [q _].
  exact (Tle_le_le a b c p q).

  split.
  destruct q as [_ [q _]].
  exact q.

  split.
  destruct p as [_[_ [p _]]].
  destruct q as [_[_ [q _]]].
  exact (Tle_le_le d e f q p).

  assert (a < f) as QQ.
  destruct p as [p1[p2 [p3 _]]].
  pose proof (Tle_lt_lt a b e p1 p2).
  exact (Tlt_le_lt a e f H p3).
  
  destruct p as [_[_ [_ p]]].
  destruct q as [_[qr [_ q]]].
  rewrite p in q.
  rewrite q.
  simpl.
  
  replace (T2 * (T2 * dist a f / dT3) / dT3) with
      (T2 * (T2 * dist a f */ dT3)*/dT3) by auto.
  
  replace (T2 * (T2 * dist a f */ dT3)*/dT3) with
      (dist a f * (T2 * T2  */ dT3 */dT3)) by ring.

  apply (Tlt_mult_pos_lt).

  + rewrite (lt_metric a f QQ).
    apply (Tlt_plus_lt (-a) a f) in QQ.
    ring_simplify in QQ.
    replace (f-a) with (-a+f) by ring; exact QQ.

  + assert (3 > 0)%Z as Q1 by intuition.
    apply (IZT_pos 3) in Q1.
    replace (IZT 3) with T3 in Q1; auto.
    pose proof T2_pos as Q2.
    apply (Tlt_mult_pos_move_rr_n T2); auto with Tiny.
    replace (T2*T2*/dT3*/dT3*T2) with
        (T2*T2*T2*/dT3*/dT3) by ring.
    replace  (T2*T2*T2*/dT3*/dT3) with
        (T2*T2*T2/dT3/dT3) by auto.
    apply (Tgt_mult_pos_move_rl T3); auto with Tiny.
    apply (Tgt_mult_pos_move_rl T3); auto with Tiny.

    replace (T3*(T3*T1)) with (T3*T3) by ring.
    replace T3 with (IZT 3) by auto.
    replace T2 with (IZT 2) by auto.
    unfold IZT.
    unfold IPT.
    unfold IPT_2.
    ring_simplify.
    replace ((T1 + T1) * ((T1 + T1) * (T1 + T1))) with
        (T0 + ((T1 + T1) * ((T1 + T1) * (T1 + T1)))) at 2  by ring.
    apply Tlt_plus_r_lt; exact T1_gt_T0.
Qed.



Definition trisect (f : T -> T) (a b : T)
  : continuous f -> uniq f a b -> [(a',b') | uniq f a' b' /\ talve a a' b' b  ].
Proof.
  intros cont [t1 [ord H]].
  apply (mjoin (f ((T2*a+b)/dT3) < T0) (T0 <(f ((a+T2*b)/dT3)))).

  + intros [c|c].
    ++ exists ((T2*a+b)/dT3); exists b.
       assert (a< ((T2 * a + b) / dT3) < b).
       +++
         assert (3>0)%Z by intuition.
         apply (IZT_pos 3) in H0.
         pose proof (T2_pos).
         pose proof (T1_gt_T0).
         
         pose proof (convexity a b (T2) (T1) t1 H1 H2) as H3.
         unfold convex in H3.
         replace (b*T1) with b in H3 by ring.
         replace (a*T2) with (T2*a) in H3 by ring.
         replace (T2+T1) with T3 in H3.

         (* path on neq *)
         assert (T2 + T1 = T3) as path by (unfold T2, T3; unfold IZT; unfold IPT; unfold IPT_2; ring).
         assert (T2 + T1 <> T0) as Path.
         rewrite path.
         auto with Tiny.         
         rewrite <- (neq_path (T2+T1) T0 Path (Tgt_neq (T2 + T1) T0
         (eq_ind (T0 + T0) (fun t : T => t < T2 + T1) (Tlt_lt_plus_lt T0 T2 T0 T1 H1 H2) T0
                 (Tplus_unit T0)))) in H3.
         assert (/dT3 = /Path).
         apply inv_unif.
         (unfold T2, T3; unfold IZT; unfold IPT; unfold IPT_2; ring).
         unfold Tdiv; rewrite H4; unfold Tdiv in H3; exact H3.
         (unfold T2, T3; unfold IZT; unfold IPT; unfold IPT_2; ring).
     
       +++
         split. 
           ++++
             destruct H0.
             destruct ord.
             
             pose proof (W_IVT_l f cont ((T2*a+b)/dT3) b H1 T0 (conj c H3)).
             destruct H4 as [x [[Q0 Q1] Q2]].

             unfold uniq.
             split; auto.
             split; auto.
             exists x.
             unfold unique.
             split; auto.
             intros x' [[P0 P1] P2].
             destruct H as [y [_ u2]].
             pose proof (u2 x (conj (conj (Tlt_lt_lt a ((T2*a+b)/dT3) x H0 Q0) Q1) Q2)).
             pose proof (u2 x' (conj (conj (Tlt_lt_lt a ((T2*a+b)/dT3) x' H0 P0) P1) P2)).
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
             rewrite (lt_metric ((T2 * a + b) / dT3) b H1).
             rewrite (lt_metric a b t1).
             assert (3>0)%Z as H3 by intuition.
             apply (IZT_pos 3) in H3.
             replace (b) with (b*T1) at 1 by ring.
             replace T1 with (/dT3*T3) at 1 by auto with Tiny.
             replace (  b * (/ dT3 * T3)) with ((T3*b)*/dT3) by ring.
             unfold Tdiv.
             unfold T3.
             unfold T2.
             unfold IZT.
             unfold IPT.
             unfold IPT_2.
             ring_simplify.
             ring.


    ++ exists a.
       exists ((a+T2*b)/dT3).

       assert (a< ((a +T2* b) / dT3) < b).
       +++
         assert (3>0)%Z by intuition.
         apply (IZT_pos 3) in H0.
         pose proof (T2_pos).
         pose proof (T1_gt_T0).
         
         pose proof (convexity a b (T1) (T2) t1 H2 H1) as H3.
         unfold convex in H3.
         replace (a*T1) with a in H3 by ring.
         replace (b*T2) with (T2*b) in H3 by ring.
         
         assert (T1 + T2 = T3) as path by (unfold T2, T3; unfold IZT; unfold IPT; unfold IPT_2; ring).
         assert (T1 + T2 <> T0) as Path.
         rewrite path.
         auto with Tiny.         
         rewrite <- (neq_path (T1+T2) T0 Path (Tgt_neq (T1 + T2) T0
         (eq_ind (T0 + T0) (fun t : T => t < T1 + T2) (Tlt_lt_plus_lt T0 T1 T0 T2 H2 H1) T0
            (Tplus_unit T0)))) in H3.
         assert (/dT3 = /Path).
         apply inv_unif.
         (unfold T2, T3; unfold IZT; unfold IPT; unfold IPT_2; ring).
         unfold Tdiv; rewrite H4; unfold Tdiv in H3; exact H3.
         
       +++
         split. 
           ++++
             destruct H0.
             destruct ord.
             
             pose proof (W_IVT_l f cont a ((a+T2*b)/dT3) H0 T0 (conj H2 c)).
             destruct H4 as [x [[Q0 Q1] Q2]].

             unfold uniq.
             split; auto.
             split; auto.
             exists x.
             unfold unique.
             split; auto.
             intros x' [[P0 P1] P2].
             destruct H as [y [_ u2]].
             pose proof (u2 x (conj (conj Q0 (Tlt_lt_lt x ((a+T2*b)/dT3) b Q1 H1)) Q2)) as H.
             pose proof (u2 x' (conj (conj P0 (Tlt_lt_lt x' ((a+T2*b)/dT3) b P1 H1)) P2)) as H4.
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
             rewrite (lt_metric a ((a + T2*b) / dT3) H0).
             rewrite (lt_metric a b t1).
             assert (3>0)%Z as H3 by intuition.
             apply (IZT_pos 3) in H3.

             replace a with (a*T1) at 2 by ring.
             replace T1 with (/dT3*T3) at 1 by auto with Tiny.
             replace (  a * (/ dT3 * T3)) with ((T3*a)*/dT3) by ring.
             unfold Tdiv.
             unfold T3.
             unfold T2.
             unfold IZT.
             unfold IPT.
             unfold IPT_2.
             ring_simplify.
             ring.

  +
    apply (M_uniq_pick f a ((T2*a+b)/dT3) ((a+T2*b)/dT3) b cont (conj t1 (conj ord H))).
    
    ++
      apply (Tlt_plus_lt (a+b) a b) in t1.
      ring_simplify in t1.
      replace (T1+T1) with T2 in t1 by auto.
      assert (3>0)%Z by intuition.
      apply (IZT_pos 3) in H0.
      assert (/dT3 > T0) as H1 by auto with Tiny.
      apply (Tlt_mult_r_pos_lt); auto.

    ++
         assert (3>0)%Z by intuition.
         apply (IZT_pos 3) in H0.
         pose proof (T2_pos).
         pose proof (T1_gt_T0).

         pose proof (convexity a b (T2) (T1) t1 H1 H2) as H3.
         unfold convex in H3.

         assert (T2 + T1 = T3) as path by (unfold T2, T3; unfold IZT; unfold IPT; unfold IPT_2; ring).
         assert (T2 + T1 <> T0) as Path.
         rewrite path.
         auto with Tiny.         
         rewrite <- (neq_path (T2+T1) T0 Path (Tgt_neq (T2 + T1) T0
         (eq_ind (T0 + T0) (fun t : T => t < T2 + T1) (Tlt_lt_plus_lt T0 T2 T0 T1 H1 H2) T0
            (Tplus_unit T0)))) in H3.
         assert (/dT3 = /Path).
         apply inv_unif.
         (unfold T2, T3; unfold IZT; unfold IPT; unfold IPT_2; ring).
         unfold Tdiv.
         rewrite H4.
         
         
         
         replace (b*T1) with b in H3 by ring.
         replace (a*T2) with (T2*a) in H3 by ring.
         replace (T2+T1) with T3 in H3.
         destruct H3; auto.
         
    ++
      assert (3>0)%Z by intuition.
      apply (IZT_pos 3) in H0.
      pose proof (T2_pos).
      pose proof (T1_gt_T0).
      
      pose proof (convexity a b (T1) (T2) t1 H2 H1) as H3.
      unfold convex in H3.

         assert (T1 + T2 = T3) as path by (unfold T2, T3; unfold IZT; unfold IPT; unfold IPT_2; ring).
         assert (T1 + T2 <> T0) as Path.
         rewrite path.
         auto with Tiny.         
         rewrite <- (neq_path (T1+T2) T0 Path (Tgt_neq (T1 + T2) T0
         (eq_ind (T0 + T0) (fun t : T => t < T1 + T2) (Tlt_lt_plus_lt T0 T1 T0 T2 H2 H1) T0
            (Tplus_unit T0)))) in H3.
         assert (/dT3 = /Path).
         apply inv_unif.
         (unfold T2, T3; unfold IZT; unfold IPT; unfold IPT_2; ring).
         unfold Tdiv.
         rewrite H4.

      
      replace (a*T1) with a in H3 by ring.
      replace (b*T2) with (T2*b) in H3 by ring.
      replace (T2+T1) with T3 in H3.
      destruct H3; auto.
      unfold T3.
      unfold T2.
      unfold IZT.
      unfold IPT.
      unfold IPT_2.
      ring.
Defined.


Definition halving (f : T -> T) (a b : T)
  : continuous f -> uniq f a b -> [(a',b') | uniq f a' b' /\ halve a a' b' b  ].
Proof.
  intros.
  pose proof (trisect f a b H H0) as one.
  apply (lift_domM ({a' : T & {b' : T | uniq f a' b' /\ talve a a' b' b}})); auto.
  intro Q.
  destruct Q as [x [y [P1 P2]]].
  
  pose proof (trisect f x y H P1) as X.
  apply (liftM ({a' : T  & ({ b' | uniq f a' b' /\ talve x a' b' y }) } )); auto.
  intros [x' [y' [P1' P2']]].
  exists x'.
  exists y'.
  split; auto.
  exact (talve_twice a x x' y' y b P2 P2').
Defined.    
Notation "{ ( a , b ) | P }" := (sigT (fun a => {b | P})) : type_scope.



Hint Resolve T1_gt_T0: Tiny.
Lemma root_approx  (f : T -> T)
         (cont : continuous f) (uni : uniq f T0 T1)  (n : nat)
  : [(a,b)| uniq f a b /\ refining T0 a b T1 n].
Proof.
  induction n.
  + apply unitM.
    exists T0; exists T1.
    split; auto.
    unfold refining.
    split; auto with Tiny.
    split.
    exact T1_gt_T0.
    split; auto with Tiny.
    simpl.
    ring_simplify; right; exact eq_refl.

  + apply (lift_domM {a : T & {b : T | uniq f a b /\ refining T0 a b T1 n} }); auto.
    intro X.
    destruct X as [x [y [p q]]].
    pose proof (halving f x y cont p).
    apply (liftM ({ (a', b')| uniq f a' b' /\ halve x a' b' y})); auto.
    intros [x' [y' [p' q']]].
    exists x'; exists y'.
    split; auto.
    exact (refining_S T0 x x' y' y T1 n q q').
Defined. 


Lemma CIVT : forall (f : T -> T),
    continuous f -> uniq f T0 T1 -> {z | T0<z<T1 /\ f z = T0}.
Proof.
  intros f cont u.
  apply mslimit.
  + (* root is unique that is uniq *)
    destruct u as [_ [_ un]]; exact un.
  + (* construct limit *)
    intro n.
    pose proof (root_approx f cont u (S n)).
    apply (liftM ({(a, b)| uniq f a b /\ refining T0 a b T1 (S n)})); auto.
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
           pose proof (Tle_lt_lt T0 x z Q1 H1) as P.
           pose proof (Tlt_le_lt z y T1 H2 Q3) as Q.
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
           apply (Tlt_plus_r_lt (-x) z y) in p2.
           replace (z+-x) with (z-x) in p2 by ring.
           replace (y+-x) with (y-x) in p2 by ring.
           left; exact p2.
       +++ pose proof (Tle_le_le (dist x z) (dist x y) (prec (S n)) F Q4) as H.
           exact (Tle_lt_lt (dist x z) (prec (S n)) (prec n) H (prec_S n)).

Defined.
