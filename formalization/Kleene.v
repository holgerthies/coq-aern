Require Import Base.

(* Kleene type *)
Parameter K : Set.
Parameter trueK : K.
Parameter falseK : K.

Definition upK : K -> Prop := fun b : K => b = trueK.
Definition downK : K -> Prop := fun b : K => b = falseK.
Definition definedK (k : K) := upK k \/ downK k.

Parameter kneg : K -> K.
Parameter kland : K -> K -> K.
Parameter klor : K -> K -> K.
Axiom definedK_is_bool : forall k, definedK k -> {upK k} + {downK k}.
  
Axiom kneg_up : forall k : K, upK (kneg k) = downK k. 
Axiom kneg_down : forall k : K, downK (kneg k) = upK k.
Axiom kland_up : forall a b : K, upK (kland a b) = upK a /\ upK b.
Axiom kland_down : forall a b : K, downK (kland a b) = downK a \/ downK b.
Axiom klor_up : forall a b : K, upK (klor a b) = upK a \/ upK b.
Axiom klor_down : forall a b : K, downK (klor a b) = downK a /\ downK b.

(* Multivalue monad *)
(* Functor: *)
Parameter M : Type -> Type.
Parameter liftM : forall A B, (A -> B) -> M A -> M B.
Axiom liftM_axiom1 : forall A B C (f : A -> B) (g : B -> C),
    liftM _ _ (fun x => g (f x)) = fun x => (liftM _ _ g) ((liftM _ _ f) x).
Axiom liftM_axiom2 : forall A, (fun x : M A => x) = liftM A A (fun x => x). 

(* Monadic structure: *)
Parameter unitM : forall T : Type, T -> M T.
Parameter multM : forall T : Type, M (M T) -> M T.
Definition lift_domM : forall A B, (A -> M B) -> M A -> M B :=
  fun A B f => fun x => multM B ((liftM A (M B) f) x).
Axiom unitM_ntrans : forall A B (f : A -> B) x, (liftM A B f) (unitM A x) = unitM B (f x).
Axiom multM_ntrans : forall A B (f : A -> B) x, multM B ((liftM (M A) (M B) (liftM A B f)) x) = (liftM A B f) (multM A x).  

(* coherence conditions for the monadic structure: *)
Axiom M_coh1 : forall A x, multM A (unitM (M A) x) = x.
Axiom M_coh2 : forall A x, multM A (liftM A (M A) (unitM A)  x) = x.
Axiom M_coh3 : forall A x, multM A (multM (M A) x) = multM A (liftM (M (M A)) (M A) (multM A) x). 

(* when A is subsingleton, A \simeq M A *)
Axiom elimM : forall A, (forall x y : A, x = y) -> is_equiv (unitM A).

Definition singletonM : forall A, isSubsingleton A -> M A -> A.
Proof.
  intros.
  exact (projP1 _ _ (elimM A H) X).
Defined.

(* lifting of a constant function is constant. This is because unit is preserved by M. *)
Lemma Munit_is_singleton : forall a : M unit, a = unitM _ tt.
Proof.
  intros.
  pose proof (elimM unit).
  assert (forall x y : unit, x = y).
  intros.
  destruct x, y; auto.
  destruct (X H).
  destruct a0.
  unfold fc, id in H1.
  apply (lp _ _ (fun k => k a)) in H1.
  rewrite (H (x a) (tt)) in H1.
  auto.
Defined.

Lemma Munit_is_subsingleton : isSubsingleton (M unit).
Proof.
  intros x y.
  rewrite (Munit_is_singleton x).
  rewrite (Munit_is_singleton y).
  auto.
Defined.

Lemma fun_to_subsingleton_id : forall {A B} (f g : A -> B), isSubsingleton B -> f = g.
Proof.
  intros.
  apply fun_ext.
  intros.
  apply H.
Defined.
  
Lemma constantM : forall {A B} b, liftM A B (fun _  => b) = fun _ => unitM _ b.
Proof.
  intros.
  pose proof (liftM_axiom1 A unit B (fun _ => tt) (fun _ => b)).
  rewrite H.
  assert
    (
      (liftM A unit (fun _ : A => tt) )
      =
      (fc  (unitM unit) (fun _ : M A => tt))
    ).
  apply fun_to_subsingleton_id.
  apply Munit_is_subsingleton.
  rewrite H0.
  pose proof (unitM_ntrans unit B (fun _ => b) tt).
  unfold fc.
  rewrite H1.
  auto.
Defined.

Definition mjoin (p q : Prop) (T : Type) : ({p}+{q} -> T) ->  M ({p}+{q}) -> M T.
Proof.
  intros f x.
  exact (liftM _ _ f x).
Defined.

(* we can get sections from repeated M-valued procedures. *)
Axiom Mrec :
  forall P : nat -> Type,
  forall R : (forall n, P n -> P (S n) -> Prop),
    M (P O) ->
    (forall n (x : P n), M {y : P (S n) | R n x y}) ->
    M {f : forall n, (P n) | forall m, R m (f m) (f (S m))}.

Definition MprojP1 : forall A (P : A -> Prop), M {x : A | P x} -> M A.
Proof.
  intros.
  apply (liftM {x : A | P x}).
  intro.
  destruct X0.
  exact x.
  exact X.
Defined.  

Definition recM :
  forall P : nat -> Type,
  forall R : (forall n, P n -> P (S n) -> Prop),
    M (P O) ->
    (forall n (x : P n), M {y : P (S n) | R n x y}) ->
    forall n, M (P n).
Proof.
  intros P R X f.
  apply nat_rect.
  exact X.
  intros.
  pose proof (f n).
  apply (lift_domM (P n)).
  intro.
  exact (MprojP1 _ _ (X1 X2)).
  exact X0.
Defined.

Definition countableMinv : forall P : nat -> Type,
    M (forall n, P n) -> (forall n, M (P n)).
Proof.
  intros P X n.
  apply (liftM _ _ (fun f => f n) X).
Defined.

Axiom Mrec_prop : forall P R X f, countableMinv _ (MprojP1 _ _ (Mrec P R X f)) = recM P R X f.
  
(* Definition Mrec_Mproj1 : *)
(*   forall P : nat -> Type, *)
(*   forall R : (forall n, P n -> P (S n) -> Prop), *)
(*     M (P O) -> *)
(*     (forall n (x : P n), M {y : P (S n) | R n x y}) -> *)
(*     M {f : forall n, (P n) | forall m, R m (f m) (f (S m))}. *)

                          
Definition countableLiftM : forall P : nat -> Type, (forall n, M (P n)) -> M (forall n, P n).
Proof.
  intros P f.
  pose proof (Mrec P (fun _ _ _ => True) (f O)).
  simpl in X.
  assert ((forall n : nat, P n -> M {_ : P (S n) | True})).
  intros.
  pose proof (f (S n)).
  apply (liftM (P (S n))).
  intro.
  exists X2.
  exact I.
  exact X1.
  pose proof (X X0).
  exact (MprojP1 _ _ X1).
Defined.

(* Axiom countableLiftM : forall P : nat -> Type, (forall n, M (P n)) -> M (forall n, P n).  *)
  

Lemma countableMprop : forall P : nat -> Type, forall f,
      countableMinv P  (countableLiftM P f) = f.
Proof.
  intros P f.
  unfold countableLiftM.
  rewrite (Mrec_prop
                P
                (fun (n : nat) (_ : P n) (_ : P (S n)) => True)
                (f 0)
                (fun (n : nat) (_ : P n) =>
                   liftM (P (S n)) {_ : P (S n) | True} (fun X2 : P (S n) =>
                                                           exist (fun _ : P (S n) => True) X2 I)
                         (f (S n)))).
  apply dfun_ext.
  intro.
  unfold recM.
  induction x.
  simpl.
  auto.
  simpl.
  rewrite IHx.
  simpl.
  unfold MprojP1.
  unfold lift_domM.
  assert (
            liftM {_ : P (S x) | True} (P (S x)) (fun X0 : {_ : P (S x) | True} => let (x0, _) := X0 in x0)
                  (liftM (P (S x)) {_ : P (S x) | True} (fun X0 : P (S x) => exist (fun _ : P (S x) => True) X0 I) (f (S x)))
=
                  ( (f (S x)))           
            
    ).
  pose proof (liftM_axiom1 _ _ _
                           (fun X0 : P (S x) => exist (fun _ : P (S x) => True) X0 I)
                           (fun X0 : {_ : P (S x) | True} => let (x0, _) := X0 in x0)
             ).
  apply (lp  _ _ (fun k => k (f (S x)))) in H.
  rewrite <- H.
  rewrite<- liftM_axiom2.
  exact eq_refl.
  rewrite H.
  assert
    (
      (liftM (P x) (M (P (S x))) (fun _ : P x => f (S x)) (f x))
      =
      unitM _ (f (S x))).

  rewrite constantM.
  exact eq_refl.
  rewrite H0.
  rewrite M_coh1.
  exact eq_refl.
Defined.

  
(* Axiom countableMprop : forall P : nat -> Type, forall f, *)
(*       countableMinv P  (countableLiftM P f) = f. *)

Parameter select : forall x y : K, upK x \/ upK y -> M ({ (upK x) } + { (upK y) }).

Notation "[ x | P ]" := (M {x | P}) : type_scope.
Notation "[ x : T | P ]" := (M {x : T | P}) : type_scope.
Notation "[ ( a , b ) | P ]" := (M (sigT (fun a => {b | P}))) : type_scope.

Definition semidec := fun P : Prop => {x : K | upK x <-> P}.

Definition choose : forall p q, semidec p -> semidec q -> p \/ q -> M ({p}+{q}).
Proof.
  intros.
  destruct H.
  destruct H0.
  destruct i.
  destruct i0.
  apply (liftM ({upK x} + {upK x0})).
  intro.
  destruct H4; auto.
  apply select.
  destruct H1; auto.
Defined.


Definition dec := fun P : Prop =>  {P} + {~ P}.
Lemma semidec_dec : forall P, semidec P -> semidec (~ P) -> dec P.
Proof.
  intros P p q.
  pose proof (choose _ _ p q (lem P)).
  apply singletonM.
  
  intros t1 t2.
  destruct t1, t2.
  induction (irrl _ p0 p1);
    auto.
  induction (n p0).
  induction (n p0).
  induction (irrl _ n n0); auto.
  exact X.
Defined.


Definition extensionM : forall A B, M (A -> B) -> (M A -> M B).
Proof.
  intros.
  apply (lift_domM A).
  intro.
  apply (liftM (A ->B)).
  auto.
  auto.
  auto.
Defined.

