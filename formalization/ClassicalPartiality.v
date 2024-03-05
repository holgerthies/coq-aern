(* Require Import Real. *)
(* Require Import Euclidean. *)
(* Require Import List. *)
(* Require Import Psatz. *)
(* Import ListNotations. *)
(* Require Import Poly. *)
Require Import Base.
Require Import ClassicalMonads.

Definition pc X := Nabla (option X).

Definition pc_unit (A : Type) : A -> pc A := fun x => Nabla_unit _ (Some x).

Definition pc_bot {A : Type} := Nabla_unit (option A) None.

Definition pc_mult (A : Type) : pc (pc A) -> pc A.
Proof.
  intro.
  apply (Nabla_bind2 X).
  intro.
  destruct X0.
  exact p.
  exact pc_bot.
Defined.

Definition pc_lift {A B} (f : A -> B) : pc A -> pc B.
Proof.
  intro.
  apply (Nabla_bind2 X).
  intro.
  destruct X0.
  exact (pc_unit _ (f a)). 
  exact pc_bot.
Defined.

Definition defined_to {X} (x : pc X) (y : X) := x = pc_unit _ y.

Definition defined {X} (x : pc X) := exists t, defined_to x t.

Definition domain {X Y} (f : X -> pc Y) := fun x :X => defined (f x).

Definition comp {X Y Z} (g : Y -> pc Z) (f : X -> pc Y) : X -> pc Z.
Proof.
  intro.
  apply f in X0.
  apply (Nabla_bind2 X0).
  intros y'.
  destruct y' as [y' | _].
  exact (g y').
  exact pc_bot.
Defined.

Lemma comp_iff {X Y Z} (g : Y -> pc Z) (f : X -> pc Y) :
  forall x z, defined_to (comp g f x) z <-> exists y, defined_to (f x) y /\ defined_to (g y) z.
Proof.
  intros.
  split.
  intros.
  unfold comp in H.
  unfold defined_to in H.
  unfold Nabla_bind2 in H.

  pose proof (Nabla_unit_surjective (f x)).
  destruct H0.
  rewrite H0 in H.
  rewrite Nabla_unit_ntrans in H.
  rewrite Nabla_coh1 in H.
  destruct x0.
  exists y.
  rewrite H, H0.
  split; auto;
    unfold defined_to;
    apply eq_refl.
  apply Nabla_unit_mono in H.
  discriminate H.

  intro.
  destruct H as [y [p q]].
  unfold defined_to in p, q.
  unfold defined_to.
  unfold comp.
  unfold Nabla_bind2.
  rewrite p.
  unfold pc_unit.
  rewrite Nabla_unit_ntrans.
  rewrite q.
  rewrite Nabla_coh1.
  auto.
Defined.


Definition pointwise_op {X} {Y} {Z} (f g : X -> pc Y) (o : Y -> Y -> pc Z) : X -> pc Z.
Proof.
  intro.
  pose proof (f X0) as x.
  pose proof (g X0) as y.
  apply (Nabla_bind2 x).
  intro x'.
  apply (Nabla_bind2 y).
  intro y'.
  destruct x' as [x' | x'].
  destruct y' as [y' | y'].
  exact (o x' y').
  exact pc_bot.
  exact pc_bot. 
Defined.

Definition pc_pair {A B} : pc A -> pc B -> pc (A * B).
Proof.
  intros x y.
  apply (Nabla_bind2 x).
  intro x'.
  destruct x'.
  apply (Nabla_bind2 y).
  intro y'.
  destruct y'.
  exact (pc_unit _ (a, b)). 
  exact pc_bot.
  exact pc_bot.
Defined.

Lemma pc_pair_iff {A B} (x : pc A) (y : pc B) :
  forall x' y', 
    defined_to x x' /\ defined_to y y' <-> defined_to (pc_pair x y) (x', y'). 
Proof.
  intros.
  split.
  intros [p q].
  unfold pc_pair.
  unfold Nabla_bind2.
  unfold defined_to in p.
  rewrite p.
  unfold pc_unit.
  rewrite Nabla_unit_ntrans.
  unfold defined_to in q.
  rewrite q.
  unfold pc_lift, pc_unit.

  rewrite Nabla_unit_ntrans.
  rewrite Nabla_coh1.
  rewrite Nabla_coh1.
  unfold defined_to.
  auto.
  intros.
  unfold pc_pair in H.
  unfold Nabla_bind2 in H.
  unfold defined_to in H.
  pose proof (Nabla_unit_surjective x) as [x'' p].
  pose proof (Nabla_unit_surjective y) as [y'' q].
  rewrite p, q in H.
  rewrite Nabla_unit_ntrans in H.
  rewrite Nabla_coh1 in H.
  destruct x''.
  
  rewrite Nabla_unit_ntrans in H.
  rewrite Nabla_coh1 in H.
  destruct y''.
  apply Nabla_unit_mono in H.
  injection H; intros.
  induction H0, H1.
  rewrite p, q.
  unfold defined_to; auto.
  apply Nabla_unit_mono in H.
  discriminate H.
  apply Nabla_unit_mono in H.
  discriminate H.
Defined.

Lemma pc_pair_fst_bot {A B} (x : pc B) : @pc_pair A B pc_bot x = pc_bot.
Proof.
  unfold pc_pair.
  unfold Nabla_bind2.
  unfold pc_bot.
  rewrite Nabla_unit_ntrans.
  rewrite Nabla_coh1.
  auto.
Defined.

Lemma pc_case {A} : forall x : pc A, x = pc_bot \/ exists x', x = pc_unit _ x'.
Proof.
  intros.
  destruct (Nabla_unit_surjective x).
  destruct x0.
  right.
  exists a; auto.
  left; auto.
Defined.


Lemma pc_pair_snd_bot {A B} (x : pc A) : @pc_pair A B x pc_bot = pc_bot.
Proof.
  unfold pc_pair.
  unfold Nabla_bind2.
  unfold pc_bot.
  destruct (pc_case x).
  induction (eq_sym H).
  unfold pc_bot.
  rewrite Nabla_unit_ntrans.
  rewrite Nabla_coh1.
  auto.
  destruct H.
  rewrite H.
  unfold pc_unit.
  rewrite Nabla_unit_ntrans.
  rewrite Nabla_coh1.
  rewrite Nabla_unit_ntrans.
  rewrite Nabla_coh1.
  auto.
Defined.

Lemma pc_unit_mono : forall (A : Type) (x y : A), pc_unit A x = pc_unit A y -> x = y.
Proof.
  intros.
  apply Nabla_unit_mono in H.
  injection H; auto.
Defined.

Lemma pc_pair_bot_case {A B} {x} {y} : @pc_pair A B x y = pc_bot -> x = pc_bot \/ y = pc_bot.
Proof.
  intro.
  destruct (pc_case x).
  left; auto.
  destruct (pc_case y).
  right; auto.
  destruct H0 as [x' p].
  destruct H1 as [y' q].
  pose proof (pc_pair_iff x y x' y').
  destruct H0.
  pose proof (H0 (conj p q)).
  rewrite H2 in H.
  apply Nabla_unit_mono in H.
  discriminate H.
Defined.

Lemma pc_unit_ntrans : forall (A B : Type) (f : A -> B) (x : A),
    pc_lift f (pc_unit A x) = pc_unit B (f x).
Proof.
  intros.
  unfold pc_lift.
  unfold pc_unit.
  unfold Nabla_bind2.
  unfold pc_unit.
  rewrite Nabla_unit_ntrans.
  rewrite Nabla_coh1.
  auto.
Defined.

Lemma pc_lift_bot : forall {A B} (f : A -> B),
    pc_lift f pc_bot = pc_bot.
Proof.
  intros.
  unfold pc_lift.
  unfold Nabla_bind2.
  unfold pc_bot.
  rewrite Nabla_unit_ntrans.
  rewrite Nabla_coh1.
  auto.
Defined.


Lemma pc_mult_ntrans : forall (A B : Type) (f : A -> B) (x : pc (pc A)),
    pc_mult B (pc_lift (pc_lift f) x) = pc_lift f (pc_mult A x).
Proof.
Admitted.


Definition pc_bind {A B} (f : A -> pc B) : pc A -> pc B.
Proof.
  intro.
  apply pc_mult.
  apply (pc_lift f).
  exact X.
Defined.

Lemma pc_bot_defined_to_absurd {A} : forall {x : A}, defined_to pc_bot x -> False.
Proof.
  intros.
  apply Nabla_unit_mono in H.
  discriminate H.
Defined.

Definition pc_lift2 {A B C} (f : A -> B -> C) : pc A -> pc B -> pc C.
Proof. 
  intros.
  pose proof (pc_pair X X0).
  apply (pc_lift (fun x => f (fst x) (snd x))).
  exact X1.
Defined.

Definition pc_lift2_fst_bot {A B C} (f : A -> B -> C) x : 
  pc_lift2 f pc_bot x = pc_bot.
Proof.
  unfold pc_lift2.
  rewrite pc_pair_fst_bot. 
  rewrite pc_lift_bot.
  auto.
Defined.

Definition pc_lift2_snd_bot {A B C} (f : A -> B -> C) x : 
  pc_lift2 f x pc_bot = pc_bot.
Proof.
  unfold pc_lift2.
  rewrite pc_pair_snd_bot. 
  rewrite pc_lift_bot.
  auto.
Defined.

Definition pc_lift2_iff {A B C} (f : A -> B -> C) :
  forall x y z',
    defined_to (pc_lift2 f x y) z' <-> exists x' y', defined_to x x' /\ defined_to y y' /\ z' = f x' y'.
Proof.
  intros.
  split.
  intro.
  destruct (pc_case x).
  rewrite H0 in H.
  unfold pc_lift2 in H.
  rewrite pc_pair_fst_bot in H.
  rewrite pc_lift_bot in H.
  contradiction (pc_bot_defined_to_absurd H).
  destruct (pc_case y).
  rewrite H1 in H.
  unfold pc_lift2 in H.
  rewrite pc_pair_snd_bot in H.
  rewrite pc_lift_bot in H.
  contradiction (pc_bot_defined_to_absurd H).
  destruct H0 as [x' p].
  destruct H1 as [y' q].
  exists x', y'.
  split.
  exact p.
  split.
  exact q.
  
  unfold defined_to in H.
  unfold pc_lift2 in H.
  destruct (pc_pair_iff x y x' y') as [l _].
  pose proof (l (conj p q)).
  rewrite H0 in H.
  rewrite pc_unit_ntrans in H.
  simpl in H.
  apply pc_unit_mono in H.
  rewrite H; auto.

  intros [x' [y' [p [q r]]]].
  rewrite r.
  unfold pc_lift2.
  destruct (pc_pair_iff x y x' y') as [l _].
  pose proof (l (conj p q)).
  rewrite H.
  rewrite pc_unit_ntrans.
  simpl.
  apply eq_refl.
Defined.

Definition pc_unit_ntrans2 {A B C} (f : A -> B -> C) x y :
  pc_lift2 f (pc_unit _ x) (pc_unit _ y) = pc_unit _ (f x y).
Proof.
  unfold pc_lift2.
  destruct (pc_pair_iff (pc_unit A x) (pc_unit B y) x y).
  pose proof (H (conj eq_refl eq_refl)).
  rewrite H1.
  apply pc_unit_ntrans.
Defined.

  
Definition pc_hprop_lem {A} : forall P, is_hprop P -> ((P + neg P) -> pc A) -> pc A.
Proof.
  intros.
  exact (Nabla_hprop_lem P H X).
Defined.

Definition pc_hprop_lem_reduce {A} P (h : is_hprop P) :
  forall (f : (P + neg P) -> pc A) t,
    pc_hprop_lem P h f = f t. 
Proof.
  intros.
  apply Nabla_hprop_lem_reduce.
Defined.



Definition pc_Prop_lem {A} : forall P : Prop, ((P + ~ P) -> pc A) -> pc A.
Proof.
  intro P.
  assert (is_hprop P).
  intros x y.
  apply irrl.
  apply Nabla_hprop_lem.
  exact H.
Defined.


Definition pc_hprop_lem_reduce_eq A P (h : is_hprop P) :
  forall (f : ((P + neg P) -> pc A)) y,
    (forall t : P, f (inl t) = y) ->  (forall t : neg P, f (inr t) = y) ->
    @pc_hprop_lem A P h f = y.
Proof.
  intros.
  apply Nabla_hprop_lem_reduce_eq; auto.
Defined.


Definition pc_ana_fun A B := {S : A * B -> Prop | forall x y1 y2, S (x, y1) -> S (x, y2) -> y1 = y2}.

Definition pc_ana_fun_to_pc_fun A B : pc_ana_fun A B -> A -> pc B.
Proof.
  intros [S p] x. 
  apply (pc_hprop_lem ({y | S (x, y)})).
  intros [a h1] [b h2].
  pose proof (p x a b h1 h2).
  destruct H.
  rewrite (irrl _ h1 h2).
  apply eq_refl.
  intros [l|r].
  destruct l.
  exact (pc_unit _ x0).
  exact pc_bot.
Defined.

Definition pc_ana_fun_to_pc_fun_defined_to A B : forall f : pc_ana_fun A B,
  forall x,
    forall fx, projP1 _ _ f (x, fx) <-> defined_to (pc_ana_fun_to_pc_fun A B f x) fx.
Proof.
  intros.
  split.
  destruct f.
  simpl.
  intro.
  apply pc_hprop_lem_reduce_eq.
  intros.
  destruct t.
  rewrite (e _ _ _ H x2).
  auto.
  intros.
  assert False.
  apply t.
  exists fx.
  auto.
  contradiction H0.
  intros.
  destruct f.
  simpl.
  unfold pc_ana_fun_to_pc_fun in H.
  apply Prop_dn_elim.
  pose proof (dn_lem {y : B | x0 (x, y)}).
  apply (@dn_lift ({y : B | x0 (x, y)} + neg {y : B | x0 (x, y)})).
  intro.
  clear H0.
  destruct X.
  destruct s.
  assert (pc_unit _  x1 = pc_unit B fx).
  rewrite <- H.
  apply eq_sym.
  apply pc_hprop_lem_reduce_eq.
  intros.
  destruct t.
  rewrite (e _ _ _ x2 x4).
  auto.

  intros.
  assert False.
  apply t.
  exists x1; auto.
  contradict H0.

  apply pc_unit_mono in H0.
  rewrite H0 in x2; auto.
  assert (pc_bot = pc_unit B fx).
  rewrite <- H.
  apply eq_sym.
  apply pc_hprop_lem_reduce_eq.
  intros.
  contradict (n t).
  intros.
  auto.
  contradict H0.
  intro.
  apply (@pc_bot_defined_to_absurd B fx).
  auto.
  auto.
Defined.

Definition pc_ana_fun_to_pc_fun_bot A B : forall f : pc_ana_fun A B,
  forall x,
    (~ exists fx, projP1 _ _ f (x, fx)) <->  (pc_ana_fun_to_pc_fun A B f x) = pc_bot.
Proof.
  intros.
  split.
  intro.
  destruct f.
  simpl.
  apply pc_hprop_lem_reduce_eq.
  intros.
  destruct t.
  contradict H.
  exists x1.
  simpl.
  auto.
  auto.
  intros.
  intro.
  destruct H0.
  destruct f.
  simpl in H0, H.
  apply Prop_dn_elim.
  pose proof (dn_lem {y : B | x1 (x, y)}).
  apply (@dn_lift ({y : B | x1 (x, y)} + neg {y : B | x1 (x, y)})).
  intro.
  clear H1.
  destruct X.
  destruct s.
  assert (pc_unit _  x0 = pc_bot).
  rewrite <- H.
  apply eq_sym.
  apply pc_hprop_lem_reduce_eq.
  intros.
  destruct t.
  
  rewrite (e _ _ _ H0 x5).
  auto.
  intro.
  assert (False).
  apply t.
  exists x0; auto.
  contradict H1.
  apply (@pc_bot_defined_to_absurd B x0).
  apply eq_sym in H1.
  auto.
  apply n.
  exists x0; auto.
  auto.
Defined.    

Definition is_total_fun {A B} (f : A -> pc B) := forall a, defined (f a). 
