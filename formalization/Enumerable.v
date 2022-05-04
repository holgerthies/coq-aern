Require Import Base.

Definition Cantor_encoding : (nat * nat) -> nat.
Admitted.
Definition Cantor_decoding : nat -> (nat * nat).
Admitted.
Lemma Cantor_pairing : forall n m, Cantor_decoding (Cantor_encoding (n, m)) = (n, m).
Admitted.

Definition is_enum (X : Type) :=
  {e : nat -> X & forall x, {n | e n = x} }.

Definition is_retract {X Y : Type} (r : Y -> X) :=
  {s : X -> Y | forall x : X, r (s x) = x}.

Definition retract (Y X : Type) := {r : Y -> X & is_retract r}. 

Lemma retract_is_enum : forall X Y, retract X Y -> is_enum X -> is_enum Y.
Proof.
  intros X Y e en.
  destruct e as [e i].
  destruct en as [ex px].
  exists (fun n => e (ex n)).
  intro y.
  destruct i.
  destruct (px (x y)).
  exists x0.
  rewrite e1.
  exact (e0 y).  
Defined.  

Lemma nat_is_enum : is_enum nat.
Proof.
  exists (fun n => n).
  intro.
  exists x.
  apply eq_refl.
Defined.

Lemma bool_is_enum_aux : nat -> bool.
Proof.
  intro n.
  destruct n.
  exact true.
  exact false.
Defined.

Lemma bool_is_enum : is_enum bool.
Proof.
  exists bool_is_enum_aux.
  intro b.
  destruct b.
  exists O.
  auto.
  exists (S O).
  auto.
Defined.

Require Import ZArith.
  
Lemma nat_retracts_positive : retract nat positive.
Proof.
  exists Pos.of_nat.
  exists Pos.to_nat.
  apply Pos2Nat.id.
Defined.

Definition tp_retracts_Z_aux : ((unit + (unit + unit)) * positive) -> Z.
Proof.
  intros.
  destruct H.
  destruct s.
  exact Z0.
  destruct s.
  exact (Zpos p).
  exact (Zneg p).
Defined.

Definition tp_retracts_Z_aux2 : Z ->((unit + (unit + unit)) * positive).
Proof.
  intros z.
  destruct z.
  split.
  left.
  exact tt.
  exact xH.

  split.
  right; left; exact tt.
  exact p.

  split.
  right; right; exact tt.
  exact p.
Defined.

Lemma tp_retracts_Z : retract ((unit + (unit + unit)) * positive) Z.
Proof.
  exists tp_retracts_Z_aux.
  exists tp_retracts_Z_aux2.
  intro z.
  destruct z; auto.
Defined.



Lemma enum_product_is_enum : forall X Y, is_enum X -> is_enum Y -> is_enum (X * Y).
Proof.
  intros X Y ex ey.
  destruct ex as [ex px].
  destruct ey as [ey py].
  exists (fun n => (ex (fst (Cantor_decoding n)), ey (snd (Cantor_decoding n)))).
  intro x.
  destruct x as [x y].
  
  destruct (px x) as [i qx]. 
  destruct (py y) as [j qy]. 
  exists (Cantor_encoding (i, j)).
  rewrite Cantor_pairing.
  simpl.
  rewrite qx, qy.
  apply eq_refl.
Defined.

Definition tp_is_enum_aux : nat -> (unit + (unit + unit)).
Proof.
  intro n.
  destruct n.
  left; exact tt.
  destruct n.
  right; left; exact tt.
  right; right; exact tt.
Defined.  
  
Lemma tp_is_enum : is_enum (unit + (unit + unit)).
Proof.
  exists tp_is_enum_aux.
  intro.
  destruct x.
  destruct u.
  exists O; auto.
  destruct s.
  destruct u.
  exists 1; auto.
  destruct u.
  exists 2; auto.
Defined.

Lemma enum_sigma_is_enum_aux : forall X (P : X -> Type), is_enum X -> (forall x, is_enum (P x)) -> nat -> {x & P x}.
Proof.
  intros.
  destruct X0.
  exists (x (fst (Cantor_decoding H))).
  destruct (X1 (x (fst (Cantor_decoding H)))).
  exact (x0 (snd (Cantor_decoding H))).
Defined.
  
Lemma enum_sigma_is_enum : forall X (P : X -> Type), is_enum X -> (forall x, is_enum (P x)) -> is_enum {x & P x}.
Proof.
  intros.
  exists (enum_sigma_is_enum_aux X P X0 X1).
  intro.
  unfold enum_sigma_is_enum_aux.
  destruct x.
  destruct (X0).
  case_eq (X1 x).
  intros.
  destruct (s x).
  destruct (s0 p).
  exists (Cantor_encoding (x2, x3)).
  simpl.
  rewrite Cantor_pairing.
  simpl.
  rewrite e.
  rewrite H.
  rewrite e0.
  apply eq_refl.
Defined.

Definition bool_sigma_retracts_coprod_aux : forall X Y,  ({b : bool & if b then X else Y}) -> (X + Y).
Proof.
  intros.
  destruct X0.
  destruct x.
  left; exact y.
  right; exact y.
Defined.

Definition bool_sigma_retracts_coprod_aux2 : forall X Y,  (X + Y) -> ({b : bool & if b then X else Y}).
Proof.
  intros.
  destruct X0.
  exists true.
  exact x.
  exists false.
  exact y.
Defined.


Lemma bool_sigma_retracts_coprod : forall X Y, retract ({b : bool & if b then X else Y}) (X + Y).
Proof.
  intros.
  exists (bool_sigma_retracts_coprod_aux X Y).
  exists (bool_sigma_retracts_coprod_aux2 X Y).
  intro.
  destruct x; simpl; auto.
Defined.
  
Lemma enum_coproduct_is_enum : forall X Y, is_enum X -> is_enum Y -> is_enum (X + Y).
Proof.
  intros X Y ex ey.
  apply (retract_is_enum _ _ (bool_sigma_retracts_coprod X Y)).
  apply enum_sigma_is_enum.
  apply bool_is_enum.
  intro.
  destruct x; auto.
Defined.
  
Lemma Z_is_enum : is_enum Z. 
Proof.
  apply (retract_is_enum _ _ tp_retracts_Z).
  apply enum_product_is_enum.
  apply tp_is_enum.
  apply (retract_is_enum _ _ nat_retracts_positive).
  apply nat_is_enum.
Defined.

