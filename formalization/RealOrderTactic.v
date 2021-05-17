Require Import Base.
Require Import Kleene.
Require Import RealAxioms.
Require Import RealRing.
Require Import RealOrder.


Open Scope Real_scope.



(* Lemma Reallt_add_r : forall z x y, x + z < y + z -> x < y. *)
(* Proof. *)
(*   intros. *)
(*   pose proof (Reallt_plus_lt (-z) _ _ H). *)
(*   ring_simplify in H0. *)
(*   exact H0. *)
(* Qed. *)

(* Lemma Realgt_add_r : forall z x y, x + z > y + z -> x > y. *)
(* Proof. *)
(*   intros. *)
(*   pose proof (Reallt_plus_lt (-z) _ _ H). *)
(*   ring_simplify in H0. *)
(*   exact H0. *)
(* Qed. *)


(* Lemma Realle_add_r : forall z x y, x + z <= y + z -> x <= y. *)
(* Proof. *)
(*   intros. *)
(*   destruct H. *)
(*   left. *)
(*   exact (Reallt_add_r z x y H). *)
(*   right. *)
(*   pose proof (lp _ _ (fun k => k - z) _ _ H). *)
(*   simpl in H0. *)
(*   ring_simplify in H0. *)
(*   exact H0. *)
(* Qed. *)

(* Lemma Realge_add_r : forall z x y, x + z >= y + z -> x >= y. *)


Lemma Realle_plus_le : forall z x y, x <= y -> z + x <= z + y.
Proof.
  intros.
  destruct H.
  left.
  apply Reallt_plus_lt.
  exact H.
  right.
  apply (lp _ _ (fun x => z + x)) in H.
  exact H.
Qed.


Lemma Realge_plus_ge : forall z x y, x >= y -> z + x >= z + y.
Proof.
  intros.
  destruct H.
  left.
  apply Reallt_plus_lt.
  exact H.
  right.
  apply (lp _ _ (fun x => z + x)) in H.
  exact H.
Qed.


Inductive ltac_No_arg : Set :=
  | ltac_no_arg : ltac_No_arg.


Ltac Tac_Real_order s t :=
  match (type of s) with
  |  (?A < ?B) =>
     match (type of t) with
     | Real =>
       ((apply (Reallt_plus_lt t _ _) in s);
        ring_simplify in s)
     | ltac_No_arg =>
       ((apply (Reallt_plus_lt (- B) _ _) in s);
        ring_simplify in s)
     | _ => fail "has to be Real"
     end
       
  | (?A <= ?B) =>
    match (type of t) with
    | Real =>
      ((apply (Realle_plus_le t _ _) in s);
       ring_simplify in s)
    | ltac_No_arg =>
      ((apply (Realle_plus_le (- B) _ _) in s);
       ring_simplify in s)
    | _ => fail "has to be Real"
    end
      
  |  (?A >= ?B) =>
     match (type of t) with
     | Real =>
       ((apply (Realge_plus_ge t _ _) in s);
        ring_simplify in s)
     | ltac_No_arg =>
       ((apply (Realge_plus_ge (- B) _ _) in s);
        ring_simplify in s)
     end
       
  | _ =>
    match goal with
    | |- (?A < ?B) =>
      match (type of s) with
      | Real =>
        (apply (Reallt_add_r s _ _);
         ring_simplify )
      | ltac_No_arg =>
        ((apply (Reallt_add_r (- B) _ _));
         ring_simplify)
      | _ => fail "has to be Real"
      end
        
    |  |- (?A <= ?B) =>
       match (type of s) with
       | Real =>
         (apply (Realle_add_r s _ _);
          ring_simplify)
       | ltac_No_arg =>
         ((apply (Realle_add_r (- B) _ _));
          ring_simplify)
       | _ => fail "has to be Real"
       end         
    |  |- (?A >= ?B) =>
       
       match (type of s) with
       | Real =>
         (apply (Realge_add_r s _ _);
          ring_simplify)
       | ltac_No_arg =>
         ((apply (Realge_add_r (- B) _ _));
          ring_simplify)
       | _ => fail "has to be Real"
       end
         
    | |- ?A => fail "cannot clean the ineqaulity" s
    end
  end
.

Tactic Notation "add_both_side_by" :=
  Tac_Real_order ltac_no_arg ltac_no_arg.
Tactic Notation "add_both_side_by" constr(x) :=
  Tac_Real_order x ltac_no_arg.
Tactic Notation "add_both_side_by" constr(x) constr(y) :=
  Tac_Real_order x y.



(* Goal forall z x y, x + z >= y + z -> x >= y. *)
(*   intros. *)
(*   add_both_side_by. *)
(*   add_both_side_by (-x). *)
(*    H (-z). *)
(*   mv_all_left. *)
          
  (* | |- (¬¬ ?A) => *)
  (*   match (type of s) with *)
  (*   | ¬¬ ?T => *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)

  (*   | ¬ ¬ ?T => *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)

  (*   | ↑↓ ?T => *)
  (*     apply sdn in s; *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)

  (*   | ↑ (↓ ?T) => *)
  (*     apply sdn in s; *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)

        
  (*   | _ => fail "type of the argument is supposed to be ¬¬ ?A" *)
  (*   end *)
      
  (* | |- neg (neg _) => *)
  (*   match (type of s) with *)
  (*   | ¬¬ ?T => *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)

  (*   | ¬ ¬ ?T => *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)
  (*   | ↑↓ ?T => *)
  (*     apply sdn in s; *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)
  (*   | ↑ (↓ ?T) => *)
  (*     apply sdn in s; *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)
 
  (*   | _ => fail "type of the argument is supposed to be ¬¬ ?A" *)

  (*   end *)
  (* | |- ↑ ?A => *)
  (*   match (type of s) with *)
  (*   | ¬¬ ?T => *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)

  (*   | ¬ ¬ ?T => *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)

  (*   | ↑↓ ?T => *)
  (*     apply sdn in s; *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)

  (*   | ↑ (↓ ?T) => *)
  (*     apply sdn in s; *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)

  (*   | _ => fail "type of the argument is supposed to be ¬¬ ?A" *)
  (*   end *)
  (* | |- updown ?A => *)
  (*   match (type of s) with *)
  (*   | ¬¬ ?T => *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)

  (*   | ¬ ¬ ?T => *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)

  (*   | ↑↓ ?T => *)
  (*     apply sdn in s; *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)

  (*   | ↑ (↓ ?T) => *)
  (*     apply sdn in s; *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in intro st; apply st in s; clear st)) *)
  (*     + *)
  (*     ((apply (cprop_dn_elim_intro T)); *)
  (*      (let st := (fresh s) in *)
  (*       intro st; *)
  (*       let stt := (fresh st) in pose proof (st s) as stt; clear st)) *)

        
  (*   | _ => fail "type of the argument is supposed to be ¬¬ ?A" *)
  (*   end *)
  (* | |- ?A => fail "Goal has to be either ¬¬ ?A or ↑ ?A But " A " is given" *)
  (* end. *)
