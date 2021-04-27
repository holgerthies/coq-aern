Require Import Real.
Require Import Reals.

(* Parameter classical : Real -> R. *)

(* (* structure homomorphism *) *)
(* Axiom classical_const0 : classical Real0 = R0. *)
(* Axiom classical_const1 : classical Real1 = R1. *)
(* Axiom classical_addition : forall x y, classical (x + y) = (classical x + classical y)%R. *)
(* Axiom classical_multiplication : forall x y, classical (x * y) = (classical x * classical y)%R. *)
(* Axiom classical_subtraction : forall x, classical (- x) = (- classical x)%R. *)
(* Axiom classical_division : forall x (p : x <> Real0), classical (/ p) = (/classical x)%R. *)

(* Axiom classical_lt : forall x y, (x < y) <-> (classical x < classical y)%R. *)

(* (* order completion... *) *)
(* Definition Prop_convert :  (Real -> Prop) -> (R -> Prop). *)
(* Proof. *)
(*   intros. *)
(*   exact (forall x : Real, classical x = H -> X x ). *)
(* Defined. *)


(* Axiom transport_eq : forall x y :R, x = y -> forall a b, classical a = x -> classical b = y -> a = b. *)
(* Axiom transport_forall : forall P : Real -> Prop, (forall x : R, (Prop_convert P) x) -> (forall x : Real, P x). *)
(* Axiom transport_exists : forall P : Real -> Prop, (exists x : R, (Prop_convert P) x) -> (exists x : Real, P x). *)
(* Goal Real1 + Real0 = Real1. *)
(* Proof. *)
(*   assert (R1 + R0 = R1)%R. *)
(*   ring. *)
(*   apply (transport_eq _ _ H). *)
(*   apply classical_addition. *)
(*   exact classical_constant1. *)
(*   exact relator_constant0. *)
(*   exact relator_constant1. *)
(* Qed. *)


(* Goal forall x : Real, exists y : Real, x = - y. *)
(* Proof. *)
(*   intros. *)
(*   apply transport_exists. *)
(*   unfold mymy. *)
(*   apply (transport_forall). *)
(*   intro. *)
(*   unfold mymy. *)
(*   intro. *)
(*   intro. *)
(*   destruct (ana x). *)
(*   exists (- x0)%R. *)
(*   intro. *)
(*   intro. *)
  
  
(*   admit. *)
(*   exact x. *)


(* Axiom classical_multiplication : classical Real0 = R0. *)
(* Axiom classical_const0 : classical Real0 = R0. *)
(* Axiom classical_const0 : classical Real0 = R0. *)
(* Axiom classical_const0 : classical Real0 = R0. *)
(* Axiom classical_const0 : classical Real0 = R0. *)


Parameter relator : Real -> R -> Prop.

(* relator homomorphism *)
Axiom relator_constant0 : relator Real0 R0.
Axiom relator_constant1 : relator Real1 R1.
Axiom relator_addition : forall x y a b, relator x a -> relator y b -> relator (x + y) (a + b)%R.
Axiom relator_multiplication : forall x y a b, relator x a -> relator y b -> relator (x * y) (a * b)%R.
Axiom relator_subtraction : forall x a, relator x a ->  relator (-x) (-a)%R.
Axiom relator_divison : forall x (p : x <> Real0) a b, relator x a -> relator (/ p) (/b)%R. 

(* relator is an anafunction *)
Axiom ana1 : forall x : Real, exists! y : R, relator x y.
(* Axiom ana2 : forall x : R, exists! y : Real, relator y x. *)



Lemma relator_unique_R : forall x y a b, relator x a -> relator y b -> x = y -> a = b.
Proof.
  intros.
  rewrite H1 in H.
  destruct (ana1 y).
  destruct H2.
  rewrite <- (H3 _ H).
  rewrite <- (H3 _ H0).
  exact (eq_refl _).
Qed.

Axiom relator_unique_Real : forall x y a b, relator x a -> relator y b -> a = b -> x = y.
(* Proof. *)
(*   intros. *)
(*   rewrite H1 in H. *)
(*   destruct (ana2 b). *)
(*   destruct H2. *)
(*   rewrite <- (H3 _ H). *)
(*   rewrite <- (H3 _ H0). *)
(*   exact (eq_refl _). *)
(* Qed. *)
-
(* Axiom transport_eq : forall x y : R, (x = y -> forall a b, relator a x -> relator b y -> a = b).  *)

Axiom transport_eq : forall a b : Real, (forall x y, relator a x -> relator b y -> x = y) -> a = b.
Axiom transport_lt : forall a b : Real, (forall x y, relator a x -> relator b y -> (x < y)%R) -> a < b.
Axiom transport_eq_inv : forall a b x y, relator a x -> relator b y -> a = b -> x = y.
Axiom transport_lt_inv : forall a b x y, relator a x -> relator b y -> (a < b) -> (x < y)%R.

Lemma transport_eq2 : forall a b x y, relator a x -> relator b y -> x = y -> a = b.
Proof.
  apply relator_unique_Real.
Defined.


Lemma transport_lt2 : forall a b x y, relator a x -> relator b y -> (x < y)%R -> a < b.
Proof.
  intros.
  apply transport_lt.
  intros.
  induction (relator_unique_R _ _ _ _ H H2).
  induction (relator_unique_R _ _ _ _ H0 H3).
  exact H1.
  apply eq_refl. 
  apply eq_refl. 
Defined.
  

Definition transport_fiber : (Real -> Prop) -> (R -> Prop).
Proof.
  intros.
  exact (forall x : Real, relator x H -> X x).
Defined.


Definition transport_leq : forall a b : Real, (forall x y, relator a x -> relator b y -> (x <= y)%R) -> a <= b.
Proof.
  intros.
  destruct (ana1 a) as [aa [hh _]].
  destruct (ana1 b) as [bb [jj _]].
  pose proof (H _ _ hh jj).
  destruct H0.
  left.
  apply (transport_lt2 _ _ _ _ hh jj H0).
  right; apply (transport_eq2 _ _ _ _ hh jj H0).
Qed.


Definition transport_geq : forall a b : Real, (forall x y, relator a x -> relator b y -> (x >= y)%R) -> a >= b.
Proof.
  intros.
  destruct (ana1 a) as [aa [hh _]].
  destruct (ana1 b) as [bb [jj _]].
  pose proof (H _ _ hh jj).
  destruct H0.
  left.
  apply (transport_lt2 _ _ _ _ jj hh H0).
  right; apply (transport_eq2 _ _ _ _ hh jj H0).
Qed.

Definition transport_neq : forall a b : Real, (forall x y, relator a x -> relator b y -> (x <> y)%R) -> a <> b.
Proof.
  intros.
  destruct (ana1 a) as [aa [hh _]].
  destruct (ana1 b) as [bb [jj _]].
  pose proof (H _ _ hh jj).
  intro.
  
  destruct H0.
  induction H1.
  apply (relator_unique_R _ _ _ _ hh jj).
  apply eq_refl.
Qed.


Definition transport_forall : forall P : Real -> Prop, (forall x : R, (transport_fiber P) x) -> (forall x : Real, P x).
  intros.
  unfold transport_fiber in H.
  destruct (ana1 x).
  destruct H0.
  exact (H x0 x H0).
Defined.
  

(* Definition transport_exists : forall P : Real -> Prop, (exists x : R, (transport_fiber P) x) -> (exists x : Real, P x). *)
(* Proof. *)
(*   intros. *)
(*   destruct H. *)
(*   unfold transport_fiber in H. *)
(*   destruct (ana2 x). *)
(*   destruct H0. *)
(*   exists x0. *)
(*   exact (H _ H0). *)
(* Defined. *)


Definition transport_leq_inv : forall a b x y, relator a x -> relator b y -> (a <= b) -> (x <= y)%R.
Proof.
  intros.
  destruct H1.
  left.
  apply (transport_lt_inv a b x y H H0).
  exact H1.
  right.
  induction H1.
  apply (relator_unique_R _ _ _ _ H H0 (eq_refl _)).
Qed.

Definition transport_geq_inv : forall a b x y, relator a x -> relator b y -> (a >= b) -> (x >= y)%R.
Proof.
  intros.
  destruct H1.
  left.
  apply (transport_lt_inv b a y x  H0 H).
  exact H1.
  right.
  induction H1.
  apply (relator_unique_R _ _ _ _ H H0 (eq_refl _)).
Qed.


Definition transport_neq_inv : forall a b x y, relator a x -> relator b y -> (a <> b) -> (x <> y)%R.
Proof.
  intros.
  intro.
  induction H2.
  exact (H1 (relator_unique_Real _ _ _ _ H H0 (eq_refl _))).
Defined.


Ltac Holger s :=
  match type of s with
  | ?x = ?y =>
    let xx := fresh "x" in
    let yy := fresh "y" in
    let Hx := fresh "Hx" in
    let Hy := fresh "Hy" in
    let H := fresh "H" in
    
    destruct (ana1 x) as [xx [Hx _ ]];
    destruct (ana1 y) as [yy [Hy _ ]];
    pose proof (transport_eq_inv _ _ _ _ Hx Hy s) as H;
    clear s

  | ?x < ?y =>
    let xx := fresh "x" in
    let yy := fresh "y" in
    let Hx := fresh "Hx" in
    let Hy := fresh "Hy" in
    let H := fresh "H" in
    
    destruct (ana1 x) as [xx [Hx _ ]];
    destruct (ana1 y) as [yy [Hy _ ]];
    pose proof (transport_lt_inv _ _ _ _ Hx Hy s) as H;
    clear s


  | ?x <= ?y =>
    let xx := fresh "x" in
    let yy := fresh "y" in
    let Hx := fresh "Hx" in
    let Hy := fresh "Hy" in
    let H := fresh "H" in
    
    destruct (ana1 x) as [xx [Hx _ ]];
    destruct (ana1 y) as [yy [Hy _ ]];
    pose proof (transport_leq_inv _ _ _ _ Hx Hy s) as H;
    clear s


  | ?x >= ?y =>
    let xx := fresh "x" in
    let yy := fresh "y" in
    let Hx := fresh "Hx" in
    let Hy := fresh "Hy" in
    let H := fresh "H" in
    
    destruct (ana1 x) as [xx [Hx _ ]];
    destruct (ana1 y) as [yy [Hy _ ]];
    pose proof (transport_geq_inv _ _ _ _ Hx Hy s) as H;
    clear s


  | ?x <> ?y =>
    let xx := fresh "x" in
    let yy := fresh "y" in
    let Hx := fresh "Hx" in
    let Hy := fresh "Hy" in
    let H := fresh "H" in
    
    destruct (ana1 x) as [xx [Hx _ ]];
    destruct (ana1 y) as [yy [Hy _ ]];
    pose proof (transport_neq_inv _ _ _ _ Hx Hy s) as H;
    clear s
                    
          
  end.

Definition skip : forall A,A -> A.
Proof.
  intros.
  exact X.
Defined.


Definition Holber0: forall x, relator Real0 x -> x = R0.
Proof.
  intros.
  rewrite (relator_unique_R _ _ _ _ relator_constant0 H (eq_refl _)).
  apply eq_refl.
Qed.

Definition Holber1: forall x, relator Real1 x -> x = R1.
Proof.
  intros.
  rewrite (relator_unique_R _ _ _ _ relator_constant1 H (eq_refl _)).
  apply eq_refl.
Qed.


Definition Holber2 : forall a b x y z, relator x a -> relator y b -> relator (x + y) z ->
                                  z = (a + b)%R.
Proof.
  intros.
  pose proof (relator_addition x y a b H H0).
  exact (relator_unique_R _ _ _ _ H1 H2 (eq_refl _)).
Defined.





Definition Holber3 : forall a b x y z, relator x a -> relator y b -> relator (x * y) z ->
                                  z = (a * b)%R.
Proof.
  intros.
  pose proof (relator_multiplication x y a b H H0).
  exact (relator_unique_R _ _ _ _ H1 H2 (eq_refl _)).
Defined.

Definition Holber4 : forall a  x  z, relator x a -> relator (-x) z ->
                                  z = (-a)%R.
Proof.
  intros.
  pose proof (relator_subtraction x a H).
  exact (relator_unique_R _ _ _ _ H0 H1 (eq_refl _)).
Defined.

Definition Holber6 : forall a  x  z (p : x <> Real0), relator x a -> relator (/p) z ->
                                  z = (/a)%R.
Proof.
  intros.
  pose proof (relator_divison x p a a H).
  exact (relator_unique_R _ _ _ _ H0 H1 (eq_refl _)).
Defined.

Definition Holber7 : forall a b x y z (p : y <> Real0), relator x a -> relator y b -> relator (x / p) z -> z = (a/b)%R.
Proof.
  intros.
  replace (a / b)%R with (a * / b)%R by auto.
  replace (x / p) with (x */ p) in H1 by auto.
  pose proof (relator_divison y p b b H0).
  apply (Holber3 _ _ _ _ _ H H2).
  exact H1.
Defined.


Definition Holber5 : forall a b x y z, relator x a -> relator y b -> relator (x - y) z ->
                                  z = (a - b)%R.
Proof.
  intros.
  replace (a - b)%R with (a + - b)%R by ring.
  replace (x - y) with (x + - y) in H1 by ring.
  pose proof (relator_subtraction y b H0).
  apply (Holber2 _ _ _ _ _ H H2 H1).
Defined.




  
Lemma eq_symm : forall {T} {x y : T}, x = y -> y = x.  
Proof.
  intros.
  rewrite H.
  apply eq_refl.
Defined.

Ltac classical :=
  match goal with
  | |- @eq Real ?x ?y => apply transport_eq;   intro; intro; intro; intro; classical (* (fail "not implemented yet") *)
  | |- ?x < ?y => apply transport_lt; intro; intro; intro; intro; classical
  | |- ?x > ?y => apply transport_lt; intro; intro; intro; intro; classical
  | |- ?x >= ?y => apply transport_geq; intro; intro; intro; intro; classical
  | |- ?x <= ?y => apply transport_leq; intro; intro; intro; intro; classical
  | |- ?x <> ?y => apply transport_neq; intro; intro; intro; intro; classical     
  (* | |- exists x : Real, ?A => apply transport_exists;  intro; intro; intro; classical *)
  | |- forall x : Real, ?A => apply (transport_forall (fun x => A));   intro; intro; intro; classical
  (* | |- forall x : Real, ?A => apply (transport_forall (fun x => A));   intro; intro; intro; classical *)

  | |- ?A => apply skip
  (* | |- ?A => match A with *)
  (*          | ?a = ?b => fail "haha" *)
  (*          | _ => fail "FAIL" A *)
  (*          end  *)


  end.


  
Ltac relate :=
  
  match goal with
  | H : (relator Real0 ?x) |- _ => (apply Holber0 in H; try induction (eq_symm H); clear H; relate)
  | H : (relator Real1 ?x) |- _ => (apply Holber1 in H; try induction (eq_symm H); clear H; relate)
  | H : (relator (?x + ?y) (?z)) |- _ =>
    (idtac ""x; 
     let a := fresh "x" in
     let b := fresh "y" in
     let Ha := fresh "Ha" in
     let Hb := fresh "Hb" in
     let Hc := fresh H in
     (destruct (ana1 x) as [a [Ha _]];
      destruct (ana1 y) as [b [Hb _]];
      pose proof (eq_symm (Holber2 _ _ _ _ _ Ha Hb H)) as Hc;
      induction ( Hc);
      clear Hc;
      clear H;
      relate
    ))

  | H : (relator (?x - ?y) (?z)) |- _ =>
    (idtac " "; 
     let a := fresh "x" in
     let b := fresh "y" in
     let Ha := fresh "Ha" in
     let Hb := fresh "Hb" in
     let Hc := fresh H in
     (destruct (ana1 x) as [a [Ha _]];
      destruct (ana1 y) as [b [Hb _]];
      pose proof (eq_symm (Holber5 _ _ _ _ _ Ha Hb H)) as Hc;
      induction ( Hc);
      clear Hc;
      clear H;
      relate
    ))

  | H : (relator (?x / ?p) (?z)) |- _ =>
    match type of  p with
    | ?y <> Real0 =>
      (idtac "";
       let a := fresh "x" in
       let b := fresh "y" in
       let Ha := fresh "Ha" in
       let Hb := fresh "Hb" in
       let Hc := fresh H in
       (destruct (ana1 x) as [a [Ha _]];
        destruct (ana1 y) as [b [Hb _]];
        pose proof (eq_symm (Holber7 _ _ _ _ _ p Ha Hb H)) as Hc;
        induction ( Hc);
        clear Hc;
        clear H;
        relate
      ))
        
    | _ => idtac "" 
    end
      
  | H : (relator (?x * ?y) (?z)) |- _ =>
    (idtac " "; 
     let a := fresh "x" in
     let b := fresh "y" in
     let Ha := fresh "Ha" in
     let Hb := fresh "Hb" in
     let Hc := fresh H in
     (destruct (ana1 x) as [a [Ha _]];
      destruct (ana1 y) as [b [Hb _]];
      pose proof (eq_symm (Holber3 _ _ _ _ _ Ha Hb H)) as Hc;
      induction ( Hc);
      clear Hc;
      clear H;
      relate
    ))

  | H : (relator (- ?x) (?y)) |- _ =>
    (idtac " "
     ;
     let a := fresh "x" in
     let Ha := fresh "Ha" in
     let Hc := fresh H in
     (destruct (ana1 x) as [a [Ha _]];
      pose proof (eq_symm (Holber3 _ _ _  Ha  H)) as Hc;
      induction ( Hc);
      clear Hc;
      clear H;
      relate
    )
)



  | H : (relator (@Realdiv ?x ?p) (?y)) |- _ =>
    (idtac ""
     (* ;  *)
     (* let a := fresh "x" in *)
     (* let Ha := fresh "Ha" in *)
     (* let Hc := fresh H in *)
     (* (destruct (ana1 x) as [a [Ha _]]; *)
     (*  pose proof (eq_symm (Holber6 _ _ _ p  Ha  H)) as Hc; *)
     (*  induction ( Hc); *)
     (*  clear Hc; *)
     (*  clear H; *)
     (*  relate *)
     (* ) *)
    )
  | H : (relator (/ ?p) (?y)) |- _ =>
    match type of p with
    | ?x <> Real0 =>
      let a := fresh "x" in
      let Ha := fresh "Ha" in
      let Hc := fresh H in
      (destruct (ana1 x) as [a [Ha _]];
       pose proof (eq_symm (Holber6 _ _ _ p  Ha  H)) as Hc;
       induction ( Hc);
       clear Hc;
       clear H;
       relate
      )

    | _ => apply skip
    end 
      
  | H1 : (relator (?x) (?y)), H2 : (relator (?x) (?z))  |- _ =>
    (idtac " ";
     induction (relator_unique_R _ _ _ _ H1 H2 (eq_refl _));
     clear H1;
     relate
    )
      
  | H1 : (relator (?x) (?z)), H2 : (relator (?y) (?z))  |- _ =>
    (idtac " ";
     induction (relator_unique_Real _ _ _ _ H1 H2 (eq_refl _));
     clear H1;
     relate
    )
                                         
  | _ => apply skip
  end.



Goal forall (y : Real) (p : y <> Real0) (z : R), relator (y/p) z -> z = z.
  classical.
  relate.
  
  intros.
  relate.

  Holger p.
  relate.
Admitted.

  
  
