(* IMPORT *)
From Stdlib Require Export Bool.
From Stdlib Require Export List.
Export ListNotations.
From Stdlib Require Export Arith.
From Stdlib Require Export Nat.
From Stdlib Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)


(* HELPER FUNCTIONS *)
Inductive id : Type :=
  Id : nat -> id.

Definition beq_id (x x' : id) : bool :=
  match x, x' with
  | Id y, Id y' => Nat.eqb y y'
  end.
Lemma beq_id_refl : forall x : id,
  true = beq_id x x.
Proof.
  intros x; destruct x as [y]; simpl; symmetry; apply Nat.eqb_refl.
Qed.
Lemma beq_id_eq: forall x x' : id,
  true = beq_id x x' -> x = x'.
Proof.
  intros x x' H; destruct x as [y]; destruct x' as [y']; simpl in H; symmetry in H;
  apply Nat.eqb_eq in H; rewrite H; reflexivity.
Qed.

(* EKSTRA HELPER FUNCTIONS *)
Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(* OPGAVER *)

(* TODO - E1 *)
Inductive form :  Type:=
  | Fvar : id -> form  (* --- MANGLER -- ER I TVIVL OM HVORDAN VI SKAL BRUGE AT ID ER NAT??? ELLER HVAD VAR ER *)
  | Ftrue : form
  | Ffalse : form
  | Fand : form -> form -> form
  | For : form -> form -> form
  | Fimplies : form -> form -> form
  | Fnot : form -> form.

(* MISSING - TODO - OBS indsæt rigtige binding levels *)
(* MISSING - TODO - Evt. indsæt for true, false og var *)
Notation "F( X )" := (Fvar X) (at level 10).
Notation "A F/\ B" := (Fand A B) (at level 10).
Notation "A F\/ B" := (For A B) (at level 10).
Notation "A F-> B" := (Fimplies A B) (at level 10).
Notation "F~ A" := (Fnot A) (at level 10).

(* Notation "True" := (Ftrue). *)

Check form.

(* E2 *)
Definition X := F( Id 1).
Definition Y := F( Id 2).
Definition Z := F( Id 3).

Definition prop1: form := 
  (X F\/ (F~ Y)) F/\ ((F~ X) F\/ Y).

Definition prop2 : form := 
  (F~ Y) F-> (X F\/ Y).

Definition prop3 : form := 
  X F/\ ((F~ X) F/\ (Ftrue)).

(* E3 *)
Definition valuation := id -> bool.
Definition empty_valuation : valuation := fun x => false.
Definition override (V : valuation ) (x : id) (b : bool ) : valuation :=
  fun y => if beq_id x y then b else V y.

Fixpoint interp (V : valuation ) (p : form ) : bool :=
  match p with
  | Fvar x => V x
  | Ftrue => true
  | Ffalse => false
  | Fand f1 f2 => andb (interp V f1) (interp V f2)
  | For f1 f2 => orb (interp V f1) (interp V f2)
  | Fimplies f1 f2 =>
      match interp V f1 with
      | true => interp V f2
      | false => true
      end
  | Fnot f => negb (interp V f)
  end.

(* Tests for korrekthed af interp *)
Definition OneTrue_TwoFalse_valuation : valuation := 
  override (empty_valuation) (Id 1) true.

Example prop1_false : interp OneTrue_TwoFalse_valuation prop1 = false.
Proof.
  reflexivity.
Qed.

Example prop2_true : interp OneTrue_TwoFalse_valuation prop2 = true.
Proof.
  reflexivity.
Qed.

Example prop3_false : interp OneTrue_TwoFalse_valuation prop3 = false.
Proof.
  reflexivity.
Qed.

(* E4 *)
Definition satisfiable (p : form ) : Prop :=
  exists V : valuation , interp V p = true.

Definition OneTrue_TwoTrue_valuation : valuation := 
  override (override (empty_valuation) (Id 2) true) (Id 1) true.

Example test1 : satisfiable prop1.
Proof.
  unfold satisfiable.
  exists OneTrue_TwoTrue_valuation.
  reflexivity.
Qed.

Example test2 : satisfiable prop2.
Proof.
  unfold satisfiable.
  exists OneTrue_TwoTrue_valuation.
  reflexivity.
Qed.

(* E5 *)
Fixpoint checkElemInList (x : id) (l : list id) : bool :=
  match l with
  | nil => false
  | h :: t =>
    match beq_id x h with
    | true => true
    | false => checkElemInList x t
    end
  end.

Fixpoint appendLists (l1 l2 :list id): list id :=
  match l2 with
  | nil => l1
  | h2 :: t2 => 
    match checkElemInList h2 l1 with
    | true => appendLists l1 t2
    | false => appendLists (l1 ++ [h2]) t2
    end
  end.

Notation "l1 +++ l2" := (appendLists l1 l2) (at level 10).

Fixpoint list_variables (p: form) : list id :=
  match p with
  | Fvar x => [x]
  | Fand f1 f2 => ((list_variables f1)) +++ (list_variables f2)
  | For f1 f2 => ((list_variables f1)) +++ (list_variables f2)
  | Fimplies f1 f2 => ((list_variables f1)) +++ (list_variables f2)
  | Fnot f => (list_variables f)
  | Ftrue => []
  | Ffalse => []
  end.

(* Fixpoint list_variables (p: form) (vl : list id) : list id :=
  match p with
  | Fvar x => vl +++ [x]
  | Fand f1 f2 => (vl +++ (list_variables f1 vl)) +++ (list_variables f2 vl)
  | For f1 f2 => (vl +++ (list_variables f1 vl)) +++ (list_variables f2 vl)
  | Fimplies f1 f2 => (vl +++ (list_variables f1 vl)) +++ (list_variables f2 vl)
  | Fnot f => vl +++ (list_variables f vl)
  | Ftrue => vl
  | Ffalse => vl
  end. *)

Example prop1_correct_var : list_variables prop1 = [(Id 1); (Id 2)].
Proof.
  reflexivity.
Qed.
Example prop2_correct_var : list_variables prop2 = [(Id 2); (Id 1)].
Proof.
  reflexivity.
Qed.
Example prop3_correct_var : list_variables prop3 = [(Id 1)].
Proof.
  reflexivity.
Qed.

Fixpoint generate_truthtable (l : list id) (V : valuation) : list valuation := 
  match l with
  | nil => [V]
  | h :: t =>
    (map (fun (W : valuation) => (override W h true)) (generate_truthtable t V)) 
    ++ (map (fun (W : valuation) => (override W h false)) (generate_truthtable t V)) 
  end.

Example generate_truthtable1 : 
  [(override empty_valuation (Id 1) true); (override empty_valuation (Id 1) false)]
  = generate_truthtable [Id 1] empty_valuation.
Proof.
  simpl. reflexivity.
Qed.

Example generate_truthtable2 : 
  [(override (override empty_valuation (Id 2) true) (Id 1) true);
    (override (override empty_valuation (Id 2) false) (Id 1) true) ;
    (override (override empty_valuation (Id 2) true) (Id 1) false) ;
    (override (override empty_valuation (Id 2) false) (Id 1) false)]
  = generate_truthtable [Id 1; Id 2] empty_valuation.
Proof.
  simpl. reflexivity.
Qed.


Definition find_valuation (p : form ) : option valuation :=
  match filter (fun (V: valuation) => interp V p) (generate_truthtable (list_variables p) empty_valuation) with
  | nil => None
  | h :: t => Some h
  end.
  
Compute (find_valuation prop1).


(* MISSING - Do better E6 *)
Definition solver (p : form ) : bool :=
  match find_valuation p with
  | Some _ => true
  | None => false
  end.


(*Explain the difference between satisfiable and solver. *)
(* 
SATISFIABLE:
Given a form, satisfiable returns a proposition, that states that a valuation
under which that form is interpreted as true (through the interp function).
This proposition might or might not in turn be provable, and such a proposition
(unproved) might be formulated for any combination of valuations and forms.

SOLVER:
Given a form, Solver will use the find_evaluation function to exhaustively search
for any valuation that satisfies the form. If such a valuation is found, solver
will return true. If not, solver will return false.
As such solver returns true for any form, for which satisfiable is provable
for that form.

*)

(* E7 *)
(* Write 2 positive and 2 negative tests of the solver and prove these
tests using the reflexivity tactic. *)

(* NEGATIVE *)
Definition prop4 : form := 
  (F(Id 1) F-> F( Id 1)) F-> (Ftrue F/\ Ffalse).

Lemma solver_prop3_false : solver prop3 = false.
Proof.
  reflexivity.
Qed.

Lemma solver_prop4_false : solver prop3 = false.
Proof.
  reflexivity.
Qed.

(* POSITIVE *)
Lemma solver_prop1_true : solver prop1 = true.
Proof.
  reflexivity.
Qed.

Lemma solver_prop2_true : solver prop2 = true.
Proof.
  reflexivity.
Qed.

(* E8 *)
Lemma solver_sound : forall p, solver p = true -> satisfiable p.
Proof.
  intros p H. 
  unfold solver in H.
  destruct (find_valuation p) eqn:EH.
  - unfold find_valuation in EH.
    (* DOKUMENTATION: https://stackoverflow.com/questions/78321778/is-is-possible-to-rename-a-coq-term *)
    set (l:= generate_truthtable (list_variables p) empty_valuation) in EH.
    induction l as [| v' l' IHl'].
    + simpl in EH. discriminate.
    + destruct (interp v' p) eqn: Ev'.
      * unfold satisfiable. exists v'. assumption.
      * simpl in EH. rewrite Ev' in EH. apply IHl' in EH. assumption. 
  - discriminate.
Qed.  

(* EXTRA *)

(* EXTRA -- Optimizer *)

Fixpoint Optimizer (p : form) : form :=
  match p with
  (* SAME *)
  | Fvar x => Fvar x
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  (* SENDES VIDERE *)
  | Fnot f => Fnot (Optimizer f)
  | Fimplies f1 f2 => Fimplies (Optimizer f1) (Optimizer f2)
  (* DIREKTE OPTIMIZED *)
  | Fand f1 f2 =>
      match Optimizer f1, Optimizer f2 with
      | Ftrue, (Fvar x) => Fvar x
      | (Fvar x), Ftrue => Fvar x
      | _, Ffalse => Ffalse
      | Ffalse, _ => Ffalse
      | _, _ => Fand (Optimizer f1) (Optimizer f2)
      end
  | For f1 f2 => 
  (* For (Optimizer f1) (Optimizer f2) *)
      match Optimizer f1, Optimizer f2 with
      | Ftrue, _ => Ftrue
      | _, Ftrue => Ftrue
      | (Fvar x), Ffalse => Fvar x
      | Ffalse, (Fvar x) => Fvar x
      | _, _ => For (Optimizer f1) (Optimizer f2)
      end
  end.

Compute (Optimizer (X F/\ Ftrue)).
Compute (Optimizer (X F/\ Ffalse)).
Compute (Optimizer ((Ftrue F\/ X) F-> (X F/\ Ftrue))).

(* Ltac rwrt_refl :=
  match goal with
    H1: interp ?V ?P -> ?E
    |- _ => rewrite H1
  end. *) (* OBS - forstår ikke hvorfor den ikke fungerer *)

Ltac rwrt_h1h2 h1 h2:=
  rewrite h1 ; rewrite h2.

Definition Optimizer_correct : forall (p:form) (v : valuation), 
    interp v p = interp v (Optimizer p).
Proof.
  intros p v. induction p ; simpl ; try reflexivity.
  - 
    destruct (Optimizer p1) eqn: Ep1 ; 
    try (
          rwrt_h1h2 IHp1 IHp2 ; 
          reflexivity
        ) ;
    simpl ; destruct (Optimizer p2) eqn:Ep2 ; try (rwrt_h1h2 IHp1 IHp2; reflexivity) ;
    try (
          rwrt_h1h2 IHp1 IHp2 ;
          apply andb_true_r 
        ) ;
    try (
          rwrt_h1h2 IHp1 IHp2 ;
          apply andb_false_r 
        ).
  - 
    destruct (Optimizer p1) eqn: Ep1 ;
    try (
          rwrt_h1h2 IHp1 IHp2 ; 
          reflexivity
        ) ;
    simpl ; destruct (Optimizer p2) eqn:Ep2 ; try (rwrt_h1h2 IHp1 IHp2; reflexivity) ;
    try (
          rwrt_h1h2 IHp1 IHp2 ;
          apply orb_true_r 
        ) ;
    try (
          rwrt_h1h2 IHp1 IHp2 ;
          apply orb_false_r 
        ).
  - rewrite IHp1. rewrite IHp2. reflexivity.
  - rewrite IHp. reflexivity.  
Qed. 

Definition solver2 (p : form ) : bool :=
  match find_valuation (Optimizer p) with
  | Some _ => true
  | None => false
  end.

Lemma solver2_sound : forall p, solver2 p = true -> satisfiable p.
Proof.
  intros p H. 
  unfold solver2 in H.
  destruct (find_valuation (Optimizer p)) eqn:EH.
  - unfold find_valuation in EH. 
    unfold filter in EH. 
    assert (L: forall x, interp x p = interp x (Optimizer p)).
    {
      apply Optimizer_correct.
    }
    set (tt := generate_truthtable (list_variables (Optimizer p)) empty_valuation) in EH.
    induction tt as [| v' l' IHl'].
    + discriminate.
    + destruct (interp v' (Optimizer p)) eqn: Ev'.
      * rewrite <- Optimizer_correct in Ev'. unfold satisfiable. exists v'. assumption.
      * apply IHl'. assumption.
  - discriminate.
Qed.

(* EXTRA -- Negation Normal Form *)

(* 
  match p with
  | Fvar x => V x
  | Ftrue => true
  | Ffalse => false
  | Fand f1 f2 => andb (interp V f1) (interp V f2)
  | For f1 f2 => orb (interp V f1) (interp V f2)
  | Fimplies f1 f2 =>
      match interp V f1 with
      | true => interp V f2
      | false => true
      end
  | Fnot f => negb (interp V f)
  end.


   match p with
  (* SAME *)
  | Fvar x => Fvar x
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  (* SENDES VIDERE *)
  | Fnot f => Fnot (Optimizer f)
  | Fimplies f1 f2 => Fimplies (Optimizer f1) (Optimizer f2)
  (* DIREKTE OPTIMIZED *)
  | Fand f1 f2 =>
      match Optimizer f1, Optimizer f2 with
      | Ftrue, (Fvar x) => Fvar x
      | (Fvar x), Ftrue => Fvar x
      | _, Ffalse => Ffalse
      | Ffalse, _ => Ffalse
      | _, _ => Fand (Optimizer f1) (Optimizer f2)
      end
  | For f1 f2 => 
  (* For (Optimizer f1) (Optimizer f2) *)
      match Optimizer f1, Optimizer f2 with
      | Ftrue, _ => Ftrue
      | _, Ftrue => Ftrue
      | (Fvar x), Ffalse => Fvar x
      | Ffalse, (Fvar x) => Fvar x
      | _, _ => For (Optimizer f1) (Optimizer f2)
      end
  end.
*)
Fixpoint Optimizer_NNF (p : form) : form :=
  match p with
  (* SAME *)
  | Fvar x => Fvar x
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  (* SENDES VIDERE *)
  | Fand f1 f2 => Fand (Optimizer_NNF f1) (Optimizer_NNF f2)
  (* | Fand f1 f2 => Fand (Optimizer_NNF f1) (Optimizer_NNF f2) *)
  | For f1 f2 => For (Optimizer_NNF f1) (Optimizer_NNF f2)
  | Fimplies f1 f2 => Fimplies (Optimizer_NNF f1) (Optimizer_NNF f2)
  (* DIREKTE OPTIMIZED *)
  | Fnot f => 
      match (Optimizer_NNF f) with
      | Fvar x => Fnot (Fvar x)
      | Ftrue => Ffalse
      | Ffalse => Ftrue
      (* | Fand f1 f2 => For ((Fnot f1)) ((Fnot f2))
      | For f1 f2 => Fand ((Fnot f1)) ((Fnot f2))
      | Fimplies f1 f2 => For ((Fnot f1)) (f2) *)
      | Fand f1 f2 => For (Optimizer_NNF (Fnot f1)) (Optimizer_NNF (Fnot f2))
      | For f1 f2 => Fand (Optimizer_NNF (Fnot f1)) (Optimizer_NNF (Fnot f2))
      | Fimplies f1 f2 => For (Optimizer_NNF (Fnot f1)) (f2)
      (* ORIGINALT KOM TIL AT SKRIVE:
        | Fand f1 f2 => For (Optimizer_NNF (Fnot f1)) (Optimizer_NNF (Fnot f2))
        | For f1 f2 => Fand (Optimizer_NNF (Fnot f1)) (Optimizer_NNF (Fnot f2))
        | Fimplies f1 f2 => For (Optimizer_NNF (Fnot f1)) (Optimizer_NNF f2)
      *)
      | Fnot f' => f'
      (* ORIGINALT KOM TIL AT SKRIVE: Fnot f' => Optimizer_NNF f' 
         DOG IKKE NØDVENDIGT DA VI HAR MATCHED MED Optimizer_NNF f*)
      end
  end.

  
  
  (* DIREKTE OPTIMIZED *)
  | Fand f1 f2 =>
      match Optimizer f1, Optimizer f2 with
      | Ftrue, (Fvar x) => Fvar x
      | (Fvar x), Ftrue => Fvar x
      | _, Ffalse => Ffalse
      | Ffalse, _ => Ffalse
      | _, _ => Fand (Optimizer f1) (Optimizer f2)
      end
  | For f1 f2 => 
  (* For (Optimizer f1) (Optimizer f2) *)
      match Optimizer f1, Optimizer f2 with
      | Ftrue, _ => Ftrue
      | _, Ftrue => Ftrue
      | (Fvar x), Ffalse => Fvar x
      | Ffalse, (Fvar x) => Fvar x
      | _, _ => For (Optimizer f1) (Optimizer f2)
      end
  end.

(* EXTRA -- Conjunctive Normal Form *)

(* EXTRA -- Completeness *)
(* 
Definition valuation := id -> bool.
Definition empty_valuation : valuation := fun x => false.
Definition override (V : valuation ) (x : id) (b : bool ) : valuation :=
  fun y => if beq_id x y then b else V y.
*)
Definition min_valuation (V : valuation) (p : form) : valuation :=
  fold (fun (elem : id) (W : valuation) => override W elem (V elem)) (list_variables p) (empty_valuation). (* ret => valuation *)

Lemma override_empty_valuation_eq : forall (V : valuation) (i : id) (b : bool),
    (override empty_valuation i b) i = b.
Proof.
  intros. unfold override. Search beq_id. rewrite <-beq_id_refl. reflexivity.
Qed.


Lemma min_valuation_preserves_interp : forall (V : valuation) (p: form),
    interp V p = interp (min_valuation V p) p.
Proof.
  intros V p. 
  (* generalize dependent V.  *)
  unfold min_valuation. unfold interp. 
  set (l:= (list_variables p)).
  induction (list_variables p) as [|IH].
  (* -  simpl. reflexivity.
  induction p; try reflexivity.
  - simpl. unfold min_valuation. simpl. symmetry. apply override_empty_valuation_eq. 
    assumption.
  - unfold min_valuation. apply override_empty_valuation_eq.
    (* unfold min_valuation. apply override_empty_valuation_eq with (). *)
  simpl. 
  admit.
  (* Problemet er, at jeg har overrided n elementer ? så jeg laver induktion på det 
    forkerte. Pt. laver jeg nemlig med det samme induktion på p *)
  - simpl. admit.
  - simpl.
    assert (L1: interp V p1 = interp (min_valuation V (p1 F/\ p2)) p1).
    {
      unfold min_valuation. simpl. rewrite override_empty_valuation_eq with (i:= ).
       simpl. rewrite IHp1. unfold interp. unfold min_valuation.
    }
  
  unfold min_valuation. simpl.
   simpl. *)

  (* rewrite IHp1. rewrite IHp2. *)

Admitted.

Search list.

Print existsb.

Search In.

Lemma contained : forall (V: valuation) (l : list id),
    existsb (valuation) (eqb)


    In 
    (fun (elem : id) => if (In elem l)=true then V elem else false)
    (generate_truthtable l empty_valuation).

Lemma min_valuation_in_truthtable : forall (V: valuation) (p : form),
    In (min_valuation V p) (generate_truthtable (list_variables p) (empty_valuation)).
Proof.
  intros V p. induction p.
  -  simpl.
Admitted.

(* REDONE list_variables *)

Lemma some_valuation_then_solver_true : forall p, exists V, 
    find_valuation p = Some V -> solver p = true.
Proof.
Admitted.

Lemma solver_complete : forall p,
    satisfiable p -> solver p = true.
Proof.
  intros p H. inversion H.
  unfold solver.
Admitted.
