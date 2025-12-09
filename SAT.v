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

Fixpoint illegal_boolean_formulas_are_present (p : form) : bool :=
  match p with
  (* SAME *)
  | Fvar x => false
  | Ftrue => false
  | Ffalse => false
  (* SENDES VIDERE *)
  | Fnot f => illegal_boolean_formulas_are_present f
  | Fimplies f1 f2 => orb (illegal_boolean_formulas_are_present f1) (illegal_boolean_formulas_are_present f2)
  (* DIREKTE OPTIMIZED *)
  | Fand f1 f2 =>
      match f1, f2 with
      | Fvar x, Ftrue => true
      | Ftrue, Fvar x => true
      | Fvar x, Ffalse => true
      | Ffalse, Fvar x => true
      | _, _ => orb (illegal_boolean_formulas_are_present f1) (illegal_boolean_formulas_are_present f2)
      end
  | For f1 f2 => 
      match  f1, f2 with
      | Fvar x, Ftrue => true
      | Ftrue, Fvar x => true
      | Fvar x, Ffalse => true
      | Ffalse, Fvar x => true
      | _, _ => orb (illegal_boolean_formulas_are_present f1) (illegal_boolean_formulas_are_present f2)
      end
  end.

Definition Optimized_form_doesn't_contain_illegal_expression (p : form) : Prop :=
  illegal_boolean_formulas_are_present (Optimizer p) = false.

Theorem Optimizer_doesn't_contain_illegal_expressions : forall p,
    Optimized_form_doesn't_contain_illegal_expression p.
Proof.
  unfold Optimized_form_doesn't_contain_illegal_expression.
  induction (p) ;
  try reflexivity ;
  try assumption ;
  try (
        simpl ;
        destruct (Optimizer f1), (Optimizer f2) ; 
        try reflexivity ; 
        try assumption ;
        try (simpl; rewrite orb_false_r ; assumption) ;
        try (simpl ; apply orb_false_intro ; assumption)
      ). 
Qed. 

(* Ltac rwrt_refl :=
  match goal with
    H1: interp ?V ?P -> ?E
    |- _ => rewrite H1
  end. *) (* OBS - forstår ikke hvorfor den ikke fungerer *)
  
Definition Optimizer_preserves_interp_on_form (p: form) (v : valuation) : Prop :=
  interp v p = interp v (Optimizer p).

Ltac rwrt_h1h2 h1 h2:=
  rewrite h1 ; rewrite h2.

Theorem Optimizer_preserves_interp : forall p v, 
    Optimizer_preserves_interp_on_form p v.
Proof.
  unfold Optimizer_preserves_interp_on_form.
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

Theorem Optimiser_correct : forall p v,
Optimized_form_doesn't_contain_illegal_expression p /\ Optimizer_preserves_interp_on_form p v.
Proof.
  intros.
  split. 
  - apply Optimizer_doesn't_contain_illegal_expressions.
  - apply Optimizer_preserves_interp.
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
      apply Optimizer_preserves_interp.
    }
    set (tt := generate_truthtable (list_variables (Optimizer p)) empty_valuation) in EH.
    induction tt as [| v' l' IHl'].
    + discriminate.
    + destruct (interp v' (Optimizer p)) eqn: Ev'.
      * rewrite <- Optimizer_preserves_interp in Ev'. unfold satisfiable. exists v'. assumption.
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
(* Fixpoint Optimizer_NNF (p : form) (b: bool) : form :=
  match p, b with
  (* SAME *)
  | Fvar x, true => Fvar x
  | Fvar x, false => Fnot (Fvar x)

  | Ftrue, true => Ftrue
  | Ftrue, false => Ffalse

  | Ffalse, true => Ffalse
  | Ffalse, false => Ftrue
  (* SENDES VIDERE *)
  | Fand f1 f2, _ => Fand (Optimizer_NNF f1 _) (Optimizer_NNF f2 _)
  | For f1 f2, _ => For (Optimizer_NNF f1 _) (Optimizer_NNF f2 _)
  | Fimplies f1 f2, _ => Fimplies (Optimizer_NNF f1 _) (Optimizer_NNF f2 _)
  (* DIREKTE OPTIMIZED *)
  | Fnot f, false => Optimizer_NNF f true
  | Fnot f, true => 
      match (Optimizer_NNF f true) with
      | Fvar x => Fnot (Fvar x)
      | Ftrue => Ffalse
      | Ffalse => Ftrue
      | Fand f1 f2 => For ((Fnot f1)) ((Fnot f2))
      | For f1 f2 => Fand ((Fnot f1)) ((Fnot f2))
      (* | Fimplies f1 f2 => For ((Fnot f1)) (f2) *)
      (* | Fand f1 f2 => For (Optimizer_NNF (Fnot f1)) (Optimizer_NNF (Fnot f2)) *)
      (* | For f1 f2 => Fand (Optimizer_NNF (Fnot f1)) (Optimizer_NNF (Fnot f2)) *)
      | Fimplies f1 f2 => For (Optimizer_NNF f1 false) (f2)
      (* ORIGINALT KOM TIL AT SKRIVE:
        | Fand f1 f2 => For (Optimizer_NNF (Fnot f1)) (Optimizer_NNF (Fnot f2))
        | For f1 f2 => Fand (Optimizer_NNF (Fnot f1)) (Optimizer_NNF (Fnot f2))
        | Fimplies f1 f2 => For (Optimizer_NNF (Fnot f1)) (Optimizer_NNF f2)
      *)
      | Fnot f' => f'
      (* ORIGINALT KOM TIL AT SKRIVE: Fnot f' => Optimizer_NNF f' 
         DOG IKKE NØDVENDIGT DA VI HAR MATCHED MED Optimizer_NNF f*)
      end
  end. *)
Fixpoint Optimizer_NNF (p : form) (b: bool) : form :=
  match p, b with
  (* SAME *)
  | Fvar x, true => Fvar x
  | Fvar x, false => Fnot (Fvar x)

  | Ftrue, true => Ftrue
  | Ftrue, false => Ffalse

  | Ffalse, true => Ffalse
  | Ffalse, false => Ftrue
  (* SENDES VIDERE *)
  | Fand f1 f2, true => Fand (Optimizer_NNF f1 true) (Optimizer_NNF f2 true)
  | Fand f1 f2, false => For (Optimizer_NNF f1 false) (Optimizer_NNF f2 false)

  | For f1 f2, true => For (Optimizer_NNF f1 true) (Optimizer_NNF f2 true)
  | For f1 f2, false => Fand (Optimizer_NNF f1 false) (Optimizer_NNF f2 false)

  | Fimplies f1 f2, true => For (Optimizer_NNF f1 false) (Optimizer_NNF f2 true)
  | Fimplies f1 f2, false => Fand (Optimizer_NNF f1 true) (Optimizer_NNF f2 false)
  (* GAMLE DEF:
  | Fimplies f1 f2, true => Fimplies (Optimizer_NNF f1 true) (Optimizer_NNF f2 true)
  | Fimplies f1 f2, false => For (Optimizer_NNF f1 false) (Optimizer_NNF f2 true)
  *)
  (* DIREKTE OPTIMIZED *)
  | Fnot f, false => Optimizer_NNF f true
  | Fnot f, true => Optimizer_NNF f false
  end.

Fixpoint implication_is_present (p : form) : bool :=
  match p with
  (* SAME *)
  | Fvar x => false
  | Ftrue => false
  | Ffalse => false
  (* SENDES VIDERE *)
  | Fnot f => implication_is_present f
  | Fand f1 f2 => orb (implication_is_present f1) (implication_is_present f2)
  | For f1 f2 => orb (implication_is_present f1) (implication_is_present f2)
  (* DIREKTE OPTIMIZED *)
  | Fimplies f1 f2 => true
  end.

Fixpoint double_negation_is_present (p : form) : bool :=
  match p with
  (* SAME *)
  | Fvar x => false
  | Ftrue => false
  | Ffalse => false
  (* SENDES VIDERE *)
  | Fand f1 f2 => orb (double_negation_is_present f1) (double_negation_is_present f2)
  | For f1 f2 => orb (double_negation_is_present f1) (double_negation_is_present f2)
  | Fimplies f1 f2 => orb (double_negation_is_present f1) (double_negation_is_present f2)
  (* DIREKTE OPTIMIZED *)
  | Fnot f => 
      match f with
      | Fnot f' => true
      | _ => double_negation_is_present f
      end
  end.

Fixpoint negated_conjunction_is_present (p : form) : bool :=
  match p with
  (* SAME *)
  | Fvar x => false
  | Ftrue => false
  | Ffalse => false
  (* SENDES VIDERE *)
  | Fand f1 f2 => orb (negated_conjunction_is_present f1) (negated_conjunction_is_present f2)
  | For f1 f2 => orb (negated_conjunction_is_present f1) (negated_conjunction_is_present f2)
  | Fimplies f1 f2 => orb (negated_conjunction_is_present f1) (negated_conjunction_is_present f2)
  (* DIREKTE OPTIMIZED *)
  | Fnot f => 
      match f with
      | Fand f1 f2 => true
      | _ => negated_conjunction_is_present f
      end
  end.

Fixpoint negated_disjunction_is_present (p : form) : bool :=
  match p with
  (* SAME *)
  | Fvar x => false
  | Ftrue => false
  | Ffalse => false
  (* SENDES VIDERE *)
  | Fand f1 f2 => orb (negated_disjunction_is_present f1) (negated_disjunction_is_present f2)
  | For f1 f2 => orb (negated_disjunction_is_present f1) (negated_disjunction_is_present f2)
  | Fimplies f1 f2 => orb (negated_disjunction_is_present f1) (negated_disjunction_is_present f2)
  (* DIREKTE OPTIMIZED *)
  | Fnot f => 
      match f with
      | For f1 f2 => true
      | _ => negated_disjunction_is_present f
      end
  end.

Definition OptimizerNNF_doesn't_contain_illegal_expression_on_form (p : form) : Prop :=
  implication_is_present (Optimizer_NNF p true) = false 
  /\ double_negation_is_present (Optimizer_NNF p true) = false
  /\ negated_conjunction_is_present (Optimizer_NNF p true) = false
  /\ negated_disjunction_is_present (Optimizer_NNF p true) = false.

Theorem OptimizerNNF_doesn't_contain_illegal_expressions : forall p,
    OptimizerNNF_doesn't_contain_illegal_expression_on_form p.
Proof.
  unfold OptimizerNNF_doesn't_contain_illegal_expression_on_form.
  split.
  - induction (p) ; try reflexivity ;
    try (simpl; apply orb_false_intro; assumption).
    + simpl. apply orb_false_intro; try assumption.
      unfold implication_is_present.
      unfold Optimizer_NNF.
    (* + simpl. apply orb_false_intro; assumption.
    + simpl. apply orb_false_intro; assumption.
  try reflexivity ;
  try assumption ;
  try (
        simpl ;
        destruct (Optimizer f1), (Optimizer f2) ; 
        try reflexivity ; 
        try assumption ;
        try (simpl; rewrite orb_false_r ; assumption) ;
        try (simpl ; apply orb_false_intro ; assumption)
      ).  *)
Admitted.

Lemma Optimizer_NNF_false_negb : forall (p:form) (v : valuation),
    negb (interp v (Optimizer_NNF p true)) = interp v (Optimizer_NNF p false).
Proof.
  intros p v. induction p; try reflexivity ; simpl.
  - rewrite <- IHp1. rewrite <- IHp2. apply negb_andb.
  - rewrite <- IHp1. rewrite <- IHp2. apply negb_orb.
  - rewrite <- IHp1. rewrite <-IHp2. rewrite negb_orb. rewrite negb_involutive. reflexivity.
  - rewrite <- IHp. apply negb_involutive.
Qed. 

Definition Optimizer_NNF_correct : forall (p:form) (v : valuation), 
    interp v p = interp v (Optimizer_NNF p true).
Proof.
  intros p v.
  induction p ; try reflexivity.
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
  - simpl. rewrite IHp1. rewrite IHp2. rewrite <- Optimizer_NNF_false_negb. 
    apply implb_orb.
  - simpl. rewrite IHp. rewrite <- Optimizer_NNF_false_negb. reflexivity.  
Qed. 

Definition solverNNF (p : form ) : bool :=
  match find_valuation (Optimizer_NNF p true) with
  | Some _ => true
  | None => false
  end.

Lemma solverNNF_sound : forall p, solverNNF p = true -> satisfiable p.
Proof.
  intros p H. 
  unfold solverNNF in H.
  destruct (find_valuation (Optimizer_NNF p true)) eqn:EH.
  - unfold find_valuation in EH. 
    unfold filter in EH. 
    assert (L: forall x, interp x p = interp x (Optimizer_NNF p true)).
    {
      apply Optimizer_NNF_correct.
    }
    set (tt := generate_truthtable (list_variables (Optimizer_NNF p true)) empty_valuation) in EH.
    induction tt as [| v' l' IHl'].
    + discriminate.
    + destruct (interp v' (Optimizer_NNF p true)) eqn: Ev'.
      * rewrite <- Optimizer_NNF_correct in Ev'. unfold satisfiable. exists v'. assumption.
      * apply IHl'. assumption.
  - discriminate.
Qed.

(* EXTRA -- Conjunctive Normal Form *)
(* Fixpoint Optimizer_DNF (p : form) : form :=
  match Optimizer_NNF p true with
  (* SAME *)
  | Fvar x => Fvar x
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  | Fnot f => Fnot f
  | For f1 f2 => For (Optimizer_DNF f1) (Optimizer_DNF f2)
  (* SENDES VIDERE *)
  | Fand f1 f2 =>
      match f1, f2 with
      | x, For y z => For (Optimizer_DNF (Fand x y)) (Optimizer_DNF (Fand x z))
      | For x y, z => For (Optimizer_DNF (Fand x z)) (Fand y z)
      | f1', f2' => Fand (Optimizer_DNF f1') (Optimizer_DNF f2')
      end
  (* IKKE MULIG *)
  | s => s
  end. *)

(* 
Inductive form :  Type:=
  | Fvar : id -> form  (* --- MANGLER -- ER I TVIVL OM HVORDAN VI SKAL BRUGE AT ID ER NAT??? ELLER HVAD VAR ER *)
  | Ftrue : form
  | Ffalse : form
  | Fand : form -> form -> form
  | For : form -> form -> form
  | Fimplies : form -> form -> form
  | Fnot : form -> form.
*)
Search plus.

Fixpoint Count_Fand (p : form) : nat :=
  match p with
  | Fand f1 f2 => 1 + ((Count_Fand f1) + (Count_Fand f2))
  | For f1 f2 => ((Count_Fand f1) + (Count_Fand f2))
  | Fimplies f1 f2 => ((Count_Fand f1) + (Count_Fand f2))
  | Fnot f => (Count_Fand f)
  (* SLUT *)
  | _ => 0
  end.

Fixpoint Count_Fand_For (p : form) : nat :=
  match p with
  | Fand f1 f2 => 1 + ((Count_Fand_For f1) + (Count_Fand_For f2))
  | For f1 f2 => 1 + ((Count_Fand_For f1) + (Count_Fand_For f2))
  | Fimplies f1 f2 => ((Count_Fand_For f1) + (Count_Fand_For f2))
  | Fnot f => (Count_Fand_For f)
  (* SLUT *)
  | _ => 0
  end.

Compute (Optimizer_NNF ((Ftrue F\/ X) F-> (X F/\ Ftrue)) true).
Compute (Count_Fand (Ffalse F/\ (F~ (F( Id 1))) F\/ ((F( Id 1)) F/\ Ftrue))).
Compute (Count_Fand (Ffalse F/\ Ftrue)).
Compute (Count_Fand (Ffalse F\/ Ftrue)).
Compute (Count_Fand_For (Ffalse F/\ (F~ (F( Id 1))) F\/ ((F( Id 1)) F/\ Ftrue))).
Compute (Count_Fand_For (Ffalse F/\ Ftrue)).
Compute (Count_Fand_For (Ffalse F\/ Ftrue)).

Fixpoint OptimizerCNF_step (p : form) : form :=
  match p with 
    (* SAME *)
    | Fvar x => Fvar x
    | Ftrue => Ftrue
    | Ffalse => Ffalse
    | Fnot f => Fnot (OptimizerCNF_step f)
    | Fand f1 f2 => Fand (OptimizerCNF_step f1) (OptimizerCNF_step f2)
    (* SENDES VIDERE *)
    | For f1 f2 =>
        match f1, f2 with
        | Fand x y, z => Fand (For z x) (For z y)
        | x, Fand y z => Fand (For x y) (For x z)
        | f1', f2' => For (OptimizerCNF_step f1') (OptimizerCNF_step f2')
      end
    (* IKKE MULIG *)
    | Fimplies f1 f2 => Fimplies (OptimizerCNF_step f1) (OptimizerCNF_step f2)
  end.

Fixpoint OptimizerCNF_run (p : form) (n : nat): form :=
  match n with
  | 0 => p
  | S n' => OptimizerCNF_run (OptimizerCNF_step p) n'
  end.

Lemma pls : forall v p1 p2,
  interp v (OptimizerCNF_step p1)
|| interp v (OptimizerCNF_step p2) =
interp v
((OptimizerCNF_step p1)
F\/ (OptimizerCNF_step p2)).
Proof.
  intros.  
  induction p1, p2 ;
  try reflexivity;
  try (simpl ; rewrite orb_andb_distrib_r ; reflexivity);
  try (simpl; rewrite orb_andb_distrib_l; reflexivity);
  try ( rewrite IHp2; reflexivity);
  try (simpl ; repeat rewrite orb_true_r ; reflexivity).
Qed.

Definition OptimizerCNF_step_preserves_interp : forall p v,
  interp v p
  = interp v (OptimizerCNF_step p).
Proof.
  intros. 
  induction p; try reflexivity.
  - simpl. rewrite IHp1. rewrite IHp2. reflexivity.
  - simpl. rewrite IHp1. rewrite IHp2. simpl.
    destruct p1 eqn:Ep1; destruct p2 eqn:Ep2 ; try apply pls.
    + simpl. rewrite <-orb_andb_distrib_r. simpl in IHp2. rewrite IHp2. reflexivity.
    + simpl. simpl in IHp2. rewrite IHp2. reflexivity.
    + simpl. rewrite <-orb_andb_distrib_r. simpl in IHp1. rewrite IHp1.
      Search orb. rewrite orb_comm. reflexivity.
    + simpl. apply orb_true_r.
    + simpl. rewrite orb_false_r. simpl in IHp1. rewrite IHp1. reflexivity.
    + simpl. simpl in IHp2. simpl in IHp1. rewrite <-IHp1. rewrite <- IHp2. rewrite <-orb_andb_distrib_r.
      apply orb_comm.
    + simpl in IHp1. simpl in IHp2. simpl. rewrite <-IHp2. rewrite <- IHp1. 
      rewrite <-orb_andb_distrib_r. Search orb. rewrite orb_assoc.
      Search andb. set (C:= interp v f3 || interp v f4). symmetry. rewrite <-orb_comm. 
      subst. subst C. rewrite orb_assoc. reflexivity.
    + simpl in IHp1. simpl in IHp2. simpl. rewrite <-IHp2. rewrite<-IHp1.
      rewrite <-orb_andb_distrib_r. apply orb_comm.
    + simpl. simpl in IHp1. simpl in IHp2. rewrite <-IHp2. 
      rewrite <-orb_andb_distrib_r. rewrite <- IHp1. rewrite orb_comm. reflexivity.
    + simpl. simpl in IHp1. simpl in IHp2. rewrite<- IHp1. rewrite<-IHp2.
      rewrite <-orb_andb_distrib_r. reflexivity.
    + simpl. simpl in IHp1. simpl in IHp2. rewrite<- IHp1. rewrite <- IHp2. 
      rewrite <-orb_andb_distrib_r. reflexivity.
    + simpl. simpl in IHp1. simpl in IHp2. rewrite <-IHp1. rewrite <-IHp2. rewrite orb_andb_distrib_r.
      reflexivity. 
  - simpl. rewrite IHp1. rewrite IHp2. reflexivity.
  - simpl. rewrite IHp. reflexivity. 
Qed.     

Definition OptimizerCNF (p : form) : form :=
  OptimizerCNF_run (Optimizer_NNF p true) (mult (Count_Fand (Optimizer_NNF p true)) (Count_Fand_For (Optimizer_NNF p true))).

Lemma pls2 : forall p n,
  (OptimizerCNF_run (OptimizerCNF_step (p)) n)
  = (OptimizerCNF_step (OptimizerCNF_run (p) n)).
Proof.
  intros. induction n.
  - 

Definition Optimizer_CNF_correct : forall (p:form) (v : valuation), 
    interp v p = interp v (OptimizerCNF p).
Proof.
  intros p v.
  unfold OptimizerCNF.
  set (n := (Count_Fand (Optimizer_NNF p true) * Count_Fand_For (Optimizer_NNF p true))).
  induction n.
  - simpl. apply Optimizer_NNF_correct.
  - simpl. rewrite <-OptimizerCNF_step_preserves_interp.
  unfold OptimizerCNF_run.
  induction p ; try reflexivity.
  - simpl.  
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
  - simpl. rewrite IHp1. rewrite IHp2. rewrite <- Optimizer_NNF_false_negb. 
    apply implb_orb.
  - simpl. rewrite IHp. rewrite <- Optimizer_NNF_false_negb. reflexivity.  
Qed. 

(* OBS - ANDEN IDÉ ER AT GENTAGE OPTIMIZER PÅ FORM N GANGE (TILSVARENDE ANTAL ) 
-- NEJ VILLE IKKE VIRKE
*)
(* 
Fixpoint Optimizer_CNF (n : nat) : form->form :=
  match n with
  | 0 => fun p => p
  | S n' => fun p =>
      match p with 
      (* SAME *)
      | Fvar x => Fvar x
      | Ftrue => Ftrue
      | Ffalse => Ffalse
      | Fnot f => Fnot f
      | Fand f1 f2 => Fand (Optimizer_CNF n' f1) (Optimizer_CNF n' f2)
      (* SENDES VIDERE *)
      | For f1 f2 =>
          match Optimizer_CNF n f1, Optimizer_CNF n f2 with
          | x, Fand y z => Fand (Optimizer_CNF n' (For x y)) (Optimizer_CNF n' (For x z))
          | Fand x y, z => Fand (Optimizer_CNF n' (For x z)) (Optimizer_CNF n' (For y z))
          | f1', f2' => For f1' f2'
          end
      (* IKKE MULIG *)
      | s => s
      end
  end.
*)

(* 
  | Fimplies f1 f2, true => For (Optimizer_NNF f1 false) (Optimizer_NNF f2 true)
  | Fimplies f1 f2, false => Fand (Optimizer_NNF f1 true) (Optimizer_NNF f2 false) *)
  (* DIREKTE OPTIMIZED *)



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
