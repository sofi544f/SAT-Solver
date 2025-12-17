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

(* OPGAVER *)

(* TODO - E1 *)
Inductive form :  Type:=
  | Fvar : id -> form 
  | Ftrue : form
  | Ffalse : form
  | Fand : form -> form -> form
  | For : form -> form -> form
  | Fimplies : form -> form -> form
  | Fnot : form -> form.

Notation "F( X )" := (Fvar X) (at level 10).
Notation "A F/\ B" := (Fand A B) (at level 10).
Notation "A F\/ B" := (For A B) (at level 10).
Notation "A F-> B" := (Fimplies A B) (at level 10).
Notation "F~ A" := (Fnot A) (at level 10).

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

(* Tests for correctness of interp *)
Definition OneTrue_valuation : valuation := 
  override (empty_valuation) (Id 1) true.

Example prop1_false : interp OneTrue_valuation prop1 = false.
Proof.
  reflexivity.
Qed.

Example prop2_true : interp OneTrue_valuation prop2 = true.
Proof.
  reflexivity.
Qed.

Example prop3_false : interp OneTrue_valuation prop3 = false.
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

(* Testing list_variables *)
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

(* Testing generate_truthtable *)
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

(* E6 *)
Definition solver (p : form ) : bool :=
  match find_valuation p with
  | Some _ => true
  | None => false
  end.


(*Explain the difference between satisfiable and solver. *)
(* 
SATISFIABLE:
Satisfiable, is a function that given a form returns a proposition that states
that there exists a valuation, s.t. interp of the valuation and form is true. 
As satisfiable just returns a proposition, it doesn’t actually in and of itself 
prove anything about the boolean formula. The returned proposition for each formula
could be provable, disprovable or neither. 

SOLVER:
Given a form, Solver will use the find_evaluation function to exhaustively search
for any valuation that satisfies the form. If such a valuation is found, solver
will return true. If not, solver will return false.


As such, solver should return true for any form p, and only those forms p, 
for which satisfiable p is provable.
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
  destruct (find_valuation p) eqn:EH; try discriminate.
  unfold find_valuation in EH.
  set (l:= generate_truthtable (list_variables p) empty_valuation) in EH. (* DOCUMENTATION: https://stackoverflow.com/questions/78321778/is-is-possible-to-rename-a-coq-term *)
  induction l as [| v' l' IHl'].
  - simpl in EH. discriminate.
  - destruct (interp v' p) eqn: Ev'.
    + unfold satisfiable. exists v'. assumption.
    + simpl in EH. rewrite Ev' in EH. apply IHl' in EH. assumption. 
Qed.  

(* EXTRA EXERCISES *)

(* EXTRA -- Boolean optimizer *)

Fixpoint Optimizer (p : form) : form :=
  match p with
  (* Base-case *)
  | Fvar x => Fvar x
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  (* Recursive *)
  | Fnot f => Fnot (Optimizer f)
  | Fimplies f1 f2 => Fimplies (Optimizer f1) (Optimizer f2)
  | Fand f1 f2 =>
      match Optimizer f1, Optimizer f2 with
      | Ftrue, (Fvar x) => Fvar x
      | (Fvar x), Ftrue => Fvar x
      | _, Ffalse => Ffalse
      | Ffalse, _ => Ffalse
      | _, _ => Fand (Optimizer f1) (Optimizer f2)
      end
  | For f1 f2 => 
      match Optimizer f1, Optimizer f2 with
      | Ftrue, _ => Ftrue
      | _, Ftrue => Ftrue
      | (Fvar x), Ffalse => Fvar x
      | Ffalse, (Fvar x) => Fvar x
      | _, _ => For (Optimizer f1) (Optimizer f2)
      end
  end.

(* Testing Optimizer *)
Example Opti_1: (Optimizer (X F/\ Ftrue)) = X.
Proof.
  reflexivity.
Qed.

Example Opti_2: (Optimizer (X F/\ Ffalse)) = Ffalse.
Proof.
  reflexivity.
Qed.

Example Opti_3: 
  (Optimizer ((Ftrue F\/ X) F-> (X F/\ Ftrue))) = Ftrue F-> X.
Proof.
  reflexivity.
Qed.

Fixpoint illegal_boolean_formulas_are_present (p : form) : bool :=
  match p with
  (* Base-case *)
  | Fvar x => false
  | Ftrue => false
  | Ffalse => false
  (* Recursive *)
  | Fnot f => illegal_boolean_formulas_are_present f
  | Fimplies f1 f2 => orb (illegal_boolean_formulas_are_present f1) (illegal_boolean_formulas_are_present f2)
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
  
Definition Optimizer_preserves_interp_on_form (p: form) (v : valuation) : Prop :=
  interp v p = interp v (Optimizer p).

Ltac rwrt_2 h1 h2:=
  rewrite h1 ; rewrite h2.

Theorem Optimizer_preserves_interp : forall p v, 
    Optimizer_preserves_interp_on_form p v.
Proof.
  unfold Optimizer_preserves_interp_on_form.
  intros p v. 
  induction p ; 
  simpl ; 
  try reflexivity.
  - 
    destruct (Optimizer p1) eqn: Ep1 ; 
    try (
          rwrt_2 IHp1 IHp2 ; 
          reflexivity
        ) ;
    simpl ; destruct (Optimizer p2) eqn:Ep2 ; try (rwrt_2 IHp1 IHp2; reflexivity) ;
    try (
          rwrt_2 IHp1 IHp2 ;
          apply andb_true_r 
        ) ;
    try (
          rwrt_2 IHp1 IHp2 ;
          apply andb_false_r 
        ).
  - 
    destruct (Optimizer p1) eqn: Ep1 ;
    try (
          rwrt_2 IHp1 IHp2 ; 
          reflexivity
        ) ;
    simpl ; destruct (Optimizer p2) eqn:Ep2 ; try (rwrt_2 IHp1 IHp2; reflexivity) ;
    try (
          rwrt_2 IHp1 IHp2 ;
          apply orb_true_r 
        ) ;
    try (
          rwrt_2 IHp1 IHp2 ;
          apply orb_false_r 
        ).
  - rwrt_2 IHp1 IHp2. reflexivity.
  - rewrite IHp. reflexivity.  
Qed. 

Theorem Optimizer_correct : forall p v,
Optimized_form_doesn't_contain_illegal_expression p /\ Optimizer_preserves_interp_on_form p v.
Proof.
  intros.
  split. 
  - apply Optimizer_doesn't_contain_illegal_expressions.
  - apply Optimizer_preserves_interp.
Qed.

Definition solver2 (p : form ) : bool :=
  solver(Optimizer p).

Lemma solver2_sound : forall p, solver2 p = true -> satisfiable p.
Proof.
  intros p H. 
  unfold solver2 in H.
  apply solver_sound in H.
  unfold satisfiable in H.
  unfold satisfiable.
  destruct H.
  exists x.
  rewrite Optimizer_preserves_interp.
  assumption.
Qed.

Lemma solver2_sound' : forall p, solver2 p = true -> satisfiable p.
Proof.
  intros p H. 
  unfold solver2 in H.
  unfold solver in H.
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
Initial definition:

Fixpoint optimizerNNF_run (p : form) : form :=
  match p with
  (* Base-case *)
  | Fvar x => Fvar x
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  (* Optimized *)
  | Fand f1 f2 => Fand (optimizerNNF_run f1) (optimizerNNF_run f2)
  | For f1 f2 => For (optimizerNNF_run f1) (optimizerNNF_run f2)

  | Fimplies f1 f2 => For (optimizerNNF_run (Fnot f1)) (optimizerNNF_run f2)
  | Fnot f => 
      match (optimizerNNF_run f) with
      | Fvar x => Fnot (Fvar x)
      | Ftrue => Ffalse
      | Ffalse => Ftrue
      | Fnot f' => f'
      | Fand f1 f2 => For (optimizerNNF_run (Fnot f1)) (optimizerNNF_run (Fnot f2))
      | For f1 f2 => Fand (optimizerNNF_run (Fnot f1)) (optimizerNNF_run (Fnot f2))
      | Fimplies f1 f2 => Fand (optimizerNNF_run f1) (optimizerNNF_run (Fnot f2))
  end. *)

Fixpoint optimizerNNF_run (p : form) (b: bool) : form :=
  match p, b with
  (* Base-case *)
  | Fvar x, true => Fvar x
  | Fvar x, false => Fnot (Fvar x)

  | Ftrue, true => Ftrue
  | Ftrue, false => Ffalse

  | Ffalse, true => Ffalse
  | Ffalse, false => Ftrue
  (* Recursive *)
  | Fand f1 f2, true => Fand (optimizerNNF_run f1 true) (optimizerNNF_run f2 true)
  | Fand f1 f2, false => For (optimizerNNF_run f1 false) (optimizerNNF_run f2 false)

  | For f1 f2, true => For (optimizerNNF_run f1 true) (optimizerNNF_run f2 true)
  | For f1 f2, false => Fand (optimizerNNF_run f1 false) (optimizerNNF_run f2 false)

  | Fimplies f1 f2, true => For (optimizerNNF_run f1 false) (optimizerNNF_run f2 true)
  | Fimplies f1 f2, false => Fand (optimizerNNF_run f1 true) (optimizerNNF_run f2 false)

  | Fnot f, false => optimizerNNF_run f true
  | Fnot f, true => optimizerNNF_run f false
  end.

Lemma optimizerNNF_run_booleq_neg : forall p,
 (optimizerNNF_run (F~ p) true) = optimizerNNF_run p false.
Proof.
  induction p; try reflexivity.
Qed.

Lemma optimizerNNF_run_double_neg : forall p,
 (optimizerNNF_run (F~ (F~ p)) true) = optimizerNNF_run p true.
Proof.
  induction p; try reflexivity.
Qed.

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

Fixpoint neg_applied_to_non_literals (p: form) : bool :=
  match p with
  (* SAME *)
  | Fvar x => false
  | Ftrue => false
  | Ffalse => false
  (* SENDES VIDERE *)
  | Fand f1 f2 => orb (neg_applied_to_non_literals f1) (neg_applied_to_non_literals f2)
  | For f1 f2 => orb (neg_applied_to_non_literals f1) (neg_applied_to_non_literals f2)
  | Fimplies f1 f2 => orb (neg_applied_to_non_literals f1) (neg_applied_to_non_literals f2)
  (* DIREKTE OPTIMIZED *)
  | Fnot f => 
      match f with
      | For _ _ => true
      | Fand _ _ => true
      | Fimplies _ _ => true
      | Fnot _ => true
      | Ftrue => true
      | Ffalse => true
      | _ => neg_applied_to_non_literals f
      end
  end.

Lemma optimizerNNF_run_neglit_eq : forall (p:form),
  neg_applied_to_non_literals (optimizerNNF_run p false) = neg_applied_to_non_literals (optimizerNNF_run p true).
Proof.
  intros p. induction p; try reflexivity ; simpl;
  try (rewrite <- IHp1; rewrite <- IHp2; reflexivity).
  rewrite IHp. reflexivity.
Qed.  

Lemma optimizerNNF_run_neg_only_applied_to_literals : forall p,
  neg_applied_to_non_literals (optimizerNNF_run p true) = false.
Proof.
  induction p; 
  try reflexivity;
  try (simpl; rewrite IHp1; rewrite IHp2; reflexivity);
  simpl;
  rewrite optimizerNNF_run_neglit_eq.
  - rwrt_2 IHp1 IHp2. reflexivity.
  - assumption.
Qed.

Lemma optimizerNNF_run_implication_eq : forall (p:form),
    implication_is_present (optimizerNNF_run p false) = implication_is_present (optimizerNNF_run p true).
Proof.
  intros p. induction p; try reflexivity ; simpl;
  try (rewrite <- IHp1; rewrite <- IHp2; reflexivity).
  rewrite IHp. reflexivity.
Qed.

Lemma optimizerNNF_run_no_impl : forall p,
  implication_is_present (optimizerNNF_run p true) = false.
Proof.
  induction p; 
  try reflexivity;
  try (simpl; rewrite IHp1; rewrite IHp2; reflexivity);
  simpl;
  rewrite optimizerNNF_run_implication_eq.
  - rwrt_2 IHp1 IHp2. reflexivity.
  - assumption.
Qed.

(* BOOLEAN-OPTIMIZER *)

Fixpoint optimizer_bool (p : form) : form :=
  match p with
  (* SAME *)
  | Fvar x => Fvar x
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  (* SENDES VIDERE *)
  | Fnot f => Fnot (optimizer_bool f)
  | Fimplies f1 f2 => Fimplies (optimizer_bool f1) (optimizer_bool f2)
  (* DIREKTE OPTIMIZED *)
  | Fand f1 f2 =>
      match optimizer_bool f1, optimizer_bool f2 with
      | Ftrue, f2' => f2'
      | f1', Ftrue => f1'
      | _, Ffalse => Ffalse
      | Ffalse, _ => Ffalse
      | _, _ => Fand (optimizer_bool f1) (optimizer_bool f2)
      end
  | For f1 f2 => 
  (* For (Optimizer f1) (Optimizer f2) *)
      match optimizer_bool f1, optimizer_bool f2 with
      | Ftrue, _ => Ftrue
      | _, Ftrue => Ftrue
      | f1', Ffalse => f1'
      | Ffalse, f2' => f2'
      | _, _ => For (optimizer_bool f1) (optimizer_bool f2)
      end
  end.

Lemma optimizer_preserves_no_neg_applied_to_non_litterals : forall p,
  neg_applied_to_non_literals p = false ->
  neg_applied_to_non_literals (optimizer_bool p) = false.
Proof. 
  intros p.
  induction p;
  intros H;
  try reflexivity;
  simpl in H.
  - apply orb_false_elim in H. destruct H as [Ha Hb]. 
    apply IHp1 in Ha. apply IHp2 in Hb.
    simpl.
    destruct (optimizer_bool p1), (optimizer_bool p2); 
    try reflexivity;
    try (simpl; simpl in Hb; assumption);
    try (simpl; rewrite orb_false_r; simpl in Ha; assumption);
    try (simpl; simpl in Ha; simpl in Hb; rwrt_2 Ha Hb; reflexivity).
  
  - apply orb_false_elim in H. destruct H as [Ha Hb]. 
    apply IHp1 in Ha. apply IHp2 in Hb.
    simpl.
    destruct (optimizer_bool p1), (optimizer_bool p2) ; 
    try reflexivity;
    try (simpl; simpl in Hb; assumption);
    try (simpl; rewrite orb_false_r; simpl in Ha; assumption);
    try (simpl; simpl in Ha; simpl in Hb; rwrt_2 Ha Hb; reflexivity).

  - apply orb_false_elim in H. destruct H as [Ha Hb]. 
    apply IHp1 in Ha. apply IHp2 in Hb.
    simpl.
    destruct (optimizer_bool p1), (optimizer_bool p2); 
    try reflexivity;
    try (simpl; simpl in Hb; assumption);
    try (simpl; rewrite orb_false_r; simpl in Ha; assumption);
    try (simpl; simpl in Ha; simpl in Hb; rwrt_2 Ha Hb; reflexivity).
  
  - simpl.
    destruct p; 
    try discriminate;
    try (simpl; reflexivity).
Qed.

Lemma optimizer_preserves_implication_is_present : forall p,
  implication_is_present p = false ->
  implication_is_present (optimizer_bool p) = false.
Proof. 
  intros p.
  induction p;
  intros H;
  try reflexivity;
  simpl in H.
  - apply orb_false_elim in H. destruct H as [Ha Hb]. 
    apply IHp1 in Ha. apply IHp2 in Hb.
    simpl.
    destruct (optimizer_bool p1), (optimizer_bool p2); 
    try reflexivity;
    try (simpl; simpl in Hb; assumption);
    try (simpl; rewrite orb_false_r; simpl in Ha; assumption);
    try (simpl; simpl in Ha; simpl in Hb; rwrt_2 Ha Hb; reflexivity).

  - apply orb_false_elim in H. destruct H as [Ha Hb]. 
    apply IHp1 in Ha. apply IHp2 in Hb.
    simpl.
    destruct (optimizer_bool p1), (optimizer_bool p2); 
    try reflexivity;
    try (simpl; simpl in Hb; assumption);
    try (simpl; rewrite orb_false_r; simpl in Ha; assumption);
    try (simpl; simpl in Ha; simpl in Hb; rwrt_2 Ha Hb; reflexivity).

  - discriminate.
  - simpl. apply IHp. assumption.
Qed.

(* CHECKING BOOLEAN OPTIMIZER *)

Fixpoint boolean_conj_disj_present (p : form) : bool :=
  match p with
  (* SAME *)
  | Fvar x => false
  | Ftrue => false
  | Ffalse => false
  (* SENDES VIDERE *)
  | Fnot f => boolean_conj_disj_present f
  | Fimplies f1 f2 => orb (boolean_conj_disj_present f1) (boolean_conj_disj_present f2)
  (* DIREKTE OPTIMIZED *)
  | Fand f1 f2 =>
      match f1, f2 with
      | _, Ftrue => true
      | Ftrue, _ => true
      | _, Ffalse => true
      | Ffalse, _ => true
      | _, _ => orb (boolean_conj_disj_present f1) (boolean_conj_disj_present f2)
      end
  | For f1 f2 => 
      match  f1, f2 with
      | _, Ftrue => true
      | Ftrue, _ => true
      | _, Ffalse => true
      | Ffalse, _ => true
      | _, _ => orb (boolean_conj_disj_present f1) (boolean_conj_disj_present f2)
      end
  end.

Definition optimizer_bool_form_contains_no_bool_conj_disj (p : form) : Prop :=
  boolean_conj_disj_present (optimizer_bool p) = false.

Theorem optimizer_bool_contains_no_bool_conj_disj : forall p,
    optimizer_bool_form_contains_no_bool_conj_disj p.
Proof.
  unfold optimizer_bool_form_contains_no_bool_conj_disj.
  induction (p) ;
  try reflexivity ;
  try assumption ;
  try (
        simpl ;
        destruct (optimizer_bool f1), (optimizer_bool f2) ; 
        try reflexivity ; 
        try assumption ;
        try (simpl; rewrite orb_false_r ; assumption) ;
        try (simpl ; apply orb_false_intro ; assumption)
      ). 
Qed. 

(* END BOOLEAN OPTIMIZER *)

Definition optimizerNNF (p:form) : form :=
  optimizer_bool (optimizerNNF_run p true).

(* Testing optimizerNNF *)

Example optiNNF1 : optimizerNNF (X F-> Y) = ((F~ (X)) F\/ (Y)).
Proof.
  reflexivity.
Qed.

Example optiNNF2 : optimizerNNF ((F~ (F~ (F~ X))) F/\ Y) = ((F~ (X)) F/\ (Y)).
Proof.
  reflexivity.
Qed.

Example optiNNF3 : optimizerNNF (Z F-> (F~ (X F/\ Y))) = ((F~ Z) F\/ ((F~ X) F\/ (F~ Y))).
Proof.
  reflexivity.
Qed.

Lemma optimizerNNF_neg_only_applied_to_literals : forall p,
  neg_applied_to_non_literals (optimizerNNF p) = false.
Proof.
  intros p.
  unfold optimizerNNF.
  apply optimizer_preserves_no_neg_applied_to_non_litterals.
  apply optimizerNNF_run_neg_only_applied_to_literals.
Qed.

Lemma optimizerNNF_no_implication_present : forall p,
  implication_is_present (optimizerNNF p) = false.
Proof.
  intros p.
  unfold optimizerNNF.
  apply optimizer_preserves_implication_is_present.
  apply optimizerNNF_run_no_impl.
Qed.

Lemma optimizerNNF_no_illegal_boolean_formulas_are_present : forall p,
  boolean_conj_disj_present (optimizerNNF p) = false.
Proof.
  intros p.
  unfold optimizerNNF.
  apply optimizer_bool_contains_no_bool_conj_disj.
Qed.

Definition optimizerNNF_doesn't_contain_illegal_expression_on_form (p : form) : Prop :=
  implication_is_present (optimizerNNF p) = false 
  /\ neg_applied_to_non_literals (optimizerNNF p) = false
  /\ boolean_conj_disj_present (optimizerNNF p) = false.

Theorem optimizerNNF_creates_correct_form : forall p,
  optimizerNNF_doesn't_contain_illegal_expression_on_form p.
Proof.
  unfold optimizerNNF_doesn't_contain_illegal_expression_on_form; repeat split.
  - apply optimizerNNF_no_implication_present.
  - apply optimizerNNF_neg_only_applied_to_literals.
  - apply optimizerNNF_no_illegal_boolean_formulas_are_present.
Qed.

Lemma optimizerNNF_run_false_negb : forall (p:form) (v : valuation),
    negb (interp v (optimizerNNF_run p true)) = interp v (optimizerNNF_run p false).
Proof.
  intros p v. 
  induction p; 
  try reflexivity ; 
  simpl.
  - rewrite <- IHp1. rewrite <- IHp2. apply negb_andb.
  - rewrite <- IHp1. rewrite <- IHp2. apply negb_orb.
  - rewrite <- IHp1. rewrite <-IHp2. rewrite negb_orb. rewrite negb_involutive. reflexivity.
  - rewrite <- IHp. apply negb_involutive.
Qed. 

(* ADDITION *)
Definition optimizer_bool_preserves_interp_on_form (p: form) (v : valuation) : Prop :=
  interp v p = interp v (optimizer_bool p).

Theorem optimizer_bool_preserves_interp : forall p v, 
    optimizer_bool_preserves_interp_on_form p v.
Proof.
  unfold optimizer_bool_preserves_interp_on_form.
  intros p v. induction p ; simpl ; try reflexivity.
  - 
    destruct (optimizer_bool p1), (optimizer_bool p2);
    try (rwrt_2 IHp1 IHp2; reflexivity);
    try (rwrt_2 IHp1 IHp2; simpl; apply andb_true_r);
    try (rwrt_2 IHp1 IHp2; simpl; apply andb_false_r).
  - 
    destruct (optimizer_bool p1), (optimizer_bool p2);
    try (rwrt_2 IHp1 IHp2; reflexivity);
    try (rwrt_2 IHp1 IHp2; simpl; apply orb_true_r);
    try (rwrt_2 IHp1 IHp2; simpl; apply orb_false_r).
  - rwrt_2 IHp1 IHp2. reflexivity.
  - rewrite IHp. reflexivity.  
Qed. 
(* END ADDITION *)

Definition optimizerNNF_preserves_interp_on_form (p: form) (v: valuation) : Prop := 
    interp v p = interp v (optimizerNNF p).
  
Theorem optimizerNNF_preservers_interp : forall p v,
  optimizerNNF_preserves_interp_on_form p v.
Proof.
  intros p v. 
  unfold optimizerNNF_preserves_interp_on_form. unfold optimizerNNF.
  rewrite <-optimizer_bool_preserves_interp.
  induction p ; 
  try reflexivity;
  simpl;
  try (rwrt_2 IHp1 IHp2; reflexivity).
  - rewrite <-optimizerNNF_run_false_negb. 
    rewrite <-IHp1. rewrite <-IHp2. 
    destruct (interp v p1), (interp v p2); 
    try reflexivity.
  - rewrite <-optimizerNNF_run_false_negb. rewrite IHp. reflexivity. 
Qed.

Theorem optimizerNNF_correct : forall p v,
optimizerNNF_doesn't_contain_illegal_expression_on_form p /\ optimizerNNF_preserves_interp_on_form p v.
Proof.
  intros.
  split. 
  - apply optimizerNNF_creates_correct_form.
  - apply optimizerNNF_preservers_interp.
Qed.

Definition solverNNF (p : form ) : bool :=
  match find_valuation (optimizerNNF p) with
  | Some _ => true
  | None => false
  end.

Lemma solverNNF_sound : forall p, solverNNF p = true -> satisfiable p.
Proof.
  intros p H. 
  unfold solverNNF in H.
  apply solver_sound in H.
  unfold satisfiable in H.
  unfold satisfiable.
  destruct H.
  exists x.
  rewrite optimizerNNF_preservers_interp.
  assumption.
Qed.

Lemma solverNNF_sound' : forall p, solverNNF p = true -> satisfiable p.
Proof.
  intros p H. 
  unfold solverNNF in H.
  destruct (find_valuation (optimizerNNF p)) eqn:EH.
  - unfold find_valuation in EH. 
    unfold filter in EH. 
    assert (L: forall x, interp x p = interp x (optimizerNNF p)).
    {
      apply optimizerNNF_preservers_interp.
    }
    set (tt := generate_truthtable (list_variables (optimizerNNF p)) empty_valuation) in EH.
    induction tt as [| v' l' IHl'].
    + discriminate.
    + destruct (interp v' (optimizerNNF p)) eqn: Ev'.
      * rewrite <- optimizerNNF_preservers_interp in Ev'. unfold satisfiable. exists v'. assumption.
      * apply IHl'. assumption.
  - discriminate.
Qed.

(* EXTRA -- Conjunctive Normal Form *)

(* 
Initial definition:

Fixpoint optimizerCNF_run (p : form) : form :=
  match p with
  (* Base-case *)
  | Fvar x => Fvar x
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  (* Optimized *)
  | Fnot f => Fnot (optimizerCNF_run f)
  | Fand f1 f2 => Fand (optimizerCNF_run f1) (optimizerCNF_run f2)
  | Fimplies f1 f2 => Fimplies (optimizerCNF_run f1) (optimizerCNF_run f2)
  | For f1 f2 => For (optimizerCNF_run f1) (optimizerCNF_run f2)

  | For f1 f2 => 
      match f1, f2 with
      | Fand x y, z => Fand (optimizerCNF_run (For z x)) (optimizerCNF_run (For z y))
      | x, Fand y z => Fand (optimizerCNF_run (For x y)) (optimizerCNF_run (For x z))
      | f1', f2' => For (optimizerCNF_run f1') (optimizerCNF_run f2')
  end. *)

Fixpoint optimizerCNF_step (p : form) : form :=
  match p with 
    (* Base-case *)
    | Fvar x => Fvar x
    | Ftrue => Ftrue
    | Ffalse => Ffalse
    (* Recursive *)
    | Fnot f => Fnot (optimizerCNF_step f)
    | Fand f1 f2 => Fand (optimizerCNF_step f1) (optimizerCNF_step f2)
    | Fimplies f1 f2 => Fimplies (optimizerCNF_step f1) (optimizerCNF_step f2)

    | For f1 f2 =>
        match f1, f2 with
        | Fand x y, z => Fand (For z x) (For z y)
        | x, Fand y z => Fand (For x y) (For x z)
        | f1', f2' => For (optimizerCNF_step f1') (optimizerCNF_step f2')
      end
  end.

Fixpoint count_steps (p: form) (n: nat) : nat :=
  match p with 
    (* Base *)
    | Fvar x => 0
    | Ftrue => 0
    | Ffalse => 0
    (* Recursive *)
    | Fnot f => count_steps f n
    | Fand f1 f2 => n + (max (count_steps f1 n) (count_steps f2 n))
    | For f1 f2 => (count_steps f1 (n + 1)) + (count_steps f2 (n + 1))
    | Fimplies f1 f2 => max (count_steps f1 n) (count_steps f2 n)
  end.

(* testing count_step *)
Example count_step1 : (count_steps (X F\/ (Z F/\ Y)) 0) = 1.
Proof.
  reflexivity.
Qed.

Example count_step2 : (count_steps (X F\/ (Z F/\ ((X) F\/ (Z F/\ Y)))) 0) = 3.
Proof.
  reflexivity.
Qed.

Definition optimizerCNF_step_preserves_interp : forall p v,
  interp v p
  = interp v (optimizerCNF_step p).
Proof.
  intros. 
  induction p; 
  simpl;
  try (rewrite IHp1; rewrite IHp2);
  try reflexivity.
  - destruct p1 eqn:Ep1; destruct p2 eqn:Ep2 ; 
    try (reflexivity);
    try (
          simpl; 
          rewrite <-orb_andb_distrib_r; 
          simpl in IHp1; 
          simpl in IHp2; 
          rwrt_2 IHp1 IHp2; 
          try reflexivity; 
          try apply orb_comm
        );
    simpl.
    + rewrite <-orb_andb_distrib_r. simpl in IHp2. rewrite IHp2. reflexivity.
    + simpl in IHp2. rewrite IHp2. reflexivity.
    + rewrite <-orb_andb_distrib_r. simpl in IHp1. rewrite IHp1. apply orb_comm.
    + rewrite orb_true_r. reflexivity.
    + rewrite orb_false_r. simpl in IHp1. rewrite IHp1. reflexivity.
  - rewrite IHp. reflexivity. 
Qed.     

Fixpoint optimizerCNF_run (p : form) (n : nat): form :=
  match n with
  | 0 => p
  | S n' => optimizerCNF_run (optimizerCNF_step p) n'
  end.

Definition optimizerCNF (p : form) : form :=
  optimizerCNF_run (optimizerNNF p) (count_steps (optimizerNNF p) 0).

Example optimizerCNF1 : 
  optimizerCNF ((X F/\ Y) F\/ (Y F/\ Z)) = (((X F\/ Y) F/\ (X F\/ Z)) F/\ ((Y F\/ Y) F/\ (Y F\/ Z))).
Proof.
  reflexivity.
Qed.

Example optimizerCNF2 : 
  optimizerCNF (Ftrue F-> (X F\/ Y)) = (X F\/ Y).
Proof.
  reflexivity.
Qed.

Example optimizerCNF3 : 
  optimizerCNF ((X F\/ Y) F-> Z) = (Z F\/ (Fnot X)) F/\ (Z F\/ (Fnot Y)).
Proof.
  reflexivity.
Qed.

Lemma optimizerCNF_run_step_step_run : forall p n,
  (optimizerCNF_run (optimizerCNF_step p) n) = (optimizerCNF_step (optimizerCNF_run p n)).
Proof.
  intros p n. generalize dependent p.
  induction n.
  - reflexivity.
  - intros p. simpl. rewrite IHn with (p:=(optimizerCNF_step p)). reflexivity.
Qed.

Theorem optimizerCNF_preserves_interp : forall p v,
  interp v p
  = interp v (optimizerCNF p).
Proof.
  intros p v.
  unfold optimizerCNF.
  set (n:= (count_steps (optimizerNNF p) 0)).
  induction n;
  simpl.
  - apply optimizerNNF_preservers_interp.
  - rewrite IHn. rewrite optimizerCNF_run_step_step_run. apply optimizerCNF_step_preserves_interp.
Qed. 

Definition solverCNF (p : form ) : bool :=
  match find_valuation (optimizerCNF p) with
  | Some _ => true
  | None => false
  end.

Lemma solverCNF_sound : forall p, solverCNF p = true -> satisfiable p.
Proof.
  intros p H. 
  unfold solverCNF in H.
  apply solver_sound in H.
  unfold satisfiable in H.
  unfold satisfiable.
  destruct H.
  exists x.
  rewrite optimizerCNF_preserves_interp.
  assumption.
Qed.

Lemma solverCNF_sound' : forall p, solverCNF p = true -> satisfiable p.
Proof.
  intros p H. 
  unfold solverCNF in H.
  destruct (find_valuation (optimizerCNF p)) eqn:EH.
  - unfold find_valuation in EH. 
    unfold filter in EH. 
    assert (L: forall x, interp x p = interp x (optimizerCNF p)).
    {
      apply optimizerCNF_preserves_interp.
    }
    set (tt := generate_truthtable (list_variables (optimizerCNF p)) empty_valuation) in EH.
    induction tt as [| v' l' IHl'].
    + discriminate.
    + destruct (interp v' (optimizerCNF p)) eqn: Ev'.
      * rewrite <- optimizerCNF_preserves_interp in Ev'. unfold satisfiable. exists v'. assumption.
      * apply IHl'. assumption.
  - discriminate.
Qed.
