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
  | Fvar : id -> form 
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

Theorem Optimizer_correct : forall p v,
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

Fixpoint optimizerNNF_run (p : form) (b: bool) : form :=
  match p, b with
  (* SAME *)
  | Fvar x, true => Fvar x
  | Fvar x, false => Fnot (Fvar x)

  | Ftrue, true => Ftrue
  | Ftrue, false => Ffalse

  | Ffalse, true => Ffalse
  | Ffalse, false => Ftrue
  (* SENDES VIDERE *)
  | Fand f1 f2, true => Fand (optimizerNNF_run f1 true) (optimizerNNF_run f2 true)
  | Fand f1 f2, false => For (optimizerNNF_run f1 false) (optimizerNNF_run f2 false)

  | For f1 f2, true => For (optimizerNNF_run f1 true) (optimizerNNF_run f2 true)
  | For f1 f2, false => Fand (optimizerNNF_run f1 false) (optimizerNNF_run f2 false)

  | Fimplies f1 f2, true => For (optimizerNNF_run f1 false) (optimizerNNF_run f2 true)
  | Fimplies f1 f2, false => Fand (optimizerNNF_run f1 true) (optimizerNNF_run f2 false)
  (* DIREKTE OPTIMIZED *)
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
  try (simpl; rewrite IHp1; rewrite IHp2; reflexivity).
  - simpl. rewrite optimizerNNF_run_neglit_eq. rewrite IHp1. rewrite IHp2. reflexivity.
  - simpl. rewrite optimizerNNF_run_neglit_eq. assumption.
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
  try (simpl; rewrite IHp1; rewrite IHp2; reflexivity).
  - simpl. rewrite optimizerNNF_run_implication_eq. rewrite IHp1. rewrite IHp2. reflexivity.
  - simpl. rewrite optimizerNNF_run_implication_eq. assumption.
Qed.

Lemma optimizer_preserves_no_neg_applied_to_non_litterals : forall p,
  neg_applied_to_non_literals p = false ->
  neg_applied_to_non_literals (Optimizer p) = false.
Proof. 
  intros p.
  induction p;
  intros H;
  try reflexivity.
  - simpl in H. 
    apply orb_false_elim in H. destruct H as [Ha Hb]. apply IHp1 in Ha. apply IHp2 in Hb.
    simpl.
    destruct (Optimizer p1), (Optimizer p2); 
    try reflexivity; 
    try (simpl; simpl in IHp2; assumption);
    try (simpl; rewrite orb_false_r; simpl in IHp1; assumption);
    try (
        simpl; simpl in Ha; simpl in Hb;
        apply orb_false_elim in Ha; apply orb_false_elim in Hb;
        destruct Ha as [Ha1 Ha2]; destruct Hb as [Hb1 Hb2];
        rewrite Ha1; rewrite Ha2; rewrite Hb1; rewrite Hb2;
        reflexivity
      );
    try (
        simpl; simpl in Ha; simpl in Hb;
        apply orb_false_elim in Ha;
        destruct Ha as [Ha1 Ha2]; 
        rewrite Ha1; rewrite Ha2; 
        assumption
    );
    try (
        simpl; simpl in Hb; simpl in Ha;
        apply orb_false_elim in Hb;
        destruct Hb as [Hb1 Hb2]; 
        rewrite Hb1; rewrite Hb2; 
        apply orb_false_intro; try reflexivity;
        assumption
    ).
    + simpl. simpl in Ha. simpl in Hb.
      rewrite Ha. rewrite Hb. reflexivity.
  
  - simpl in H. 
    apply orb_false_elim in H. destruct H as [Ha Hb]. apply IHp1 in Ha. apply IHp2 in Hb.
    simpl.
    destruct (Optimizer p1), (Optimizer p2); 
    try reflexivity; 
    try (simpl; simpl in IHp2; assumption);
    try (simpl; rewrite orb_false_r; simpl in IHp1; assumption);
    try (
        simpl; simpl in Ha; simpl in Hb;
        apply orb_false_elim in Ha; apply orb_false_elim in Hb;
        destruct Ha as [Ha1 Ha2]; destruct Hb as [Hb1 Hb2];
        rewrite Ha1; rewrite Ha2; rewrite Hb1; rewrite Hb2;
        reflexivity
      );
    try (
        simpl; simpl in Ha; simpl in Hb;
        apply orb_false_elim in Ha;
        destruct Ha as [Ha1 Ha2]; 
        rewrite Ha1; rewrite Ha2; 
        assumption
    );
    try (
        simpl; simpl in Hb; simpl in Ha;
        apply orb_false_elim in Hb;
        destruct Hb as [Hb1 Hb2]; 
        rewrite Hb1; rewrite Hb2; 
        apply orb_false_intro; try reflexivity;
        assumption
    ).
    + simpl. simpl in Ha. simpl in Hb.
      rewrite Ha. rewrite Hb. reflexivity.

  - simpl in H. 
    apply orb_false_elim in H. destruct H as [Ha Hb]. apply IHp1 in Ha. apply IHp2 in Hb.
    simpl.
    destruct (Optimizer p1), (Optimizer p2); 
    try reflexivity; 
    try (simpl; simpl in IHp2; assumption);
    try (simpl; rewrite orb_false_r; simpl in IHp1; assumption);
    try (
        simpl; simpl in Ha; simpl in Hb;
        apply orb_false_elim in Ha; apply orb_false_elim in Hb;
        destruct Ha as [Ha1 Ha2]; destruct Hb as [Hb1 Hb2];
        rewrite Ha1; rewrite Ha2; rewrite Hb1; rewrite Hb2;
        reflexivity
      );
    try (
        simpl; simpl in Ha; simpl in Hb;
        apply orb_false_elim in Ha;
        destruct Ha as [Ha1 Ha2]; 
        rewrite Ha1; rewrite Ha2; 
        assumption
    );
    try (
        simpl; simpl in Hb; simpl in Ha;
        apply orb_false_elim in Hb;
        destruct Hb as [Hb1 Hb2]; 
        rewrite Hb1; rewrite Hb2; 
        apply orb_false_intro; try reflexivity;
        assumption
    ).
    + simpl. simpl in Ha. simpl in Hb.
      rewrite Ha. rewrite Hb. reflexivity.
  
  - simpl in H. simpl.
    destruct p; 
    try discriminate;
    try (simpl; reflexivity).
Qed.

Lemma optimizer_preserves_implication_is_present : forall p,
  implication_is_present p = false ->
  implication_is_present (Optimizer p) = false.
Proof. 
  intros p.
  induction p;
  intros H;
  try reflexivity.
  - simpl in H. 
    apply orb_false_elim in H. destruct H as [Ha Hb]. apply IHp1 in Ha. apply IHp2 in Hb.
    simpl.
    destruct (Optimizer p1), (Optimizer p2); 
    try reflexivity; 
    try (simpl; simpl in IHp2; assumption);
    try (simpl; rewrite orb_false_r; simpl in IHp1; assumption);
    try (
        simpl; simpl in Ha; simpl in Hb;
        apply orb_false_elim in Ha; apply orb_false_elim in Hb;
        destruct Ha as [Ha1 Ha2]; destruct Hb as [Hb1 Hb2];
        rewrite Ha1; rewrite Ha2; rewrite Hb1; rewrite Hb2;
        reflexivity
      );
    try (
        simpl; simpl in Ha; simpl in Hb;
        apply orb_false_elim in Ha;
        destruct Ha as [Ha1 Ha2]; 
        rewrite Ha1; rewrite Ha2; 
        assumption
    );
    try (
        simpl; simpl in Hb; simpl in Ha;
        apply orb_false_elim in Hb;
        destruct Hb as [Hb1 Hb2]; 
        rewrite Hb1; rewrite Hb2; 
        apply orb_false_intro; try reflexivity;
        assumption
    ).
    + simpl in Hb. discriminate.
    + simpl. simpl in Ha. simpl in Hb.
      rewrite Ha. rewrite Hb. reflexivity.
  
  - simpl in H. 
    apply orb_false_elim in H. destruct H as [Ha Hb]. apply IHp1 in Ha. apply IHp2 in Hb.
    simpl.
    destruct (Optimizer p1), (Optimizer p2); 
    try reflexivity; 
    try (simpl; simpl in IHp2; assumption);
    try (simpl; rewrite orb_false_r; simpl in IHp1; assumption);
    try (
        simpl; simpl in Ha; simpl in Hb;
        apply orb_false_elim in Ha; apply orb_false_elim in Hb;
        destruct Ha as [Ha1 Ha2]; destruct Hb as [Hb1 Hb2];
        rewrite Ha1; rewrite Ha2; rewrite Hb1; rewrite Hb2;
        reflexivity
      );
    try (
        simpl; simpl in Ha; simpl in Hb;
        apply orb_false_elim in Ha;
        destruct Ha as [Ha1 Ha2]; 
        rewrite Ha1; rewrite Ha2; 
        assumption
    );
    try (
        simpl; simpl in Hb; simpl in Ha;
        apply orb_false_elim in Hb;
        destruct Hb as [Hb1 Hb2]; 
        rewrite Hb1; rewrite Hb2; 
        apply orb_false_intro; try reflexivity;
        assumption
    ).
    + simpl in Hb. discriminate.
    + simpl. simpl in Ha. simpl in Hb.
      rewrite Ha. rewrite Hb. reflexivity.

  - simpl in H. discriminate.
  - simpl in H. simpl. apply IHp. assumption.
Qed.

Definition optimizerNNF (p:form) : form :=
  Optimizer (optimizerNNF_run p true).

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
  illegal_boolean_formulas_are_present (optimizerNNF p) = false.
Proof.
  intros p.
  unfold optimizerNNF.
  apply Optimizer_doesn't_contain_illegal_expressions.
Qed.

Definition optimizerNNF_doesn't_contain_illegal_expression_on_form (p : form) : Prop :=
  implication_is_present (optimizerNNF p) = false 
  /\ neg_applied_to_non_literals (optimizerNNF p) = false
  /\ illegal_boolean_formulas_are_present (optimizerNNF p) = false.

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

Definition optimizerNNF_preserves_interp_on_form (p: form) (v: valuation) : Prop := 
    interp v p = interp v (optimizerNNF p).
  
Theorem optimizerNNF_preservers_interp : forall p v,
  optimizerNNF_preserves_interp_on_form p v.
Proof.
  intros p v. 
  unfold optimizerNNF_preserves_interp_on_form. unfold optimizerNNF.
  rewrite <-Optimizer_preserves_interp.
  induction p ; try reflexivity.
  - simpl. rewrite IHp1. rewrite IHp2. reflexivity.
  - simpl. rewrite IHp1. rewrite IHp2. reflexivity.
  - simpl. rewrite <-optimizerNNF_run_false_negb. 
    rewrite <-IHp1. rewrite <-IHp2. 
    destruct (interp v p1), (interp v p2); 
    try reflexivity.
  - simpl. rewrite <-optimizerNNF_run_false_negb. rewrite IHp. reflexivity. 
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

Fixpoint optimizerCNF_step (p : form) : form :=
  match p with 
    (* SAME *)
    | Fvar x => Fvar x
    | Ftrue => Ftrue
    | Ffalse => Ffalse
    | Fnot f => Fnot (optimizerCNF_step f)
    | Fand f1 f2 => Fand (optimizerCNF_step f1) (optimizerCNF_step f2)
    (* SENDES VIDERE *)
    | For f1 f2 =>
        match f1, f2 with
        | Fand x y, z => Fand (For z x) (For z y)
        | x, Fand y z => Fand (For x y) (For x z)
        | f1', f2' => For (optimizerCNF_step f1') (optimizerCNF_step f2')
      end
    (* IKKE MULIG *)
    | Fimplies f1 f2 => Fimplies (optimizerCNF_step f1) (optimizerCNF_step f2)
  end.

Fixpoint count_steps (p: form) (n: nat) : nat :=
  match p with 
    (* SAME *)
    | Fvar x => 0
    | Ftrue => 0
    | Ffalse => 0
    | Fnot f => count_steps f n
    | Fand f1 f2 => n + (count_steps f1 n) + (count_steps f2 n)
    (* SENDES VIDERE *)
    | For f1 f2 => (count_steps f1 (n + 1)) + (count_steps f2 (n + 1))
    | Fimplies f1 f2 => (count_steps f1 n) + (count_steps f2 n)
  end.

Compute (count_steps (X F\/ (Z F/\ Y)) 0).
Compute (count_steps (X F\/ (Z F/\ ((X) F\/ (Z F/\ Y)))) 0).

Lemma optimizerCNF_step_dec_with_nat : forall p n,
  le (count_steps p n) (count_steps p (n+1)).
Proof.
  intros p.
  induction p; 
  try reflexivity;
  intros n; simpl;
  try (apply Nat.add_le_mono);
  try auto.
  - apply Nat.add_le_mono; auto.
    rewrite Nat.add_1_r. auto.
Qed.

Fixpoint count_Fand (p : form) : nat :=
  match p with
  | Fand f1 f2 => 1 + ((count_Fand f1) + (count_Fand f2))
  | For f1 f2 => ((count_Fand f1) + (count_Fand f2))
  | Fimplies f1 f2 => ((count_Fand f1) + (count_Fand f2))
  | Fnot f => (count_Fand f)
  (* SLUT *)
  | _ => 0
  end.

Lemma count_fand_0_count_step_0: forall p n,
  count_Fand p = 0 ->
  count_steps p n = 0.
Proof.
  induction p;
  intros n H;
  try reflexivity.
  - discriminate.
  - simpl. simpl in H.
    destruct (count_Fand p1) eqn: E1, (count_Fand p2 ) eqn:E2; try discriminate.
    specialize (IHp1 (n+1)). specialize (IHp2 (n+1)).
    rewrite IHp1; try rewrite IHp2; try reflexivity.
  - simpl. simpl in H.
    destruct (count_Fand p1) eqn: E1, (count_Fand p2 ) eqn:E2; try discriminate.
    specialize (IHp1 (n)). specialize (IHp2 (n)).
    rewrite IHp1; try rewrite IHp2; try reflexivity.
  - simpl. simpl in H.
    destruct (count_Fand p) eqn: E1; try discriminate.
    specialize (IHp (n)).
    rewrite IHp; reflexivity.
Qed.

Lemma count_step_or_0_count_fand_0 : forall p1 p2,
  count_steps (p1 F\/ p2) 0 = 0 ->
  count_Fand (p1 F\/ p2) = 0.
Proof.
  intros p1 p2.
  simpl.
  (* set (P:= (p1 F\/ p2)). *)
  induction p1; induction p2; 
  try reflexivity;
  try discriminate;
  intros H;
  (* simpl;  *)
  simpl in H;
  try (simpl; simpl in IHp2; apply IHp2; assumption);
  (* try (simpl in IHp2_1; simpl in IHp2_2); *)
  try (
    simpl;
    simpl in IHp2_1; simpl in IHp2_2; simpl in H;
    destruct (count_steps p2_1 1) eqn:Ep1, (count_steps p2_2 1) eqn:Ep2; try discriminate;
    simpl in H;
    apply IHp2_1 in H as Ha; rewrite Ha;
    apply IHp2_2 in H as Hb; rewrite Hb;
    reflexivity
      );
  try(
    simpl;
    simpl in IHp2_1; simpl in IHp2_2; simpl in H;
    destruct (count_steps p2_1 2) eqn:Ep1, (count_steps p2_2 2) eqn:Ep2; 
    try discriminate;
    assert (L1: le (count_steps p2_1 1) (count_steps p2_1 2)); try apply optimizerCNF_step_dec_with_nat;
    assert (L2: le (count_steps p2_2 1) (count_steps p2_2 2)); try apply optimizerCNF_step_dec_with_nat;
    rewrite Ep1 in L1; rewrite Ep2 in L2;
    apply Arith_base.le_n_0_eq_stt in L1; symmetry in L1;
    apply Arith_base.le_n_0_eq_stt in L2; symmetry in L2;
    apply IHp2_1 in L1; rewrite L1;
    apply IHp2_2 in L2; rewrite L2;
    reflexivity
  );
  try (simpl; simpl in IHp1; apply IHp1; assumption);
  try (
    try rewrite Nat.add_0_r; 
    try rewrite Nat.add_0_r in H;
    repeat rewrite Nat.add_0_r in IHp1_1;
    repeat rewrite Nat.add_0_r in IHp1_2;
    simpl;
    simpl in IHp1_1; simpl in IHp1_2; simpl in H;
    try rewrite Nat.add_0_r;
    try (rewrite Nat.add_0_r in H);
    destruct (count_steps p1_1 1) eqn:Ep1, (count_steps p1_2 1) eqn:Ep2; try discriminate;
    simpl in H;
    apply IHp1_1 in H as Ha; rewrite Ha;
    apply IHp1_2 in H as Hb; rewrite Hb;
    reflexivity
      );
  try(
    try rewrite Nat.add_0_r; 
    try rewrite Nat.add_0_r in H;
    repeat rewrite Nat.add_0_r in IHp1_1;
    repeat rewrite Nat.add_0_r in IHp1_2;
    simpl;
    simpl in IHp1_1; simpl in IHp1_2; simpl in H;
    destruct (count_steps p1_1 2) eqn:Ep1, (count_steps p1_2 2) eqn:Ep2; 
    try discriminate;
    assert (L1: le (count_steps p1_1 1) (count_steps p1_1 2)); try apply optimizerCNF_step_dec_with_nat;
    assert (L2: le (count_steps p1_2 1) (count_steps p1_2 2)); try apply optimizerCNF_step_dec_with_nat;
    rewrite Ep1 in L1; rewrite Ep2 in L2;
    apply Arith_base.le_n_0_eq_stt in L1; symmetry in L1;
    apply Arith_base.le_n_0_eq_stt in L2; symmetry in L2;
    apply IHp1_1 in L1; rewrite L1;
    apply IHp1_2 in L2; rewrite L2;
    reflexivity
  ).

  - simpl.
    simpl in H. 
    simpl in IHp1_1. simpl in IHp1_2.
    clear IHp2_1. clear IHp2_2.
    (* simpl in IHp2_1. simpl in IHp2_2. *)
    destruct  (count_steps p1_1 2) eqn:Ep1, 
              (count_steps p1_2 2) eqn:Ep2,
              (count_steps p2_1 2) eqn:Ep1', 
              (count_steps p2_2 2) eqn:Ep2'; try discriminate.
    clear H. 
    simpl in IHp1_1. simpl in IHp1_2.
    rewrite Nat.add_0_r in IHp1_1. 
    rewrite Nat.add_0_r in IHp1_2.
    assert (L1: le (count_steps p1_1 1) (count_steps p1_1 2)); try apply optimizerCNF_step_dec_with_nat.
    assert (L2: le (count_steps p1_2 1) (count_steps p1_2 2)); try apply optimizerCNF_step_dec_with_nat.
    rewrite Ep1 in L1. rewrite Ep2 in L2.
    apply Arith_base.le_n_0_eq_stt in L1. symmetry in L1.
    apply Arith_base.le_n_0_eq_stt in L2. symmetry in L2.
    apply IHp1_1 in L1. 
    apply IHp1_2 in L2. 
    destruct  (count_Fand p1_1) eqn:EEp1, 
              (count_Fand p1_2) eqn:EEp2,
              (count_Fand p2_1) eqn:EEp1', 
              (count_Fand p2_2) eqn:EEp2'; try discriminate.
    reflexivity.

  - simpl in H. 
    simpl in IHp1_1. simpl in IHp1_2.
    clear IHp2_1. clear IHp2_2. simpl.
    destruct  (count_steps p1_1 2) eqn:Ep1, 
              (count_steps p1_2 2) eqn:Ep2,
              (count_steps p2_1 1) eqn:Ep1', 
              (count_steps p2_2 1) eqn:Ep2'; try discriminate.
    clear H. 
    simpl in IHp1_1. simpl in IHp1_2.
    rewrite Nat.add_0_r in IHp1_1. 
    rewrite Nat.add_0_r in IHp1_2.
    assert (L1: le (count_steps p1_1 1) (count_steps p1_1 2)); try apply optimizerCNF_step_dec_with_nat.
    assert (L2: le (count_steps p1_2 1) (count_steps p1_2 2)); try apply optimizerCNF_step_dec_with_nat.
    rewrite Ep1 in L1. rewrite Ep2 in L2.
    apply Arith_base.le_n_0_eq_stt in L1. symmetry in L1.
    apply Arith_base.le_n_0_eq_stt in L2. symmetry in L2.
    apply IHp1_1 in L1. 
    apply IHp1_2 in L2. 
    destruct  (count_Fand p1_1) eqn:EEp1, 
              (count_Fand p1_2) eqn:EEp2,
              (count_Fand p2_1) eqn:EEp1', 
              (count_Fand p2_2) eqn:EEp2'; try discriminate.
    reflexivity.

  - simpl in H. 
    simpl in IHp1_1. simpl in IHp1_2.
    clear IHp2_1. clear IHp2_2. simpl.
    destruct  (count_steps p1_1 1) eqn:Ep1, 
              (count_steps p1_2 1) eqn:Ep2,
              (count_steps p2_1 2) eqn:Ep1', 
              (count_steps p2_2 2) eqn:Ep2'; try discriminate.
    (* clear H.  *)
    simpl in IHp1_1. simpl in IHp1_2.
    simpl in H.
    apply IHp1_1 in H as Ha. apply IHp1_2 in H as Hb.
    (* rewrite Nat.add_0_r in IHp1_1.  *)
    (* rewrite Nat.add_0_r in IHp1_2. *)
    destruct  (count_Fand p1_1) eqn:EEp1, 
              (count_Fand p1_2) eqn:EEp2,
              (count_Fand p2_1) eqn:EEp1', 
              (count_Fand p2_2) eqn:EEp2'; try discriminate.
    reflexivity.
  
  - simpl in H. 
    simpl in IHp1_1. simpl in IHp1_2.
    clear IHp2_1. clear IHp2_2. simpl.
    destruct  (count_steps p1_1 1) eqn:Ep1, 
              (count_steps p1_2 1) eqn:Ep2,
              (count_steps p2_1 1) eqn:Ep1', 
              (count_steps p2_2 1) eqn:Ep2'; try discriminate.
    (* clear H.  *)
    simpl in IHp1_1. simpl in IHp1_2.
    simpl in H.
    apply IHp1_1 in H as Ha. apply IHp1_2 in H as Hb.
    (* rewrite Nat.add_0_r in IHp1_1.  *)
    (* rewrite Nat.add_0_r in IHp1_2. *)
    destruct  (count_Fand p1_1) eqn:EEp1, 
              (count_Fand p1_2) eqn:EEp2,
              (count_Fand p2_1) eqn:EEp1', 
              (count_Fand p2_2) eqn:EEp2'; try discriminate.
    reflexivity.
Qed.

Lemma optimizerCNF_or_eq0_always_eq0 : forall p1 p2 n,
  count_steps (p1 F\/ p2) 0 = 0 ->
  count_steps (p1 F\/ p2) n = 0.
Proof.
  intros p1 p2 n H.
  apply count_step_or_0_count_fand_0 in H.
  apply count_fand_0_count_step_0.
  assumption.
Qed.

Lemma count_Fand_0_optimizerCNF_remove: forall p,
  count_Fand p = 0 -> 
  optimizerCNF_step (p) = p.
Proof.
  induction p;
  intros H;
  try reflexivity.
  - discriminate.
  - simpl in H.
    destruct (count_Fand p1) eqn:Ep1, (count_Fand p2) eqn:Ep2; try discriminate. 
    simpl in H.
    simpl.
    apply IHp1 in H as Ha. rewrite Ha.
    apply IHp2 in H as Hb. rewrite Hb.
    destruct p1, p2; try discriminate; try reflexivity.
  - simpl in H.
    destruct (count_Fand p1) eqn:Ep1, (count_Fand p2) eqn:Ep2; try discriminate. 
    simpl in H.
    simpl.
    apply IHp1 in H as Ha. rewrite Ha.
    apply IHp2 in H as Hb. rewrite Hb.
    reflexivity.
  - simpl in H. apply IHp in H. simpl. rewrite H. reflexivity. 
Qed.

Lemma optimizerCNF_step_never_increases_step_count_from_0 : forall p,
  count_steps (p) 0 = 0 ->
  count_steps (optimizerCNF_step p) 0 = 0.
Proof.
  intros p.
  (* set (P:= optimizerNNF p). *)
  induction p;
  try reflexivity.
  - simpl. intros H. 
    destruct (count_steps p1 0), (count_steps p2 0); try discriminate.
    simpl in H. apply IHp1 in H as Ha. apply IHp2 in H as Hb.
    rewrite Ha. rewrite Hb. reflexivity.

  - intros H.
    apply count_step_or_0_count_fand_0 in H as H'.
    apply count_Fand_0_optimizerCNF_remove in H'.
    rewrite H'. apply H.
  
  - simpl. intros H. 
    destruct (count_steps p1 0), (count_steps p2 0); try discriminate.
    simpl in H. apply IHp1 in H as Ha. apply IHp2 in H as Hb.
    rewrite Ha. rewrite Hb. reflexivity.
  
  - simpl. intros H. apply IHp. assumption.
Qed.

(* 
Lemma optimizerCNF_step_never_increases_step_count_from_0 : forall p,
  count_steps (p) 0 = 0 ->
  count_steps (optimizerCNF_step (optimizerNNF p)) 0 = 0.
Proof.
  intros p.
  set (P:= optimizerNNF p).
  induction P;
  try reflexivity.
  - simpl. intros H. 
    destruct (count_steps P1 0), (count_steps P2 0); try discriminate.
    simpl in H. apply IHP1 in H as Ha. apply IHP2 in H as Hb.
    rewrite Ha. rewrite Hb. reflexivity.

  - intros H. simpl in H.
    (* apply Arith_base.le_n_0_eq_stt in H. *)
    assert (L1: count_steps P1 0 <= count_steps P1 1).
    {
      apply optimizerCNF_step_dec_with_nat.
    }
    assert (L2: count_steps P2 0 <= count_steps P2 1).
    {
      apply optimizerCNF_step_dec_with_nat.
    }
    destruct (count_steps P1 1) eqn:Ep1, (count_steps P2 1)eqn:Ep2; try discriminate.
    apply Arith_base.le_n_0_eq_stt in L1. apply Arith_base.le_n_0_eq_stt in L2.
    symmetry in L1. symmetry in L2.
    apply IHP1 in L1. apply IHP2 in L2.
    simpl. 
    destruct P1 eqn:Ep1'.
    + destruct P2 eqn:Ep2'; try reflexivity.
      * simpl. simpl in L2.
    unfold count_steps.
    destruct (optimizerCNF_step (P1 F\/ P2)) eqn:E; try reflexivity.
    + inversion E.
      destruct f1, f2; try reflexivity; try discriminate. 
    simpl.


    destruct P1 , P2; try reflexivity; try discriminate.
    + destruct (optimizerCNF_step (P2_1 F\/ P2_2)) eqn:E; try reflexivity.
      * simpl.
     simpl. 
    
    try auto.
    simpl.
    Search le.
    assert (L1: count_steps P1 0 <= count_steps P1 1).
    {
      apply optimizerCNF_step_dec_with_nat.
    } rewrite
      Search le. Print Arith_base.le_n_0_eq_stt.
    }
    destruct P1, P2; try reflexivity; try discriminate.
    +   
    destruct (count_steps P1 0), (count_steps P2 0); try discriminate.
    simpl in H. apply IHP1 in H as Ha. apply IHP2 in H as Hb.
    rewrite Ha. rewrite Hb. reflexivity.
Admitted.
*)

Lemma optimizerCNF_step_reduce_count_step: forall p,
  count_steps (optimizerNNF p) 0 = 0 
  \/ le (count_steps (optimizerCNF_step (optimizerNNF p)) 0) (count_steps (optimizerNNF p) 0).
Proof.
  intros p.
  induction (optimizerNNF p);
  try (left; reflexivity).
  - destruct IHf1 as [IH1a | IH1b].
    + simpl. rewrite IH1a. simpl. destruct IHf2 as [IH2a | IH2b].
      * left. simpl. assumption.
      * apply optimizerCNF_step_never_increases_step_count_from_0 in IH1a as IH1a'.
        rewrite IH1a'. right. simpl. assumption.
    + simpl. destruct IHf2 as [IH2a | IH2b].
      * apply optimizerCNF_step_never_increases_step_count_from_0 in IH2a as IH2a'.
        rewrite IH2a'. rewrite IH2a. right.
        repeat rewrite Nat.add_0_r. assumption.
      * right. 
        assert (L1: le 
                    (count_steps (optimizerCNF_step f1) 0 +
                    count_steps (optimizerCNF_step f2) 0)
                    (count_steps f1 0 +
                    count_steps (optimizerCNF_step f2) 0)).
        {
          apply add_le_mono_r_proj_l2r. assumption.
        }
        assert (L2: le 
                    (count_steps f1 0 +
                    count_steps (optimizerCNF_step f2) 0)
                    (count_steps f1 0 +
                    count_steps f2 0)).
        {
          apply add_le_mono_l_proj_l2r. assumption.
        }
        apply Nat.le_trans with (m:= (count_steps f1 0 + count_steps (optimizerCNF_step f2) 0));
        assumption.
  
  - right. destruct IHf1 as [IH1a | IH1b].
    + simpl. destruct IHf2 as [IH2a | IH2b].
      * admit.
      *  
      
      left. simpl. assumption.
      * apply optimizerCNF_step_never_increases_step_count_from_0 in IH1a as IH1a'.
        rewrite IH1a'. right. simpl. assumption.
    + simpl. destruct IHf2 as [IH2a | IH2b].
      * apply optimizerCNF_step_never_increases_step_count_from_0 in IH2a as IH2a'.
        rewrite IH2a'. rewrite IH2a. right.
        repeat rewrite Nat.add_0_r. assumption.
      * right. 
        assert (L1: le 
                    (count_steps (optimizerCNF_step f1) 0 +
                    count_steps (optimizerCNF_step f2) 0)
                    (count_steps f1 0 +
                    count_steps (optimizerCNF_step f2) 0)).
        {
          apply add_le_mono_r_proj_l2r. assumption.
        }
        assert (L2: le 
                    (count_steps f1 0 +
                    count_steps (optimizerCNF_step f2) 0)
                    (count_steps f1 0 +
                    count_steps f2 0)).
        {
          apply add_le_mono_l_proj_l2r. assumption.
        }
        apply Nat.le_trans with (m:= (count_steps f1 0 + count_steps (optimizerCNF_step f2) 0));
        assumption.

      
Admitted.
      Search add.
        simpl. 

      apply  rewrite IH1a. simpl. 
      rewrite IH1a. rewrite IH2a. reflexivity.
      * inversion IH2b.
        **    


Fixpoint Count_Fand (p : form) : nat :=
  match p with
  | Fand f1 f2 => 1 + ((Count_Fand f1) + (Count_Fand f2))
  | For f1 f2 => ((Count_Fand f1) + (Count_Fand f2))
  | Fimplies f1 f2 => ((Count_Fand f1) + (Count_Fand f2))
  | Fnot f => (Count_Fand f)
  (* SLUT *)
  | _ => 0
  end.

(* Fixpoint Count_Fand_For (p : form) : nat :=
  match p with
  | Fand f1 f2 => 1 + ((Count_Fand_For f1) + (Count_Fand_For f2))
  | For f1 f2 => 1 + ((Count_Fand_For f1) + (Count_Fand_For f2))
  | Fimplies f1 f2 => ((Count_Fand_For f1) + (Count_Fand_For f2))
  | Fnot f => (Count_Fand_For f)
  (* SLUT *)
  | _ => 0
  end. *)

Compute (OptimizerNNF ((Ftrue F\/ X) F-> (X F/\ Ftrue))).
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
  OptimizerCNF_run (OptimizerNNF p) (Count_Fand (OptimizerNNF p)).
  (* OptimizerCNF_run (OptimizerNNF p) (mult (Count_Fand (OptimizerNNF p)) (Count_Fand_For (OptimizerNNF p))). *)

Fixpoint illegal_boolean_formulas_are_presentCNF (p : form) : bool :=
  match p with
  (* SAME *)
  | Fvar x => false
  | Ftrue => false
  | Ffalse => false
  (* SENDES VIDERE *)
  | Fnot f => illegal_boolean_formulas_are_presentCNF f
  | Fimplies f1 f2 => orb (illegal_boolean_formulas_are_presentCNF f1) (illegal_boolean_formulas_are_presentCNF f2)
  (* DIREKTE OPTIMIZED *)
  | Fand f1 f2 => orb (illegal_boolean_formulas_are_presentCNF f1) (illegal_boolean_formulas_are_presentCNF f2)
  | For f1 f2 =>
        match f1, f2 with
        | Fand x y, _ => false
        | _, Fand y z => false
        | f1', f2' => orb (illegal_boolean_formulas_are_presentCNF f1') (illegal_boolean_formulas_are_presentCNF f2')
      end
  end.

Lemma pls11: forall p,
  illegal_boolean_formulas_are_presentCNF (OptimizerNNF_run p false)
  = illegal_boolean_formulas_are_presentCNF (OptimizerNNF_run p true).
Proof.
  intros p. induction p; try reflexivity.
  - simpl.  
 simpl;
  try (rewrite <- IHp1; rewrite <- IHp2; reflexivity).
  rewrite IHp. reflexivity.

Lemma pls10 : forall p1 p2: form,
  illegal_boolean_formulas_are_presentCNF (OptimizerNNF p1) = false
  -> illegal_boolean_formulas_are_presentCNF (OptimizerNNF p2) = false
  -> illegal_boolean_formulas_are_presentCNF (OptimizerNNF (p1 F/\ p2))= false.
Proof.
  intros.
  (* unfold illegal_boolean_formulas_are_presentCNF. ; repeat split. *)
  (* destruct p eqn: Ep; try reflexivity. *)
  unfold OptimizerNNF.
      set (P:= Optimizer (p1 F/\ p2)).
      induction P; 
      try reflexivity ;
      try (simpl ; rewrite IHP1 ; rewrite IHP2 ; reflexivity).
      * simpl. rewrite IHP2. rewrite IHP1. rewrite orb_false_r.
        destruct (OptimizerNNF_run P1 true), (OptimizerNNF_run P2 true); reflexivity.
         (* rewrite pls3. rewrite IHP1. *)
        (* reflexivity. *)
      * simpl. rewrite IHP2. rewrite orb_false_r. Search illegal_boolean_formulas_are_presentCNFrewrite pls3. assumption.
Admitted.

(* unfold OptimizerNNF_doesn't_contain_illegal_expression_on_form ; repeat split.
  - destruct p eqn: Ep; try reflexivity.
    + unfold OptimizerNNF.
      set (P:= Optimizer (f1 F/\ f2)).
      induction P; 
      try reflexivity ;
      try (simpl ; rewrite IHP1 ; rewrite IHP2 ; reflexivity).
      * simpl. rewrite IHP2. rewrite orb_false_r. rewrite pls3. rewrite IHP1.
        reflexivity.
      * simpl. rewrite pls3. assumption. *)

Definition OptimizedCNF_form_doesn't_contain_illegal_expression (p : form) : Prop :=
  illegal_boolean_formulas_are_presentCNF (OptimizerCNF p) = false.

Theorem OptimizerCNF_doesn't_contain_illegal_expressions : forall p,
    OptimizedCNF_form_doesn't_contain_illegal_expression p.
Proof.
  unfold OptimizedCNF_form_doesn't_contain_illegal_expression.
  unfold OptimizerCNF.
  intros p.
  (* set (P:= OptimizerNNF p). *)
  set (n:= Count_Fand (OptimizerNNF p)).
  induction n.
  - simpl. 
    induction (p);
    try reflexivity.
    + simpl. 
  - unfold OptimizerCNF.
    set (n:= Count_Fand (OptimizerNNF (f1 F/\ f2))).
    (* set (m:= Count_Fand_For (OptimizerNNF (f1 F/\ f2))). *)
    induction n.
    + simpl.   

  destruct p eqn: Ep; try reflexivity.
    + unfold OptimizerNNF.
      set (P:= Optimizer (f1 F/\ f2)).
      induction P; 
      try reflexivity ;
      try (simpl ; rewrite IHP1 ; rewrite IHP2 ; reflexivity).
      * simpl. rewrite IHP2. rewrite orb_false_r. rewrite pls3. rewrite IHP1.
        reflexivity.
      * simpl. rewrite pls3. assumption.
    + unfold OptimizerNNF.
      set (P:= Optimizer (f1 F\/ f2)).
      induction P; 
      try reflexivity ;
      try (simpl ; rewrite IHP1 ; rewrite IHP2 ; reflexivity).
      * simpl. rewrite IHP2. rewrite orb_false_r. rewrite pls3. rewrite IHP1.
        reflexivity.
      * simpl. rewrite pls3. assumption.
    + unfold OptimizerNNF.
      set (P:= Optimizer (f1 F-> f2)).
      induction P; 
      try reflexivity ;
      try (simpl ; rewrite IHP1 ; rewrite IHP2 ; reflexivity).
      * simpl. rewrite IHP2. rewrite orb_false_r. rewrite pls3. rewrite IHP1.
        reflexivity.
      * simpl. rewrite pls3. assumption.  
    + unfold OptimizerNNF.
      set (P:= Optimizer (F~ f)).
      induction P; 
      try reflexivity ;
      try (simpl ; rewrite IHP1 ; rewrite IHP2 ; reflexivity).
      * simpl. rewrite IHP2. rewrite orb_false_r. rewrite pls3. rewrite IHP1.
        reflexivity.
      * simpl. rewrite pls3. assumption.

  try assumption .
  try (
        simpl ;
        destruct (Optimizer f1), (Optimizer f2) ; 
        try reflexivity ; 
        try assumption ;
        try (simpl; rewrite orb_false_r ; assumption) ;
        try (simpl ; apply orb_false_intro ; assumption)
      ). 
Qed. 

Lemma pls2 : forall p n,
  (OptimizerCNF_run (OptimizerCNF_step (p)) n)
  = (OptimizerCNF_step (OptimizerCNF_run (p) n)).
Proof.
  intros. generalize dependent p. induction n.
  - reflexivity.
  - intros p. simpl. rewrite IHn with (p:= (OptimizerCNF_step p)). reflexivity. 
Qed. 

Definition OptimizerCNF_correct : forall (p:form) (v : valuation), 
    interp v p = interp v (OptimizerCNF p).
Proof.
  intros p v.
  unfold OptimizerCNF.
  set (n := (Count_Fand (OptimizerNNF p) * Count_Fand_For (OptimizerNNF p))).
  induction n.
  - simpl. apply OptimizerNNF_correct.
  - simpl. rewrite pls2 with (p:= (OptimizerNNF p)). rewrite <-OptimizerCNF_step_preserves_interp. assumption. 
Qed.

Definition solverCNF (p : form ) : bool :=
  match find_valuation (OptimizerCNF p) with
  | Some _ => true
  | None => false
  end.

Lemma solverCNF_sound : forall p, solverCNF p = true -> satisfiable p.
Proof.
  intros p H. 
  unfold solverCNF in H.
  destruct (find_valuation (OptimizerCNF p)) eqn:EH.
  - unfold find_valuation in EH. 
    unfold filter in EH. 
    assert (L: forall x, interp x p = interp x (OptimizerCNF p)).
    {
      apply OptimizerCNF_correct.
    }
    set (tt := generate_truthtable (list_variables (OptimizerCNF p)) empty_valuation) in EH.
    induction tt as [| v' l' IHl'].
    + discriminate.
    + destruct (interp v' (OptimizerCNF p)) eqn: Ev'.
      * rewrite <- OptimizerCNF_correct in Ev'. unfold satisfiable. exists v'. assumption.
      * apply IHl'. assumption.
  - discriminate.
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
(* Definition min_valuation (V : valuation) (p : form) : valuation :=
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
Admitted. *)
