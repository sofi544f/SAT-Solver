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

(* HELPER FUNCTIONS -- EXTRA *)
Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

(*  *)

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
(* MANGLER - TODO - Finish writing prop in compact notation *)
Definition prop1 : form := 
  Fand (For (Fvar (Id 1)) (Fnot (Fvar (Id 2)))) (For (Fnot (Fvar (Id 1))) (Fvar (Id 2))).

Definition prop1' (x y : id) : form := 
  (F( x ) F\/ (F~ F( y ))) F/\ ((F~ F( x )) F\/ F(y)).



Definition prop2 : form := 
  Fimplies (Fnot (Fvar (Id 2))) (For (Fvar (Id 1)) (Fvar (Id 2))).

(* Compute (prop2 (Id 1) (Id 2)). *)

Definition prop3 : form := 
  Fand (Fvar (Id 1)) (Fand (Fnot (Fvar (Id 1))) (Ftrue)).

Compute (prop3).

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

(* MANGLER - TODO - OBS two already false, så unødvendigt *)
Definition OneTrue_TwoFalse_valuation : valuation := 
  override (override (empty_valuation) (Id 2) false) (Id 1) true.

Compute (interp OneTrue_TwoFalse_valuation (prop1)).
Compute (interp OneTrue_TwoFalse_valuation (prop2)).
Compute (interp OneTrue_TwoFalse_valuation (prop3)).

(* E4 *)
Definition satisfiable (p : form ) : Prop :=
  exists V : valuation , interp V p = true.

Definition OneTrue_TwoTrue_valuation : valuation := 
  override (override (empty_valuation) (Id 2) true) (Id 1) true.

Lemma test1 : satisfiable prop1.
Proof.
  unfold satisfiable.
  exists OneTrue_TwoTrue_valuation.
  reflexivity.
Qed.

Lemma test2 : satisfiable prop2.
Proof.
  unfold satisfiable.
  exists OneTrue_TwoTrue_valuation.
  reflexivity.
Qed.

(* TODO - E5 *)
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

Fixpoint list_variables (p: form) (vl : list id) : list id :=
  match p with
  | Fvar x => vl +++ [x]
  | Fand f1 f2 => (vl +++ (list_variables f1 vl)) +++ (list_variables f2 vl)
  | For f1 f2 => (vl +++ (list_variables f1 vl)) +++ (list_variables f2 vl)
  | Fimplies f1 f2 => (vl +++ (list_variables f1 vl)) +++ (list_variables f2 vl)
  | Fnot f => vl +++ (list_variables f vl)
  | Ftrue => vl
  | Ffalse => vl
  end.

Lemma prop1_correct_var : list_variables prop1 [] = [(Id 1); (Id 2)].
Proof.
  reflexivity.
Qed.
Lemma prop2_correct_var : list_variables prop2 [] = [(Id 2); (Id 1)].
Proof.
  reflexivity.
Qed.
Lemma prop3_correct_var : list_variables prop3 [] = [(Id 1)].
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

Lemma generate_truthtable1 : 
  [(override empty_valuation (Id 1) true); (override empty_valuation (Id 1) false)]
  = generate_truthtable [Id 1] empty_valuation.
Proof.
  simpl. reflexivity.
Qed.

Lemma generate_truthtable2 : 
  [(override (override empty_valuation (Id 2) true) (Id 1) true);
    (override (override empty_valuation (Id 2) false) (Id 1) true) ;
    (override (override empty_valuation (Id 2) true) (Id 1) false) ;
    (override (override empty_valuation (Id 2) false) (Id 1) false)]
  = generate_truthtable [Id 1; Id 2] empty_valuation.
Proof.
  simpl. reflexivity.
Qed.

(* Fixpoint check_truthtable (p: form) (l : list valuation) : option valuation :=
  match l with
  | nil => None
  | h :: t =>
    match interp h p with
    | false => check_truthtable p t
    | true => Some h
    end
  end. *)

Definition find_valuation (p : form ) : option valuation :=
  match filter (fun (V: valuation) => interp V p) (generate_truthtable (list_variables p []) empty_valuation) with
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
(* MISSING *)

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

(* TODO - E8 *)
Lemma solver_sound : forall p, solver p = true -> satisfiable p.
Proof.
  intros p H. 
  unfold solver in H.
  destruct (find_valuation p) eqn:EH.
  - unfold satisfiable. unfold find_valuation in EH. 
  destruct H.
  inversion H.

(* EXTRA *)