(* IMPORT *)
From Stdlib Require Export Bool.
From Stdlib Require Export List.
Export ListNotations.
From Stdlib Require Export Arith.
From Stdlib Require Export Nat.
From Stdlib Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)

(*  *)
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

Definition prop3 (x : id) : form := 
  Fand (Fvar x) (Fand (Fnot (Fvar x)) (Ftrue)).

Compute (prop3 (Id 1)).

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
Compute (interp OneTrue_TwoFalse_valuation (prop3 (Id 1))).

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
Definition find_valuation (p : form ) : option valuation
(* fill out *).

(* TODO - E6 *)
Definition solver (p : form ) : bool :=
  match find_valuation p with
  | Some _ => true
  | None => false
  end.

(* MISSING: Explain the difference between satisfiable and solver. *)

(* TODO - E7 *)
(* Write 2 positive and 2 negative tests of the solver and prove these
tests using the reflexivity tactic. *)
(* MISSING *)

(* TODO - E8 *)
Lemma solver_sound : forall p, solver p = true -> satisfiable p.

(* EXTRA *)