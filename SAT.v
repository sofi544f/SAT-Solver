(* IMPORT *)


(*  *)

(* TODO - E1 *)
Inductive form :=
| var : id -> form
(* fill out *) .

(* TODO - E2 two coq definitions *)

(* TODO - E3 *)
Definition valuation := id -> bool .
Definition empty_valuation : valuation := fun x => false .
Definition override (V : valuation ) (x : id) (b : bool ) : valuation :=
  fun y => if beq_id x y then b else V y.

Fixpoint interp (V : valuation ) (p : form ) : bool :=
(* fill out *)admit.

(* TODO - E4 *)
Definition satisfiable (p : form ) : Prop :=
  exists V : valuation , interp V p = true .

Lemma test1 : satisfiable (* formula 1 *) .
Lemma test2 : satisfiable (* formula 2 *) .

(* TODO - E5 *)
Definition find_valuation (p : form ) : option valuation :=
(* fill out *)admit.

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