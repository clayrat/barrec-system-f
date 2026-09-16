(** * Proof-free executable unification

    The legacy W-in-Coq unifier returns substitutions bundled with large
    dependent proofs.  This worklist implementation keeps only computational
    data in its result.  Structural fuel is split in two: an equation scan is
    bounded by the worklist size, while every substitution consumes one of the
    finitely many variables from the input. *)

From Stdlib Require Import List.
Import ListNotations.

From SystemF.HM Require Import UnifySpec.
From SystemF.HM.W Require Import Occurs.

Inductive unify_result : Set :=
| unified : substitution -> unify_result
| rejected : unify_result.

Definition equation := (ty * ty)%type.

Fixpoint exec_ty_size (t : ty) : nat :=
  match t with
  | arrow l r => 1 + exec_ty_size l + exec_ty_size r
  | _ => 1
  end.

Definition equation_size (e : equation) : nat :=
  exec_ty_size (fst e) + exec_ty_size (snd e).

Fixpoint equations_size (equations : list equation) : nat :=
  match equations with
  | [] => 0
  | equation :: rest => 1 + equation_size equation + equations_size rest
  end.

Definition apply_subst_equation
    (s : substitution) (e : equation) : equation :=
  (apply_subst s (fst e), apply_subst s (snd e)).

Inductive scan_result : Set :=
| equations_solved
| equations_failed
| equation_binding : id -> ty -> list equation -> scan_result
| scan_fuel_exhausted.

Inductive solve_result : Set :=
| solution : substitution -> solve_result
| unsatisfiable
| solver_fuel_exhausted.

(** Scan and decompose equations until a variable can be eliminated.  Arrow
    decomposition and deletion of equal equations strictly decrease
    [equations_size], so that amount of structural fuel is sufficient. *)
Fixpoint scan_equations
    (fuel : nat) (equations : list equation) : scan_result :=
  match equations with
  | [] => equations_solved
  | (t1, t2) :: rest =>
      match fuel with
      | 0 => scan_fuel_exhausted
      | S fuel' =>
          if eq_ty_dec t1 t2 then
            scan_equations fuel' rest
          else
            match t1, t2 with
            | var v, t =>
                if occurs_dec v t then equations_failed
                else equation_binding v t rest
            | t, var v =>
                if occurs_dec v t then equations_failed
                else equation_binding v t rest
            | con _, con _ => equations_failed
            | arrow l r, arrow l' r' =>
                scan_equations fuel' ((l, l') :: (r, r') :: rest)
            | _, _ => equations_failed
            end
      end
  end.

(** Each successful binding eliminates that variable from every remaining
    equation.  Consequently no input variable is bound more than once. *)
Fixpoint solve_equations
    (variable_fuel : nat)
    (variables : list id)
    (equations : list equation) : solve_result :=
  match scan_equations (equations_size equations) equations with
  | equations_solved => solution []
  | equations_failed => unsatisfiable
  | scan_fuel_exhausted => solver_fuel_exhausted
  | equation_binding v t rest =>
      match variable_fuel with
      | 0 => solver_fuel_exhausted
      | S variable_fuel' =>
          if in_dec eq_id_dec v variables then
            match solve_equations variable_fuel'
              (remove eq_id_dec v variables)
              (map (apply_subst_equation [(v, t)]) rest) with
            | solution s => solution (comp_subst [(v, t)] s)
            | unsatisfiable => unsatisfiable
            | solver_fuel_exhausted => solver_fuel_exhausted
            end
          else solver_fuel_exhausted
      end
  end.

Definition initial_variables (t1 t2 : ty) : list id :=
  nodup eq_id_dec (ids_ty t1 ++ ids_ty t2).

Definition unify_exec_result (t1 t2 : ty) : solve_result :=
  let variables := initial_variables t1 t2 in
  solve_equations (length variables) variables [(t1, t2)].

Definition unify_exec (t1 t2 : ty) : unify_result :=
  match unify_exec_result t1 t2 with
  | solution s => unified s
  | unsatisfiable => rejected
  | solver_fuel_exhausted => rejected
  end.
