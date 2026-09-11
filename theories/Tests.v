(** * Fast regression tests

    Meaningful computations are frozen as kernel-checked equalities as the
    corresponding algorithms become available.  Unification, type-variable
    scope, Church checking, and relational-formula regressions remain to be
    added with those implementations.

    Use Examples.v as the common source for Rocq and OCaml fixtures.
    BBC experiments belong in bench/ and do not run during this build. *)

From SystemF Require Import Examples.
From SystemF.F Require Import Syntax Check OperationalSemantics.
From SystemF.FreeTheorems Require Import Generate.

(** ** Capture-avoiding substitution *)

(** The free variable supplied as the argument remains free underneath the
    abstraction instead of being captured by it. *)
Example term_subst1_avoids_capture :
  term_subst1 0 (Abs (Var 1)) (Var 0) = Abs (Var 1).
Proof. reflexivity. Qed.

(** The abstraction's own bound variable is not replaced. *)
Example term_subst1_preserves_inner_binder :
  term_subst1 0 (Abs (Var 0)) (Var 42) = Abs (Var 0).
Proof. reflexivity. Qed.

(** Variables above the removed index are shifted down. *)
Example term_subst1_closes_gap :
  term_subst1 0 (Var 1) (Var 42) = Var 0.
Proof. reflexivity. Qed.

(** ** Weak-head reduction *)

Example term1_is_whnf :
  wh_step (fterm_to_term term1) = None.
Proof. reflexivity. Qed.

Example term3_takes_one_step :
  wh_step (fterm_to_term term3) = Some (fterm_to_term term1).
Proof. reflexivity. Qed.

Example term4_takes_one_step :
  wh_step (fterm_to_term term4) = Some (fterm_to_term term1).
Proof. reflexivity. Qed.

(** A redex is found underneath applications on the left spine. *)
Example wh_step_follows_left_spine :
  wh_step
    (App (App (Abs (Var 0)) (Abs (Var 0))) (Var 0)) =
  Some (App (Abs (Var 0)) (Var 0)).
Proof. reflexivity. Qed.

(** Weak-head reduction does not inspect an argument of a stuck head. *)
Example wh_step_does_not_reduce_arguments :
  wh_step
    (App (Var 0) (App (Abs (Var 0)) (Var 1))) =
  None.
Proof. reflexivity. Qed.

(** Weak-head reduction does not proceed under an abstraction. *)
Example wh_step_does_not_reduce_under_abs :
  wh_step
    (Abs (App (Abs (Var 0)) (Var 1))) =
  None.
Proof. reflexivity. Qed.

(** ** Fuel and exact-step oracle *)

Example term4_zero_fuel_is_unchanged :
  run_fuel 0 (fterm_to_term term4) = fterm_to_term term4.
Proof. reflexivity. Qed.

Example term4_one_fuel_reaches_whnf :
  run_fuel 1 (fterm_to_term term4) = fterm_to_term term1.
Proof. reflexivity. Qed.

Example term4_excess_fuel_is_harmless :
  run_fuel 5 (fterm_to_term term4) = fterm_to_term term1.
Proof. reflexivity. Qed.

Example term3_cap_zero_is_insufficient :
  eval_cap 0 (fterm_to_term term3) = None.
Proof. reflexivity. Qed.

Example term3_exact_step_count :
  eval_cap 1 (fterm_to_term term3) =
  Some (1, fterm_to_term term1).
Proof. reflexivity. Qed.

Example term4_exact_step_count :
  eval_cap 1 (fterm_to_term term4) =
  Some (1, fterm_to_term term1).
Proof. reflexivity. Qed.
