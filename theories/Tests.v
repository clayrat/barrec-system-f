(** * Fast regression tests

    Meaningful computations are frozen as kernel-checked equalities as the
    corresponding algorithms become available.  Church checking and
    relational-formula regressions remain to be added with those
    implementations.

    Use Examples.v as the common source for Rocq and OCaml fixtures.
    BBC experiments belong in bench/ and do not run during this build. *)

From Stdlib Require Import List.
Import ListNotations.

From SystemF Require Import Examples.
From SystemF.F Require Import Syntax Check OperationalSemantics.
From SystemF.FreeTheorems Require Import Generate.
From SystemF.HM Require Import Infer Unify.
Require Import SystemF.HM.Examples.

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

(** ** Hindley--Milner unification *)

(** [unify_exec] is the proof-free computational core.  These equalities are
    reduced by the kernel, including recursive arrow decomposition. *)
Example unify_exec_same_arrow :
  unify_exec
    (arrow (var 0) (var 1))
    (arrow (var 0) (var 1)) = unified nil.
Proof. reflexivity. Qed.

Example unify_exec_arrow_binding :
  unify_exec
    (arrow (var 0) (var 1))
    (arrow (var 0) (var 2)) = unified [(1, var 2)].
Proof. reflexivity. Qed.

Example unify_exec_two_bindings :
  unify_exec
    (arrow (var 0) (arrow (var 1) (var 0)))
    (arrow (con 7) (arrow (con 8) (con 7))) =
  unified [(0, con 7); (1, con 8)].
Proof. reflexivity. Qed.

Example unify_exec_two_bindings_is_principal :
  is_principal_unifier
    (arrow (var 0) (arrow (var 1) (var 0)))
    (arrow (con 7) (arrow (con 8) (con 7)))
    [(0, con 7); (1, con 8)].
Proof.
  apply unify_exec_success_principal.
  reflexivity.
Qed.

Example unify_exec_two_bindings_preserve_freshness :
  preserves_freshness
    (arrow (var 0) (arrow (var 1) (var 0)))
    (arrow (con 7) (arrow (con 8) (con 7)))
    [(0, con 7); (1, con 8)].
Proof.
  apply unify_exec_preserves_freshness.
  reflexivity.
Qed.

Example unify_exec_rejects_occurs_cycle :
  unify_exec (var 0) (arrow (var 0) (var 1)) = rejected.
Proof. reflexivity. Qed.

Example unify_exec_occurs_cycle_has_no_unifier : forall s,
  apply_subst s (var 0) <>
  apply_subst s (arrow (var 0) (var 1)).
Proof.
  apply unify_exec_rejected_no_unifier.
  reflexivity.
Qed.

(** The old dependent implementation remains the checked reference. *)

(** Equality must be tested before the occurs check: a variable unifies with
    itself using the identity substitution. *)
Example unify_same_variable :
  run_unify (var 0) (var 0) = unified nil.
Proof. reflexivity. Qed.

Example unify_same_variable_is_principal :
  is_principal_unifier (var 0) (var 0) nil.
Proof.
  apply run_unify_principal.
  reflexivity.
Qed.

Example unify_same_variable_preserves_freshness :
  preserves_freshness (var 0) (var 0) nil.
Proof.
  apply run_unify_preserves_freshness.
  reflexivity.
Qed.

Example unify_rejects_occurs_cycle :
  run_unify (var 0) (arrow (var 0) (var 1)) = rejected.
Proof. reflexivity. Qed.

Example occurs_cycle_has_no_unifier : forall s,
  apply_subst s (var 0) <>
  apply_subst s (arrow (var 0) (var 1)).
Proof.
  apply run_unify_rejected_no_unifier.
  reflexivity.
Qed.

Example unify_rejects_distinct_constants :
  run_unify (con 0) (con 1) = rejected.
Proof. reflexivity. Qed.

Example distinct_constants_have_no_unifier : forall s,
  apply_subst s (con 0) <> apply_subst s (con 1).
Proof.
  apply run_unify_rejected_no_unifier.
  reflexivity.
Qed.

Example proof_free_and_checked_rejection_correspond : forall t1 t2,
  unify_exec t1 t2 = rejected <-> run_unify t1 t2 = rejected.
Proof.
  apply unify_exec_rejected_iff_run_unify_rejected.
Qed.

Example proof_free_and_checked_success_correspond :
  is_unifier (var 0) (var 0) nil /\
  is_unifier (var 0) (var 0) nil /\
  factors_through nil nil /\ factors_through nil nil.
Proof.
  eapply unify_exec_checked_correspondence;
    reflexivity.
Qed.

(** ** Proof-free Algorithm W *)

Example w_exec_repeated_application :
  runW_exec repeated_application [] =
  inferred
    (arrow
      (arrow (var 1) (var 3))
      (arrow (var 1) (var 3)))
    [(0, arrow (var 1) (var 3)); (2, var 3)].
Proof. reflexivity. Qed.

Example w_exec_repeated_application_succeeds :
  infer_exec_succeeds repeated_application = true.
Proof. reflexivity. Qed.

Example w_exec_rejects_missing_variable :
  runW_exec (var_t 42) [] = inference_rejected.
Proof. reflexivity. Qed.

(** The second syntactic rejection in the variable branch is unreachable:
    the canonical instantiation always has enough entries for the scheme. *)
Example w_exec_scheme_instantiation_cannot_fail : forall st sigma,
  exists tau,
    SubstSchm.apply_inst_subst
      (SubstSchm.compute_inst_subst st (Schemes.max_gen_vars sigma)) sigma =
    Some tau.
Proof.
  apply computed_instantiation_succeeds.
Qed.

Example w_exec_rejects_constant_application :
  runW_exec (app_t (const_t 0) (const_t 1)) [] =
  inference_rejected.
Proof. reflexivity. Qed.

(** Rejections are not merely executable outcomes: the kernel checks that
    each one excludes every declarative Hindley--Milner type. *)
Example w_exec_missing_variable_rejection_is_sound : forall tau,
  ~ has_type [] (var_t 42) tau.
Proof.
  apply runW_exec_rejected_no_typing.
  reflexivity.
Qed.

Example w_exec_unification_rejection_is_sound : forall tau,
  ~ has_type [] (app_t (const_t 0) (const_t 1)) tau.
Proof.
  apply runW_exec_rejected_no_typing.
  reflexivity.
Qed.

(** Failure propagated from the function position of an application. *)
Example w_exec_rejects_failed_function :
  runW_exec (app_t (var_t 0) (const_t 1)) [] =
  inference_rejected.
Proof. reflexivity. Qed.

Example w_exec_failed_function_is_untypable : forall tau,
  ~ has_type [] (app_t (var_t 0) (const_t 1)) tau.
Proof.
  apply runW_exec_rejected_no_typing.
  reflexivity.
Qed.

(** Failure propagated from the argument after a successful function. *)
Example w_exec_rejects_failed_argument :
  runW_exec (app_t (lam_t 0 (var_t 0)) (var_t 1)) [] =
  inference_rejected.
Proof. reflexivity. Qed.

Example w_exec_failed_argument_is_untypable : forall tau,
  ~ has_type [] (app_t (lam_t 0 (var_t 0)) (var_t 1)) tau.
Proof.
  apply runW_exec_rejected_no_typing.
  reflexivity.
Qed.

(** Failure propagated through a lambda body. *)
Example w_exec_rejects_failed_lambda_body :
  runW_exec (lam_t 0 (var_t 1)) [] = inference_rejected.
Proof. reflexivity. Qed.

Example w_exec_failed_lambda_body_is_untypable : forall tau,
  ~ has_type [] (lam_t 0 (var_t 1)) tau.
Proof.
  apply runW_exec_rejected_no_typing.
  reflexivity.
Qed.

(** Both recursive failure sites of [let] are covered separately. *)
Example w_exec_rejects_failed_let_bound :
  runW_exec (let_t 0 (var_t 1) (var_t 0)) [] =
  inference_rejected.
Proof. reflexivity. Qed.

Example w_exec_failed_let_bound_is_untypable : forall tau,
  ~ has_type [] (let_t 0 (var_t 1) (var_t 0)) tau.
Proof.
  apply runW_exec_rejected_no_typing.
  reflexivity.
Qed.

Example w_exec_rejects_failed_let_body :
  runW_exec (let_t 0 (const_t 0) (var_t 1)) [] =
  inference_rejected.
Proof. reflexivity. Qed.

Example w_exec_failed_let_body_is_untypable : forall tau,
  ~ has_type [] (let_t 0 (const_t 0) (var_t 1)) tau.
Proof.
  apply runW_exec_rejected_no_typing.
  reflexivity.
Qed.

(** [runW] retains the dependent proof contract; [runW_exec] freezes the same
    computational branch structure in a form reducible by the kernel. *)

(** ** Successful contract of the checked [runW] *)

Example runW_constant_success :
  runW (const_t 7) [] = inl (con 7, []).
Proof. reflexivity. Qed.

(** Applying the public theorem checks the whole successful postcondition,
    including freshness, declarative typing, and completeness. *)
Example runW_constant_satisfies_success_contract :
  runW_success_spec (const_t 7) [] (con 7) [].
Proof.
  apply runW_success_contract.
  reflexivity.
Qed.

(** ** Checked/executable W correspondence *)

Example runW_exec_constant_matches_checked :
  observe_checked_result (runW (const_t 7) []) =
  runW_exec (const_t 7) [].
Proof.
  apply runW_exec_checked_correspondence.
Qed.

Example runW_exec_recursive_arrow_matches_checked :
  observe_checked_result (runW repeated_application []) =
  runW_exec repeated_application [].
Proof.
  apply runW_exec_checked_correspondence.
Qed.

Example runW_missing_variable_has_checked_failure :
  exists failure, runW (var_t 42) [] = inr failure.
Proof.
  apply (proj1
    (runW_exec_rejected_iff_checked_rejected (var_t 42) [])).
  reflexivity.
Qed.

Example runW_missing_variable_checked_failure_is_sound : forall failure,
  runW (var_t 42) [] = inr failure ->
  forall tau, ~ has_type [] (var_t 42) tau.
Proof.
  apply runW_checked_rejected_no_typing.
Qed.
