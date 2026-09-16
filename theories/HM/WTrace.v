(** * Computational trace for Algorithm W

    [W_trace_exec] follows the branches of [W_exec] and records the six
    operations used in the lecture presentation: fresh variables,
    instantiation, unification, generalization, substitution composition, and
    failure.  The trace lives in [Set], so it survives extraction.

    [W_trace_exec_erases] and [runWTrace_result] state the key instrumentation
    contract: discarding the events gives exactly the original proof-free W
    result, including rejection. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.

From SystemF.HM Require Import Unify WExec.
From SystemF.HM.W Require Import
  Context Gen Schemes SubstSchm Typing.

Inductive WTraceFailure : Set :=
| trace_missing_variable : id -> WTraceFailure
| trace_instantiation_failure : id -> schm -> WTraceFailure
| trace_unification_failure : ty -> ty -> WTraceFailure.

Inductive WTraceEvent : Set :=
| trace_fresh : id -> WTraceEvent
| trace_instantiate : id -> id -> schm -> option ty -> WTraceEvent
| trace_unify : ty -> ty -> unify_result -> WTraceEvent
| trace_generalize : id -> ty -> schm -> WTraceEvent
| trace_compose : substitution -> substitution -> substitution -> WTraceEvent
| trace_fail : WTraceFailure -> WTraceEvent.

(** The first identifier in [trace_instantiate] is the source variable and
    the second is the first fresh type-variable identifier used by the
    instantiation. *)

Inductive w_trace_state_result : Set :=
| traced_state_success :
    ty -> substitution -> id -> list WTraceEvent -> w_trace_state_result
| traced_state_rejected : list WTraceEvent -> w_trace_state_result.

Definition trace_state_result
    (result : w_trace_state_result) : w_state_result :=
  match result with
  | traced_state_success tau substitution state _ =>
      w_state_success tau substitution state
  | traced_state_rejected _ => w_state_rejected
  end.

Definition trace_state_events
    (result : w_trace_state_result) : list WTraceEvent :=
  match result with
  | traced_state_success _ _ _ events => events
  | traced_state_rejected events => events
  end.

(** This definition intentionally mirrors [W_exec].  Intermediate results
    are shared with the event payloads; the uninstrumented algorithm is not
    called as a second pass. *)
Fixpoint W_trace_exec
    (expression : hmterm) (environment : hmctx) (state : id)
    : w_trace_state_result :=
  match expression with
  | const_t constant =>
      traced_state_success (con constant) [] state []

  | var_t variable =>
      match in_ctx variable environment with
      | None =>
          traced_state_rejected
            [trace_fail (trace_missing_variable variable)]
      | Some sigma =>
          let count := max_gen_vars sigma in
          let instance :=
            apply_inst_subst (compute_inst_subst state count) sigma in
          let event := trace_instantiate variable state sigma instance in
          match instance with
          | None =>
              traced_state_rejected
                [event; trace_fail (trace_instantiation_failure variable sigma)]
          | Some tau =>
              traced_state_success tau [] (state + count) [event]
          end
      end

  | lam_t variable body =>
      let alpha := state in
      match W_trace_exec body
        ((variable, ty_to_schm (var alpha)) :: environment) (S state) with
      | traced_state_rejected events =>
          traced_state_rejected (trace_fresh alpha :: events)
      | traced_state_success tau substitution state' events =>
          traced_state_success
            (arrow (apply_subst substitution (var alpha)) tau)
            substitution state' (trace_fresh alpha :: events)
      end

  | app_t function argument =>
      match W_trace_exec function environment state with
      | traced_state_rejected function_events =>
          traced_state_rejected function_events
      | traced_state_success tau1 s1 state1 function_events =>
          match W_trace_exec argument
              (apply_subst_ctx s1 environment) state1 with
          | traced_state_rejected argument_events =>
              traced_state_rejected (function_events ++ argument_events)
          | traced_state_success tau2 s2 state2 argument_events =>
              let alpha := state2 in
              let left := apply_subst s2 tau1 in
              let right := arrow tau2 (var alpha) in
              let unification := unify_exec left right in
              let prefix :=
                function_events ++ argument_events ++
                  [trace_fresh alpha;
                   trace_unify left right unification] in
              match unification with
              | rejected =>
                  traced_state_rejected
                    (prefix ++
                      [trace_fail (trace_unification_failure left right)])
              | unified unifier =>
                  let argument_then_unifier := comp_subst s2 unifier in
                  let final_substitution :=
                    comp_subst s1 argument_then_unifier in
                  traced_state_success
                    (apply_subst unifier (var alpha))
                    final_substitution
                    (S state2)
                    (prefix ++
                      [trace_compose s2 unifier argument_then_unifier;
                       trace_compose
                         s1 argument_then_unifier final_substitution])
              end
          end
      end

  | let_t variable bound body =>
      match W_trace_exec bound environment state with
      | traced_state_rejected bound_events =>
          traced_state_rejected bound_events
      | traced_state_success tau1 s1 state1 bound_events =>
          let environment' := apply_subst_ctx s1 environment in
          let sigma := gen_ty tau1 environment' in
          let generalization := trace_generalize variable tau1 sigma in
          match W_trace_exec body
              ((variable, sigma) :: environment') state1 with
          | traced_state_rejected body_events =>
              traced_state_rejected
                (bound_events ++ generalization :: body_events)
          | traced_state_success tau2 s2 state2 body_events =>
              let final_substitution := comp_subst s1 s2 in
              traced_state_success tau2 final_substitution state2
                (bound_events ++ generalization :: body_events ++
                  [trace_compose s1 s2 final_substitution])
          end
      end
  end.

Record WTraceResult : Set := {
  trace_result : w_result;
  trace_events : list WTraceEvent
}.

Definition runWTrace (expression : hmterm) (environment : hmctx) : WTraceResult :=
  match W_trace_exec expression environment (initial_state_exec environment) with
  | traced_state_success tau substitution _ events =>
      {| trace_result := inferred tau substitution;
         trace_events := events |}
  | traced_state_rejected events =>
      {| trace_result := inference_rejected;
         trace_events := events |}
  end.

(** Small executable observations used by regressions and presentation code. *)
Fixpoint trace_instantiation_count
    (variable : id) (events : list WTraceEvent) : nat :=
  match events with
  | [] => 0
  | trace_instantiate found _ _ _ :: events' =>
      (if Nat.eqb variable found then 1 else 0) +
        trace_instantiation_count variable events'
  | _ :: events' => trace_instantiation_count variable events'
  end.

Fixpoint trace_generalization_count
    (variable : id) (events : list WTraceEvent) : nat :=
  match events with
  | [] => 0
  | trace_generalize found _ _ :: events' =>
      (if Nat.eqb variable found then 1 else 0) +
        trace_generalization_count variable events'
  | _ :: events' => trace_generalization_count variable events'
  end.

Fixpoint trace_failure_count (events : list WTraceEvent) : nat :=
  match events with
  | [] => 0
  | trace_fail _ :: events' => S (trace_failure_count events')
  | _ :: events' => trace_failure_count events'
  end.

(** ** Erasure of instrumentation *)

Theorem W_trace_exec_erases : forall expression environment state,
  trace_state_result (W_trace_exec expression environment state) =
  W_exec expression environment state.
Proof.
  induction expression as
      [variable
      | function IHfunction argument IHargument
      | variable bound IHbound body IHbody
      | variable body IHbody
      | constant];
    intros environment state;
    cbn [W_trace_exec W_exec].
  - destruct (in_ctx variable environment) as [sigma |] eqn:Hlookup;
      cbn [trace_state_result].
    + destruct (apply_inst_subst
        (compute_inst_subst state (max_gen_vars sigma)) sigma);
        reflexivity.
    + reflexivity.
  - destruct (W_trace_exec function environment state)
      as [tau1 s1 state1 function_events | function_events]
      eqn:Hfunction.
    + specialize (IHfunction environment state).
      rewrite Hfunction in IHfunction.
      cbn [trace_state_result] in IHfunction.
      rewrite <- IHfunction.
      destruct (W_trace_exec argument (apply_subst_ctx s1 environment) state1)
        as [tau2 s2 state2 argument_events | argument_events]
        eqn:Hargument.
      * specialize (IHargument (apply_subst_ctx s1 environment) state1).
        rewrite Hargument in IHargument.
        cbn [trace_state_result] in IHargument.
        rewrite <- IHargument.
        destruct (unify_exec (apply_subst s2 tau1)
          (arrow tau2 (var state2))); reflexivity.
      * specialize (IHargument (apply_subst_ctx s1 environment) state1).
        rewrite Hargument in IHargument.
        cbn [trace_state_result] in IHargument.
        now rewrite <- IHargument.
    + specialize (IHfunction environment state).
      rewrite Hfunction in IHfunction.
      cbn [trace_state_result] in IHfunction.
      now rewrite <- IHfunction.
  - destruct (W_trace_exec bound environment state)
      as [tau1 s1 state1 bound_events | bound_events] eqn:Hbound.
    + specialize (IHbound environment state).
      rewrite Hbound in IHbound.
      cbn [trace_state_result] in IHbound.
      rewrite <- IHbound.
      destruct (W_trace_exec body
        ((variable, gen_ty tau1 (apply_subst_ctx s1 environment)) ::
          apply_subst_ctx s1 environment) state1)
        as [tau2 s2 state2 body_events | body_events] eqn:Hbody.
      * specialize (IHbody
          ((variable, gen_ty tau1 (apply_subst_ctx s1 environment)) ::
            apply_subst_ctx s1 environment) state1).
        rewrite Hbody in IHbody.
        cbn [trace_state_result] in IHbody.
        now rewrite <- IHbody.
      * specialize (IHbody
          ((variable, gen_ty tau1 (apply_subst_ctx s1 environment)) ::
            apply_subst_ctx s1 environment) state1).
        rewrite Hbody in IHbody.
        cbn [trace_state_result] in IHbody.
        now rewrite <- IHbody.
    + specialize (IHbound environment state).
      rewrite Hbound in IHbound.
      cbn [trace_state_result] in IHbound.
      now rewrite <- IHbound.
  - destruct (W_trace_exec body
      ((variable, ty_to_schm (var state)) :: environment) (S state))
      as [tau substitution state' events | events] eqn:Hbody.
    + specialize (IHbody
        ((variable, ty_to_schm (var state)) :: environment) (S state)).
      rewrite Hbody in IHbody.
      cbn [trace_state_result] in IHbody.
      now rewrite <- IHbody.
    + specialize (IHbody
        ((variable, ty_to_schm (var state)) :: environment) (S state)).
      rewrite Hbody in IHbody.
      cbn [trace_state_result] in IHbody.
      now rewrite <- IHbody.
  - reflexivity.
Qed.

Theorem runWTrace_result : forall expression environment,
  trace_result (runWTrace expression environment) =
  runW_exec expression environment.
Proof.
  intros expression environment.
  unfold runWTrace, runW_exec.
  destruct (W_trace_exec expression environment
    (initial_state_exec environment))
    as [tau substitution state events | events] eqn:Htrace.
  - pose proof
      (W_trace_exec_erases expression environment
        (initial_state_exec environment)) as Herase.
    rewrite Htrace in Herase.
    cbn [trace_state_result] in Herase |- *.
    now rewrite <- Herase.
  - pose proof
      (W_trace_exec_erases expression environment
        (initial_state_exec environment)) as Herase.
    rewrite Htrace in Herase.
    cbn [trace_state_result] in Herase |- *.
    now rewrite <- Herase.
Qed.
