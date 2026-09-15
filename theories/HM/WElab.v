(** * Structural elaboration trace for Algorithm W

    [W_elab] is a single-pass, proof-free counterpart of [W_exec].  Besides
    the inferred type, substitution, and fresh-variable state, a successful
    run returns a tree containing precisely the choices needed by the later
    HM-to-Church reifier: lambda annotations, scheme generalizations, scheme
    instantiations, and application unifiers.

    Constants are rejected at this boundary.  They have HM types, but the
    project currently has no corresponding System F term interpretation.
    Consequently correspondence with [W_exec] is stated for [constant_free]
    source terms. *)

From Stdlib Require Import List.
Import ListNotations.

From SystemF.HM Require Import
  ElabScope Unify WCorrespondence WCorrect WExec WExecCorrect.
From SystemF.HM.WInCoq Require Import
  Context Gen Infer Schemes SubstSchm Typing.

Inductive WElabFailure : Set :=
| elab_unsupported_constant : id -> WElabFailure
| elab_missing_variable : id -> WElabFailure
| elab_instantiation_failure : id -> schm -> WElabFailure
| elab_unification_failure : ty -> ty -> WElabFailure.

(** Types in this tree still use W's globally fresh identifiers.  A later
    reifier applies the final W substitution and translates those identifiers
    into System F de Bruijn variables. *)
Inductive WElabTree : Set :=
| elab_variable :
    id -> schm -> inst_subst -> ty -> WElabTree
| elab_lambda :
    id -> id -> ty -> WElabTree -> WElabTree
| elab_application :
    WElabTree -> WElabTree ->
    id -> ty -> ty -> substitution -> ty -> WElabTree
| elab_let :
    id -> ty -> list id -> schm ->
    WElabTree -> WElabTree -> WElabTree.

(** Constructor fields of [WElabTree]:

    - variable: source name, looked-up scheme, instantiation substitution,
      instantiated type;
    - lambda: source binder, fresh type identifier, current parameter type,
      body;
    - application: function and argument trees, fresh result identifier,
      the two types passed to unification, unifier, inferred result type;
    - let: source binder, inferred bound type, generalized identifiers in
      first-occurrence order, generalized scheme, bound and body trees. *)

Fixpoint w_elab_tree_type (tree : WElabTree) : ty :=
  match tree with
  | elab_variable _ _ _ instance => instance
  | elab_lambda _ _ parameter body =>
      arrow parameter (w_elab_tree_type body)
  | elab_application _ _ _ _ _ _ result => result
  | elab_let _ _ _ _ _ body => w_elab_tree_type body
  end.

(** The substitutions returned by all recursive calls are recoverable from
    the audit tree.  This lets the Church reifier push precisely the
    remaining substitution into each child instead of applying the root
    substitution twice to already-normalized annotations. *)
Fixpoint w_elab_tree_substitution (tree : WElabTree) : substitution :=
  match tree with
  | elab_variable _ _ _ _ => []
  | elab_lambda _ _ _ body => w_elab_tree_substitution body
  | elab_application function argument _ _ _ unifier _ =>
      compose_subst
        (w_elab_tree_substitution function)
        (compose_subst
          (w_elab_tree_substitution argument) unifier)
  | elab_let _ _ _ _ bound body =>
      compose_subst
        (w_elab_tree_substitution bound)
        (w_elab_tree_substitution body)
  end.

Fixpoint w_elab_tree_source (tree : WElabTree) : term :=
  match tree with
  | elab_variable variable _ _ _ => var_t variable
  | elab_lambda variable _ _ body =>
      lam_t variable (w_elab_tree_source body)
  | elab_application function argument _ _ _ _ _ =>
      app_t (w_elab_tree_source function) (w_elab_tree_source argument)
  | elab_let variable _ _ _ bound body =>
      let_t variable
        (w_elab_tree_source bound) (w_elab_tree_source body)
  end.

Lemma w_elab_tree_source_constant_free : forall tree,
  constant_free (w_elab_tree_source tree).
Proof.
  induction tree as
      [variable sigma instantiation instance
      | variable alpha parameter body IHbody
      | function IHfunction argument IHargument
          alpha left right unifier result
      | variable bound_type generalized sigma
          bound IHbound body IHbody];
    cbn [w_elab_tree_source constant_free].
  - exact I.
  - exact IHbody.
  - now split.
  - now split.
Qed.

Fixpoint w_elab_instantiation_count
    (variable : id) (tree : WElabTree) : nat :=
  match tree with
  | elab_variable found _ _ _ =>
      if Nat.eqb variable found then 1 else 0
  | elab_lambda _ _ _ body =>
      w_elab_instantiation_count variable body
  | elab_application function argument _ _ _ _ _ =>
      w_elab_instantiation_count variable function +
      w_elab_instantiation_count variable argument
  | elab_let _ _ _ _ bound body =>
      w_elab_instantiation_count variable bound +
      w_elab_instantiation_count variable body
  end.

Inductive w_elab_state_result : Set :=
| w_elab_state_success :
    ty -> substitution -> id -> WElabTree -> w_elab_state_result
| w_elab_state_rejected : WElabFailure -> w_elab_state_result.

Inductive w_elab_result : Set :=
| elaborated : ty -> substitution -> WElabTree -> w_elab_result
| elaboration_rejected : WElabFailure -> w_elab_result.

Definition erase_w_elab_state
    (result : w_elab_state_result) : w_state_result :=
  match result with
  | w_elab_state_success tau substitution state _ =>
      w_state_success tau substitution state
  | w_elab_state_rejected _ => w_state_rejected
  end.

Definition erase_w_elab_result (result : w_elab_result) : w_result :=
  match result with
  | elaborated tau substitution _ => inferred tau substitution
  | elaboration_rejected _ => inference_rejected
  end.

(** Compute the scheme and retain the generalized HM identifiers that
    [gen_ty] normally discards. *)
Definition generalize_for_elaboration
    (tau : ty) (environment : ctx) : schm * list id :=
  gen_ty_aux tau environment [].

Lemma generalize_for_elaboration_scheme : forall tau environment,
  fst (generalize_for_elaboration tau environment) =
  gen_ty tau environment.
Proof. reflexivity. Qed.

Fixpoint W_elab
    (expression : term) (environment : ctx) (state : id)
    : w_elab_state_result :=
  match expression with
  | const_t constant =>
      w_elab_state_rejected (elab_unsupported_constant constant)

  | var_t variable =>
      match in_ctx variable environment with
      | None =>
          w_elab_state_rejected (elab_missing_variable variable)
      | Some sigma =>
          let count := max_gen_vars sigma in
          let instantiation := compute_inst_subst state count in
          match apply_inst_subst instantiation sigma with
          | None =>
              w_elab_state_rejected
                (elab_instantiation_failure variable sigma)
          | Some tau =>
              w_elab_state_success tau [] (state + count)
                (elab_variable variable sigma instantiation tau)
          end
      end

  | lam_t variable body =>
      let alpha := state in
      match W_elab body
          ((variable, ty_to_schm (var alpha)) :: environment) (S state) with
      | w_elab_state_rejected failure =>
          w_elab_state_rejected failure
      | w_elab_state_success tau substitution state' body_tree =>
          let parameter := apply_subst substitution (var alpha) in
          w_elab_state_success
            (arrow parameter tau) substitution state'
            (elab_lambda variable alpha parameter body_tree)
      end

  | app_t function argument =>
      match W_elab function environment state with
      | w_elab_state_rejected failure =>
          w_elab_state_rejected failure
      | w_elab_state_success tau1 s1 state1 function_tree =>
          match W_elab argument (apply_subst_ctx s1 environment) state1 with
          | w_elab_state_rejected failure =>
              w_elab_state_rejected failure
          | w_elab_state_success tau2 s2 state2 argument_tree =>
              let alpha := state2 in
              let left := apply_subst s2 tau1 in
              let right := arrow tau2 (var alpha) in
              match unify_exec left right with
              | rejected =>
                  w_elab_state_rejected
                    (elab_unification_failure left right)
              | unified unifier =>
                  let result := apply_subst unifier (var alpha) in
                  w_elab_state_success result
                    (compose_subst s1 (compose_subst s2 unifier))
                    (S state2)
                    (elab_application
                      function_tree argument_tree alpha left right
                      unifier result)
              end
          end
      end

  | let_t variable bound body =>
      match W_elab bound environment state with
      | w_elab_state_rejected failure =>
          w_elab_state_rejected failure
      | w_elab_state_success tau1 s1 state1 bound_tree =>
          let environment' := apply_subst_ctx s1 environment in
          let generalization :=
            generalize_for_elaboration tau1 environment' in
          let sigma := fst generalization in
          let generalized := snd generalization in
          match W_elab body
              ((variable, sigma) :: environment') state1 with
          | w_elab_state_rejected failure =>
              w_elab_state_rejected failure
          | w_elab_state_success tau2 s2 state2 body_tree =>
              w_elab_state_success tau2 (compose_subst s1 s2) state2
                (elab_let variable tau1 generalized sigma
                  bound_tree body_tree)
          end
      end
  end.

Definition runW_elab
    (expression : term) (environment : ctx) : w_elab_result :=
  match W_elab expression environment (initial_state_exec environment) with
  | w_elab_state_success tau substitution _ tree =>
      elaborated tau substitution tree
  | w_elab_state_rejected failure => elaboration_rejected failure
  end.

(** ** Computational correspondence *)

Theorem W_elab_erases : forall expression environment state,
  constant_free expression ->
  erase_w_elab_state (W_elab expression environment state) =
  W_exec expression environment state.
Proof.
  induction expression as
      [variable
      | function IHfunction argument IHargument
      | variable bound IHbound body IHbody
      | variable body IHbody
      | constant];
    intros environment state Hfragment;
    cbn [constant_free] in Hfragment;
    cbn [W_elab W_exec].
  - destruct (in_ctx variable environment) as [sigma |] eqn:Hlookup;
      cbn [erase_w_elab_state].
    + destruct (apply_inst_subst
        (compute_inst_subst state (max_gen_vars sigma)) sigma);
        reflexivity.
    + reflexivity.
  - destruct Hfragment as [Hfunction_fragment Hargument_fragment].
    destruct (W_elab function environment state)
      as [tau1 s1 state1 function_tree | function_failure]
      eqn:Hfunction.
    + specialize
        (IHfunction environment state Hfunction_fragment).
      rewrite Hfunction in IHfunction.
      cbn [erase_w_elab_state] in IHfunction.
      rewrite <- IHfunction.
      destruct (W_elab argument (apply_subst_ctx s1 environment) state1)
        as [tau2 s2 state2 argument_tree | argument_failure]
        eqn:Hargument.
      * specialize (IHargument
          (apply_subst_ctx s1 environment) state1 Hargument_fragment).
        rewrite Hargument in IHargument.
        cbn [erase_w_elab_state] in IHargument.
        rewrite <- IHargument.
        destruct (unify_exec (apply_subst s2 tau1)
          (arrow tau2 (var state2))); reflexivity.
      * specialize (IHargument
          (apply_subst_ctx s1 environment) state1 Hargument_fragment).
        rewrite Hargument in IHargument.
        cbn [erase_w_elab_state] in IHargument.
        now rewrite <- IHargument.
    + specialize (IHfunction environment state Hfunction_fragment).
      rewrite Hfunction in IHfunction.
      cbn [erase_w_elab_state] in IHfunction.
      now rewrite <- IHfunction.
  - destruct Hfragment as [Hbound_fragment Hbody_fragment].
    destruct (W_elab bound environment state)
      as [tau1 s1 state1 bound_tree | bound_failure] eqn:Hbound.
    + specialize (IHbound environment state Hbound_fragment).
      rewrite Hbound in IHbound.
      cbn [erase_w_elab_state] in IHbound.
      rewrite <- IHbound.
      destruct (generalize_for_elaboration tau1
        (apply_subst_ctx s1 environment))
        as [sigma generalized] eqn:Hgeneralization.
      assert (Hsigma :
        gen_ty tau1 (apply_subst_ctx s1 environment) = sigma).
      { rewrite <- generalize_for_elaboration_scheme.
        now rewrite Hgeneralization. }
      rewrite Hsigma.
      destruct (W_elab body
          ((variable, sigma) :: apply_subst_ctx s1 environment) state1)
        as [tau2 s2 state2 body_tree | body_failure] eqn:Hbody.
      * specialize (IHbody
          ((variable, sigma) :: apply_subst_ctx s1 environment)
          state1 Hbody_fragment).
        rewrite Hbody in IHbody.
        cbn [erase_w_elab_state] in IHbody.
        cbn [fst snd].
        rewrite Hbody.
        cbn [erase_w_elab_state].
        now rewrite <- IHbody.
      * specialize (IHbody
          ((variable, sigma) :: apply_subst_ctx s1 environment)
          state1 Hbody_fragment).
        rewrite Hbody in IHbody.
        cbn [erase_w_elab_state] in IHbody.
        cbn [fst snd].
        rewrite Hbody.
        cbn [erase_w_elab_state].
        now rewrite <- IHbody.
    + specialize (IHbound environment state Hbound_fragment).
      rewrite Hbound in IHbound.
      cbn [erase_w_elab_state] in IHbound.
      now rewrite <- IHbound.
  - destruct (W_elab body
      ((variable, ty_to_schm (var state)) :: environment) (S state))
      as [tau substitution state' body_tree | body_failure] eqn:Hbody.
    + specialize (IHbody
        ((variable, ty_to_schm (var state)) :: environment)
        (S state) Hfragment).
      rewrite Hbody in IHbody.
      cbn [erase_w_elab_state] in IHbody.
      now rewrite <- IHbody.
    + specialize (IHbody
        ((variable, ty_to_schm (var state)) :: environment)
        (S state) Hfragment).
      rewrite Hbody in IHbody.
      cbn [erase_w_elab_state] in IHbody.
      now rewrite <- IHbody.
  - contradiction.
Qed.

Theorem runW_elab_erases : forall expression environment,
  constant_free expression ->
  erase_w_elab_result (runW_elab expression environment) =
  runW_exec expression environment.
Proof.
  intros expression environment Hfragment.
  unfold runW_elab, runW_exec.
  destruct (W_elab expression environment
    (initial_state_exec environment))
    as [tau substitution state tree | failure] eqn:Helaboration.
  - pose proof
      (W_elab_erases expression environment
        (initial_state_exec environment) Hfragment) as Herase.
    rewrite Helaboration in Herase.
    cbn [erase_w_elab_state erase_w_elab_result] in Herase |- *.
    now rewrite <- Herase.
  - pose proof
      (W_elab_erases expression environment
        (initial_state_exec environment) Hfragment) as Herase.
    rewrite Helaboration in Herase.
    cbn [erase_w_elab_state erase_w_elab_result] in Herase |- *.
    now rewrite <- Herase.
Qed.

Corollary runW_elab_checked_correspondence : forall expression environment,
  constant_free expression ->
  erase_w_elab_result (runW_elab expression environment) =
  observe_checked_result (runW expression environment).
Proof.
  intros expression environment Hfragment.
  rewrite runW_elab_erases by exact Hfragment.
  symmetry.
  apply runW_exec_checked_correspondence.
Qed.

Corollary runW_elab_success_iff_exec_success : forall
    expression environment tau substitution,
  constant_free expression ->
  ((exists tree,
      runW_elab expression environment =
        elaborated tau substitution tree) <->
   runW_exec expression environment = inferred tau substitution).
Proof.
  intros expression environment tau substitution Hfragment.
  pose proof
    (runW_elab_erases expression environment Hfragment) as Hbridge.
  destruct (runW_elab expression environment)
    as [tau' substitution' tree | failure] eqn:Helaboration;
    cbn [erase_w_elab_result] in Hbridge.
  - split.
    + intros [tree' Hsuccess].
      inversion Hsuccess; subst.
      symmetry. exact Hbridge.
    + intro Hsuccess.
      rewrite Hsuccess in Hbridge.
      inversion Hbridge; subst.
      now exists tree.
  - split.
    + intros [tree Hsuccess]. discriminate.
    + intro Hsuccess.
      rewrite Hsuccess in Hbridge.
      discriminate.
Qed.

Corollary runW_elab_rejected_iff_exec_rejected : forall
    expression environment,
  constant_free expression ->
  ((exists failure,
      runW_elab expression environment = elaboration_rejected failure) <->
   runW_exec expression environment = inference_rejected).
Proof.
  intros expression environment Hfragment.
  pose proof
    (runW_elab_erases expression environment Hfragment) as Hbridge.
  destruct (runW_elab expression environment)
    as [tau substitution tree | failure] eqn:Helaboration;
    cbn [erase_w_elab_result] in Hbridge.
  - split.
    + intros [failure Hfailure]. discriminate.
    + intro Hfailure.
      rewrite Hfailure in Hbridge.
      discriminate.
  - split.
    + intro Hfailure. symmetry. exact Hbridge.
    + intro Hfailure. now exists failure.
Qed.

Corollary runW_elab_success_iff_checked_success : forall
    expression environment tau substitution,
  constant_free expression ->
  ((exists tree,
      runW_elab expression environment =
        elaborated tau substitution tree) <->
   runW expression environment = inl (tau, substitution)).
Proof.
  intros expression environment tau substitution Hfragment.
  rewrite runW_elab_success_iff_exec_success by exact Hfragment.
  apply runW_exec_success_iff_checked_success.
Qed.

Corollary runW_elab_rejected_iff_checked_rejected : forall
    expression environment,
  constant_free expression ->
  ((exists elaboration_failure,
      runW_elab expression environment =
        elaboration_rejected elaboration_failure) <->
   exists checked_failure,
      runW expression environment = inr checked_failure).
Proof.
  intros expression environment Hfragment.
  rewrite runW_elab_rejected_iff_exec_rejected by exact Hfragment.
  apply runW_exec_rejected_iff_checked_rejected.
Qed.

(** Full public correspondence with the original dependent [runW].  Failure
    certificates have different types, so the rejection clause compares
    their existence; successful results agree on the exact type and
    substitution while retaining the elaboration tree. *)
Definition runW_elab_checked_spec
    (expression : term) (environment : ctx) : Prop :=
  (forall tau substitution,
    (exists tree,
      runW_elab expression environment =
        elaborated tau substitution tree) <->
    runW expression environment = inl (tau, substitution)) /\
  ((exists elaboration_failure,
      runW_elab expression environment =
        elaboration_rejected elaboration_failure) <->
   exists checked_failure,
      runW expression environment = inr checked_failure).

Theorem runW_elab_checked_full_correspondence : forall
    expression environment,
  constant_free expression ->
  runW_elab_checked_spec expression environment.
Proof.
  intros expression environment Hfragment.
  split.
  - intros tau substitution.
    now apply runW_elab_success_iff_checked_success.
  - now apply runW_elab_rejected_iff_checked_rejected.
Qed.

Corollary runW_elab_success_contract : forall
    expression environment tau substitution tree,
  constant_free expression ->
  runW_elab expression environment = elaborated tau substitution tree ->
  runW_success_spec expression environment tau substitution.
Proof.
  intros expression environment tau substitution tree Hfragment Hrun.
  apply runW_exec_success_contract.
  apply (proj1
    (runW_elab_success_iff_exec_success
      expression environment tau substitution Hfragment)).
  now exists tree.
Qed.

Corollary runW_elab_rejected_no_typing : forall
    expression environment failure,
  constant_free expression ->
  runW_elab expression environment = elaboration_rejected failure ->
  forall tau, ~ has_type environment expression tau.
Proof.
  intros expression environment failure Hfragment Hrun.
  apply runW_exec_rejected_no_typing.
  apply (proj1
    (runW_elab_rejected_iff_exec_rejected
      expression environment Hfragment)).
  now exists failure.
Qed.

(** Every successful tree describes exactly its source term and exposes the
    same root type returned by the algorithm. *)
Theorem W_elab_tree_contract : forall expression environment state
    tau substitution state' tree,
  W_elab expression environment state =
    w_elab_state_success tau substitution state' tree ->
  w_elab_tree_source tree = expression /\
  w_elab_tree_type tree = tau.
Proof.
  induction expression as
      [variable
      | function IHfunction argument IHargument
      | variable bound IHbound body IHbody
      | variable body IHbody
      | constant];
    intros environment state tau substitution state' tree Hrun;
    cbn [W_elab] in Hrun.
  - destruct (in_ctx variable environment) as [sigma |] eqn:Hlookup;
      try discriminate.
    destruct (apply_inst_subst
      (compute_inst_subst state (max_gen_vars sigma)) sigma)
      as [instance |] eqn:Hinstance; try discriminate.
    inversion Hrun; subst tau substitution state' tree.
    split; reflexivity.
  - destruct (W_elab function environment state)
      as [tau1 s1 state1 function_tree | function_failure]
      eqn:Hfunction; try discriminate.
    destruct (W_elab argument (apply_subst_ctx s1 environment) state1)
      as [tau2 s2 state2 argument_tree | argument_failure]
      eqn:Hargument; try discriminate.
    destruct (unify_exec (apply_subst s2 tau1)
      (arrow tau2 (var state2))) as [unifier |] eqn:Hunify;
      try discriminate.
    inversion Hrun; subst.
    pose proof
      (IHfunction environment state tau1 s1 state1 function_tree Hfunction)
      as [Hfunction_source Hfunction_type].
    pose proof
      (IHargument (apply_subst_ctx s1 environment) state1
        tau2 s2 state2 argument_tree Hargument)
      as [Hargument_source Hargument_type].
    split; cbn [w_elab_tree_source w_elab_tree_type].
    + now rewrite Hfunction_source, Hargument_source.
    + reflexivity.
  - destruct (W_elab bound environment state)
      as [tau1 s1 state1 bound_tree | bound_failure]
      eqn:Hbound; try discriminate.
    destruct (generalize_for_elaboration tau1
      (apply_subst_ctx s1 environment))
      as [sigma generalized] eqn:Hgeneralization.
    cbn [fst snd] in Hrun.
    destruct (W_elab body
      ((variable, sigma) :: apply_subst_ctx s1 environment) state1)
      as [tau2 s2 state2 body_tree | body_failure]
      eqn:Hbody; try discriminate.
    pose proof
      (IHbound environment state tau1 s1 state1 bound_tree Hbound)
      as [Hbound_source Hbound_type].
    pose proof
      (IHbody ((variable, sigma) :: apply_subst_ctx s1 environment)
        state1 tau2 s2 state2 body_tree Hbody)
      as [Hbody_source Hbody_type].
    inversion Hrun; subst tau substitution state' tree.
    split; cbn [w_elab_tree_source w_elab_tree_type].
    + now rewrite Hbound_source, Hbody_source.
    + exact Hbody_type.
  - destruct (W_elab body
      ((variable, ty_to_schm (var state)) :: environment) (S state))
      as [body_type body_substitution body_state body_tree | body_failure]
      eqn:Hbody; try discriminate.
    pose proof
      (IHbody ((variable, ty_to_schm (var state)) :: environment)
        (S state) body_type body_substitution body_state body_tree Hbody)
      as [Hbody_source Hbody_type].
    inversion Hrun; subst tau substitution state' tree.
    split; cbn [w_elab_tree_source w_elab_tree_type].
    + now rewrite Hbody_source.
    + now rewrite Hbody_type.
  - discriminate.
Qed.

Corollary runW_elab_tree_contract : forall expression environment
    tau substitution tree,
  runW_elab expression environment = elaborated tau substitution tree ->
  w_elab_tree_source tree = expression /\
  w_elab_tree_type tree = tau.
Proof.
  intros expression environment tau substitution tree Hrun.
  unfold runW_elab in Hrun.
  destruct (W_elab expression environment
    (initial_state_exec environment))
    as [tau' substitution' state tree' | failure] eqn:Helaboration;
    try discriminate.
  inversion Hrun; subst tau substitution tree.
  now apply W_elab_tree_contract with
    (environment := environment)
    (state := initial_state_exec environment)
    (substitution := substitution') (state' := state).
Qed.

Theorem W_elab_tree_substitution_contract : forall
    expression environment state tau substitution state' tree,
  W_elab expression environment state =
    w_elab_state_success tau substitution state' tree ->
  w_elab_tree_substitution tree = substitution.
Proof.
  induction expression as
      [variable
      | function IHfunction argument IHargument
      | variable bound IHbound body IHbody
      | variable body IHbody
      | constant];
    intros environment state tau substitution state' tree Hrun;
    cbn [W_elab] in Hrun.
  - destruct (in_ctx variable environment) as [sigma |] eqn:Hlookup;
      try discriminate.
    destruct (apply_inst_subst
      (compute_inst_subst state (max_gen_vars sigma)) sigma)
      as [instance |] eqn:Hinstance; try discriminate.
    inversion Hrun; subst.
    reflexivity.
  - destruct (W_elab function environment state)
      as [tau1 s1 state1 function_tree | function_failure]
      eqn:Hfunction; try discriminate.
    destruct (W_elab argument (apply_subst_ctx s1 environment) state1)
      as [tau2 s2 state2 argument_tree | argument_failure]
      eqn:Hargument; try discriminate.
    destruct (unify_exec (apply_subst s2 tau1)
      (arrow tau2 (var state2))) as [unifier |] eqn:Hunify;
      try discriminate.
    inversion Hrun; subst.
    cbn [w_elab_tree_substitution].
    rewrite
      (IHfunction environment state tau1 s1 state1
        function_tree Hfunction),
      (IHargument (apply_subst_ctx s1 environment) state1
        tau2 s2 state2 argument_tree Hargument).
    reflexivity.
  - destruct (W_elab bound environment state)
      as [tau1 s1 state1 bound_tree | bound_failure]
      eqn:Hbound; try discriminate.
    destruct (generalize_for_elaboration tau1
      (apply_subst_ctx s1 environment))
      as [sigma generalized] eqn:Hgeneralization.
    cbn [fst snd] in Hrun.
    destruct (W_elab body
      ((variable, sigma) :: apply_subst_ctx s1 environment) state1)
      as [tau2 s2 state2 body_tree | body_failure]
      eqn:Hbody; try discriminate.
    inversion Hrun; subst.
    cbn [w_elab_tree_substitution].
    rewrite
      (IHbound environment state tau1 s1 state1 bound_tree Hbound),
      (IHbody ((variable, sigma) :: apply_subst_ctx s1 environment)
        state1 tau s2 state' body_tree Hbody).
    reflexivity.
  - destruct (W_elab body
      ((variable, ty_to_schm (var state)) :: environment) (S state))
      as [body_type body_substitution body_state body_tree | body_failure]
      eqn:Hbody; try discriminate.
    inversion Hrun; subst.
    cbn [w_elab_tree_substitution].
    now apply IHbody with
      (environment :=
        (variable, ty_to_schm (var state)) :: environment)
      (state := S state) (tau := body_type)
      (substitution := substitution) (state' := state').
  - discriminate.
Qed.

Corollary runW_elab_tree_substitution_contract : forall
    expression environment tau substitution tree,
  runW_elab expression environment = elaborated tau substitution tree ->
  w_elab_tree_substitution tree = substitution.
Proof.
  intros expression environment tau substitution tree Hrun.
  unfold runW_elab in Hrun.
  destruct (W_elab expression environment
      (initial_state_exec environment))
    as [tau' substitution' state tree' | failure] eqn:Helaboration;
    try discriminate.
  inversion Hrun; subst.
  apply W_elab_tree_substitution_contract with
    (expression := expression)
    (environment := environment)
    (state := initial_state_exec environment)
    (tau := tau) (substitution := substitution) (state' := state)
    (tree := tree).
  exact Helaboration.
Qed.

Corollary runW_elab_success_constant_free : forall expression environment
    tau substitution tree,
  runW_elab expression environment = elaborated tau substitution tree ->
  constant_free expression.
Proof.
  intros expression environment tau substitution tree Hrun.
  pose proof
    (runW_elab_tree_contract expression environment
      tau substitution tree Hrun) as [Hsource Htype].
  rewrite <- Hsource.
  apply w_elab_tree_source_constant_free.
Qed.
