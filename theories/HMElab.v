(** * Type-level bridge from Algorithm W to System F

    A successful W result is first generalized with [gen_ty] in the
    substituted environment.  At the closed top level that environment is
    empty.  Generalized scheme variables become explicit outer [TForall]
    binders, free scheme variables are resolved in an ambient System F type
    context, and HM constants are interpreted by an explicit client-supplied
    map to closed System F types.

    Generalized variables are numbered by first occurrence from left to
    right.  Thus [sc_gen 0] becomes the outermost quantifier: in a body under
    [n] binders it is represented by de Bruijn index [n - 1].

    This file establishes the type bridge, connects it to [relgen], and
    reifies a successful [WElabTree] into explicit Church-style System F
    syntax.  Acceptance by the independent checker and preservation of
    erasure are the next proof layer. *)

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

From SystemF.F Require Import Syntax OPE Scope TypeSubstitution Check.
From SystemF.F Require Export RawTyping.
From SystemF.FreeTheorems Require Import Formula Generate.
From SystemF.HM Require Import ElabScope Erasure Infer.
From SystemF.HM Require Export ElabSemantics.
From SystemF.HM.WInCoq Require Import Gen Schemes Subst SubstSchm.
From SystemF.HM.WInCoq Require Import Context Disjoints ListIds.


(** [free_variables_scoped depth resolve sigma] says that every [sc_var]
    has an ambient de Bruijn index below [depth].  [sc_gen] variables are
    checked separately because they are bound by the quantifiers introduced
    by this bridge. *)
Fixpoint free_variables_scoped
    (depth : nat) (resolve : id -> nat) (sigma : schm) : Prop :=
  match sigma with
  | sc_var variable => resolve variable < depth
  | sc_con _ => True
  | sc_gen _ => True
  | sc_arrow domain codomain =>
      free_variables_scoped depth resolve domain /\
      free_variables_scoped depth resolve codomain
  end.


(** Translate the body under all generalized binders.  Ambient free
    variables are shifted by [quantifier_count]; generalized variable [i]
    uses the reversed index [quantifier_count - S i] so that [0] denotes the
    first, outermost quantifier. *)
Fixpoint scheme_body_to_type
    (constants : ConstantInterpretation)
    (resolve : id -> nat)
    (quantifier_count : nat)
    (sigma : schm) : type :=
  match sigma with
  | sc_var variable => TVar (quantifier_count + resolve variable)
  | sc_con name => constants name
  | sc_gen variable => TVar (quantifier_count - S variable)
  | sc_arrow domain codomain =>
      TArrow
        (scheme_body_to_type constants resolve quantifier_count domain)
        (scheme_body_to_type constants resolve quantifier_count codomain)
  end.

Fixpoint quantify_scheme (count : nat) (body : type) : type :=
  match count with
  | 0 => body
  | S count => TForall (quantify_scheme count body)
  end.

Definition scheme_to_systemf
    (constants : ConstantInterpretation)
    (resolve : id -> nat)
    (sigma : schm) : type :=
  let count := max_gen_vars sigma in
  quantify_scheme count
    (scheme_body_to_type constants resolve count sigma).

(** ** Scope correctness *)

Lemma scheme_body_to_type_scoped : forall constants resolve sigma
    ambient_depth quantifier_count,
  constants_closed constants ->
  free_variables_scoped ambient_depth resolve sigma ->
  generalized_variables_scoped quantifier_count sigma ->
  closed (quantifier_count + ambient_depth)
    (scheme_body_to_type constants resolve quantifier_count sigma).
Proof.
  intros constants resolve sigma.
  induction sigma as
      [variable | name | variable | domain IHdomain codomain IHcodomain];
    intros ambient_depth quantifier_count Hconstants Hfree Hgeneralized;
    cbn [free_variables_scoped generalized_variables_scoped
      scheme_body_to_type closed] in *.
  - lia.
  - apply closed_mono with (n := 0).
    + lia.
    + apply Hconstants.
  - lia.
  - destruct Hfree as [Hfree_left Hfree_right].
    destruct Hgeneralized as [Hgen_left Hgen_right].
    split.
    + now apply IHdomain.
    + now apply IHcodomain.
Qed.

Lemma quantify_scheme_scoped : forall count ambient_depth body,
  closed (count + ambient_depth) body ->
  closed ambient_depth (quantify_scheme count body).
Proof.
  induction count as [| count IH]; intros ambient_depth body Hbody.
  - exact Hbody.
  - cbn [quantify_scheme closed].
    apply IH.
    replace (count + S ambient_depth)
      with (S count + ambient_depth) by lia.
    exact Hbody.
Qed.

Theorem scheme_to_systemf_scoped : forall constants resolve sigma
    ambient_depth,
  constants_closed constants ->
  free_variables_scoped ambient_depth resolve sigma ->
  closed ambient_depth (scheme_to_systemf constants resolve sigma).
Proof.
  intros constants resolve sigma ambient_depth Hconstants Hfree.
  unfold scheme_to_systemf.
  apply quantify_scheme_scoped.
  apply scheme_body_to_type_scoped.
  - exact Hconstants.
  - exact Hfree.
  - apply generalized_variables_scoped_max.
Qed.

(** Generalization in an empty HM context cannot leave an [sc_var]. *)
Lemma gen_ty_aux_empty_free_variables_scoped : forall tau variables,
  free_variables_scoped 0 (fun _ => 0)
    (fst (gen_ty_aux tau [] variables)).
Proof.
  induction tau as
      [variable | name | domain IHdomain codomain IHcodomain];
    intros variables;
    cbn [gen_ty_aux].
  - unfold FV_ctx.
    cbn [ListIds.in_list_id].
    destruct (ListIds.index_list_id variable variables); exact I.
  - exact I.
  - destruct (gen_ty_aux domain [] variables)
      as [domain_scheme domain_variables] eqn:Hdomain.
    destruct (gen_ty_aux codomain [] domain_variables)
      as [codomain_scheme codomain_variables] eqn:Hcodomain.
    cbn [free_variables_scoped].
    split.
    + specialize (IHdomain variables).
      rewrite Hdomain in IHdomain.
      exact IHdomain.
    + specialize (IHcodomain domain_variables).
      rewrite Hcodomain in IHcodomain.
      exact IHcodomain.
Qed.

Corollary gen_ty_empty_free_variables_scoped : forall tau,
  free_variables_scoped 0 (fun _ => 0) (gen_ty tau []).
Proof.
  intro tau.
  unfold gen_ty.
  apply gen_ty_aux_empty_free_variables_scoped.
Qed.

Definition hm_principal_scheme (tau : ty) : schm :=
  gen_ty tau [].

Definition hm_principal_type
    (constants : ConstantInterpretation) (tau : ty) : type :=
  scheme_to_systemf constants (fun _ => 0) (hm_principal_scheme tau).

Theorem hm_principal_type_closed : forall constants tau,
  constants_closed constants ->
  closed 0 (hm_principal_type constants tau).
Proof.
  intros constants tau Hconstants.
  unfold hm_principal_type, hm_principal_scheme.
  apply scheme_to_systemf_scoped.
  - exact Hconstants.
  - apply gen_ty_empty_free_variables_scoped.
Qed.

(** ** Public checked and executable W entry points *)

Definition infer_systemf_type_checked
    (constants : ConstantInterpretation) (expression : term) : option type :=
  match runW expression [] with
  | inl (tau, _) => Some (hm_principal_type constants tau)
  | inr _ => None
  end.

Definition infer_systemf_type_exec
    (constants : ConstantInterpretation) (expression : term) : option type :=
  match runW_exec expression [] with
  | inferred tau _ => Some (hm_principal_type constants tau)
  | inference_rejected => None
  end.

Theorem infer_systemf_type_correspondence : forall constants expression,
  infer_systemf_type_checked constants expression =
  infer_systemf_type_exec constants expression.
Proof.
  intros constants expression.
  unfold infer_systemf_type_checked, infer_systemf_type_exec.
  destruct (runW expression []) as [[tau substitution] | failure]
    eqn:Hrun.
  - pose proof
      (proj2
        (runW_exec_success_iff_checked_success
          expression [] tau substitution) Hrun) as Hexec.
    rewrite Hexec.
    reflexivity.
  - assert (Hexec : runW_exec expression [] = inference_rejected).
    { apply (proj2
        (runW_exec_rejected_iff_checked_rejected expression [])).
      now exists failure. }
    rewrite Hexec.
    reflexivity.
Qed.

Theorem infer_systemf_type_exec_closed : forall constants expression T,
  constants_closed constants ->
  infer_systemf_type_exec constants expression = Some T ->
  closed 0 T.
Proof.
  intros constants expression T Hconstants Hinfer.
  unfold infer_systemf_type_exec in Hinfer.
  destruct (runW_exec expression []) as [tau substitution |]
    eqn:Hrun; try discriminate.
  inversion Hinfer; subst T.
  now apply hm_principal_type_closed.
Qed.

Theorem infer_systemf_type_checked_closed : forall constants expression T,
  constants_closed constants ->
  infer_systemf_type_checked constants expression = Some T ->
  closed 0 T.
Proof.
  intros constants expression T Hconstants Hinfer.
  rewrite infer_systemf_type_correspondence in Hinfer.
  now apply infer_systemf_type_exec_closed
    with (constants := constants) (expression := expression).
Qed.

Definition BridgedType : Type :=
  {T : type | closed 0 T}.

Definition infer_systemf_type
    (constants : ConstantInterpretation)
    (Hconstants : constants_closed constants)
    (expression : term) : option BridgedType :=
  match runW_exec expression [] with
  | inferred tau _ =>
      Some (exist _ (hm_principal_type constants tau)
        (hm_principal_type_closed constants tau Hconstants))
  | inference_rejected => None
  end.

Definition infer_relational_formula_exec
    (constants : ConstantInterpretation)
    (expression : term) : option RelFormula :=
  match infer_systemf_type_exec constants expression with
  | Some T => Some (relgen T)
  | None => None
  end.

Theorem infer_relational_formula_exec_closed : forall constants expression T,
  constants_closed constants ->
  infer_systemf_type_exec constants expression = Some T ->
  closed_formula (relgen T).
Proof.
  intros constants expression T Hconstants Hinfer.
  apply relgen_closed.
  now apply infer_systemf_type_exec_closed
    with (constants := constants) (expression := expression).
Qed.

(** ** Reification of a W elaboration tree *)

(** Source names are resolved through a nearest-binder-first term-variable
    stack.  W type identifiers are interpreted separately by the semantic
    valuation from [ElabSemantics].  Constants remain available at the type
    level through [constants], even though [W_elab] rejects source-level
    constants.

    The remaining error constructor is useful when the semantic reifier is
    called directly on an arbitrary tree and term-variable stack.  It is
    unreachable for a tree produced by a successful closed [runW_elab]:
    [runW_elab_success_names_scoped] supplies exactly the missing name-scope
    invariant. *)
Inductive ChurchReifyError : Set :=
| reify_unbound_term_variable : id -> ChurchReifyError.

Inductive WChurchError : Set :=
| church_inference_failure : WElabFailure -> WChurchError
| church_reification_failure : ChurchReifyError -> WChurchError
| church_checker_failure : TypeError -> WChurchError
| church_checker_type_mismatch : type -> type -> WChurchError.

(** Explicit type applications are left-associated in instantiation order. *)
Fixpoint apply_type_arguments
    (function : RawChurch) (arguments : list type) : RawChurch :=
  match arguments with
  | [] => function
  | argument :: arguments' =>
      apply_type_arguments (RCTApp function argument) arguments'
  end.

(** [generalized] is in first-occurrence (outermost-first) order. *)
Fixpoint wrap_type_abstractions
    (generalized : list id) (body : RawChurch) : RawChurch :=
  match generalized with
  | [] => body
  | _ :: generalized' =>
      RCTAbs (wrap_type_abstractions generalized' body)
  end.


Definition types_closed (depth : nat) (types : list type) : Prop :=
  forall T, In T types -> closed depth T.

Lemma raw_typing_apply_type_arguments : forall
    depth context raw arguments body,
  types_closed depth arguments ->
  RawTyping depth context raw
    (quantify_type (length arguments) body) ->
  RawTyping depth context (apply_type_arguments raw arguments)
    (instantiate_type
      (quantify_type (length arguments) body) arguments).
Proof.
  intros depth context raw arguments.
  revert raw.
  induction arguments as [| argument arguments IH];
    intros raw body Harguments Htyping.
  - exact Htyping.
  - assert (Hargument : closed depth argument).
    { apply Harguments. now left. }
    assert (Hrest : types_closed depth arguments).
    { intros T HT. apply Harguments. now right. }
    cbn [length quantify_type instantiate_type apply_type_arguments].
    set (body' :=
      substitute_type
        (keep_type_substitution_n (length arguments)
          (scons argument ids)) body).
    assert (Htype :
      type_subst 0 (quantify_type (length arguments) body) argument =
      quantify_type (length arguments) body').
    { unfold body'.
      rewrite <- substitute_type_single.
      apply substitute_type_quantify. }
    rewrite Htype.
    apply IH with (body := body').
    + exact Hrest.
    + rewrite <- Htype.
      now apply RawTypingTApp.
Qed.

Lemma raw_typing_wrap_type_abstractions : forall
    generalized depth context body T,
  RawTyping (length generalized + depth)
    (lift_type_context_by (length generalized) context) body T ->
  RawTyping depth context
    (wrap_type_abstractions generalized body)
    (quantify_type (length generalized) T).
Proof.
  induction generalized as [| variable generalized IH];
    intros depth context body T Htyping.
  - cbn [length wrap_type_abstractions quantify_type] in Htyping |- *.
    rewrite lift_type_context_by_zero in Htyping.
    exact Htyping.
  - cbn [length wrap_type_abstractions quantify_type].
    apply RawTypingTAbs.
    apply IH.
    replace (length generalized + S depth)
      with (S (length generalized + depth)) by lia.
    rewrite lift_type_context_by_after_lift.
    exact Htyping.
Qed.


(** The reifier is semantic in the following precise sense: W type variables
    are interpreted by a [TypeValuation], and every application or [let]
    transports that valuation through the substitution recorded at the
    corresponding node.  Consequently the generated annotations follow the
    local typing derivation, rather than being reconstructed from the final W
    result alone.

    An earlier implementation used a stack backend.  It carried an explicit
    nearest-first list of generalized W variables together with one final
    substitution.  Monotypes were translated by looking variables up in that
    stack; entering a generalized [let] pushed its variables, and variable
    occurrences translated their saved instantiations after applying the
    final substitution.  This organization has some potential advantages: it
    is first-order, exposes de Bruijn allocation directly, is easy to inspect
    in extracted code, and could make a useful optimized backend once related
    to this definition by an equivalence theorem.

    We deliberately keep only the semantic backend.  A stack seeded from the
    principal result does not account for unconstrained variables that occur
    only in internal annotations, while one global final substitution hides
    the local substitution discipline needed by the preservation proof.  The
    valuation-based definition handles both points compositionally and is the
    implementation certified by [W_elab_semantic_type_preservation]. *)
Fixpoint reify_w_elab_tree_semantic
    (constants : ConstantInterpretation)
    (valuation : TypeValuation)
    (term_variables : list id)
    (tree : WElabTree) : Result ChurchReifyError RawChurch :=
  match tree with
  | elab_variable variable _ instantiation _ =>
      match lookup_binder variable term_variables with
      | None => Err (reify_unbound_term_variable variable)
      | Some index =>
          Ok
            (apply_type_arguments (RCVar index)
              (denote_instantiation constants valuation instantiation))
      end
  | elab_lambda variable _ parameter body =>
      match reify_w_elab_tree_semantic constants valuation
          (variable :: term_variables) body with
      | Err error => Err error
      | Ok body' =>
          Ok
            (RCAbs (denote_monotype constants valuation parameter) body')
      end
  | elab_application function argument _ _ _ unifier _ =>
      let argument_valuation :=
        valuation_after_substitution constants unifier valuation in
      let function_valuation :=
        valuation_after_substitution constants
          (compose_subst (w_elab_tree_substitution argument) unifier)
          valuation in
      match reify_w_elab_tree_semantic constants function_valuation
          term_variables function with
      | Err error => Err error
      | Ok function' =>
          match reify_w_elab_tree_semantic constants argument_valuation
              term_variables argument with
          | Err error => Err error
          | Ok argument' => Ok (RCApp function' argument')
          end
      end
  | elab_let variable _ generalized sigma bound body =>
      let body_valuation :=
        valuation_after_substitution constants
          (w_elab_tree_substitution body) valuation in
      let annotation := denote_scheme constants body_valuation sigma in
      match reify_w_elab_tree_semantic constants
          (generalized_valuation generalized body_valuation)
          term_variables bound with
      | Err error => Err error
      | Ok bound' =>
          match reify_w_elab_tree_semantic constants valuation
              (variable :: term_variables) body with
          | Err error => Err error
          | Ok body' =>
              Ok
                (RCApp
                  (RCAbs annotation body')
                  (wrap_type_abstractions generalized bound'))
          end
      end
  end.

Lemma in_ctx_some_name : forall variable environment sigma,
  in_ctx variable environment = Some sigma ->
  In variable (map fst environment).
Proof.
  intros variable environment.
  induction environment as [| [name annotation] environment IH];
    intro sigma; cbn [in_ctx].
  - discriminate.
  - destruct (eq_id_dec name variable) as [Hequal | Hdifferent].
    + intro Hlookup.
      now left.
    + intro Hlookup.
      right.
      now apply IH with sigma.
Qed.

Lemma has_type_names_scoped : forall environment expression tau,
  has_type environment expression tau ->
  hm_names_scoped (map fst environment) expression.
Proof.
  intros environment expression tau Htyping.
  induction Htyping;
    cbn [hm_names_scoped].
  - exact I.
  - now apply in_ctx_some_name with sigma.
  - exact IHHtyping.
  - now split.
  - now split.
Qed.

Lemma apply_subst_ctx_names : forall substitution environment,
  map fst (apply_subst_ctx substitution environment) =
  map fst environment.
Proof.
  intros substitution environment.
  induction environment as [| [variable sigma] environment IH].
  - reflexivity.
  - cbn [apply_subst_ctx map].
    now rewrite IH.
Qed.


(** The central preservation invariant.  It is deliberately stated for an
    arbitrary HM environment and an arbitrary scoped interpretation of W's
    metavariables; the closed principal-type theorem below is just its
    empty-context instance.  In particular, successful W construction also
    proves that semantic reification cannot fail. *)
Theorem W_elab_semantic_type_preservation : forall
    expression environment state tau substitution state' tree
    constants valuation depth,
  constants_closed constants ->
  valuation_scoped depth valuation ->
  W_elab expression environment state =
    w_elab_state_success tau substitution state' tree ->
  { raw : RawChurch &
    (reify_w_elab_tree_semantic constants valuation
      (map fst environment) tree = Ok raw) *
    RawTyping depth
      (denote_context constants
        (valuation_after_substitution constants substitution valuation)
        environment)
      raw (denote_monotype constants valuation tau) }%type.
Proof.
  induction expression as
      [variable
      | function IHfunction argument IHargument
      | variable bound IHbound body IHbody
      | variable body IHbody
      | constant];
    intros environment state tau substitution state' tree
      constants valuation depth Hconstants Hvaluation Hrun;
    cbn [W_elab] in Hrun.
  - destruct (in_ctx variable environment) as [sigma |] eqn:Hlookup;
      try discriminate.
    remember (compute_inst_subst state (max_gen_vars sigma))
      as instantiation eqn:Hinstantiation.
    destruct (apply_inst_subst instantiation sigma)
      as [instance |] eqn:Hinstance; try discriminate.
    inversion Hrun; subst tau substitution state' tree.
    destruct (lookup_binder_denote_context_sig
      constants valuation environment variable sigma Hlookup)
      as [index [Hbinder Hindex]].
    assert (Hlength : length instantiation = max_gen_vars sigma).
    { subst instantiation.
      apply length_compute_inst_subst. }
    assert (Hdenotation_length :
      length (denote_instantiation constants valuation instantiation) =
      max_gen_vars sigma).
    { rewrite denote_instantiation_is_map, map_length.
      exact Hlength. }
    exists
      (apply_type_arguments (RCVar index)
        (denote_instantiation constants valuation instantiation)).
    split.
    + cbn [reify_w_elab_tree_semantic].
      now rewrite Hbinder.
    + replace
        (denote_context constants
          (valuation_after_substitution constants [] valuation) environment)
        with (denote_context constants valuation environment).
      2: {
        apply denote_context_valuation_ext.
        intro meta.
        unfold valuation_after_substitution.
        now rewrite apply_subst_nil. }
      rewrite <- (denote_scheme_instantiation
        constants valuation sigma instantiation instance
        Hconstants Hlength Hinstance).
      rewrite <- denote_instantiation_is_map.
      unfold denote_scheme.
      rewrite <- Hdenotation_length.
      apply raw_typing_apply_type_arguments.
      * intros T HT.
        rewrite denote_instantiation_is_map in HT.
        apply in_map_iff in HT.
        destruct HT as [argument [HT Hargument]].
        subst T.
        now apply denote_monotype_scoped.
      * apply RawTypingVar.
        unfold denote_scheme in Hindex.
        rewrite <- Hdenotation_length in Hindex.
        exact Hindex.

  - destruct (W_elab function environment state)
      as [function_type function_substitution function_state function_tree
          | function_failure]
      eqn:Hfunction; try discriminate.
    destruct (W_elab argument
        (apply_subst_ctx function_substitution environment) function_state)
      as [argument_type argument_substitution argument_state argument_tree
          | argument_failure]
      eqn:Hargument; try discriminate.
    remember (apply_subst argument_substitution function_type) as left.
    remember (arrow argument_type (var argument_state)) as right.
    destruct (unify_exec left right) as [unifier |]
      eqn:Hunification; try discriminate.
    inversion Hrun; subst tau substitution state' tree.
    assert (Hargument_substitution :
      w_elab_tree_substitution argument_tree = argument_substitution).
    { now apply W_elab_tree_substitution_contract with
        (expression := argument)
        (environment := apply_subst_ctx function_substitution environment)
        (state := function_state) (tau := argument_type)
        (state' := argument_state). }
    assert (Hfunction_valuation :
      valuation_scoped depth
        (valuation_after_substitution constants
          (compose_subst argument_substitution unifier) valuation)).
    { now apply valuation_after_substitution_scoped. }
    destruct (IHfunction environment state function_type
      function_substitution function_state function_tree constants
      (valuation_after_substitution constants
        (compose_subst argument_substitution unifier) valuation)
      depth Hconstants Hfunction_valuation Hfunction)
      as [function_raw [Hfunction_reification Hfunction_typing]].
    assert (Hargument_valuation :
      valuation_scoped depth
        (valuation_after_substitution constants unifier valuation)).
    { now apply valuation_after_substitution_scoped. }
    destruct (IHargument
      (apply_subst_ctx function_substitution environment) function_state
      argument_type argument_substitution argument_state argument_tree
      constants
      (valuation_after_substitution constants unifier valuation)
      depth Hconstants Hargument_valuation Hargument)
      as [argument_raw [Hargument_reification Hargument_typing]].
    rewrite apply_subst_ctx_names in Hargument_reification.
    exists (RCApp function_raw argument_raw).
    split.
    + cbn [reify_w_elab_tree_semantic].
      rewrite Hargument_substitution.
      now rewrite Hfunction_reification, Hargument_reification.
    + assert (Hfunction_context :
        denote_context constants
          (valuation_after_substitution constants function_substitution
            (valuation_after_substitution constants
              (compose_subst argument_substitution unifier) valuation))
          environment =
        denote_context constants
          (valuation_after_substitution constants
            (compose_subst function_substitution
              (compose_subst argument_substitution unifier)) valuation)
          environment).
      { symmetry.
        apply denote_context_after_compose. }
      rewrite Hfunction_context in Hfunction_typing.
      assert (Hargument_context :
        denote_context constants
          (valuation_after_substitution constants argument_substitution
            (valuation_after_substitution constants unifier valuation))
          (apply_subst_ctx function_substitution environment) =
        denote_context constants
          (valuation_after_substitution constants
            (compose_subst function_substitution
              (compose_subst argument_substitution unifier)) valuation)
          environment).
      { transitivity
          (denote_context constants
            (valuation_after_substitution constants
              (compose_subst argument_substitution unifier) valuation)
            (apply_subst_ctx function_substitution environment)).
        - symmetry. apply denote_context_after_compose.
        - transitivity
            (denote_context constants
              (valuation_after_substitution constants function_substitution
                (valuation_after_substitution constants
                  (compose_subst argument_substitution unifier) valuation))
              environment).
          + symmetry.
            now apply denote_context_after_substitution.
          + symmetry.
            apply denote_context_after_compose. }
      rewrite Hargument_context in Hargument_typing.
      assert (Hunifier : is_unifier left right unifier).
      { now apply unify_exec_success_sound. }
      unfold is_unifier in Hunifier.
      assert (Hfunction_type :
        denote_monotype constants
          (valuation_after_substitution constants
            (compose_subst argument_substitution unifier) valuation)
          function_type =
        TArrow
          (denote_monotype constants
            (valuation_after_substitution constants unifier valuation)
            argument_type)
          (denote_monotype constants valuation
            (apply_subst unifier (var argument_state)))).
      { rewrite denote_monotype_after_substitution.
        rewrite apply_compose_equiv.
        rewrite <- Heqleft, Hunifier, Heqright.
        cbn [apply_subst denote_monotype].
        now rewrite denote_monotype_after_substitution. }
      rewrite Hfunction_type in Hfunction_typing.
      now apply RawTypingApp with
        (A := denote_monotype constants
          (valuation_after_substitution constants unifier valuation)
          argument_type).
  - destruct (W_elab bound environment state)
      as [bound_type bound_substitution bound_state bound_tree
          | bound_failure]
      eqn:Hbound; try discriminate.
    remember (apply_subst_ctx bound_substitution environment)
      as bound_environment eqn:Hbound_environment.
    destruct (generalize_for_elaboration bound_type bound_environment)
      as [sigma generalized] eqn:Hgeneralization.
    subst bound_environment.
    destruct (W_elab body
        ((variable, sigma) :: apply_subst_ctx bound_substitution environment)
        bound_state)
      as [body_type body_substitution body_state body_tree | body_failure]
      eqn:Hbody; try discriminate.
    cbn [fst snd] in Hrun.
    rewrite Hbody in Hrun.
    inversion Hrun; subst tau substitution state' tree.
    assert (Hbody_substitution :
      w_elab_tree_substitution body_tree = body_substitution).
    { now apply W_elab_tree_substitution_contract with
        (expression := body)
        (environment :=
          (variable, sigma) :: apply_subst_ctx bound_substitution environment)
        (state := bound_state) (tau := body_type)
        (state' := body_state). }
    assert (Hbody_valuation :
      valuation_scoped depth
        (valuation_after_substitution constants body_substitution valuation)).
    { now apply valuation_after_substitution_scoped. }
    assert (Hbound_valuation :
      valuation_scoped (length generalized + depth)
        (generalized_valuation generalized
          (valuation_after_substitution constants body_substitution
            valuation))).
    { now apply generalized_valuation_scoped. }
    destruct (IHbound environment state bound_type bound_substitution
      bound_state bound_tree constants
      (generalized_valuation generalized
        (valuation_after_substitution constants body_substitution valuation))
      (length generalized + depth) Hconstants Hbound_valuation Hbound)
      as [bound_raw [Hbound_reification Hbound_typing]].
    destruct (IHbody
      ((variable, sigma) :: apply_subst_ctx bound_substitution environment)
      bound_state
      body_type body_substitution body_state body_tree constants valuation
      depth Hconstants Hvaluation Hbody)
      as [body_raw [Hbody_reification Hbody_typing]].
    cbn [map fst] in Hbody_reification.
    rewrite apply_subst_ctx_names in Hbody_reification.
    exists
      (RCApp
        (RCAbs
          (denote_scheme constants
            (valuation_after_substitution constants body_substitution
              valuation) sigma)
          body_raw)
        (wrap_type_abstractions generalized bound_raw)).
    split.
    + cbn [reify_w_elab_tree_semantic].
      rewrite Hbody_substitution.
      now rewrite Hbound_reification, Hbody_reification.
    + assert (Hbody_context :
        denote_context constants
          (valuation_after_substitution constants body_substitution valuation)
          (apply_subst_ctx bound_substitution environment) =
        denote_context constants
          (valuation_after_substitution constants
            (compose_subst bound_substitution body_substitution) valuation)
          environment).
      { transitivity
          (denote_context constants
            (valuation_after_substitution constants bound_substitution
              (valuation_after_substitution constants body_substitution
                valuation)) environment).
        - symmetry.
          now apply denote_context_after_substitution.
        - symmetry.
          apply denote_context_after_compose. }
      cbn [denote_context] in Hbody_typing.
      rewrite Hbody_context in Hbody_typing.
      assert (Hgeneralization_disjoint :
        are_disjoints
          (FV_ctx (apply_subst_ctx bound_substitution environment))
          generalized).
      { now apply generalize_for_elaboration_disjoint with
          (tau := bound_type) (sigma := sigma). }
      assert (Hbound_context :
        denote_context constants
          (valuation_after_substitution constants bound_substitution
            (generalized_valuation generalized
              (valuation_after_substitution constants body_substitution
                valuation))) environment =
        lift_type_context_by (length generalized)
          (denote_context constants
            (valuation_after_substitution constants
              (compose_subst bound_substitution body_substitution) valuation)
            environment)).
      { transitivity
          (denote_context constants
            (generalized_valuation generalized
              (valuation_after_substitution constants body_substitution
                valuation))
            (apply_subst_ctx bound_substitution environment)).
        - now apply denote_context_after_substitution.
        - rewrite (denote_context_generalized constants
            (valuation_after_substitution constants body_substitution valuation)
            (apply_subst_ctx bound_substitution environment) generalized
            Hconstants Hgeneralization_disjoint).
          now rewrite Hbody_context. }
      rewrite Hbound_context in Hbound_typing.
      rewrite (generalize_for_elaboration_denotation
        bound_type (apply_subst_ctx bound_substitution environment)
        sigma generalized constants
        (valuation_after_substitution constants body_substitution valuation)
        Hgeneralization) in Hbound_typing.
      assert (Hgeneralization_length :
        length generalized = max_gen_vars sigma).
      { now apply generalize_for_elaboration_length with
          (tau := bound_type)
          (environment := apply_subst_ctx bound_substitution environment). }
      assert (Hbound_polymorphic :
        RawTyping depth
          (denote_context constants
            (valuation_after_substitution constants
              (compose_subst bound_substitution body_substitution) valuation)
            environment)
          (wrap_type_abstractions generalized bound_raw)
          (denote_scheme constants
            (valuation_after_substitution constants body_substitution valuation)
            sigma)).
      { unfold denote_scheme.
        rewrite <- Hgeneralization_length.
        now apply raw_typing_wrap_type_abstractions. }
      apply RawTypingApp with
        (A := denote_scheme constants
          (valuation_after_substitution constants body_substitution valuation)
          sigma).
      * apply RawTypingAbs.
        -- apply denote_scheme_scoped.
           ++ exact Hconstants.
           ++ exact Hbody_valuation.
        -- exact Hbody_typing.
      * exact Hbound_polymorphic.
    + cbn [fst snd] in Hrun.
      rewrite Hbody in Hrun.
      discriminate.
  - destruct (W_elab body
      ((variable, ty_to_schm (var state)) :: environment) (S state))
      as [body_type body_substitution body_state body_tree | body_failure]
      eqn:Hbody; try discriminate.
    inversion Hrun; subst tau substitution state' tree.
    destruct (IHbody
      ((variable, ty_to_schm (var state)) :: environment) (S state)
      body_type body_substitution body_state body_tree
      constants valuation depth Hconstants Hvaluation Hbody)
      as [body_raw [Hbody_reification Hbody_typing]].
    cbn [map fst] in Hbody_reification.
    exists
      (RCAbs
        (denote_monotype constants valuation
          (apply_subst body_substitution (var state)))
        body_raw).
    split.
    + cbn [reify_w_elab_tree_semantic].
      now rewrite Hbody_reification.
    + apply RawTypingAbs.
      * now apply denote_monotype_scoped.
      * cbn [denote_context] in Hbody_typing.
        unfold denote_scheme in Hbody_typing.
        cbn [ty_to_schm max_gen_vars quantify_type denote_scheme_body]
          in Hbody_typing.
        rewrite lift_type_by_zero in Hbody_typing.
        exact Hbody_typing.
  - discriminate.
Qed.

Corollary runW_elab_semantic_type_preservation : forall
    expression environment tau substitution tree
    constants valuation depth,
  constants_closed constants ->
  valuation_scoped depth valuation ->
  runW_elab expression environment = elaborated tau substitution tree ->
  { raw : RawChurch &
    (reify_w_elab_tree_semantic constants valuation
      (map fst environment) tree = Ok raw) *
    RawTyping depth
      (denote_context constants
        (valuation_after_substitution constants substitution valuation)
        environment)
      raw (denote_monotype constants valuation tau) }%type.
Proof.
  intros expression environment tau substitution tree
    constants valuation depth Hconstants Hvaluation Hrun.
  unfold runW_elab in Hrun.
  destruct (W_elab expression environment
    (initial_state_exec environment))
    as [tau' substitution' state' tree' | failure]
    eqn:Helaboration; try discriminate.
  inversion Hrun; subst tau substitution tree.
  now apply W_elab_semantic_type_preservation with
    (expression := expression) (environment := environment)
      (state := initial_state_exec environment) (state' := state').
Qed.

Lemma quantify_type_is_quantify_scheme : forall count body,
  quantify_type count body = quantify_scheme count body.
Proof.
  induction count as [| count IH]; intro body.
  - reflexivity.
  - cbn [quantify_type quantify_scheme].
    now rewrite IH.
Qed.

Lemma denote_scheme_body_without_free_variables : forall
    constants valuation resolve sigma quantifier_count,
  free_variables_scoped 0 resolve sigma ->
  denote_scheme_body constants valuation quantifier_count sigma =
  scheme_body_to_type constants resolve quantifier_count sigma.
Proof.
  intros constants valuation resolve sigma.
  induction sigma as
      [variable | name | variable | domain IHdomain codomain IHcodomain];
    intros quantifier_count Hfree;
    cbn [free_variables_scoped denote_scheme_body scheme_body_to_type] in *.
  - lia.
  - reflexivity.
  - reflexivity.
  - destruct Hfree as [Hdomain Hcodomain].
    now rewrite (IHdomain quantifier_count Hdomain),
      (IHcodomain quantifier_count Hcodomain).
Qed.

Lemma denote_scheme_without_free_variables : forall
    constants valuation resolve sigma,
  free_variables_scoped 0 resolve sigma ->
  denote_scheme constants valuation sigma =
  scheme_to_systemf constants resolve sigma.
Proof.
  intros constants valuation resolve sigma Hfree.
  unfold denote_scheme, scheme_to_systemf.
  rewrite quantify_type_is_quantify_scheme.
  f_equal.
  now apply denote_scheme_body_without_free_variables.
Qed.

Lemma generalized_principal_scheme_denotation : forall
    constants tau sigma generalized,
  generalize_for_elaboration tau [] = (sigma, generalized) ->
  denote_scheme constants reification_default_valuation sigma =
  hm_principal_type constants tau.
Proof.
  intros constants tau sigma generalized Hgeneralization.
  unfold hm_principal_type, hm_principal_scheme.
  assert (Hscheme : sigma = gen_ty tau []).
  { symmetry.
    rewrite <- generalize_for_elaboration_scheme.
    now rewrite Hgeneralization. }
  subst sigma.
  apply denote_scheme_without_free_variables.
  apply gen_ty_empty_free_variables_scoped.
Qed.

Theorem W_elab_success_names_scoped : forall expression environment state
    tau substitution state' tree,
  W_elab expression environment state =
    w_elab_state_success tau substitution state' tree ->
  hm_names_scoped (map fst environment) expression.
Proof.
  induction expression as
      [variable
      | function IHfunction argument IHargument
      | variable bound IHbound body IHbody
      | variable body IHbody
      | constant];
    intros environment state tau substitution state' tree Helaboration;
    cbn [W_elab] in Helaboration.
  - destruct (in_ctx variable environment)
      as [sigma |] eqn:Hlookup; try discriminate.
    destruct (apply_inst_subst
      (compute_inst_subst state (max_gen_vars sigma)) sigma)
      as [instance |] eqn:Hinstance; try discriminate.
    now apply in_ctx_some_name with sigma.

  - destruct (W_elab function environment state)
      as [tau1 s1 state1 function_tree | function_failure]
      eqn:Hfunction; try discriminate.
    destruct (W_elab argument (apply_subst_ctx s1 environment) state1)
      as [tau2 s2 state2 argument_tree | argument_failure]
      eqn:Hargument; try discriminate.
    destruct (unify_exec (apply_subst s2 tau1)
      (arrow tau2 (var state2))) as [unifier |]
      eqn:Hunify; try discriminate.
    cbn [hm_names_scoped].
    split.
    + now apply IHfunction with
        (state := state) (tau := tau1) (substitution := s1)
        (state' := state1) (tree := function_tree).
    + pose proof
        (IHargument (apply_subst_ctx s1 environment) state1
          tau2 s2 state2 argument_tree Hargument) as Hscope.
      now rewrite apply_subst_ctx_names in Hscope.

  - destruct (W_elab bound environment state)
      as [tau1 s1 state1 bound_tree | bound_failure]
      eqn:Hbound; try discriminate.
    destruct (generalize_for_elaboration tau1
      (apply_subst_ctx s1 environment))
      as [sigma generalized] eqn:Hgeneralization.
    cbn [fst snd] in Helaboration.
    destruct (W_elab body
      ((variable, sigma) :: apply_subst_ctx s1 environment) state1)
      as [tau2 s2 state2 body_tree | body_failure]
      eqn:Hbody; try discriminate.
    cbn [hm_names_scoped].
    split.
    + now apply IHbound with
        (state := state) (tau := tau1) (substitution := s1)
        (state' := state1) (tree := bound_tree).
    + pose proof
        (IHbody ((variable, sigma) :: apply_subst_ctx s1 environment)
          state1 tau2 s2 state2 body_tree Hbody) as Hscope.
      cbn [map fst] in Hscope.
      rewrite apply_subst_ctx_names in Hscope.
      exact Hscope.

  - destruct (W_elab body
      ((variable, ty_to_schm (var state)) :: environment) (S state))
      as [body_type body_substitution body_state body_tree | body_failure]
      eqn:Hbody; try discriminate.
    cbn [hm_names_scoped].
    pose proof
      (IHbody ((variable, ty_to_schm (var state)) :: environment)
        (S state) body_type body_substitution body_state body_tree Hbody)
      as Hscope.
    cbn [map] in Hscope.
    exact Hscope.

  - discriminate.
Qed.

Corollary runW_elab_success_names_scoped : forall
    expression environment tau substitution tree,
  runW_elab expression environment =
    elaborated tau substitution tree ->
  hm_names_scoped (map fst environment) expression.
Proof.
  intros expression environment tau substitution tree Helaboration.
  unfold runW_elab in Helaboration.
  destruct (W_elab expression environment
    (initial_state_exec environment))
    as [tau' substitution' state tree' | failure]
    eqn:Htree; try discriminate.
  inversion Helaboration; subst tau' substitution' tree'.
  now apply W_elab_success_names_scoped with
    (state := initial_state_exec environment)
    (tau := tau) (substitution := substitution)
    (state' := state) (tree := tree).
Qed.


Record RawChurchElaboration : Type := {
  raw_church_hm_type : ty;
  raw_church_substitution : substitution;
  raw_church_tree : WElabTree;
  raw_church_systemf_type : type;
  raw_church_term : RawChurch
}.

Lemma runW_elab_success_erases : forall expression tau substitution tree,
  runW_elab expression [] = elaborated tau substitution tree ->
  exists erased, erase_hm_closed expression = Some erased.
Proof.
  intros expression tau substitution tree Helaboration.
  assert (Hfragment : constant_free expression).
  { now apply runW_elab_success_constant_free
      with (environment := []) (tau := tau)
        (substitution := substitution) (tree := tree). }
  apply (proj2 (erase_hm_closed_success_iff expression)).
  split; [exact Hfragment |].
  exact
    (runW_elab_success_names_scoped
      expression [] tau substitution tree Helaboration).
Qed.

(** The unchecked builder retains the error sum of W and the general semantic
    reifier.  Reification failure is impossible after a successful closed W
    elaboration, as proved by [runWChurch_unchecked_complete]; [runWChurch]
    below additionally installs the independent checker as the public
    type-safety boundary. *)
Definition runWChurch_unchecked
    (constants : ConstantInterpretation)
    (expression : term)
    : Result WChurchError RawChurchElaboration :=
  match runW_elab expression [] with
  | elaboration_rejected failure =>
      Err (church_inference_failure failure)
  | elaborated tau final_substitution tree =>
      let generalization := generalize_for_elaboration tau [] in
      let generalized := snd generalization in
      match reify_w_elab_tree_semantic constants
          (generalized_valuation generalized reification_default_valuation)
          [] tree with
      | Err error => Err (church_reification_failure error)
      | Ok body =>
          Ok
            {| raw_church_hm_type := tau;
               raw_church_substitution := final_substitution;
               raw_church_tree := tree;
               raw_church_systemf_type :=
                 hm_principal_type constants tau;
               raw_church_term :=
                 wrap_type_abstractions generalized body |}
      end
  end.

Theorem reify_w_elab_tree_semantic_total_from_erasure : forall
    constants valuation term_variables tree erased,
  erase_hm term_variables (w_elab_tree_source tree) = Some erased ->
  exists raw,
    reify_w_elab_tree_semantic constants valuation term_variables tree =
      Ok raw.
Proof.
  intros constants valuation term_variables tree.
  revert constants valuation term_variables.
  induction tree as
      [variable sigma instantiation instance
      | variable alpha parameter body IHbody
      | function IHfunction argument IHargument
          alpha left right unifier result
      | variable bound_type generalized sigma
          bound IHbound body IHbody];
    intros constants valuation term_variables erased Herasure;
    cbn [w_elab_tree_source erase_hm] in Herasure.
  - destruct (lookup_binder variable term_variables)
      as [index |] eqn:Hlookup; try discriminate.
    exists
      (apply_type_arguments (RCVar index)
        (denote_instantiation constants valuation instantiation)).
    cbn [reify_w_elab_tree_semantic].
    now rewrite Hlookup.
  - destruct (erase_hm (variable :: term_variables)
      (w_elab_tree_source body)) as [body_erased |]
      eqn:Herase_body; try discriminate.
    destruct (IHbody constants valuation (variable :: term_variables)
      body_erased Herase_body) as [body' Hbody].
    exists (RCAbs (denote_monotype constants valuation parameter) body').
    cbn [reify_w_elab_tree_semantic].
    now rewrite Hbody.
  - destruct (erase_hm term_variables (w_elab_tree_source function))
      as [function_erased |] eqn:Herase_function; try discriminate.
    destruct (erase_hm term_variables (w_elab_tree_source argument))
      as [argument_erased |] eqn:Herase_argument; try discriminate.
    destruct (IHfunction constants
      (valuation_after_substitution constants
        (compose_subst (w_elab_tree_substitution argument) unifier)
        valuation)
      term_variables function_erased Herase_function)
      as [function' Hfunction].
    destruct (IHargument constants
      (valuation_after_substitution constants unifier valuation)
      term_variables argument_erased Herase_argument)
      as [argument' Hargument].
    exists (RCApp function' argument').
    cbn [reify_w_elab_tree_semantic].
    now rewrite Hfunction, Hargument.
  - destruct (erase_hm term_variables (w_elab_tree_source bound))
      as [bound_erased |] eqn:Herase_bound; try discriminate.
    destruct (erase_hm (variable :: term_variables)
      (w_elab_tree_source body)) as [body_erased |]
      eqn:Herase_body; try discriminate.
    set (body_valuation := valuation_after_substitution constants
      (w_elab_tree_substitution body) valuation).
    destruct (IHbound constants
      (generalized_valuation generalized body_valuation)
      term_variables bound_erased Herase_bound) as [bound' Hbound].
    destruct (IHbody constants valuation (variable :: term_variables)
      body_erased Herase_body) as [body' Hbody].
    exists
      (RCApp
        (RCAbs (denote_scheme constants body_valuation sigma) body')
        (wrap_type_abstractions generalized bound')).
    cbn [reify_w_elab_tree_semantic].
    fold body_valuation.
    now rewrite Hbound, Hbody.
Qed.

(** Type defaulting removes the only type-level reification failure.  A
    successful closed W elaboration also supplies term-variable scope, so
    the unchecked Church builder is complete for successful [runW_elab]. *)
Theorem runWChurch_unchecked_complete : forall
    constants expression tau final_substitution tree,
  runW_elab expression [] =
    elaborated tau final_substitution tree ->
  exists elaboration,
    runWChurch_unchecked constants expression = Ok elaboration.
Proof.
  intros constants expression tau final_substitution tree Helaboration.
  destruct (runW_elab_success_erases
      expression tau final_substitution tree Helaboration)
    as [erased Herasure].
  pose proof
    (runW_elab_tree_contract expression []
      tau final_substitution tree Helaboration) as [Hsource Htype].
  unfold erase_hm_closed in Herasure.
  rewrite <- Hsource in Herasure.
  destruct (generalize_for_elaboration tau [])
    as [sigma generalized] eqn:Hgeneralization.
  destruct (reify_w_elab_tree_semantic_total_from_erasure constants
      (generalized_valuation generalized reification_default_valuation)
      [] tree erased Herasure)
    as [body Hreification].
  unfold runWChurch_unchecked.
  rewrite Helaboration, Hgeneralization.
  cbn [snd].
  rewrite Hreification.
  eexists.
  reflexivity.
Qed.

Theorem runWChurch_unchecked_type_preservation : forall
    constants expression elaboration,
  constants_closed constants ->
  runWChurch_unchecked constants expression = Ok elaboration ->
  RawTyping 0 [] (raw_church_term elaboration)
    (hm_principal_type constants (raw_church_hm_type elaboration)).
Proof.
  intros constants expression elaboration Hconstants Hchurch.
  unfold runWChurch_unchecked in Hchurch.
  destruct (runW_elab expression [])
    as [tau final_substitution tree | failure]
    eqn:Helaboration; try discriminate.
  destruct (generalize_for_elaboration tau [])
    as [sigma generalized] eqn:Hgeneralization.
  destruct (reify_w_elab_tree_semantic constants
    (generalized_valuation generalized reification_default_valuation)
    [] tree) as [body | error] eqn:Hreification.
  2: {
    cbn [snd] in Hchurch.
    rewrite Hreification in Hchurch.
    discriminate. }
  cbn [snd] in Hchurch.
  rewrite Hreification in Hchurch.
  inversion Hchurch; subst elaboration.
  destruct (runW_elab_semantic_type_preservation
    expression [] tau final_substitution tree constants
    (generalized_valuation generalized reification_default_valuation)
    (length generalized) Hconstants)
    as [semantic_body [Hsemantic_reification Hsemantic_typing]].
  - replace (length generalized) with (length generalized + 0) by lia.
    apply generalized_valuation_scoped.
    apply reification_default_valuation_scoped.
  - exact Helaboration.
  - cbn [map fst] in Hsemantic_reification.
    rewrite Hreification in Hsemantic_reification.
    inversion Hsemantic_reification; subst semantic_body.
    cbn [denote_context raw_church_term raw_church_hm_type]
      in Hsemantic_typing |- *.
    replace (length generalized) with (length generalized + 0)
      in Hsemantic_typing by lia.
    change
      (RawTyping (length generalized + 0)
        (lift_type_context_by (length generalized) []) body
        (denote_monotype constants
          (generalized_valuation generalized reification_default_valuation)
          tau)) in Hsemantic_typing.
    pose proof (raw_typing_wrap_type_abstractions
      generalized 0 [] body
      (denote_monotype constants
        (generalized_valuation generalized reification_default_valuation)
        tau) Hsemantic_typing) as Hwrapped.
    rewrite (generalize_for_elaboration_denotation
      tau [] sigma generalized constants reification_default_valuation
      Hgeneralization) in Hwrapped.
    rewrite <- (generalized_principal_scheme_denotation
      constants tau sigma generalized Hgeneralization).
    unfold denote_scheme.
    rewrite <- (generalize_for_elaboration_length
      tau [] sigma generalized Hgeneralization).
    exact Hwrapped.
Qed.

(** Every term constructed by the W-to-Church frontend is accepted by the
    independent kernel checker, and the checker's synthesized type is
    exactly W's generalized principal type. *)
Theorem runWChurch_unchecked_checkClosed_principal : forall
    constants expression elaboration,
  constants_closed constants ->
  runWChurch_unchecked constants expression = Ok elaboration ->
  exists checked : Checked 0 [] (raw_church_term elaboration),
    checkClosed (raw_church_term elaboration) = Ok checked /\
    projT1 checked =
      hm_principal_type constants (raw_church_hm_type elaboration).
Proof.
  intros constants expression elaboration Hconstants Hchurch.
  apply raw_typing_checkClosed.
  exact (runWChurch_unchecked_type_preservation
    constants expression elaboration Hconstants Hchurch).
Qed.

Corollary runWChurch_unchecked_scoped : forall
    constants expression elaboration,
  constants_closed constants ->
  runWChurch_unchecked constants expression = Ok elaboration ->
  scoped 0 (raw_church_term elaboration).
Proof.
  intros constants expression elaboration Hconstants Hchurch.
  pose proof (runWChurch_unchecked_type_preservation
    constants expression elaboration Hconstants Hchurch) as Htyping.
  destruct (raw_typing_scope_and_type 0 []
    (raw_church_term elaboration)
    (hm_principal_type constants (raw_church_hm_type elaboration))
    Htyping (Forall_nil _)) as [_ Hscoped].
  exact Hscoped.
Qed.

Theorem runWChurch_unchecked_success_iff_runW_elab_success : forall
    constants expression,
  (exists elaboration,
    runWChurch_unchecked constants expression = Ok elaboration) <->
  exists tau final_substitution tree,
    runW_elab expression [] =
      elaborated tau final_substitution tree.
Proof.
  intros constants expression.
  split.
  - intros [elaboration Hchurch].
    unfold runWChurch_unchecked in Hchurch.
    destruct (runW_elab expression [])
      as [tau final_substitution tree | failure]
      eqn:Helaboration; try discriminate.
    now exists tau, final_substitution, tree.
  - intros [tau [final_substitution [tree Helaboration]]].
    now apply runWChurch_unchecked_complete
      with (tau := tau) (final_substitution := final_substitution)
        (tree := tree).
Qed.

Record CheckedChurchElaboration : Type := {
  checked_church_elaboration : RawChurchElaboration;
  checked_church_certificate :
    Checked 0 [] (raw_church_term checked_church_elaboration);
  checked_church_type :
    projT1 checked_church_certificate =
    raw_church_systemf_type checked_church_elaboration
}.

(** Retain the intrinsic [fterm] built by [checkClosed], rather than merely
    using the checker as a Boolean guard.  The equality proof is erased by
    extraction; the checked type and intrinsic term remain available to the
    evaluator and the later bound bridge. *)
Definition certify_raw_church_elaboration
    (elaboration : RawChurchElaboration)
    : Result WChurchError CheckedChurchElaboration :=
  match checkClosed (raw_church_term elaboration) with
  | Err error => Err (church_checker_failure error)
  | Ok checked =>
      let inferred_type := projT1 checked in
      let expected_type := raw_church_systemf_type elaboration in
      match type_eq_dec inferred_type expected_type with
      | left equality =>
          Ok
            {| checked_church_elaboration := elaboration;
               checked_church_certificate := checked;
               checked_church_type := equality |}
      | right _ =>
          Err
            (church_checker_type_mismatch
              expected_type inferred_type)
      end
  end.

Definition erase_checked_church_result
    (result : Result WChurchError CheckedChurchElaboration)
    : Result WChurchError RawChurchElaboration :=
  match result with
  | Ok checked => Ok (checked_church_elaboration checked)
  | Err error => Err error
  end.

Definition validate_raw_church_elaboration
    (elaboration : RawChurchElaboration)
    : Result WChurchError RawChurchElaboration :=
  erase_checked_church_result
    (certify_raw_church_elaboration elaboration).

(** Proof-carrying closed bridge used by downstream consumers. *)
Definition runWChurchChecked
    (constants : ConstantInterpretation)
    (expression : term)
    : Result WChurchError CheckedChurchElaboration :=
  match runWChurch_unchecked constants expression with
  | Err error => Err error
  | Ok elaboration => certify_raw_church_elaboration elaboration
  end.

(** Public raw projection.  Its successful branch has passed both structural
    reification and the independent Church checker; [runWChurchChecked]
    exposes the retained certificate when an intrinsic term is needed. *)
Definition runWChurch
    (constants : ConstantInterpretation)
    (expression : term)
    : Result WChurchError RawChurchElaboration :=
  erase_checked_church_result
    (runWChurchChecked constants expression).

Theorem runWChurch_checked_correspondence : forall constants expression,
  erase_checked_church_result (runWChurchChecked constants expression) =
  runWChurch constants expression.
Proof. reflexivity. Qed.

(** ** Type correspondence of the W-to-Church bridge *)

Lemma validate_raw_church_elaboration_success : forall elaboration result,
  validate_raw_church_elaboration elaboration = Ok result ->
  result = elaboration /\
  exists checked : Checked 0 [] (raw_church_term elaboration),
    checkClosed (raw_church_term elaboration) = Ok checked /\
    projT1 checked = raw_church_systemf_type elaboration.
Proof.
  intros elaboration result Hvalidate.
  unfold validate_raw_church_elaboration,
    certify_raw_church_elaboration,
    erase_checked_church_result in Hvalidate.
  destruct (checkClosed (raw_church_term elaboration))
    as [checked | error] eqn:Hcheck; try discriminate.
  destruct (type_eq_dec
      (projT1 checked) (raw_church_systemf_type elaboration))
    as [Hequal | Hunequal]; try discriminate.
  inversion Hvalidate; subst result.
  split.
  - reflexivity.
  - exists checked.
    now split.
Qed.

Theorem runWChurch_unchecked_W_contract : forall
    constants expression elaboration,
  runWChurch_unchecked constants expression = Ok elaboration ->
  runW_exec expression [] =
    inferred
      (raw_church_hm_type elaboration)
      (raw_church_substitution elaboration) /\
  raw_church_systemf_type elaboration =
    hm_principal_type constants (raw_church_hm_type elaboration).
Proof.
  intros constants expression elaboration Hchurch.
  unfold runWChurch_unchecked in Hchurch.
  destruct (runW_elab expression [])
    as [tau final_substitution tree | failure] eqn:Helaboration;
    try discriminate.
  destruct (generalize_for_elaboration tau [])
    as [sigma generalized] eqn:Hgeneralization.
  destruct (reify_w_elab_tree_semantic constants
      (generalized_valuation generalized reification_default_valuation)
      [] tree) as [body | error] eqn:Hreification;
    try discriminate.
  all: cbn in Hchurch; rewrite Hreification in Hchurch.
  - inversion Hchurch; subst elaboration.
    assert (Hfragment : constant_free expression).
    { exact
        (runW_elab_success_constant_free
          expression [] tau final_substitution tree Helaboration). }
    pose proof (runW_elab_erases expression [] Hfragment) as Hinference.
    rewrite Helaboration in Hinference.
    cbn [erase_w_elab_result] in Hinference.
    split.
    + symmetry. exact Hinference.
    + reflexivity.
  - discriminate.
Qed.

(** Consequently the public checker boundary cannot turn a successful W
    elaboration into a checker error or a type-mismatch error. *)
Theorem runWChurch_complete_for_successful_W : forall
    constants expression tau final_substitution tree,
  constants_closed constants ->
  runW_elab expression [] = elaborated tau final_substitution tree ->
  exists elaboration,
    runWChurch constants expression = Ok elaboration.
Proof.
  intros constants expression tau final_substitution tree
    Hconstants Helaboration.
  destruct (runWChurch_unchecked_complete constants expression tau
    final_substitution tree Helaboration) as [elaboration Hunchecked].
  destruct (runWChurch_unchecked_checkClosed_principal
    constants expression elaboration Hconstants Hunchecked)
    as [checked [Hcheck Hchecked_type]].
  destruct (runWChurch_unchecked_W_contract
    constants expression elaboration Hunchecked)
    as [_ Helaboration_type].
  unfold runWChurch, runWChurchChecked.
  rewrite Hunchecked.
  unfold certify_raw_church_elaboration, erase_checked_church_result.
  rewrite Hcheck.
  destruct (type_eq_dec
    (projT1 checked) (raw_church_systemf_type elaboration))
    as [Hequal | Hunequal].
  - exists elaboration.
    reflexivity.
  - exfalso.
    apply Hunequal.
    rewrite Hchecked_type.
    symmetry.
    exact Helaboration_type.
Qed.

Corollary runWChurch_unchecked_infer_type : forall
    constants expression elaboration,
  runWChurch_unchecked constants expression = Ok elaboration ->
  infer_systemf_type_exec constants expression =
  Some (raw_church_systemf_type elaboration).
Proof.
  intros constants expression elaboration Hchurch.
  destruct (runWChurch_unchecked_W_contract
      constants expression elaboration Hchurch)
    as [Hinference Htype].
  unfold infer_systemf_type_exec.
  rewrite Hinference.
  now rewrite Htype.
Qed.

Lemma runWChurch_success_unchecked : forall constants expression elaboration,
  runWChurch constants expression = Ok elaboration ->
  runWChurch_unchecked constants expression = Ok elaboration.
Proof.
  intros constants expression elaboration Hchurch.
  unfold runWChurch, runWChurchChecked in Hchurch.
  destruct (runWChurch_unchecked constants expression)
    as [built | error] eqn:Hbuilt; try discriminate.
  unfold certify_raw_church_elaboration,
    erase_checked_church_result in Hchurch.
  destruct (checkClosed (raw_church_term built))
    as [checked | type_error] eqn:Hcheck; try discriminate.
  destruct (type_eq_dec
      (projT1 checked) (raw_church_systemf_type built))
    as [Hequal | Hunequal]; try discriminate.
  inversion Hchurch; subst elaboration.
  reflexivity.
Qed.

Theorem runWChurch_success_iff_runW_elab_success : forall
    constants expression,
  constants_closed constants ->
  (exists elaboration,
    runWChurch constants expression = Ok elaboration) <->
  exists tau final_substitution tree,
    runW_elab expression [] =
      elaborated tau final_substitution tree.
Proof.
  intros constants expression Hconstants.
  split.
  - intros [elaboration Hchurch].
    apply (proj1
      (runWChurch_unchecked_success_iff_runW_elab_success
        constants expression)).
    exists elaboration.
    now apply runWChurch_success_unchecked.
  - intros [tau [final_substitution [tree Helaboration]]].
    now apply runWChurch_complete_for_successful_W
      with (tau := tau) (final_substitution := final_substitution)
        (tree := tree).
Qed.

Corollary runWChurch_W_contract : forall constants expression elaboration,
  runWChurch constants expression = Ok elaboration ->
  runW_exec expression [] =
    inferred
      (raw_church_hm_type elaboration)
      (raw_church_substitution elaboration) /\
  raw_church_systemf_type elaboration =
    hm_principal_type constants (raw_church_hm_type elaboration).
Proof.
  intros constants expression elaboration Hchurch.
  apply runWChurch_unchecked_W_contract.
  now apply runWChurch_success_unchecked.
Qed.

(** A successful public bridge is accepted by the independent checker at
    exactly the principal System F type obtained from executable W. *)
Theorem runWChurch_type_bridge : forall constants expression elaboration,
  runWChurch constants expression = Ok elaboration ->
  exists checked : Checked 0 [] (raw_church_term elaboration),
    checkClosed (raw_church_term elaboration) = Ok checked /\
    projT1 checked = raw_church_systemf_type elaboration /\
    infer_systemf_type_exec constants expression =
      Some (raw_church_systemf_type elaboration).
Proof.
  intros constants expression elaboration Hchurch.
  pose proof Hchurch as Hunchecked.
  apply runWChurch_success_unchecked in Hunchecked.
  assert (Hvalidate :
    validate_raw_church_elaboration elaboration = Ok elaboration).
  { unfold runWChurch, runWChurchChecked in Hchurch.
    rewrite Hunchecked in Hchurch.
    exact Hchurch. }
  apply validate_raw_church_elaboration_success in Hvalidate.
  destruct Hvalidate as [_ [checked [Hcheck Htype]]].
  exists checked.
  split; [exact Hcheck |].
  split; [exact Htype |].
  now apply runWChurch_unchecked_infer_type.
Qed.

Corollary runWChurch_is_well_typed : forall constants expression elaboration,
  runWChurch constants expression = Ok elaboration ->
  exists checked : Checked 0 [] (raw_church_term elaboration),
    checkClosed (raw_church_term elaboration) = Ok checked.
Proof.
  intros constants expression elaboration Hchurch.
  destruct (runWChurch_type_bridge
      constants expression elaboration Hchurch)
    as [checked [Hcheck _]].
  now exists checked.
Qed.

(** These two syntactic operations change only the explicit type layer. *)
Lemma erase_raw_apply_type_arguments : forall function arguments,
  erase_raw (apply_type_arguments function arguments) = erase_raw function.
Proof.
  intros function arguments.
  revert function.
  induction arguments as [| argument arguments IH]; intro function.
  - reflexivity.
  - cbn [apply_type_arguments].
    rewrite IH.
    reflexivity.
Qed.

Lemma erase_raw_wrap_type_abstractions : forall generalized body,
  erase_raw (wrap_type_abstractions generalized body) = erase_raw body.
Proof.
  induction generalized as [| variable generalized IH]; intro body.
  - reflexivity.
  - cbn [wrap_type_abstractions erase_raw].
    exact (IH body).
Qed.

(** ** Preservation of term erasure *)


Theorem reify_w_elab_tree_semantic_preserves_erasure : forall
    constants valuation term_variables tree raw,
  reify_w_elab_tree_semantic constants valuation term_variables tree = Ok raw ->
  erase_hm term_variables (w_elab_tree_source tree) =
    Some (erase_raw raw).
Proof.
  intros constants valuation term_variables tree.
  revert constants valuation term_variables.
  induction tree as
      [variable sigma instantiation instance
      | variable alpha parameter body IHbody
      | function IHfunction argument IHargument
          alpha left right unifier result
      | variable bound_type generalized sigma
          bound IHbound body IHbody];
    intros constants valuation term_variables raw Hreification;
    cbn [reify_w_elab_tree_semantic] in Hreification.
  - destruct (lookup_binder variable term_variables)
      as [index |] eqn:Hlookup; try discriminate.
    inversion Hreification; subst raw.
    cbn [w_elab_tree_source erase_hm].
    rewrite Hlookup.
    cbn.
    now rewrite erase_raw_apply_type_arguments.
  - destruct (reify_w_elab_tree_semantic constants valuation
      (variable :: term_variables) body)
      as [body' | error] eqn:Hbody; try discriminate.
    inversion Hreification; subst raw.
    cbn [w_elab_tree_source erase_hm erase_raw].
    now rewrite (IHbody constants valuation
      (variable :: term_variables) body' Hbody).
  - set (argument_valuation :=
      valuation_after_substitution constants unifier valuation).
    set (function_valuation :=
      valuation_after_substitution constants
        (compose_subst (w_elab_tree_substitution argument) unifier)
        valuation).
    fold argument_valuation function_valuation in Hreification.
    destruct (reify_w_elab_tree_semantic constants function_valuation
      term_variables function) as [function' | error]
      eqn:Hfunction; try discriminate.
    destruct (reify_w_elab_tree_semantic constants argument_valuation
      term_variables argument) as [argument' | error]
      eqn:Hargument; try discriminate.
    inversion Hreification; subst raw.
    cbn [w_elab_tree_source erase_hm erase_raw].
    rewrite (IHfunction constants function_valuation term_variables
      function' Hfunction).
    rewrite (IHargument constants argument_valuation term_variables
      argument' Hargument).
    reflexivity.
  - set (body_valuation := valuation_after_substitution constants
      (w_elab_tree_substitution body) valuation).
    fold body_valuation in Hreification.
    destruct (reify_w_elab_tree_semantic constants
      (generalized_valuation generalized body_valuation)
      term_variables bound) as [bound' | error]
      eqn:Hbound; try discriminate.
    destruct (reify_w_elab_tree_semantic constants valuation
      (variable :: term_variables) body) as [body' | error]
      eqn:Hbody; try discriminate.
    inversion Hreification; subst raw.
    cbn [w_elab_tree_source erase_hm erase_raw].
    rewrite (IHbound constants
      (generalized_valuation generalized body_valuation)
      term_variables bound' Hbound).
    rewrite (IHbody constants valuation (variable :: term_variables)
      body' Hbody).
    now rewrite erase_raw_wrap_type_abstractions.
Qed.

Theorem runWChurch_unchecked_preserves_erasure : forall
    constants expression elaboration,
  runWChurch_unchecked constants expression = Ok elaboration ->
  erase_hm_closed expression =
    Some (erase_raw (raw_church_term elaboration)).
Proof.
  intros constants expression elaboration Hchurch.
  unfold runWChurch_unchecked in Hchurch.
  destruct (runW_elab expression [])
    as [tau final_substitution tree | failure] eqn:Helaboration;
    try discriminate.
  destruct (generalize_for_elaboration tau [])
    as [sigma generalized] eqn:Hgeneralization.
  destruct (reify_w_elab_tree_semantic constants
      (generalized_valuation generalized reification_default_valuation)
      [] tree) as [body | error] eqn:Hreification;
    try discriminate.
  all: cbn in Hchurch; rewrite Hreification in Hchurch.
  - inversion Hchurch; subst elaboration.
    pose proof
      (reify_w_elab_tree_semantic_preserves_erasure
        constants
        (generalized_valuation generalized reification_default_valuation)
        [] tree body Hreification) as Herasure.
    pose proof
      (runW_elab_tree_contract expression []
        tau final_substitution tree Helaboration) as [Hsource Htype].
    unfold erase_hm_closed.
    rewrite <- Hsource.
    cbn [raw_church_term].
    rewrite erase_raw_wrap_type_abstractions.
    exact Herasure.
  - discriminate.
Qed.

Theorem runWChurch_preserves_erasure : forall
    constants expression elaboration,
  runWChurch constants expression = Ok elaboration ->
  erase_hm_closed expression =
    Some (erase_raw (raw_church_term elaboration)).
Proof.
  intros constants expression elaboration Hchurch.
  apply
    (runWChurch_unchecked_preserves_erasure
      constants expression elaboration).
  now apply runWChurch_success_unchecked.
Qed.

(** Erasure of the retained checker certificate, ready for the reducer and
    Blot's [bound]. *)
Definition checked_church_erasure
    (checked : CheckedChurchElaboration) : SystemF.F.Syntax.term :=
  match checked_church_certificate checked with
  | existT _ _ (exist _ intrinsic _) => fterm_to_term intrinsic
  end.

Lemma checked_church_erasure_is_raw : forall checked,
  erase_raw
    (raw_church_term (checked_church_elaboration checked)) =
  checked_church_erasure checked.
Proof.
  intros [elaboration certificate Htype].
  destruct certificate as [T [intrinsic Hcertificate]].
  destruct Hcertificate as [Hclosed [Hscoped Hforget]].
  cbn [checked_church_elaboration
    checked_church_certificate checked_church_erasure].
  rewrite <- Hforget.
  apply erase_raw_forget.
Qed.

Theorem runWChurchChecked_preserves_erasure : forall
    constants expression checked,
  runWChurchChecked constants expression = Ok checked ->
  erase_hm_closed expression = Some (checked_church_erasure checked).
Proof.
  intros constants expression checked Hchecked.
  assert (Hraw :
    runWChurch constants expression =
    Ok (checked_church_elaboration checked)).
  { unfold runWChurch.
    rewrite Hchecked.
    reflexivity. }
  pose proof
    (runWChurch_preserves_erasure
      constants expression (checked_church_elaboration checked) Hraw)
    as Herasure.
  rewrite checked_church_erasure_is_raw in Herasure.
  exact Herasure.
Qed.
