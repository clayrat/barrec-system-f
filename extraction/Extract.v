(** * Extraction driver

    Syntax, erasure, the independent weak-head reducer, the proof-free HM
    inference ([unify_exec], [runW_exec]), its computational event trace, the
    structural [W_elab] tree, and shared examples are exported.
    The dependent W-in-Coq [runW] and [unify''] stay inside Rocq as the
    reference proof; their equivalence with the extracted code is the
    theorem [runW_exec_checked_correspondence]. The Church checker is
    exported both as the computational [check_core] and as the certified
    [checkClosed]; [check_core_correspondence] proves that the certificate
    changes nothing observable. The relational generator is exported together
    with its proof-carrying closed-input wrapper.  The executable W result is
    generalized and translated to a closed System F type before it is handed
    to that generator.  The repaired Blot bound is exported from the shared
    intrinsic syntax; its [brec] dependency remains an explicit custom OCaml
    extraction boundary. Silent-by-default hooks in the handwritten
    [Barrec_trace] module feed both the concise live demo and full TSV runs.

    Natural numbers use the standard [ExtrOcamlNatInt] representation.
    In particular, extracted predecessor and subtraction remain truncated
    at zero.  OCaml [int] overflow is therefore the only extra-runtime trust
    boundary: callers must keep inputs and computed bounds below [max_int]. *)

From Stdlib Require Import Extraction ExtrOcamlNatInt.
From SystemF.F Require Import Syntax Check OperationalSemantics.
From SystemF.BarRec Require Import Bound.
From SystemF.FreeTheorems Require Import
  Formula Generate ListTheorem FilterTheorem NegativeTheorem Presentation.
From SystemF.HM Require Import ElabScope Erasure Infer TypeDAG Unify Examples.
From SystemF Require Import CurryChurchBoundary Examples HMElab Normalization.

Extraction Language OCaml.
Set Extraction Output Directory ".".

Extraction "systemf.ml"
  type_lift type_subst term_equal term_lift fterm_to_term
  term_subst1 wh_step run_fuel eval_cap
  brec bound
  type1 term1 type2 term2 term3 term4 erased_examples
  check_core checkClosed checked_inferred erase_raw
  raw_term1 raw_term2 raw_term3 raw_term4
  boundary_curry_identity boundary_identity_type
  boundary_identity_arrow_type boundary_raw_polymorphic_identity
  boundary_raw_identity_at_identity_type boundary_raw_type_application
  boundary_raw_annotated_application boundary_checked_type
  boundary_hm_identity boundary_hm_identity_church_view
  FormulaType ValueExpr RelationExpr RelFormula
  formula_type_lift value_lift value_type_lift relation_lift
  formula_value_lift formula_type_lift_in formula_relation_lift
  Projection project_type_with formula_type_of_type project_type
  relate relgen generateClosed
  church_list_type polymorphic_list_endomorphism_type
  list_relation list_endomorphism_formula
  church_bool_type polymorphic_filter_type filter_formula
  negative_occurrence_type negative_occurrence_formula
  ChurchTypeAbbreviation recognize_church_type
  recognize_formula_church_type postprocess_relation
  relate_presented relgen_presented
  unify_exec runW_exec
  constant_freeb lookup_binder erase_hm erase_hm_closed
  hm_let_identity_self_application hm_dead_internal_type_variable
  WElabFailure WElabTree w_elab_state_result w_elab_result
  W_elab runW_elab erase_w_elab_state erase_w_elab_result
  w_elab_tree_type w_elab_tree_source w_elab_instantiation_count
  WTraceFailure WTraceEvent WTraceResult runWTrace
  trace_instantiation_count trace_generalization_count trace_failure_count
  TypeDAGNode SystemF.HM.TypeDAG.TypeDAG
  type_dag_size type_to_dag type_dag_decode
  hm_term_tree_size inferred_type_tree_size inferred_type_dag
  inferred_type_dag_size inferred_type_representation_sizes
  repeated_application hm_pair hm_pair_application hm_pair_dup_lets
  hm_monomorphic_pair_dup_family hm_polymorphic_pair_dup_family
  hm_fixed_result_pair_type hm_monomorphic_shared_pair_type
  hm_monomorphic_shared_pair_type_tree_size
  hm_monomorphic_shared_pair_type_dag_size
  polymorphic_pair_application infer_exec_succeeds
  scheme_body_to_type quantify_scheme scheme_to_systemf
  hm_principal_scheme hm_principal_type
  infer_systemf_type_exec infer_relational_formula_exec
  ChurchReifyError WChurchError RawChurchElaboration
  CheckedChurchElaboration
  reification_default_type
  apply_type_arguments wrap_type_abstractions
  reify_w_elab_tree_semantic runWChurch_unchecked
  certify_raw_church_elaboration erase_checked_church_result
  validate_raw_church_elaboration runWChurchChecked runWChurch
  checked_church_erasure
  NormalizationBoundSource NormalizationResult normalization_erasure
  normalize_intrinsic normalize_intrinsic_with_cap
  normalize_checked normalize_checked_with_cap
  normalizeClosed normalizeClosedWithCap
  normalize_checked_church normalize_checked_church_with_cap
  default_normalization_cap
  runWBarNormalization runWNormalizationWithCap runWNormalization.
