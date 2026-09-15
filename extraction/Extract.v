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
    to that generator. Add the repaired bound when it becomes available.

    Keep natural numbers as Peano data for now. Any later native numeric
    mapping must preserve truncated subtraction and predecessor, and
    address overflow for bounds. *)

From Stdlib Require Import Extraction ExtrOcamlBasic.
From SystemF.F Require Import Syntax Check OperationalSemantics.
From SystemF.FreeTheorems Require Import
  Formula Generate ListTheorem FilterTheorem NegativeTheorem Presentation.
From SystemF.HM Require Import ElabScope Erasure Infer Unify Examples.
From SystemF Require Import Examples HMElab.

Extraction Language OCaml.
Set Extraction Output Directory ".".

Extraction "systemf.ml"
  type_lift type_subst term_equal term_lift fterm_to_term
  term_subst1 wh_step run_fuel eval_cap
  type1 term1 type2 term2 term3 term4 erased_examples
  check_core checkClosed checked_inferred erase_raw
  raw_term1 raw_term2 raw_term3 raw_term4
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
  repeated_application hm_pair polymorphic_pair_application infer_exec_succeeds
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
  checked_church_erasure.
