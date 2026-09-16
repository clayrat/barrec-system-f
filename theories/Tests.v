(** * Fast regression tests

    Meaningful computations are frozen as kernel-checked equalities as the
    corresponding algorithms become available.  Derived presentation laws
    and term-level W elaboration remain separate later layers.

    Use Examples.v as the common source for Rocq and OCaml fixtures.
    BBC experiments belong in bench/ and do not run during this build. *)

From Stdlib Require Import List Lia.
Import ListNotations.

From SystemF Require Import CurryChurchBoundary Examples HMElab Normalization.
From SystemF.F Require Import Syntax OPE Scope Check OperationalSemantics.
From SystemF.FreeTheorems Require Import
  Formula Generate Correctness Fundamental ListTheorem FilterTheorem
  NegativeTheorem Presentation.
From SystemF.HM Require Import ElabScope Erasure Infer TypeDAG Unify.
Require Import SystemF.HM.Examples.

(** ** Type-variable scope *)

Example polymorphic_identity_type_is_closed : closed 0 type1.
Proof.
  cbn [closed type1].
  lia.
Qed.

Example free_type_variable_is_not_closed : ~ closed 0 (TVar 0).
Proof.
  cbn [closed].
  lia.
Qed.

Example closed_dec_accepts_polymorphic_identity :
  match closed_dec 0 type1 with
  | left _ => true
  | right _ => false
  end = true.
Proof. reflexivity. Qed.

Example closed_dec_rejects_free_type_variable :
  match closed_dec 0 (TVar 0) with
  | left _ => true
  | right _ => false
  end = false.
Proof. reflexivity. Qed.

Example lifting_preserves_type_scope :
  closed 1 (type_lift 0 type1).
Proof.
  apply closed_type_lift0.
  exact polymorphic_identity_type_is_closed.
Qed.

Example substitution_preserves_type_scope :
  closed 0
    (type_subst 0
      (TArrow (TVar 0) (TVar 0))
      type1).
Proof.
  apply closed_type_subst0.
  - cbn [closed]. lia.
  - exact polymorphic_identity_type_is_closed.
Qed.

(** ** OPE renaming and parallel substitution *)

Example ope_weakening_crosses_forall :
  ren wk
    (TForall (TArrow (TVar 0) (TVar 1))) =
  TForall (TArrow (TVar 0) (TVar 2)).
Proof. reflexivity. Qed.

Example ope_weakening_is_blots_lift : forall T,
  ren wk T = type_lift 0 T.
Proof. apply ren_wk. Qed.

Example parallel_substitution_lifts_under_forall :
  sub (scons (TVar 0) ids) (TForall (TVar 1)) =
  TForall (TVar 1).
Proof. reflexivity. Qed.

Example parallel_substitution_is_blots_substitution : forall T U,
  sub (scons U ids) T = type_subst 0 T U.
Proof. apply sub_scons_ids. Qed.

(** ** Relational-formula syntax *)

Definition three_namespace_formula : RelFormula :=
  RFForallType
    (RFForallType
      (RFForallRelation (RTVar 1) (RTVar 0)
        (RFForallValue (RTVar 1)
          (RFForallValue (RTVar 0)
            (RFRel (RRBound 0) (RVBound 1) (RVBound 0)))))).

Example relational_formula_uses_three_scoped_namespaces :
  closed_formula three_namespace_formula.
Proof.
  cbn [closed_formula three_namespace_formula formula_scoped
    formula_type_scoped relation_scoped value_scoped].
  lia.
Qed.

Example value_weakening_crosses_only_value_binders :
  formula_value_lift 0
    (RFForallValue (RTVar 0)
      (RFRel (RRBound 0) (RVBound 0) (RVBound 1))) =
  RFForallValue (RTVar 0)
    (RFRel (RRBound 0) (RVBound 0) (RVBound 2)).
Proof. reflexivity. Qed.

Example type_weakening_crosses_only_type_binders :
  formula_type_lift_in 0
    (RFForallType
      (RFForallValue (RTVar 0)
        (RFEqual
          (RVTypeApp (RVBound 0) (RTVar 0))
          (RVTypeApp (RVBound 0) (RTVar 1))))) =
  RFForallType
    (RFForallValue (RTVar 0)
      (RFEqual
        (RVTypeApp (RVBound 0) (RTVar 0))
        (RVTypeApp (RVBound 0) (RTVar 2)))).
Proof. reflexivity. Qed.

Example relation_weakening_crosses_only_relation_binders :
  formula_relation_lift 0
    (RFForallRelation (RTVar 1) (RTVar 0)
      (RFRel
        (RRApp (RRBound 0) (RRBound 1))
        (RVBound 1) (RVBound 0))) =
  RFForallRelation (RTVar 1) (RTVar 0)
    (RFRel
      (RRApp (RRBound 0) (RRBound 2))
      (RVBound 1) (RVBound 0)).
Proof. reflexivity. Qed.

(** ** Relational generator *)

Example relational_projection_orders_endpoint_types :
  project_type ProjectLeft
      (TArrow (TVar 0) (TVar 1)) =
    RTArrow (RTVar 1) (RTVar 3) /\
  project_type ProjectRight
      (TArrow (TVar 0) (TVar 1)) =
    RTArrow (RTVar 0) (RTVar 2).
Proof. split; reflexivity. Qed.

Definition polymorphic_identity_formula : RelFormula :=
  RFForallType
    (RFForallType
      (RFForallRelation (RTVar 1) (RTVar 0)
        (RFForallValue (RTVar 1)
          (RFForallValue (RTVar 0)
            (RFImplies
              (RFRel (RRBound 0) (RVBound 1) (RVBound 0))
              (RFRel (RRBound 0)
                (RVApp
                  (RVTypeApp (RVFree 0) (RTVar 1))
                  (RVBound 1))
                (RVApp
                  (RVTypeApp (RVFree 0) (RTVar 0))
                  (RVBound 0)))))))).

(** [forall X. X -> X] becomes
    [forall A B R x y, R x y -> R (f[A] x) (f[B] y)]. *)
Example relgen_polymorphic_identity :
  relgen type1 = polymorphic_identity_formula.
Proof. reflexivity. Qed.

Example relgen_polymorphic_identity_is_closed :
  closed_formula (relgen type1).
Proof.
  apply relgen_closed.
  exact polymorphic_identity_type_is_closed.
Qed.

Definition generated_polymorphic_identity : GeneratedFormula :=
  generateClosed type1 polymorphic_identity_type_is_closed.

Example generated_formula_keeps_computational_result :
  proj1_sig generated_polymorphic_identity = polymorphic_identity_formula.
Proof. reflexivity. Qed.

Example shared_identity_formula_has_expected_semantics :
  forall (model : RelModel)
      formula_types relations values free_values free_relations,
    formula_sem model formula_types relations values
        free_values free_relations (relgen type1) <->
    forall (left_type right_type : SemanticType model)
        (relation : SemanticRelation model),
      relation_between relation left_type right_type ->
      forall left_value,
        left_type left_value ->
      forall right_value,
        right_type right_value ->
        relation left_value right_value ->
        relation
          (model_apply model
            (model_type_apply model (free_values 0) left_type)
            left_value)
          (model_apply model
            (model_type_apply model (free_values 0) right_type)
            right_value).
Proof.
  intros.
  apply polymorphic_identity_semantics.
Qed.

(** ** Fundamental theorem for terms *)

Example intrinsic_identity_satisfies_fundamental_theorem : forall
    (model : ParametricModel)
    (left_types right_types : Environment (SemanticType model))
    (relations : Environment (SemanticRelation model))
    (left_values right_values : Environment (model_value model)),
  logical_relation model type1 left_types right_types relations
    (fderiv_sem model term1 left_types left_values)
    (fderiv_sem model term1 right_types right_values).
Proof.
  intros.
  apply closed_fderiv_parametricity.
Qed.

Example intrinsic_identity_validates_its_generated_formula : forall
    (model : ParametricModel)
    (formula_types types : Environment (SemanticType model))
    (relations : Environment (SemanticRelation model))
    (values term_values free_values : Environment (model_value model))
    (free_relations : Environment (SemanticRelation model)),
  paired_type_environment formula_types types types ->
  free_values 0 = fderiv_sem model term1 types term_values ->
  formula_sem model formula_types relations values
    free_values free_relations (relgen type1).
Proof.
  intros model formula_types types relations values term_values
    free_values free_relations Hpaired Hprogram.
  now apply (closed_fderiv_satisfies_relgen model type1 term1
    formula_types types relations values term_values
    free_values free_relations).
Qed.

(** ** List-endomorphism free theorem *)

Example church_list_abbreviation_has_expected_shape :
  church_list_type (TVar 0) =
  TForall
    (TArrow (TVar 0)
      (TArrow
        (TArrow (TVar 1) (TArrow (TVar 0) (TVar 0)))
        (TVar 0))).
Proof. reflexivity. Qed.

Example list_endomorphism_generator_input_is_closed :
  closed 0 polymorphic_list_endomorphism_type.
Proof.
  exact polymorphic_list_endomorphism_type_closed.
Qed.

Example generated_list_endomorphism_is_closed :
  closed_formula (relgen polymorphic_list_endomorphism_type).
Proof.
  exact generated_list_endomorphism_formula_closed.
Qed.

Example readable_list_endomorphism_formula_is_closed :
  closed_formula list_endomorphism_formula.
Proof.
  exact list_endomorphism_formula_closed.
Qed.

Example ListRel_abbreviation_preserves_generated_meaning : forall
    (model : RelModel) type_environment relation_environment
    value_environment free_values free_relations,
  ChurchListRelationAbbreviation model (free_relations 0) ->
  (formula_sem model type_environment relation_environment
      value_environment free_values free_relations
      list_endomorphism_formula <->
   formula_sem model type_environment relation_environment
      value_environment free_values free_relations
      (relgen polymorphic_list_endomorphism_type)).
Proof.
  apply list_relation_abbreviation_preserves_semantics.
Qed.

Example graph_specialisation_reduces_ListRel_to_map : forall
    (A B : Type) (mapping : A -> B) left right,
  ListRel (relation_graph mapping) left right <->
  map mapping left = right.
Proof.
  apply ListRel_graph_iff_map.
Qed.

Example list_endomorphism_free_theorem_implies_naturality : forall
    (function : PolymorphicListEndomorphism),
  ListEndomorphismParametric function ->
  forall (A B : Type) (mapping : A -> B) (values : list A),
    map mapping (function A values) =
    function B (map mapping values).
Proof.
  apply list_endomorphism_map_law.
Qed.

(** ** Filter free theorem *)

Example church_bool_abbreviation_has_expected_shape :
  church_bool_type =
  TForall (TArrow (TVar 0) (TArrow (TVar 0) (TVar 0))).
Proof. reflexivity. Qed.

Example filter_generator_input_is_closed :
  closed 0 polymorphic_filter_type.
Proof.
  exact polymorphic_filter_type_closed.
Qed.

Example generated_filter_formula_is_closed :
  closed_formula (relgen polymorphic_filter_type).
Proof.
  exact generated_filter_formula_closed.
Qed.

Example readable_filter_formula_is_closed :
  closed_formula filter_formula.
Proof.
  exact filter_formula_closed.
Qed.

Example filter_abbreviations_preserve_generated_meaning : forall
    (model : RelModel) type_environment relation_environment
    value_environment free_values free_relations,
  ChurchBoolEqualityAbbreviation model ->
  ChurchListRelationAbbreviation model (free_relations 0) ->
  (formula_sem model type_environment relation_environment
      value_environment free_values free_relations filter_formula <->
   formula_sem model type_environment relation_environment
      value_environment free_values free_relations
      (relgen polymorphic_filter_type)).
Proof.
  apply filter_abbreviations_preserve_semantics.
Qed.

Example filter_predicates_agree_on_related_values : forall
    (A B : Type) (R : A -> B -> Prop)
    (left_predicate : A -> bool) (right_predicate : B -> bool),
  PredicatesAgree R left_predicate right_predicate ->
  forall x y, R x y -> left_predicate x = right_predicate y.
Proof.
  intros A B R left_predicate right_predicate Hagree x y Hrelated.
  now apply Hagree with (x := x) (y := y).
Qed.

Example filter_free_theorem_implies_map_law : forall
    (candidate : PolymorphicFilter),
  FilterParametric candidate ->
  forall (A B : Type) (mapping : A -> B)
      (left_predicate : A -> bool) (right_predicate : B -> bool),
    (forall value,
      left_predicate value = right_predicate (mapping value)) ->
    forall values,
      map mapping (candidate A left_predicate values) =
      candidate B right_predicate (map mapping values).
Proof.
  apply filter_map_law.
Qed.

(** ** Negative occurrence *)

Example negative_occurrence_generator_input_is_closed :
  closed 0 negative_occurrence_type.
Proof.
  exact negative_occurrence_type_closed.
Qed.

Example negative_occurrence_generator_has_expected_formula :
  relgen negative_occurrence_type = negative_occurrence_formula.
Proof.
  exact relgen_negative_occurrence.
Qed.

Example negative_occurrence_result_is_closed :
  closed_formula (relgen negative_occurrence_type).
Proof.
  rewrite relgen_negative_occurrence.
  exact negative_occurrence_formula_closed.
Qed.

Example negative_occurrence_graph_premise_is_a_commuting_square : forall
    (A B : Type) (mapping : A -> B)
    (left_function : A -> A) (right_function : B -> B),
  EndomorphismsAgree (relation_graph mapping)
      left_function right_function <->
  forall value,
    mapping (left_function value) = right_function (mapping value).
Proof.
  apply endomorphisms_agree_graph_iff.
Qed.

Example negative_occurrence_free_theorem_implies_naturality : forall
    (iterator : PolymorphicIterator),
  IteratorParametric iterator ->
  forall (A B : Type) (mapping : A -> B)
      (left_function : A -> A) (right_function : B -> B),
    (forall value,
      mapping (left_function value) = right_function (mapping value)) ->
    forall value,
      mapping (iterator A left_function value) =
      iterator B right_function (mapping value).
Proof.
  apply negative_occurrence_naturality.
Qed.

Example negative_occurrence_really_needs_its_premise :
  IteratorParametric apply_once /\
  ~ EndomorphismsAgree (@eq bool) negb (fun value => value) /\
  apply_once bool negb false <>
    apply_once bool (fun value => value) false.
Proof.
  repeat split.
  - exact apply_once_parametric.
  - exact negative_premise_is_necessary.
  - exact apply_once_fails_without_negative_premise.
Qed.

(** ** Checked Church presentation rules *)

Example source_printer_recognizes_Bool_and_list :
  recognize_church_type church_bool_type = Some CABool /\
  recognize_church_type (church_list_type (TVar 3)) =
    Some (CAListVariable 3).
Proof.
  split.
  - exact recognize_church_bool.
  - apply recognize_church_list_variable.
Qed.

Example formula_printer_recognizes_Bool_and_list :
  recognize_formula_church_type
      (formula_type_of_type church_bool_type) = Some CABool /\
  recognize_formula_church_type
      (formula_type_of_type (church_list_type (TVar 3))) =
    Some (CAListVariable 3).
Proof.
  split.
  - exact recognize_formula_church_bool.
  - apply recognize_formula_church_list_variable.
Qed.

Example source_print_recognition_has_no_false_positive : forall T view,
  recognize_church_type T = Some view -> T = expand_church_type view.
Proof.
  apply recognize_church_type_sound.
Qed.

Example formula_print_recognition_has_no_false_positive : forall T view,
  recognize_formula_church_type T = Some view ->
  T = expand_formula_church_type view.
Proof.
  apply recognize_formula_church_type_sound.
Qed.

Example presented_generator_uses_ListRel :
  relgen_presented polymorphic_list_endomorphism_type =
  list_endomorphism_formula.
Proof.
  exact presented_list_endomorphism_computes.
Qed.

Example presented_generator_uses_Bool_equality_and_ListRel :
  relgen_presented polymorphic_filter_type = filter_formula.
Proof.
  exact presented_filter_computes.
Qed.

Example presented_generator_does_not_change_unabbreviated_types :
  relgen_presented negative_occurrence_type = negative_occurrence_formula.
Proof.
  reflexivity.
Qed.

Example presented_relation_is_a_postprocess_of_relate : forall T lhs rhs,
  relate_presented T lhs rhs =
  postprocess_relation T lhs rhs (relate T lhs rhs).
Proof.
  apply relate_presented_is_postprocessing.
Qed.

Example presentation_guard_rejects_an_unrelated_formula :
  postprocess_relation church_bool_type
    (RVFree 0) (RVFree 0) RFTop = RFTop.
Proof. reflexivity. Qed.

Example presented_generator_preserves_semantics_for_every_type : forall
    (model : RelModel) T
    (formula_types left_types right_types :
      Environment (SemanticType model))
    (relations : Environment (SemanticRelation model))
    (values free_values : Environment (model_value model))
    (free_relations : Environment (SemanticRelation model)),
  paired_type_environment formula_types left_types right_types ->
  relation_environment_between left_types right_types relations ->
  ChurchBoolEqualityAbbreviation model ->
  ChurchListRelationAbbreviation model (free_relations 0) ->
  (formula_sem model formula_types relations values
      free_values free_relations (relgen_presented T) <->
   formula_sem model formula_types relations values
      free_values free_relations (relgen T)).
Proof.
  apply relgen_presented_semantics.
Qed.

Example Bool_print_rule_has_explicit_semantic_contract : forall
    (model : RelModel) formula_types left_types right_types relations
    values free_values free_relations lhs rhs,
  paired_type_environment formula_types left_types right_types ->
  ChurchBoolEqualityAbbreviation model ->
  (formula_sem model formula_types relations values
      free_values free_relations (RFEqual lhs rhs) <->
   formula_sem model formula_types relations values
      free_values free_relations (relate church_bool_type lhs rhs)).
Proof.
  apply bool_relation_print_rule_sound.
Qed.

Example ListRel_print_rule_has_explicit_semantic_contract : forall
    (model : RelModel) index formula_types left_types right_types relations
    values free_values free_relations lhs rhs,
  paired_type_environment formula_types left_types right_types ->
  relation_between (relations index)
    (left_types index) (right_types index) ->
  ChurchListRelationAbbreviation model (free_relations 0) ->
  (formula_sem model formula_types relations values
      free_values free_relations
      (RFRel (list_relation (RRBound index)) lhs rhs) <->
   formula_sem model formula_types relations values
      free_values free_relations
      (relate (church_list_type (TVar index)) lhs rhs)).
Proof.
  apply list_relation_print_rule_sound.
Qed.

Example presented_list_formula_preserves_generated_semantics : forall
    (model : RelModel) type_environment relation_environment
    value_environment free_values free_relations,
  ChurchListRelationAbbreviation model (free_relations 0) ->
  (formula_sem model type_environment relation_environment
      value_environment free_values free_relations
      (relgen_presented polymorphic_list_endomorphism_type) <->
   formula_sem model type_environment relation_environment
      value_environment free_values free_relations
      (relgen polymorphic_list_endomorphism_type)).
Proof.
  apply presented_list_endomorphism_semantics.
Qed.

Example presented_filter_formula_preserves_generated_semantics : forall
    (model : RelModel) type_environment relation_environment
    value_environment free_values free_relations,
  ChurchBoolEqualityAbbreviation model ->
  ChurchListRelationAbbreviation model (free_relations 0) ->
  (formula_sem model type_environment relation_environment
      value_environment free_values free_relations
      (relgen_presented polymorphic_filter_type) <->
   formula_sem model type_environment relation_environment
      value_environment free_values free_relations
      (relgen polymorphic_filter_type)).
Proof.
  apply presented_filter_semantics.
Qed.

(** ** Raw Church syntax *)

Definition raw_bad_free_type_argument : fterm :=
  FTApp (FTLam raw_term1) (TVar 0).

Example raw_polymorphic_identity_is_scoped :
  scoped 0 raw_term1.
Proof.
  cbn [scoped raw_term1 closed].
  lia.
Qed.

Example scoped_dec_accepts_raw_polymorphic_identity :
  match scoped_dec 0 raw_term1 with
  | left _ => true
  | right _ => false
  end = true.
Proof. reflexivity. Qed.

(** This is [(Lambda a. id)[b]]: the body ignores [a], but the explicit
    argument [b] is nevertheless out of scope at the top level. *)
Example scoped_dec_rejects_free_type_argument :
  match scoped_dec 0 raw_bad_free_type_argument with
  | left _ => true
  | right _ => false
  end = false.
Proof. reflexivity. Qed.

Example forget_polymorphic_identity :
  forget term1 = raw_term1.
Proof. reflexivity. Qed.

Example forget_shared_church_examples :
  forget term1 = raw_term1 /\
  forget term2 = raw_term2 /\
  forget term3 = raw_term3 /\
  forget term4 = raw_term4.
Proof. repeat split; reflexivity. Qed.

Example forgetting_preserves_erasure :
  fterm_to_term (forget term2) = fderiv_to_term term2.
Proof. apply fterm_to_term_forget. Qed.

(** ** Type equality and dependent variable lookup *)

Example type_equality_accepts_identical_types :
  match type_eq_dec type1 type1 with
  | left _ => true
  | right _ => false
  end = true.
Proof. reflexivity. Qed.

Example type_equality_rejects_distinct_shapes :
  match type_eq_dec type1 (TArrow type1 type1) with
  | left _ => true
  | right _ => false
  end = false.
Proof. reflexivity. Qed.

Example dependent_lookup_returns_type_and_position :
  match lookup_dvar [TVar 0; type1] 1 with
  | Ok (existT _ T variable) => (T, dvar_to_nat variable)
  | Err _ => (TVar 99, 99)
  end = (type1, 1).
Proof. reflexivity. Qed.

Example dependent_lookup_preserves_original_bad_index :
  match lookup_dvar [type1] 2 with
  | Err (UnboundTermVariable index) => index
  | _ => 99
  end = 2.
Proof. reflexivity. Qed.

(** ** Computational Church checker *)

Definition checked_closed_type (raw : fterm) : option type :=
  match check_core 0 [] raw with
  | Ok (existT _ T _) => Some T
  | Err _ => None
  end.

Example check_core_accepts_polymorphic_identity :
  checked_closed_type raw_term1 = Some type1.
Proof. reflexivity. Qed.

(** [raw_term2] is the impredicative introduction example
    [lambda x : forall X, X -> X. x [forall X, X -> X] x]. *)
Example check_core_accepts_impredicative_application :
  checked_closed_type raw_term2 = Some type2.
Proof. reflexivity. Qed.

Example check_core_accepts_shared_reduction_examples :
  checked_closed_type raw_term3 = Some type1 /\
  checked_closed_type raw_term4 = Some type1.
Proof. split; reflexivity. Qed.

Definition raw_ctx_shift : fterm :=
  FTLam (FLam (TVar 0) (FTLam (FVar 0))).

Example check_core_shifts_ctx_under_type_abstraction :
  checked_closed_type raw_ctx_shift =
  Some
    (TForall
      (TArrow (TVar 0) (TForall (TVar 1)))).
Proof. reflexivity. Qed.

Definition raw_type_mismatch : fterm :=
  FApp
    (FLam type1 (FVar 0))
    (FLam type1 (FVar 0)).

Example check_core_rejects_type_mismatch :
  check_core 0 [] raw_type_mismatch =
  Err (TypeMismatch type1 type2).
Proof. reflexivity. Qed.

Example check_core_rejects_non_function_application :
  check_core 0 [] (FApp raw_term1 raw_term1) =
  Err (ExpectedArrow type1).
Proof. reflexivity. Qed.

Example check_core_rejects_non_polymorphic_type_application :
  check_core 0 [] (FTApp (FLam type1 (FVar 0)) type1) =
  Err (ExpectedForall type2).
Proof. reflexivity. Qed.

Example check_core_rejects_free_term_variable :
  check_core 0 [] (FVar 0) =
  Err (UnboundTermVariable 0).
Proof. reflexivity. Qed.

Example check_core_rejects_free_type_annotation :
  check_core 0 [] (FLam (TVar 0) (FVar 0)) =
  Err (TypeAnnotationOutOfScope (TVar 0)).
Proof. reflexivity. Qed.

Example check_core_rejects_free_type_argument :
  check_core 0 [] raw_bad_free_type_argument =
  Err (TypeArgumentOutOfScope (TVar 0)).
Proof. reflexivity. Qed.

(** ** Proof-carrying Church checker *)

Definition certified_closed_type (raw : fterm) : option type :=
  match checkClosed raw with
  | Ok (existT _ T _) => Some T
  | Err _ => None
  end.

Example checkClosed_accepts_shared_examples :
  certified_closed_type raw_term1 = Some type1 /\
  certified_closed_type raw_term2 = Some type2 /\
  certified_closed_type raw_term3 = Some type1 /\
  certified_closed_type raw_term4 = Some type1.
Proof. repeat split; reflexivity. Qed.

(** ** Curry/Church boundary *)

Example curry_church_boundary_kernel_regression :
  fterm_to_term boundary_raw_polymorphic_identity = boundary_curry_identity /\
  fterm_to_term boundary_raw_identity_at_identity_type = boundary_curry_identity /\
  boundary_checked_type boundary_raw_polymorphic_identity =
    Some boundary_identity_type /\
  boundary_checked_type boundary_raw_identity_at_identity_type =
    Some boundary_identity_arrow_type /\
  fterm_to_term boundary_raw_type_application =
    fterm_to_term boundary_raw_annotated_application /\
  boundary_hm_identity_church_view =
    Some
      (boundary_identity_type,
       boundary_raw_polymorphic_identity).
Proof. repeat split; reflexivity. Qed.

Example checkClosed_preserves_the_core_result : forall raw,
  erase_checked_result (checkClosed raw) = check_core 0 [] raw.
Proof. apply checkClosed_core_correspondence. Qed.

Example polymorphic_identity_has_a_public_certificate :
  exists checked : Checked 0 [] raw_term1,
    checkClosed raw_term1 = Ok checked.
Proof.
  apply (proj2 (checkClosed_accepts_iff_typing raw_term1)).
  exists type1, term1.
  split.
  - exact raw_polymorphic_identity_is_scoped.
  - reflexivity.
Qed.

Example checkClosed_rejects_type_mismatch :
  checkClosed raw_type_mismatch =
  Err (TypeMismatch type1 type2).
Proof. reflexivity. Qed.

Example rejected_type_mismatch_has_no_intrinsic_typing :
  ~ exists T (t : fderiv [] T),
      scoped 0 raw_type_mismatch /\ forget t = raw_type_mismatch.
Proof.
  apply checkClosed_rejected_no_typing
    with (error := TypeMismatch type1 type2).
  reflexivity.
Qed.

(** ** Capture-avoiding substitution *)

(** The free variable supplied as the argument remains free underneath the
    abstraction instead of being captured by it. *)
Example term_subst1_avoids_capture :
  term_subst1 0 (Lam (Var 1)) (Var 0) = Lam (Var 1).
Proof. reflexivity. Qed.

(** The abstraction's own bound variable is not replaced. *)
Example term_subst1_preserves_inner_binder :
  term_subst1 0 (Lam (Var 0)) (Var 42) = Lam (Var 0).
Proof. reflexivity. Qed.

(** Variables above the removed index are shifted down. *)
Example term_subst1_closes_gap :
  term_subst1 0 (Var 1) (Var 42) = Var 0.
Proof. reflexivity. Qed.

(** ** Weak-head reduction *)

Example term1_is_whnf :
  wh_step (fderiv_to_term term1) = None.
Proof. reflexivity. Qed.

Example term3_takes_one_step :
  wh_step (fderiv_to_term term3) = Some (fderiv_to_term term1).
Proof. reflexivity. Qed.

Example term4_takes_one_step :
  wh_step (fderiv_to_term term4) = Some (fderiv_to_term term1).
Proof. reflexivity. Qed.

(** A redex is found underneath applications on the left spine. *)
Example wh_step_follows_left_spine :
  wh_step
    (App (App (Lam (Var 0)) (Lam (Var 0))) (Var 0)) =
  Some (App (Lam (Var 0)) (Var 0)).
Proof. reflexivity. Qed.

(** Weak-head reduction does not inspect an argument of a stuck head. *)
Example wh_step_does_not_reduce_arguments :
  wh_step
    (App (Var 0) (App (Lam (Var 0)) (Var 1))) =
  None.
Proof. reflexivity. Qed.

(** Weak-head reduction does not proceed under an abstraction. *)
Example wh_step_does_not_reduce_under_lam :
  wh_step
    (Lam (App (Lam (Var 0)) (Var 1))) =
  None.
Proof. reflexivity. Qed.

(** ** Fuel and exact-step oracle *)

Example term4_zero_fuel_is_unchanged :
  run_fuel 0 (fderiv_to_term term4) = fderiv_to_term term4.
Proof. reflexivity. Qed.

Example term4_one_fuel_reaches_whnf :
  run_fuel 1 (fderiv_to_term term4) = fderiv_to_term term1.
Proof. reflexivity. Qed.

Example term4_excess_fuel_is_harmless :
  run_fuel 5 (fderiv_to_term term4) = fderiv_to_term term1.
Proof. reflexivity. Qed.

Example term3_cap_zero_is_insufficient :
  eval_cap 0 (fderiv_to_term term3) = None.
Proof. reflexivity. Qed.

Example term3_exact_step_count :
  eval_cap 1 (fderiv_to_term term3) =
  Some (1, fderiv_to_term term1).
Proof. reflexivity. Qed.

Example term4_exact_step_count :
  eval_cap 1 (fderiv_to_term term4) =
  Some (1, fderiv_to_term term1).
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

(** The generated source remains linear: every new level contributes one
    [let], two applications, the pair variable, and two occurrences of the
    previous value. *)
Lemma hm_pair_dup_lets_has_linear_source_size : forall depth current,
  hm_term_tree_size (hm_pair_dup_lets depth current) = 6 * depth + 1.
Proof.
  induction depth as [| depth IH]; intro current.
  - reflexivity.
  - cbn [hm_pair_dup_lets hm_pair_application hm_term_tree_size].
    rewrite IH.
    lia.
Qed.

Example hm_monomorphic_pair_dup_family_has_linear_source_size : forall depth,
  hm_term_tree_size (hm_monomorphic_pair_dup_family depth) =
  6 * depth + 11.
Proof.
  intro depth.
  cbn [hm_monomorphic_pair_dup_family hm_term_tree_size].
  rewrite hm_pair_dup_lets_has_linear_source_size.
  unfold hm_pair.
  cbn [hm_term_tree_size].
  lia.
Qed.

Example hm_polymorphic_pair_dup_family_has_linear_source_size : forall depth,
  hm_term_tree_size (hm_polymorphic_pair_dup_family depth) =
  6 * depth + 13.
Proof.
  intro depth.
  cbn [hm_polymorphic_pair_dup_family hm_term_tree_size].
  rewrite hm_pair_dup_lets_has_linear_source_size.
  unfold hm_pair.
  cbn [hm_term_tree_size].
  lia.
Qed.

Lemma hm_pair_dup_lets_is_constant_free : forall depth current,
  constant_freeb (hm_pair_dup_lets depth current) = true.
Proof.
  induction depth as [| depth IH]; intro current.
  - reflexivity.
  - cbn [hm_pair_dup_lets hm_pair_application constant_freeb].
    apply IH.
Qed.

Example hm_pair_dup_families_are_in_the_elaboration_fragment : forall depth,
  constant_freeb (hm_monomorphic_pair_dup_family depth) = true /\
  constant_freeb (hm_polymorphic_pair_dup_family depth) = true.
Proof.
  intro depth.
  cbn [hm_monomorphic_pair_dup_family hm_polymorphic_pair_dup_family
    hm_pair constant_freeb].
  now rewrite !hm_pair_dup_lets_is_constant_free.
Qed.

Lemma hm_pair_dup_lets_names_scoped : forall depth current binders,
  In 0 binders ->
  In current binders ->
  hm_names_scoped binders (hm_pair_dup_lets depth current).
Proof.
  induction depth as [| depth IH]; intros current binders Hpair Hcurrent.
  - exact Hcurrent.
  - cbn [hm_pair_dup_lets hm_pair_application hm_names_scoped].
    repeat split; try assumption.
    apply IH.
    + now right.
    + now left.
Qed.

Example hm_pair_dup_families_are_closed : forall depth,
  hm_names_scoped [] (hm_monomorphic_pair_dup_family depth) /\
  hm_names_scoped [] (hm_polymorphic_pair_dup_family depth).
Proof.
  intro depth.
  split.
  - cbn [hm_monomorphic_pair_dup_family hm_pair hm_names_scoped].
    split.
    + cbn. tauto.
    + apply hm_pair_dup_lets_names_scoped; cbn; tauto.
  - cbn [hm_polymorphic_pair_dup_family hm_pair hm_names_scoped].
    split.
    + cbn. tauto.
    + split.
      * cbn. tauto.
      * apply hm_pair_dup_lets_names_scoped; cbn; tauto.
Qed.

Example hm_pair_dup_families_have_closed_erasures : forall depth,
  (exists erased,
    erase_hm_closed (hm_monomorphic_pair_dup_family depth) = Some erased) /\
  (exists erased,
    erase_hm_closed (hm_polymorphic_pair_dup_family depth) = Some erased).
Proof.
  intro depth.
  destruct (hm_pair_dup_families_are_in_the_elaboration_fragment depth)
    as [Hmono_free Hpoly_free].
  destruct (hm_pair_dup_families_are_closed depth)
    as [Hmono_scoped Hpoly_scoped].
  split; apply (proj2 (erase_hm_closed_success_iff _)); split.
  - now apply (proj1 (constant_freeb_true_iff _)).
  - exact Hmono_scoped.
  - now apply (proj1 (constant_freeb_true_iff _)).
  - exact Hpoly_scoped.
Qed.

(** These are measurements, not a lower-bound theorem.  They freeze the
    intended contrast: linear source sizes versus rapidly duplicated type
    trees, with the let-polymorphic variant already larger at each positive
    depth because both copies receive fresh instantiations. *)
Example hm_monomorphic_pair_dup_type_tree_sizes :
  map
    (fun depth =>
      inferred_type_tree_size (hm_monomorphic_pair_dup_family depth))
    [0; 1; 2; 3] =
  [Some 3; Some 9; Some 21; Some 45].
Proof. reflexivity. Qed.

Example hm_polymorphic_pair_dup_type_tree_sizes :
  map
    (fun depth =>
      inferred_type_tree_size (hm_polymorphic_pair_dup_family depth))
    [0; 1; 2; 3] =
  [Some 3; Some 11; Some 27; Some 59].
Proof. reflexivity. Qed.

(** Hash-consing is visible in the representation: the two equal children of
    the arrow point to identifier zero rather than storing two variable
    nodes. *)
Example type_dag_shares_equal_arrow_children :
  type_to_dag (arrow (var 0) (var 0)) =
  {| type_dag_nodes :=
       [type_dag_var 0; type_dag_arrow 0 0];
     type_dag_root := 1;
     type_dag_height := 2 |}.
Proof. reflexivity. Qed.

Example type_dag_shared_arrow_decodes :
  type_dag_decode (type_to_dag (arrow (var 0) (var 0))) =
  Some (arrow (var 0) (var 0)).
Proof. apply type_to_dag_correct. Qed.

(** With a genuinely monomorphic fixed-result pair, the ordinary tree doubles
    its previous payload while the maximally shared DAG adds exactly three
    arrow nodes at each positive depth. *)
Example hm_monomorphic_shared_pair_type_tree_sizes :
  map hm_monomorphic_shared_pair_type_tree_size [0; 1; 2; 3; 4] =
  [1; 7; 19; 43; 91].
Proof. reflexivity. Qed.

Example hm_monomorphic_shared_pair_type_dag_sizes :
  map hm_monomorphic_shared_pair_type_dag_size [0; 1; 2; 3; 4] =
  [1; 5; 8; 11; 14].
Proof. reflexivity. Qed.

(** The real source language has no primitive product, so its Church pair has
    a generalized result variable.  Even the lambda-bound-base family loses
    part of the ideal sharing; fresh let-polymorphic instantiations lose more.
    These exact DAG measurements keep the distinction honest. *)
Example hm_monomorphic_pair_dup_type_dag_sizes :
  map
    (fun depth =>
      inferred_type_dag_size (hm_monomorphic_pair_dup_family depth))
    [0; 1; 2; 3] =
  [Some 2; Some 6; Some 14; Some 30].
Proof. reflexivity. Qed.

Example hm_polymorphic_pair_dup_type_dag_sizes :
  map
    (fun depth =>
      inferred_type_dag_size (hm_polymorphic_pair_dup_family depth))
    [0; 1; 2; 3] =
  [Some 2; Some 8; Some 20; Some 44].
Proof. reflexivity. Qed.

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

(** ** Source fragment for HM-to-System-F elaboration *)

Example elaboration_fragment_accepts_end_to_end_fixture :
  constant_free hm_let_identity_self_application.
Proof.
  cbn [hm_let_identity_self_application constant_free].
  tauto.
Qed.

Example elaboration_fragment_boolean_accepts_end_to_end_fixture :
  constant_freeb hm_let_identity_self_application = true.
Proof. reflexivity. Qed.

Example elaboration_fragment_rejects_a_constant :
  ~ constant_free (const_t 0).
Proof. exact (fun impossible => impossible). Qed.

Example elaboration_fragment_rejects_nested_constants :
  constant_freeb
    (let_t 0 (lam_t 1 (var_t 1))
      (app_t (var_t 0) (const_t 7))) = false.
Proof. reflexivity. Qed.

Example elaboration_fragment_decision_is_exact : forall expression,
  constant_freeb expression = true <-> constant_free expression.
Proof. apply constant_freeb_true_iff. Qed.

(** ** Erasure of named HM terms *)

Definition erased_hm_let_identity_self_application :
    SystemF.F.Syntax.term :=
  App
    (Lam (App (Var 0) (Var 0)))
    (Lam (Var 0)).

Example hm_erasure_desugars_the_end_to_end_let :
  erase_hm_closed hm_let_identity_self_application =
  Some erased_hm_let_identity_self_application.
Proof. reflexivity. Qed.

Example hm_erasure_uses_nearest_binder_under_shadowing :
  erase_hm_closed (lam_t 0 (lam_t 0 (var_t 0))) =
  Some (Lam (Lam (Var 0))).
Proof. reflexivity. Qed.

Example hm_erasure_keeps_outer_binder_index :
  erase_hm_closed (lam_t 0 (lam_t 1 (var_t 0))) =
  Some (Lam (Lam (Var 1))).
Proof. reflexivity. Qed.

Example hm_erasure_rejects_an_unbound_name :
  erase_hm_closed (var_t 42) = None.
Proof. reflexivity. Qed.

Example hm_erasure_rejects_a_constant :
  erase_hm_closed (const_t 0) = None.
Proof. reflexivity. Qed.

Example hm_erasure_domain_is_exact : forall expression,
  (exists erased, erase_hm_closed expression = Some erased) <->
  constant_free expression /\ hm_names_scoped [] expression.
Proof. apply erase_hm_closed_success_iff. Qed.

(** ** Structural Algorithm W elaboration *)

Definition hm_let_identity_self_application_substitution : substitution :=
  [(1, arrow (var 2) (var 2));
   (3, arrow (var 2) (var 2))].

Definition hm_let_identity_self_application_tree : WElabTree :=
  elab_let 0 (arrow (var 0) (var 0)) [0]
    (sc_arrow (sc_gen 0) (sc_gen 0))
    (elab_lambda 1 0 (var 0)
      (elab_variable 1 (sc_var 0) [] (var 0)))
    (elab_application
      (elab_variable 0
        (sc_arrow (sc_gen 0) (sc_gen 0))
        [var 1] (arrow (var 1) (var 1)))
      (elab_variable 0
        (sc_arrow (sc_gen 0) (sc_gen 0))
        [var 2] (arrow (var 2) (var 2)))
      3
      (arrow (var 1) (var 1))
      (arrow (arrow (var 2) (var 2)) (var 3))
      hm_let_identity_self_application_substitution
      (arrow (var 2) (var 2))).

Example w_elab_end_to_end_result :
  runW_elab hm_let_identity_self_application [] =
  elaborated
    (arrow (var 2) (var 2))
    hm_let_identity_self_application_substitution
    hm_let_identity_self_application_tree.
Proof. reflexivity. Qed.

Example w_elab_records_both_identity_instantiations :
  w_elab_instantiation_count 0
    hm_let_identity_self_application_tree = 2.
Proof. reflexivity. Qed.

Example w_elab_tree_recovers_source_and_type :
  w_elab_tree_source hm_let_identity_self_application_tree =
    hm_let_identity_self_application /\
  w_elab_tree_type hm_let_identity_self_application_tree =
    arrow (var 2) (var 2).
Proof. split; reflexivity. Qed.

Example w_elab_erases_to_W_for_the_whole_fragment : forall
    expression environment,
  constant_free expression ->
  erase_w_elab_result (runW_elab expression environment) =
  runW_exec expression environment.
Proof. apply runW_elab_erases. Qed.

Example w_elab_matches_checked_W_for_the_whole_fragment : forall
    expression environment,
  constant_free expression ->
  erase_w_elab_result (runW_elab expression environment) =
  observe_checked_result (runW expression environment).
Proof. apply runW_elab_checked_correspondence. Qed.

Example w_elab_has_full_checked_W_correspondence : forall
    expression environment,
  constant_free expression ->
  runW_elab_checked_spec expression environment.
Proof. apply runW_elab_checked_full_correspondence. Qed.

Example w_elab_end_to_end_result_is_the_checked_W_result :
  runW hm_let_identity_self_application [] =
  inl
    (arrow (var 2) (var 2),
     hm_let_identity_self_application_substitution).
Proof.
  assert (Hfragment : constant_free hm_let_identity_self_application).
  { cbn [hm_let_identity_self_application constant_free].
    tauto. }
  apply (proj1
    (runW_elab_success_iff_checked_success
      hm_let_identity_self_application []
      (arrow (var 2) (var 2))
      hm_let_identity_self_application_substitution Hfragment)).
  exists hm_let_identity_self_application_tree.
  exact w_elab_end_to_end_result.
Qed.

Example w_elab_rejects_outside_fragment :
  runW_elab (const_t 7) [] =
  elaboration_rejected (elab_unsupported_constant 7).
Proof. reflexivity. Qed.

Example w_elab_preserves_missing_variable_failure :
  runW_elab (var_t 42) [] =
  elaboration_rejected (elab_missing_variable 42).
Proof. reflexivity. Qed.

Example w_elab_preserves_occurs_check_failure :
  runW_elab (lam_t 0 (app_t (var_t 0) (var_t 0))) [] =
  elaboration_rejected
    (elab_unification_failure (var 0) (arrow (var 0) (var 1))).
Proof. reflexivity. Qed.

(** ** Type bridge from W to System F *)

Definition test_constant_types (_ : id) : type := type1.

Example test_constant_types_are_closed :
  constants_closed test_constant_types.
Proof.
  intro name.
  exact polymorphic_identity_type_is_closed.
Qed.

Example scheme_bridge_preserves_constant_interpretation :
  scheme_to_systemf test_constant_types (fun variable => variable)
    (sc_con 7) = type1.
Proof. reflexivity. Qed.

(** [sc_gen 0] is the first/outer binder and [sc_gen 1] the second/inner
    binder, hence indices [1] and [0] in the body. *)
Example scheme_bridge_fixes_generalization_order :
  scheme_to_systemf test_constant_types (fun variable => variable)
    (sc_arrow (sc_gen 0) (sc_gen 1)) =
  TForall (TForall (TArrow (TVar 1) (TVar 0))).
Proof. reflexivity. Qed.

(** The free variable remains outside the quantifier introduced for the
    generalized variable. *)
Example scheme_bridge_distinguishes_free_variables :
  scheme_to_systemf test_constant_types (fun variable => variable)
    (sc_arrow (sc_var 0) (sc_gen 0)) =
  TForall (TArrow (TVar 1) (TVar 0)).
Proof. reflexivity. Qed.

Example scheme_with_one_ambient_variable_is_scoped :
  closed 1
    (scheme_to_systemf test_constant_types (fun variable => variable)
      (sc_arrow (sc_var 0) (sc_gen 0))).
Proof.
  apply scheme_to_systemf_scoped.
  - exact test_constant_types_are_closed.
  - cbn [free_variables_scoped].
    lia.
Qed.

(** ** Reification of W into explicit Church syntax *)

Example dead_type_variable_default_is_closed_at_every_depth : forall n,
  closed n reification_default_type.
Proof. apply reification_default_type_closed. Qed.

Example reifier_rejects_an_unbound_term_variable :
  reify_w_elab_tree_semantic test_constant_types
    reification_default_valuation []
    (elab_variable 42 (sc_var 0) [] (var 0)) =
  Err (reify_unbound_term_variable 42).
Proof. reflexivity. Qed.

Definition raw_hm_dead_internal_type_variable : fterm :=
  FTLam
    (FLam (TVar 0)
      (FApp
        (FLam (TArrow type1 type1) (FVar 1))
        (FLam type1 (FVar 0)))).

(** The type of the unused [y] is ['2 -> '2], while ['2] does not occur in
    the principal result ['3 -> '3].  It is therefore instantiated with the
    closed reification default instead of causing a spurious rejection. *)
Example runWChurch_defaults_a_dead_internal_type_variable :
  match runWChurch test_constant_types hm_dead_internal_type_variable with
  | Ok elaboration =>
      church_systemf_type elaboration = type1 /\
      church_term elaboration = raw_hm_dead_internal_type_variable
  | Err _ => False
  end.
Proof. vm_compute; split; reflexivity. Qed.

Example unchecked_reification_is_complete_for_successful_W : forall
    expression,
  (exists elaboration,
    runWChurch_unchecked test_constant_types expression = Ok elaboration) <->
  exists tau substitution tree,
    runW_elab expression [] = elaborated tau substitution tree.
Proof. apply runWChurch_unchecked_success_iff_runW_elab_success. Qed.

Example every_successful_raw_W_reification_is_scoped : forall
    expression elaboration,
  runWChurch_unchecked test_constant_types expression = Ok elaboration ->
  scoped 0 (church_term elaboration).
Proof.
  intros expression elaboration Hchurch.
  eapply runWChurch_unchecked_scoped.
  - apply test_constant_types_are_closed.
  - exact Hchurch.
Qed.

Example every_successful_raw_W_reification_checks_at_its_principal_type :
  forall expression elaboration,
  runWChurch_unchecked test_constant_types expression = Ok elaboration ->
  exists checked : Checked 0 [] (church_term elaboration),
    checkClosed (church_term elaboration) = Ok checked /\
    projT1 checked =
      hm_principal_type test_constant_types
        (church_hm_type elaboration).
Proof.
  intros expression elaboration Hchurch.
  exact (runWChurch_unchecked_checkClosed_principal
    test_constant_types expression elaboration
    test_constant_types_are_closed Hchurch).
Qed.

Example type_arguments_are_left_associated :
  apply_type_arguments (FVar 0) [TVar 1; TVar 0] =
  FTApp (FTApp (FVar 0) (TVar 1)) (TVar 0).
Proof. reflexivity. Qed.

Definition hm_apply_expression : hmterm :=
  lam_t 0 (lam_t 1 (app_t (var_t 0) (var_t 1))).

Definition raw_hm_apply_expression : fterm :=
  FTLam
    (FTLam
      (FLam (TArrow (TVar 1) (TVar 0))
        (FLam (TVar 1) (FApp (FVar 1) (FVar 0))))).

(** A full two-quantifier regression checks that reversing the binder stack
    and emitting outer abstractions are paired operations. *)
Example runWChurch_preserves_two_quantifier_order :
  match runWChurch test_constant_types hm_apply_expression with
  | Ok elaboration => Some (church_term elaboration)
  | Err _ => None
  end = Some raw_hm_apply_expression.
Proof. reflexivity. Qed.

Example reified_two_quantifier_term_is_accepted :
  certified_closed_type raw_hm_apply_expression =
  Some
    (TForall
      (TForall
        (TArrow
          (TArrow (TVar 1) (TVar 0))
          (TArrow (TVar 1) (TVar 0))))).
Proof. reflexivity. Qed.

Definition raw_hm_let_identity_self_application : fterm :=
  FTLam
    (FApp
      (FLam
        (TForall (TArrow (TVar 0) (TVar 0)))
        (FApp
          (FTApp (FVar 0) (TArrow (TVar 0) (TVar 0)))
          (FTApp (FVar 0) (TVar 0))))
      (FTLam (FLam (TVar 0) (FVar 0)))).

Definition hm_let_identity_self_application_church_result :
    ChurchElaboration :=
  {| church_hm_type := arrow (var 2) (var 2);
     church_substitution :=
       hm_let_identity_self_application_substitution;
     church_tree := hm_let_identity_self_application_tree;
     church_systemf_type := type1;
     church_term := raw_hm_let_identity_self_application |}.

(** This freezes the full bridge, including the two distinct occurrences
    [id [a -> a]] and [id [a]] and the [let]-bound [Lambda]. *)
Example runWChurch_builds_the_expected_raw_term :
  runWChurch test_constant_types hm_let_identity_self_application =
  Ok hm_let_identity_self_application_church_result.
Proof. reflexivity. Qed.

Example runWChurch_end_to_end_type_bridge :
  exists checked : Checked 0 [] raw_hm_let_identity_self_application,
    checkClosed raw_hm_let_identity_self_application = Ok checked /\
    projT1 checked = type1 /\
    infer_systemf_type_exec
      test_constant_types hm_let_identity_self_application = Some type1.
Proof.
  exact
    (runWChurch_type_bridge
      test_constant_types
      hm_let_identity_self_application
      hm_let_identity_self_application_church_result
      runWChurch_builds_the_expected_raw_term).
Qed.

Example runWChurchChecked_retains_the_checker_certificate :
  exists checked : CheckedChurchElaboration,
    runWChurchChecked
      test_constant_types hm_let_identity_self_application = Ok checked.
Proof.
  pose proof runWChurch_builds_the_expected_raw_term as Hraw.
  unfold runWChurch in Hraw.
  destruct (runWChurchChecked
      test_constant_types hm_let_identity_self_application)
    as [checked | error] eqn:Hchecked.
  - now exists checked.
  - discriminate.
Qed.

Example runWChurch_end_to_end_erasure_bridge :
  erase_hm_closed hm_let_identity_self_application =
  Some
    (fterm_to_term
      (church_term hm_let_identity_self_application_church_result)).
Proof.
  exact
    (runWChurch_preserves_erasure
      test_constant_types
      hm_let_identity_self_application
      hm_let_identity_self_application_church_result
      runWChurch_builds_the_expected_raw_term).
Qed.

Example checked_W_term_reaches_the_shared_untyped_syntax :
  exists checked : CheckedChurchElaboration,
    runWChurchChecked
      test_constant_types hm_let_identity_self_application = Ok checked /\
    checked_church_erasure checked =
      erased_hm_let_identity_self_application.
Proof.
  destruct runWChurchChecked_retains_the_checker_certificate
    as [checked Hchecked].
  exists checked.
  split; [exact Hchecked |].
  pose proof
    (runWChurchChecked_preserves_erasure
      test_constant_types hm_let_identity_self_application
      checked Hchecked) as Herasure.
  rewrite hm_erasure_desugars_the_end_to_end_let in Herasure.
  now inversion Herasure.
Qed.

(** ** Main W-to-System-F end-to-end acceptance test

    Both downstream branches start from the same HM input.  The type branch
    reaches the relational generator; the term branch retains the checked
    intrinsic term, crosses the proved erasure bridge, and reaches the exact
    weak-head evaluator.  The external bar-recursive bound is deliberately
    not part of this fast test until stage 7 imports its repaired core. *)
Example main_hm_systemf_pipeline_acceptance :
  exists checked : CheckedChurchElaboration,
    runWChurchChecked
      test_constant_types hm_let_identity_self_application = Ok checked /\
    checked_church_elaboration checked =
      hm_let_identity_self_application_church_result /\
    infer_relational_formula_exec
      test_constant_types hm_let_identity_self_application =
      Some polymorphic_identity_formula /\
    checked_church_erasure checked =
      erased_hm_let_identity_self_application /\
    eval_cap 2 (checked_church_erasure checked) =
      Some (2, Lam (Var 0)).
Proof.
  destruct checked_W_term_reaches_the_shared_untyped_syntax
    as [checked [Hchecked Herasure]].
  exists checked.
  split; [exact Hchecked |].
  split.
  - pose proof runWChurch_builds_the_expected_raw_term as Hraw.
    unfold runWChurch in Hraw.
    rewrite Hchecked in Hraw.
    cbn [erase_checked_church_result] in Hraw.
    now inversion Hraw.
  - split.
    + reflexivity.
    + split; [exact Herasure |].
      rewrite Herasure.
      reflexivity.
Qed.

(** The normalization wrapper does not reconstruct or separately erase the
    term: its reducer input is the erasure already retained by the checked
    W-to-Church pipeline. *)
Example main_W_normalization_wrapper_uses_the_common_erasure : forall
    normalization,
  runWNormalization
    test_constant_types hm_let_identity_self_application = Ok normalization ->
  normalization_erasure normalization =
  erased_hm_let_identity_self_application.
Proof.
  intros normalization Hnormalization.
  pose proof
    (runWNormalization_preserves_erasure
      test_constant_types hm_let_identity_self_application
      normalization Hnormalization) as Herasure.
  rewrite hm_erasure_desugars_the_end_to_end_let in Herasure.
  now inversion Herasure.
Qed.

Example every_successful_W_normalization_uses_its_bound_as_fuel : forall
    constants expression normalization,
  runWNormalization constants expression = Ok normalization ->
  normalization_result normalization =
  run_fuel
    (normalization_bound normalization)
    (normalization_erasure normalization).
Proof. apply runWNormalization_result. Qed.

(** The default frontend avoids the pathological BBC expansion on this small
    term: the independent evaluator supplies its exact two-step bound. *)
Example main_W_normalization_takes_the_exact_fast_path :
  exists normalization,
    runWNormalization
      test_constant_types hm_let_identity_self_application =
      Ok normalization /\
    normalization_bound_source normalization = exact_evaluation_bound /\
    normalization_bound normalization = 2 /\
    normalization_result normalization = Lam (Var 0).
Proof.
  eexists.
  repeat split; reflexivity.
Qed.

Example reified_W_term_is_accepted_by_the_independent_checker :
  certified_closed_type raw_hm_let_identity_self_application = Some type1.
Proof. reflexivity. Qed.

Example reified_W_term_has_the_expected_erasure :
  fterm_to_term raw_hm_let_identity_self_application =
  erased_hm_let_identity_self_application.
Proof. reflexivity. Qed.

Definition hm_identity_expression : hmterm :=
  lam_t 0 (var_t 0).

Example w_identity_result :
  runW_exec hm_identity_expression [] =
  inferred (arrow (var 0) (var 0)) [].
Proof. reflexivity. Qed.

Example w_identity_generalizes_to_systemf_identity :
  hm_principal_type test_constant_types
    (arrow (var 0) (var 0)) = type1.
Proof. reflexivity. Qed.

Example inferred_identity_has_systemf_type :
  infer_systemf_type_exec test_constant_types hm_identity_expression =
  Some type1.
Proof. reflexivity. Qed.

Example inferred_identity_has_certified_systemf_type :
  option_map (@proj1_sig type (closed 0))
    (infer_systemf_type test_constant_types
      test_constant_types_are_closed hm_identity_expression) =
  Some type1.
Proof. reflexivity. Qed.

Example inferred_identity_reaches_relational_generator :
  infer_relational_formula_exec test_constant_types hm_identity_expression =
  Some polymorphic_identity_formula.
Proof. reflexivity. Qed.

Definition repeated_application_systemf_type : type :=
  TForall
    (TForall
      (TArrow
        (TArrow (TVar 1) (TVar 0))
        (TArrow (TVar 1) (TVar 0)))).

Example inferred_repeated_application_has_systemf_type :
  infer_systemf_type_exec test_constant_types repeated_application =
  Some repeated_application_systemf_type.
Proof. reflexivity. Qed.

Example checked_and_executable_type_bridges_agree :
  infer_systemf_type_checked test_constant_types repeated_application =
  infer_systemf_type_exec test_constant_types repeated_application.
Proof. apply infer_systemf_type_correspondence. Qed.

Example inferred_repeated_application_type_is_closed :
  closed 0 repeated_application_systemf_type.
Proof.
  eapply infer_systemf_type_exec_closed.
  - exact test_constant_types_are_closed.
  - exact inferred_repeated_application_has_systemf_type.
Qed.

(** ** Computational W trace *)

Example tracing_preserves_every_W_result : forall expression environment,
  trace_result (runWTrace expression environment) =
  runW_exec expression environment.
Proof. apply runWTrace_result. Qed.

Example w_identity_trace_records_freshness_and_instantiation :
  runWTrace hm_identity_expression [] =
  {| trace_result := inferred (arrow (var 0) (var 0)) [];
     trace_events :=
       [trace_fresh 0;
        trace_instantiate 0 1 (sc_var 0) (Some (var 0))] |}.
Proof. reflexivity. Qed.

Definition hm_self_application : hmterm :=
  lam_t 0 (app_t (var_t 0) (var_t 0)).

(** The rejected equation exposes the occurs-check situation
    ['0 = '0 -> '1] directly in the trace. *)
Example w_self_application_trace_records_failure :
  runWTrace hm_self_application [] =
  {| trace_result := inference_rejected;
     trace_events :=
       [trace_fresh 0;
        trace_instantiate 0 1 (sc_var 0) (Some (var 0));
        trace_instantiate 0 1 (sc_var 0) (Some (var 0));
        trace_fresh 1;
        trace_unify (var 0) (arrow (var 0) (var 1)) rejected;
        trace_fail
          (trace_unification_failure
            (var 0) (arrow (var 0) (var 1)))] |}.
Proof. reflexivity. Qed.

Definition traced_pair_application_type : option ty :=
  match trace_result (runWTrace polymorphic_pair_application []) with
  | inferred tau _ => Some tau
  | inference_rejected => None
  end.

Example w_pair_trace_has_church_pair_type :
  traced_pair_application_type =
  Some
    (arrow
      (arrow (con 0) (arrow (con 1) (var 8)))
      (var 8)).
Proof. reflexivity. Qed.

(** The two occurrences [id 0] and [id true] instantiate the generalized
    identity scheme independently. *)
Example w_pair_trace_instantiates_identity_twice :
  trace_instantiation_count 1
    (trace_events (runWTrace polymorphic_pair_application [])) = 2.
Proof. reflexivity. Qed.

Example w_pair_trace_generalizes_pair_and_identity :
  trace_generalization_count 0
      (trace_events (runWTrace polymorphic_pair_application [])) = 1 /\
  trace_generalization_count 1
      (trace_events (runWTrace polymorphic_pair_application [])) = 1.
Proof. split; reflexivity. Qed.

Example w_pair_trace_has_no_failure :
  trace_failure_count
    (trace_events (runWTrace polymorphic_pair_application [])) = 0.
Proof. reflexivity. Qed.
