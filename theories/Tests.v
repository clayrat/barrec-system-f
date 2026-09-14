(** * Fast regression tests

    Meaningful computations are frozen as kernel-checked equalities as the
    corresponding algorithms become available.  Derived presentation laws
    and term-level W elaboration remain separate later layers.

    Use Examples.v as the common source for Rocq and OCaml fixtures.
    BBC experiments belong in bench/ and do not run during this build. *)

From Stdlib Require Import List Lia.
Import ListNotations.

From SystemF Require Import Examples HMElab.
From SystemF.F Require Import Syntax OPE Scope Check OperationalSemantics.
From SystemF.FreeTheorems Require Import
  Formula Generate Correctness Fundamental ListTheorem FilterTheorem
  NegativeTheorem Presentation.
From SystemF.HM Require Import Infer Unify.
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
    (fterm_sem model term1 left_types left_values)
    (fterm_sem model term1 right_types right_values).
Proof.
  intros.
  apply closed_fterm_parametricity.
Qed.

Example intrinsic_identity_validates_its_generated_formula : forall
    (model : ParametricModel)
    (formula_types types : Environment (SemanticType model))
    (relations : Environment (SemanticRelation model))
    (values term_values free_values : Environment (model_value model))
    (free_relations : Environment (SemanticRelation model)),
  paired_type_environment formula_types types types ->
  free_values 0 = fterm_sem model term1 types term_values ->
  formula_sem model formula_types relations values
    free_values free_relations (relgen type1).
Proof.
  intros model formula_types types relations values term_values
    free_values free_relations Hpaired Hprogram.
  now apply (closed_fterm_satisfies_relgen model type1 term1
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

Definition raw_bad_free_type_argument : RawChurch :=
  RCTApp (RCTAbs raw_term1) (TVar 0).

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
  erase_raw (forget term2) = fterm_to_term term2.
Proof. apply erase_raw_forget. Qed.

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
  match lookup_fvar [TVar 0; type1] 1 with
  | Ok (existT _ T variable) => (T, fvar_to_nat variable)
  | Err _ => (TVar 99, 99)
  end = (type1, 1).
Proof. reflexivity. Qed.

Example dependent_lookup_preserves_original_bad_index :
  match lookup_fvar [type1] 2 with
  | Err (UnboundTermVariable index) => index
  | _ => 99
  end = 2.
Proof. reflexivity. Qed.

(** ** Computational Church checker *)

Definition checked_closed_type (raw : RawChurch) : option type :=
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

Definition raw_context_shift : RawChurch :=
  RCTAbs (RCAbs (TVar 0) (RCTAbs (RCVar 0))).

Example check_core_shifts_context_under_type_abstraction :
  checked_closed_type raw_context_shift =
  Some
    (TForall
      (TArrow (TVar 0) (TForall (TVar 1)))).
Proof. reflexivity. Qed.

Definition raw_type_mismatch : RawChurch :=
  RCApp
    (RCAbs type1 (RCVar 0))
    (RCAbs type1 (RCVar 0)).

Example check_core_rejects_type_mismatch :
  check_core 0 [] raw_type_mismatch =
  Err (TypeMismatch type1 type2).
Proof. reflexivity. Qed.

Example check_core_rejects_non_function_application :
  check_core 0 [] (RCApp raw_term1 raw_term1) =
  Err (ExpectedArrow type1).
Proof. reflexivity. Qed.

Example check_core_rejects_non_polymorphic_type_application :
  check_core 0 [] (RCTApp (RCAbs type1 (RCVar 0)) type1) =
  Err (ExpectedForall type2).
Proof. reflexivity. Qed.

Example check_core_rejects_free_term_variable :
  check_core 0 [] (RCVar 0) =
  Err (UnboundTermVariable 0).
Proof. reflexivity. Qed.

Example check_core_rejects_free_type_annotation :
  check_core 0 [] (RCAbs (TVar 0) (RCVar 0)) =
  Err (TypeAnnotationOutOfScope (TVar 0)).
Proof. reflexivity. Qed.

Example check_core_rejects_free_type_argument :
  check_core 0 [] raw_bad_free_type_argument =
  Err (TypeArgumentOutOfScope (TVar 0)).
Proof. reflexivity. Qed.

(** ** Proof-carrying Church checker *)

Definition certified_closed_type (raw : RawChurch) : option type :=
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
  ~ exists T (t : fterm [] T),
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

Definition hm_identity_expression : SystemF.HM.WInCoq.Typing.term :=
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

Definition hm_self_application : SystemF.HM.WInCoq.Typing.term :=
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
