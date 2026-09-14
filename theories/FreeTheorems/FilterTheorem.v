(** * The free theorem for filter

    [Bool] and lists are Church encodings in the source type.  The readable
    formula uses equality for related booleans and [ListRel] for related
    lists.  Both are presentation reductions whose semantic requirements are
    kept explicit below. *)

From Stdlib Require Import List Lia.
Import ListNotations.

From SystemF.F Require Import Syntax Scope.
From SystemF.FreeTheorems Require Import
  Formula Generate Correctness ListTheorem.

(** [Bool] is [forall r. r -> r -> r]. *)
Definition church_bool_type : type :=
  TForall
    (TArrow (TVar 0)
      (TArrow (TVar 0) (TVar 0))).

(** [forall a. (a -> Bool) -> list a -> list a]. *)
Definition polymorphic_filter_type : type :=
  TForall
    (TArrow
      (TArrow (TVar 0) church_bool_type)
      (TArrow
        (church_list_type (TVar 0))
        (church_list_type (TVar 0)))).

Theorem polymorphic_filter_type_closed :
  closed 0 polymorphic_filter_type.
Proof.
  cbn [polymorphic_filter_type church_bool_type closed].
  split.
  - repeat split; lia.
  - split; apply church_list_type_closed; cbn [closed]; lia.
Qed.

(** With predicates [p] and [q] already bound, this formula says
    [R x y -> p x = q y]. *)
Definition predicates_agree_formula : RelFormula :=
  RFForallValue (RTVar 1)
    (RFForallValue (RTVar 0)
      (RFImplies
        (RFRel (RRBound 0) (RVBound 1) (RVBound 0))
        (RFEqual
          (RVApp (RVBound 3) (RVBound 1))
          (RVApp (RVBound 2) (RVBound 0))))).

Definition filter_formula : RelFormula :=
  RFForallType
    (RFForallType
      (RFForallRelation (RTVar 1) (RTVar 0)
        (RFForallValue
          (project_type ProjectLeft
            (TArrow (TVar 0) church_bool_type))
          (RFForallValue
            (project_type ProjectRight
              (TArrow (TVar 0) church_bool_type))
            (RFImplies predicates_agree_formula
              (RFForallValue
                (project_type ProjectLeft
                  (church_list_type (TVar 0)))
                (RFForallValue
                  (project_type ProjectRight
                    (church_list_type (TVar 0)))
                  (RFImplies
                    (RFRel (list_relation (RRBound 0))
                      (RVBound 1) (RVBound 0))
                    (RFRel (list_relation (RRBound 0))
                      (RVApp
                        (RVApp
                          (RVTypeApp (RVFree 0) (RTVar 1))
                          (RVBound 3))
                        (RVBound 1))
                      (RVApp
                        (RVApp
                          (RVTypeApp (RVFree 0) (RTVar 0))
                          (RVBound 2))
                        (RVBound 0))))))))))).

Theorem filter_formula_closed :
  closed_formula filter_formula.
Proof.
  vm_compute.
  lia.
Qed.

Theorem generated_filter_formula_closed :
  closed_formula (relgen polymorphic_filter_type).
Proof.
  apply relgen_closed.
  exact polymorphic_filter_type_closed.
Qed.

(** ** Semantic meaning and presentation reductions *)

Definition semantic_church_bool (model : RelModel) : SemanticType model :=
  source_type_sem model (fun _ _ => True) church_bool_type.

Definition semantic_predicate
    (model : RelModel) (A : SemanticType model) : SemanticType model :=
  fun predicate =>
    forall value,
      A value ->
      semantic_church_bool model (model_apply model predicate value).

Definition semantic_predicates_agree_by_equality
    (model : RelModel)
    (A B : SemanticType model)
    (R : SemanticRelation model)
    (left_predicate right_predicate : model_value model) : Prop :=
  forall left_value,
    A left_value ->
    forall right_value,
      B right_value ->
      R left_value right_value ->
      model_apply model left_predicate left_value =
      model_apply model right_predicate right_value.

Theorem filter_formula_semantics : forall
    (model : RelModel) type_environment relation_environment
    value_environment free_values free_relations,
  formula_sem model type_environment relation_environment
      value_environment free_values free_relations filter_formula <->
  forall (A B : SemanticType model) (R : SemanticRelation model),
    relation_between R A B ->
    forall left_predicate,
      semantic_predicate model A left_predicate ->
    forall right_predicate,
      semantic_predicate model B right_predicate ->
      semantic_predicates_agree_by_equality model A B R
        left_predicate right_predicate ->
    forall left_list,
      semantic_church_list model A left_list ->
    forall right_list,
      semantic_church_list model B right_list ->
      semantic_list_relation model (free_relations 0) R
        left_list right_list ->
      semantic_list_relation model (free_relations 0) R
        (model_apply model
          (model_apply model
            (model_type_apply model (free_values 0) A)
            left_predicate)
          left_list)
        (model_apply model
          (model_apply model
            (model_type_apply model (free_values 0) B)
            right_predicate)
          right_list).
Proof.
  reflexivity.
Qed.

Definition semantic_church_bool_relation
    (model : RelModel) : SemanticRelation model :=
  source_type_rel model church_bool_type
    (fun _ => semantic_church_bool model)
    (fun _ => semantic_church_bool model)
    (fun _ _ _ => True).

Definition semantic_predicates_agree_relationally
    (model : RelModel)
    (A B : SemanticType model)
    (R : SemanticRelation model)
    (left_predicate right_predicate : model_value model) : Prop :=
  forall left_value,
    A left_value ->
    forall right_value,
      B right_value ->
      R left_value right_value ->
      semantic_church_bool_relation model
        (model_apply model left_predicate left_value)
        (model_apply model right_predicate right_value).

Theorem generated_filter_formula_semantics : forall
    (model : RelModel) type_environment relation_environment
    value_environment free_values free_relations,
  formula_sem model type_environment relation_environment
      value_environment free_values free_relations
      (relgen polymorphic_filter_type) <->
  forall (A B : SemanticType model) (R : SemanticRelation model),
    relation_between R A B ->
    forall left_predicate,
      semantic_predicate model A left_predicate ->
    forall right_predicate,
      semantic_predicate model B right_predicate ->
      semantic_predicates_agree_relationally model A B R
        left_predicate right_predicate ->
    forall left_list,
      semantic_church_list model A left_list ->
    forall right_list,
      semantic_church_list model B right_list ->
      semantic_church_list_relation model A B R
        left_list right_list ->
      semantic_church_list_relation model A B R
        (model_apply model
          (model_apply model
            (model_type_apply model (free_values 0) A)
            left_predicate)
          left_list)
        (model_apply model
          (model_apply model
            (model_type_apply model (free_values 0) B)
            right_predicate)
          right_list).
Proof.
  reflexivity.
Qed.

(** This is the exact model property needed to print the relational
    interpretation of Church booleans as ordinary equality. *)
Definition ChurchBoolEqualityAbbreviation (model : RelModel) : Prop :=
  forall left right,
    semantic_church_bool_relation model left right <-> left = right.

Theorem filter_abbreviations_preserve_semantics : forall
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
  intros model type_environment relation_environment value_environment
    free_values free_relations Hbool Hlist.
  rewrite filter_formula_semantics.
  rewrite generated_filter_formula_semantics.
  split; intros H A B R HR left_predicate Hleft_predicate
    right_predicate Hright_predicate Hagree left Hleft right Hright Hrelated.
  - apply (proj1 (Hlist A B R HR _ _)).
    apply H; try assumption.
    + intros left_value HA right_value HB Hrelation.
      apply (proj1 (Hbool _ _)).
      now apply Hagree.
    + apply (proj2 (Hlist A B R HR _ _)).
      exact Hrelated.
  - apply (proj2 (Hlist A B R HR _ _)).
    apply H; try assumption.
    + intros left_value HA right_value HB Hrelation.
      apply (proj2 (Hbool _ _)).
      now apply Hagree.
    + apply (proj1 (Hlist A B R HR _ _)).
      exact Hrelated.
Qed.

(** ** The familiar theorem over ordinary lists and booleans *)

Definition PolymorphicFilter : Type :=
  forall A : Type, (A -> bool) -> list A -> list A.

Definition PredicatesAgree {A B : Type}
    (R : A -> B -> Prop) (left : A -> bool) (right : B -> bool) : Prop :=
  forall x y, R x y -> left x = right y.

Definition FilterParametric (candidate : PolymorphicFilter) : Prop :=
  forall (A B : Type) (R : A -> B -> Prop)
      (left_predicate : A -> bool) (right_predicate : B -> bool),
    PredicatesAgree R left_predicate right_predicate ->
    forall left right,
      ListRel R left right ->
      ListRel R
        (candidate A left_predicate left)
        (candidate B right_predicate right).

Theorem filter_map_law : forall (candidate : PolymorphicFilter),
  FilterParametric candidate ->
  forall (A B : Type) (mapping : A -> B)
      (left_predicate : A -> bool) (right_predicate : B -> bool),
    (forall value,
      left_predicate value = right_predicate (mapping value)) ->
    forall values,
      map mapping (candidate A left_predicate values) =
      candidate B right_predicate (map mapping values).
Proof.
  intros candidate Hparametric A B mapping left_predicate right_predicate
    Hagree values.
  apply (proj1
    (ListRel_graph_iff_map A B mapping
      (candidate A left_predicate values)
      (candidate B right_predicate (map mapping values)))).
  apply Hparametric.
  - intros x y Hgraph.
    unfold relation_graph in Hgraph.
    subst y.
    apply Hagree.
  - apply (proj2
      (ListRel_graph_iff_map A B mapping values (map mapping values))).
    reflexivity.
Qed.
