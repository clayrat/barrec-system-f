(** * The list-endomorphism free theorem

    Lists are a surface abbreviation for their Church encoding in the source
    System F syntax.  The generator still traverses that encoding; the
    smaller [list_endomorphism_formula] is the presentation form in which the
    generated relation for the encoding is named [ListRel].

    The last section is deliberately independent of the realizability model.
    It proves the familiar [map] law from the relational contract by choosing
    the graph of a function as the element relation.  A fundamental theorem
    for System F is what supplies that relational contract for a typed term;
    it is not assumed globally in this module. *)

From Stdlib Require Import List Lia.
Import ListNotations.

From SystemF.F Require Import Syntax Scope.
From SystemF.FreeTheorems Require Import Formula Generate Correctness.

(** [list A] is [forall r. r -> (A -> r -> r) -> r].  Since the result
    variable is introduced inside the encoding, the free element type must be
    weakened once. *)
Definition church_list_type (A : type) : type :=
  TForall
    (TArrow (TVar 0)
      (TArrow
        (TArrow (type_lift 0 A)
          (TArrow (TVar 0) (TVar 0)))
        (TVar 0))).

Definition polymorphic_list_endomorphism_type : type :=
  TForall
    (TArrow
      (church_list_type (TVar 0))
      (church_list_type (TVar 0))).

Lemma church_list_type_closed : forall n A,
  closed n A -> closed n (church_list_type A).
Proof.
  intros n A HA.
  cbn [church_list_type closed].
  repeat split; try lia.
  now apply closed_type_lift0.
Qed.

Theorem polymorphic_list_endomorphism_type_closed :
  closed 0 polymorphic_list_endomorphism_type.
Proof.
  cbn [polymorphic_list_endomorphism_type closed].
  split; apply church_list_type_closed; cbn [closed]; lia.
Qed.

(** Free relation symbol zero is printed as [ListRel].  This formula reads

      forall A B (R : A -> B -> Prop) xs ys,
        ListRel R xs ys ->
        ListRel R (g [A] xs) (g [B] ys).

    It is a presentation abbreviation, not a second generator. *)
Definition list_relation (relation : RelationExpr) : RelationExpr :=
  RRApp (RRFree 0) relation.

Definition list_endomorphism_formula : RelFormula :=
  RFForallType
    (RFForallType
      (RFForallRelation (RTVar 1) (RTVar 0)
        (RFForallValue
          (project_type ProjectLeft (church_list_type (TVar 0)))
          (RFForallValue
            (project_type ProjectRight (church_list_type (TVar 0)))
            (RFImplies
              (RFRel (list_relation (RRBound 0))
                (RVBound 1) (RVBound 0))
              (RFRel (list_relation (RRBound 0))
                (RVApp
                  (RVTypeApp (RVFree 0) (RTVar 1))
                  (RVBound 1))
                (RVApp
                  (RVTypeApp (RVFree 0) (RTVar 0))
                  (RVBound 0)))))))).

Theorem list_endomorphism_formula_closed :
  closed_formula list_endomorphism_formula.
Proof.
  vm_compute.
  lia.
Qed.

Theorem generated_list_endomorphism_formula_closed :
  closed_formula (relgen polymorphic_list_endomorphism_type).
Proof.
  apply relgen_closed.
  exact polymorphic_list_endomorphism_type_closed.
Qed.

(** ** Meaning of the readable formula *)

Definition semantic_church_list
    (model : RelModel) (element : SemanticType model) : SemanticType model :=
  fun encoded =>
    forall result : SemanticType model,
      forall nil_value,
        result nil_value ->
      forall cons_value,
        (forall element_value,
          element element_value ->
          forall accumulated,
            result accumulated ->
            result
              (model_apply model
                (model_apply model cons_value element_value)
                accumulated)) ->
        result
          (model_apply model
            (model_apply model
              (model_type_apply model encoded result)
              nil_value)
            cons_value).

Definition semantic_list_relation
    (model : RelModel)
    (list_relation_operator relation : SemanticRelation model) :
    SemanticRelation model :=
  model_relation_apply model list_relation_operator relation.

Theorem list_endomorphism_formula_semantics : forall
    (model : RelModel) type_environment relation_environment
    value_environment free_values free_relations,
  formula_sem model type_environment relation_environment
      value_environment free_values free_relations
      list_endomorphism_formula <->
  forall (A B : SemanticType model) (R : SemanticRelation model),
    relation_between R A B ->
    forall left_list,
      semantic_church_list model A left_list ->
    forall right_list,
      semantic_church_list model B right_list ->
      semantic_list_relation model (free_relations 0) R
        left_list right_list ->
      semantic_list_relation model (free_relations 0) R
        (model_apply model
          (model_type_apply model (free_values 0) A)
          left_list)
        (model_apply model
          (model_type_apply model (free_values 0) B)
          right_list).
Proof.
  reflexivity.
Qed.

(** The generator does not know the name [ListRel]: it expands the Church
    encoding.  This definition names that expanded relation directly. *)
Definition semantic_church_list_relation
    (model : RelModel)
    (A B : SemanticType model)
    (R : SemanticRelation model) : SemanticRelation model :=
  source_type_rel model (church_list_type (TVar 0))
    (env_extend A (fun _ => A))
    (env_extend B (fun _ => B))
    (env_extend R (fun _ => R)).

Theorem generated_list_endomorphism_formula_semantics : forall
    (model : RelModel) type_environment relation_environment
    value_environment free_values free_relations,
  formula_sem model type_environment relation_environment
      value_environment free_values free_relations
      (relgen polymorphic_list_endomorphism_type) <->
  forall (A B : SemanticType model) (R : SemanticRelation model),
    relation_between R A B ->
    forall left_list,
      semantic_church_list model A left_list ->
    forall right_list,
      semantic_church_list model B right_list ->
      semantic_church_list_relation model A B R
        left_list right_list ->
      semantic_church_list_relation model A B R
        (model_apply model
          (model_type_apply model (free_values 0) A)
          left_list)
        (model_apply model
          (model_type_apply model (free_values 0) B)
          right_list).
Proof.
  reflexivity.
Qed.

(** A model may expose the expanded Church relation through the named
    relation operator used by the pretty formula.  Keeping this law explicit
    records exactly what the presentation abbreviation assumes. *)
Definition ChurchListRelationAbbreviation
    (model : RelModel) (operator : SemanticRelation model) : Prop :=
  forall (A B : SemanticType model) (R : SemanticRelation model),
    relation_between R A B ->
    forall left right,
      semantic_list_relation model operator R left right <->
      semantic_church_list_relation model A B R left right.

Theorem list_relation_abbreviation_preserves_semantics : forall
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
  intros model type_environment relation_environment value_environment
    free_values free_relations Habbreviation.
  rewrite list_endomorphism_formula_semantics.
  rewrite generated_list_endomorphism_formula_semantics.
  split; intros H A B R HR left Hleft right Hright Hrelated.
  - apply (proj1 (Habbreviation A B R HR _ _)).
    apply H; try assumption.
    apply (proj2 (Habbreviation A B R HR _ _)).
    exact Hrelated.
  - apply (proj2 (Habbreviation A B R HR _ _)).
    apply H; try assumption.
    apply (proj1 (Habbreviation A B R HR _ _)).
    exact Hrelated.
Qed.

(** ** Specialisation to ordinary lists *)

Definition ListRel {A B : Type}
    (R : A -> B -> Prop) : list A -> list B -> Prop :=
  Forall2 R.

Definition relation_graph {A B : Type}
    (function : A -> B) : A -> B -> Prop :=
  fun left right => function left = right.

Theorem ListRel_graph_iff_map : forall
    (A B : Type) (function : A -> B) left right,
  ListRel (relation_graph function) left right <->
  map function left = right.
Proof.
  intros A B function left right.
  split.
  - intro Hrelated.
    induction Hrelated as [| x y left right Hxy Hrelated IH].
    + reflexivity.
    + cbn [relation_graph] in Hxy.
      cbn [map].
      now rewrite Hxy, IH.
  - intro Hequal.
    subst right.
    induction left as [| x left IH]; cbn [map].
    + constructor.
    + constructor.
      * reflexivity.
      * exact IH.
Qed.

Definition PolymorphicListEndomorphism : Type :=
  forall A : Type, list A -> list A.

(** This is the readable free theorem generated for
    [forall a. list a -> list a]. *)
Definition ListEndomorphismParametric
    (function : PolymorphicListEndomorphism) : Prop :=
  forall (A B : Type) (R : A -> B -> Prop) left right,
    ListRel R left right ->
    ListRel R (function A left) (function B right).

(** Choosing [R x y := f x = y] turns both [ListRel] occurrences into
    equations about [map]. *)
Theorem list_endomorphism_map_law : forall
    (function : PolymorphicListEndomorphism),
  ListEndomorphismParametric function ->
  forall (A B : Type) (mapping : A -> B) (values : list A),
    map mapping (function A values) =
    function B (map mapping values).
Proof.
  intros function Hparametric A B mapping values.
  apply (proj1
    (ListRel_graph_iff_map A B mapping
      (function A values)
      (function B (map mapping values)))).
  apply Hparametric.
  apply (proj2
    (ListRel_graph_iff_map A B mapping values (map mapping values))).
  reflexivity.
Qed.
