(** * Correctness of relational-formula generation

    The generated syntax is interpreted in an abstract realizability model.
    Values form one carrier; semantic types are predicates on values and
    semantic relations are binary predicates.  The model supplies term and
    type application.  Extensionality of type application is an explicit
    model law rather than a global axiom.

    [source_type_rel] is the direct relational interpretation of a System F
    type.  Its variable, arrow, and universal cases are the corresponding
    clauses of Atkey's [ty_rel], presented over an untyped carrier so that the
    development does not require [-impredicative-set].  The main theorem
    [relate_correct] states that interpreting the printable formula produced
    by [relate] is equivalent to this direct interpretation.

    This is correctness of formula generation.  The fundamental theorem that
    a well-typed System F term is related to itself is a separate result. *)

From Stdlib Require Import Lia PeanoNat.

From SystemF.F Require Import Syntax.
From SystemF.FreeTheorems Require Import Formula Generate.

Record RelModel : Type := {
  model_value : Type;
  model_apply : model_value -> model_value -> model_value;
  model_type_apply :
    model_value -> (model_value -> Prop) -> model_value;
  model_type_apply_ext : forall value A B,
    (forall argument, A argument <-> B argument) ->
    model_type_apply value A = model_type_apply value B;
  model_relation_apply :
    (model_value -> model_value -> Prop) ->
    (model_value -> model_value -> Prop) ->
    model_value -> model_value -> Prop
}.

Definition SemanticType (model : RelModel) : Type :=
  model_value model -> Prop.

Definition SemanticRelation (model : RelModel) : Type :=
  model_value model -> model_value model -> Prop.

Definition Environment (A : Type) : Type := nat -> A.

Definition env_extend {A : Type}
    (head : A) (tail : Environment A) : Environment A :=
  fun index =>
    match index with
    | 0 => head
    | S index => tail index
    end.

Fixpoint formula_type_sem
    (model : RelModel)
    (type_environment : Environment (SemanticType model))
    (T : FormulaType) : SemanticType model :=
  match T with
  | RTVar index => type_environment index
  | RTArrow A B =>
      fun function =>
        forall argument,
          formula_type_sem model type_environment A argument ->
          formula_type_sem model type_environment B
            (model_apply model function argument)
  | RTForall body =>
      fun function =>
        forall A : SemanticType model,
          formula_type_sem model (env_extend A type_environment) body
            (model_type_apply model function A)
  end.

Fixpoint value_sem
    (model : RelModel)
    (type_environment : Environment (SemanticType model))
    (value_environment : Environment (model_value model))
    (free_values : Environment (model_value model))
    (value : ValueExpr) : model_value model :=
  match value with
  | RVBound index => value_environment index
  | RVFree name => free_values name
  | RVApp function argument =>
      model_apply model
        (value_sem model type_environment value_environment
          free_values function)
        (value_sem model type_environment value_environment
          free_values argument)
  | RVTypeApp function T =>
      model_type_apply model
        (value_sem model type_environment value_environment
          free_values function)
        (formula_type_sem model type_environment T)
  end.

Fixpoint relation_sem
    (model : RelModel)
    (relation_environment : Environment (SemanticRelation model))
    (free_relations : Environment (SemanticRelation model))
    (relation : RelationExpr) : SemanticRelation model :=
  match relation with
  | RRBound index => relation_environment index
  | RRFree name => free_relations name
  | RRApp constructor argument =>
      model_relation_apply model
        (relation_sem model relation_environment free_relations constructor)
        (relation_sem model relation_environment free_relations argument)
  end.

Definition relation_between
    {model : RelModel}
    (relation : SemanticRelation model)
    (left right : SemanticType model) : Prop :=
  forall left_value right_value,
    relation left_value right_value ->
    left left_value /\ right right_value.

Fixpoint formula_sem
    (model : RelModel)
    (type_environment : Environment (SemanticType model))
    (relation_environment : Environment (SemanticRelation model))
    (value_environment : Environment (model_value model))
    (free_values : Environment (model_value model))
    (free_relations : Environment (SemanticRelation model))
    (formula : RelFormula) : Prop :=
  match formula with
  | RFTop => True
  | RFRel relation lhs rhs =>
      relation_sem model relation_environment free_relations relation
        (value_sem model type_environment value_environment free_values lhs)
        (value_sem model type_environment value_environment free_values rhs)
  | RFEqual lhs rhs =>
      value_sem model type_environment value_environment free_values lhs =
      value_sem model type_environment value_environment free_values rhs
  | RFAnd lhs rhs =>
      formula_sem model type_environment relation_environment
        value_environment free_values free_relations lhs /\
      formula_sem model type_environment relation_environment
        value_environment free_values free_relations rhs
  | RFImplies premise conclusion =>
      formula_sem model type_environment relation_environment
        value_environment free_values free_relations premise ->
      formula_sem model type_environment relation_environment
        value_environment free_values free_relations conclusion
  | RFForallValue T body =>
      forall value : model_value model,
        formula_type_sem model type_environment T value ->
        formula_sem model type_environment relation_environment
          (env_extend value value_environment)
          free_values free_relations body
  | RFForallType body =>
      forall A : SemanticType model,
        formula_sem model (env_extend A type_environment)
          relation_environment value_environment
          free_values free_relations body
  | RFForallRelation A B body =>
      forall relation : SemanticRelation model,
        relation_between relation
          (formula_type_sem model type_environment A)
          (formula_type_sem model type_environment B) ->
        formula_sem model type_environment
          (env_extend relation relation_environment)
          value_environment free_values free_relations body
  end.

(** ** Direct interpretation of source types *)

Fixpoint source_type_sem
    (model : RelModel)
    (type_environment : Environment (SemanticType model))
    (T : type) : SemanticType model :=
  match T with
  | TVar index => type_environment index
  | TArrow A B =>
      fun function =>
        forall argument,
          source_type_sem model type_environment A argument ->
          source_type_sem model type_environment B
            (model_apply model function argument)
  | TForall body =>
      fun function =>
        forall A : SemanticType model,
          source_type_sem model (env_extend A type_environment) body
            (model_type_apply model function A)
  end.

Fixpoint source_type_rel
    (model : RelModel)
    (T : type)
    (left_types right_types : Environment (SemanticType model))
    (relations : Environment (SemanticRelation model))
    (lhs rhs : model_value model) : Prop :=
  match T with
  | TVar index => relations index lhs rhs
  | TArrow A B =>
      forall left_argument,
        source_type_sem model left_types A left_argument ->
      forall right_argument,
        source_type_sem model right_types A right_argument ->
        source_type_rel model A left_types right_types relations
          left_argument right_argument ->
        source_type_rel model B left_types right_types relations
          (model_apply model lhs left_argument)
          (model_apply model rhs right_argument)
  | TForall body =>
      forall (left_type right_type : SemanticType model)
          (relation : SemanticRelation model),
        relation_between relation left_type right_type ->
        source_type_rel model body
          (env_extend left_type left_types)
          (env_extend right_type right_types)
          (env_extend relation relations)
          (model_type_apply model lhs left_type)
          (model_type_apply model rhs right_type)
  end.

(** ** Environment and weakening lemmas *)

Definition renaming_environment
    {model : RelModel}
    (rho : nat -> nat)
    (formula_environment source_environment :
      Environment (SemanticType model)) : Prop :=
  forall index value,
    formula_environment (rho index) value <->
    source_environment index value.

Lemma project_type_with_correct : forall (model : RelModel) T rho
    formula_environment source_environment,
  renaming_environment rho formula_environment source_environment ->
  forall value,
    formula_type_sem model formula_environment
      (project_type_with rho T) value <->
    source_type_sem model source_environment T value.
Proof.
  intros model T.
  induction T as [index | A IHA B IHB | body IHbody];
    intros rho formula_environment source_environment Hrenamed value.
  - apply Hrenamed.
  - cbn [project_type_with formula_type_sem source_type_sem].
    split; intros H argument Hargument.
    + apply (proj1
        (IHB rho formula_environment source_environment
          Hrenamed (model_apply model value argument))).
      apply H.
      apply (proj2
        (IHA rho formula_environment source_environment
          Hrenamed argument)).
      exact Hargument.
    + apply (proj2
        (IHB rho formula_environment source_environment
          Hrenamed (model_apply model value argument))).
      apply H.
      apply (proj1
        (IHA rho formula_environment source_environment
          Hrenamed argument)).
      exact Hargument.
  - cbn [project_type_with formula_type_sem source_type_sem].
    split; intros H A.
    + assert (HrenamedA :
          renaming_environment (lift_type_renaming rho)
            (env_extend A formula_environment)
            (env_extend A source_environment)).
      { intros [| index] argument;
          cbn [lift_type_renaming env_extend].
        - reflexivity.
        - apply Hrenamed. }
      apply (proj1
        (IHbody (lift_type_renaming rho)
          (env_extend A formula_environment)
          (env_extend A source_environment) HrenamedA
          (model_type_apply model value A))).
      apply H.
    + assert (HrenamedA :
          renaming_environment (lift_type_renaming rho)
            (env_extend A formula_environment)
            (env_extend A source_environment)).
      { intros [| index] argument;
          cbn [lift_type_renaming env_extend].
        - reflexivity.
        - apply Hrenamed. }
      apply (proj2
        (IHbody (lift_type_renaming rho)
          (env_extend A formula_environment)
          (env_extend A source_environment) HrenamedA
          (model_type_apply model value A))).
      apply H.
Qed.

Definition paired_type_environment
    {model : RelModel}
    (formula_environment left_environment right_environment :
      Environment (SemanticType model)) : Prop :=
  forall index value,
    (formula_environment (projection_index ProjectLeft index) value <->
      left_environment index value) /\
    (formula_environment (projection_index ProjectRight index) value <->
      right_environment index value).

Corollary project_type_correct : forall (model : RelModel) projection T
    formula_environment left_environment right_environment,
  paired_type_environment formula_environment
    left_environment right_environment ->
  forall value,
    formula_type_sem model formula_environment
      (project_type projection T) value <->
    source_type_sem model
      (match projection with
       | ProjectLeft => left_environment
       | ProjectRight => right_environment
       end) T value.
Proof.
  intros model projection T formula_environment
    left_environment right_environment Hpaired value.
  unfold project_type.
  apply project_type_with_correct.
  intros index argument.
  specialize (Hpaired index argument).
  destruct projection; tauto.
Qed.

Lemma paired_type_environment_extend : forall (model : RelModel)
    (formula_environment left_environment right_environment :
      Environment (SemanticType model))
    (left_type right_type : SemanticType model),
  paired_type_environment formula_environment
    left_environment right_environment ->
  paired_type_environment
    (env_extend right_type (env_extend left_type formula_environment))
    (env_extend left_type left_environment)
    (env_extend right_type right_environment).
Proof.
  intros model formula_environment left_environment right_environment
    left_type right_type Hpaired [| index] value.
  - cbn [projection_index env_extend].
    tauto.
  - cbn [projection_index env_extend].
    replace (2 * S index) with (S (S (2 * index))) by lia.
    cbn [env_extend].
    apply Hpaired.
Qed.

Definition lifted_type_environment
    {model : RelModel}
    (cutoff : nat)
    (new_environment old_environment :
      Environment (SemanticType model)) : Prop :=
  forall index value,
    new_environment (lift_index cutoff index) value <->
    old_environment index value.

Lemma lifted_type_environment_under_binder : forall (model : RelModel) cutoff
    (new_environment old_environment :
      Environment (SemanticType model))
    (A : SemanticType model),
  lifted_type_environment cutoff new_environment old_environment ->
  lifted_type_environment (S cutoff)
    (env_extend A new_environment) (env_extend A old_environment).
Proof.
  intros model cutoff new_environment old_environment A Hlift
    [| index] value.
  - cbn [lift_index env_extend].
    reflexivity.
  - unfold lift_index at 1.
    cbn [env_extend].
    change
      (env_extend A new_environment
        (if index <? cutoff then S index else S (S index)) value <->
       old_environment index value).
    destruct (index <? cutoff) eqn:Hindex;
      cbn [env_extend].
    + specialize (Hlift index value).
      unfold lift_index in Hlift.
      rewrite Hindex in Hlift.
      exact Hlift.
    + specialize (Hlift index value).
      unfold lift_index in Hlift.
      rewrite Hindex in Hlift.
      exact Hlift.
Qed.

Lemma formula_type_lift_correct : forall (model : RelModel) T cutoff
    new_environment old_environment,
  lifted_type_environment cutoff new_environment old_environment ->
  forall value,
    formula_type_sem model new_environment
      (formula_type_lift cutoff T) value <->
    formula_type_sem model old_environment T value.
Proof.
  intros model T.
  induction T as [index | A IHA B IHB | body IHbody];
    intros cutoff new_environment old_environment Hlift value.
  - apply Hlift.
  - cbn [formula_type_lift formula_type_sem].
    split; intros H argument Hargument.
    + apply (proj1
        (IHB cutoff new_environment old_environment Hlift
          (model_apply model value argument))).
      apply H.
      apply (proj2
        (IHA cutoff new_environment old_environment Hlift argument)).
      exact Hargument.
    + apply (proj2
        (IHB cutoff new_environment old_environment Hlift
          (model_apply model value argument))).
      apply H.
      apply (proj1
        (IHA cutoff new_environment old_environment Hlift argument)).
      exact Hargument.
  - cbn [formula_type_lift formula_type_sem].
    split; intros H A.
    + apply (proj1
        (IHbody (S cutoff)
          (env_extend A new_environment)
          (env_extend A old_environment)
          (lifted_type_environment_under_binder model cutoff
            new_environment old_environment A Hlift)
          (model_type_apply model value A))).
      apply H.
    + apply (proj2
        (IHbody (S cutoff)
          (env_extend A new_environment)
          (env_extend A old_environment)
          (lifted_type_environment_under_binder model cutoff
            new_environment old_environment A Hlift)
          (model_type_apply model value A))).
      apply H.
Qed.

Definition lifted_value_environment
    {model : RelModel}
    (cutoff : nat)
    (new_environment old_environment :
      Environment (model_value model)) : Prop :=
  forall index,
    new_environment (lift_index cutoff index) = old_environment index.

Lemma value_lift_correct : forall (model : RelModel) value cutoff type_environment
    new_environment old_environment free_values,
  lifted_value_environment cutoff new_environment old_environment ->
  value_sem model type_environment new_environment free_values
    (value_lift cutoff value) =
  value_sem model type_environment old_environment free_values value.
Proof.
  intros model value.
  induction value as
      [index | name | function IHfunction argument IHargument
       | function IHfunction T];
    intros cutoff type_environment new_environment old_environment
      free_values Hlift;
    cbn [value_lift value_sem].
  - apply Hlift.
  - reflexivity.
  - now rewrite (IHfunction cutoff type_environment new_environment
        old_environment free_values Hlift),
      (IHargument cutoff type_environment new_environment
        old_environment free_values Hlift).
  - now rewrite (IHfunction cutoff type_environment new_environment
        old_environment free_values Hlift).
Qed.

Lemma value_type_lift_correct : forall (model : RelModel) value cutoff
    new_type_environment old_type_environment
    value_environment free_values,
  lifted_type_environment cutoff
    new_type_environment old_type_environment ->
  value_sem model new_type_environment value_environment free_values
    (value_type_lift cutoff value) =
  value_sem model old_type_environment value_environment free_values value.
Proof.
  intros model value.
  induction value as
      [index | name | function IHfunction argument IHargument
       | function IHfunction T];
    intros cutoff new_type_environment old_type_environment
      value_environment free_values Hlift;
    cbn [value_type_lift value_sem].
  - reflexivity.
  - reflexivity.
  - now rewrite (IHfunction cutoff new_type_environment
        old_type_environment value_environment free_values Hlift),
      (IHargument cutoff new_type_environment
        old_type_environment value_environment free_values Hlift).
  - rewrite (IHfunction cutoff new_type_environment
      old_type_environment value_environment free_values Hlift).
    apply model_type_apply_ext.
    intro argument.
    apply formula_type_lift_correct.
    exact Hlift.
Qed.

Lemma env_extend_lift_zero : forall A (head : A) tail index,
  env_extend head tail (lift_index 0 index) = tail index.
Proof.
  intros A head tail index.
  unfold lift_index.
  destruct (index <? 0) eqn:Hindex.
  - apply Nat.ltb_lt in Hindex.
    lia.
  - reflexivity.
Qed.

Lemma value_weaken_twice_correct : forall (model : RelModel) value type_environment
    value_environment free_values left_value right_value,
  value_sem model type_environment
    (env_extend right_value (env_extend left_value value_environment))
    free_values (value_weaken_twice value) =
  value_sem model type_environment value_environment free_values value.
Proof.
  intros model value type_environment value_environment free_values
    left_value right_value.
  unfold value_weaken_twice.
  rewrite (value_lift_correct model (value_lift 0 value) 0
    type_environment
    (env_extend right_value (env_extend left_value value_environment))
    (env_extend left_value value_environment) free_values).
  - apply value_lift_correct.
    intros index.
    apply env_extend_lift_zero.
  - intros index.
    apply env_extend_lift_zero.
Qed.

Lemma value_type_weaken_twice_correct : forall (model : RelModel) value
    type_environment value_environment free_values
    left_type right_type,
  value_sem model
    (env_extend right_type (env_extend left_type type_environment))
    value_environment free_values (value_type_weaken_twice value) =
  value_sem model type_environment value_environment free_values value.
Proof.
  intros model value type_environment value_environment free_values
    left_type right_type.
  unfold value_type_weaken_twice.
  rewrite (value_type_lift_correct model (value_type_lift 0 value) 0
    (env_extend right_type (env_extend left_type type_environment))
    (env_extend left_type type_environment)
    value_environment free_values).
  - apply value_type_lift_correct.
    intros index argument.
    rewrite env_extend_lift_zero.
    reflexivity.
  - intros index argument.
    rewrite env_extend_lift_zero.
    reflexivity.
Qed.

(** ** Generator correspondence *)

Theorem relate_correct : forall (model : RelModel) T
    formula_types left_types right_types relations
    values free_values free_relations lhs rhs,
  paired_type_environment formula_types left_types right_types ->
  formula_sem model formula_types relations values
      free_values free_relations (relate T lhs rhs) <->
  source_type_rel model T left_types right_types relations
    (value_sem model formula_types values free_values lhs)
    (value_sem model formula_types values free_values rhs).
Proof.
  intros model T.
  induction T as [index | A IHA B IHB | body IHbody];
    intros formula_types left_types right_types relations
      values free_values free_relations lhs rhs Hpaired.
  - reflexivity.
  - cbn [relate formula_sem source_type_rel].
    split.
    + intros H left_argument Hleft right_argument Hright Hrelated.
      rewrite <- (value_weaken_twice_correct model lhs formula_types
        values free_values left_argument right_argument).
      rewrite <- (value_weaken_twice_correct model rhs formula_types
        values free_values left_argument right_argument).
      apply (proj1
        (IHB formula_types left_types right_types relations
          (env_extend right_argument (env_extend left_argument values))
          free_values free_relations
          (RVApp (value_weaken_twice lhs) (RVBound 1))
          (RVApp (value_weaken_twice rhs) (RVBound 0)) Hpaired)).
      apply H.
      * apply (proj2
          (project_type_correct model ProjectLeft A formula_types
            left_types right_types Hpaired left_argument)).
        exact Hleft.
      * apply (proj2
          (project_type_correct model ProjectRight A formula_types
            left_types right_types Hpaired right_argument)).
        exact Hright.
      * apply (proj2
          (IHA formula_types left_types right_types relations
            (env_extend right_argument (env_extend left_argument values))
            free_values free_relations
            (RVBound 1) (RVBound 0) Hpaired)).
        exact Hrelated.
    + intros H left_argument Hleft right_argument Hright Hrelated.
      apply (proj2
        (IHB formula_types left_types right_types relations
          (env_extend right_argument (env_extend left_argument values))
          free_values free_relations
          (RVApp (value_weaken_twice lhs) (RVBound 1))
          (RVApp (value_weaken_twice rhs) (RVBound 0)) Hpaired)).
      cbn [value_sem env_extend].
      rewrite !value_weaken_twice_correct.
      apply H.
      * apply (proj1
          (project_type_correct model ProjectLeft A formula_types
            left_types right_types Hpaired left_argument)).
        exact Hleft.
      * apply (proj1
          (project_type_correct model ProjectRight A formula_types
            left_types right_types Hpaired right_argument)).
        exact Hright.
      * apply (proj1
          (IHA formula_types left_types right_types relations
            (env_extend right_argument (env_extend left_argument values))
            free_values free_relations
            (RVBound 1) (RVBound 0) Hpaired)).
        exact Hrelated.
  - cbn [relate formula_sem source_type_rel].
    split.
    + intros H left_type right_type relation Hrelation.
      rewrite <- (value_type_weaken_twice_correct model lhs formula_types
        values free_values left_type right_type).
      rewrite <- (value_type_weaken_twice_correct model rhs formula_types
        values free_values left_type right_type).
      apply (proj1
        (IHbody
          (env_extend right_type (env_extend left_type formula_types))
          (env_extend left_type left_types)
          (env_extend right_type right_types)
          (env_extend relation relations)
          values free_values free_relations
          (RVTypeApp (value_type_weaken_twice lhs) (RTVar 1))
          (RVTypeApp (value_type_weaken_twice rhs) (RTVar 0))
          (paired_type_environment_extend model formula_types
            left_types right_types left_type right_type Hpaired))).
      apply H.
      exact Hrelation.
    + intros H left_type right_type relation Hrelation.
      apply (proj2
        (IHbody
          (env_extend right_type (env_extend left_type formula_types))
          (env_extend left_type left_types)
          (env_extend right_type right_types)
          (env_extend relation relations)
          values free_values free_relations
          (RVTypeApp (value_type_weaken_twice lhs) (RTVar 1))
          (RVTypeApp (value_type_weaken_twice rhs) (RTVar 0))
          (paired_type_environment_extend model formula_types
            left_types right_types left_type right_type Hpaired))).
      cbn [value_sem formula_type_sem env_extend].
      rewrite !value_type_weaken_twice_correct.
      apply H.
      exact Hrelation.
Qed.

Corollary relgen_correct : forall (model : RelModel) T
    formula_types left_types right_types relations
    values free_values free_relations,
  paired_type_environment formula_types left_types right_types ->
  formula_sem model formula_types relations values
      free_values free_relations (relgen T) <->
  source_type_rel model T left_types right_types relations
    (free_values 0) (free_values 0).
Proof.
  intros model T formula_types left_types right_types relations
    values free_values free_relations Hpaired.
  unfold relgen.
  apply relate_correct.
  exact Hpaired.
Qed.

(** The familiar reading of the first generated example. *)
Corollary polymorphic_identity_semantics : forall (model : RelModel)
    formula_types relations values free_values free_relations,
  formula_sem model formula_types relations values free_values free_relations
      (relgen (TForall (TArrow (TVar 0) (TVar 0)))) <->
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
  reflexivity.
Qed.
