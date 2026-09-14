(** * Printable relational formulas

    The relational translation is syntax, not a [Prop]-valued semantic
    function.  Its output must survive extraction so that the OCaml driver
    can print it.  Type, relation, and value variables therefore have three
    independent de Bruijn namespaces.

    [FormulaType] annotates quantified values and explicit type applications.
    [ValueExpr] contains only the neutral expressions needed by generated
    formulas.  [RelationExpr] admits named relation combinators in addition
    to bound relations; this leaves room for later presentation-only
    abbreviations such as [ListRel] and relation graphs. *)

From Stdlib Require Import Lia PeanoNat.

Implicit Types
  (cutoff type_depth relation_depth value_depth : nat).

(** Types appearing inside formulas.  Their variables use the type-variable
    namespace of the enclosing [RelFormula]. *)
Inductive FormulaType : Type :=
| RTVar : nat -> FormulaType
| RTArrow : FormulaType -> FormulaType -> FormulaType
| RTForall : FormulaType -> FormulaType.

(** Neutral value expressions.  Bound variables are shifted by value
    binders; free symbols are stable identifiers intended for printers and
    later formula specialisation. *)
Inductive ValueExpr : Type :=
| RVBound : nat -> ValueExpr
| RVFree : nat -> ValueExpr
| RVApp : ValueExpr -> ValueExpr -> ValueExpr
| RVTypeApp : ValueExpr -> FormulaType -> ValueExpr.

(** Relations have their own namespace.  [RRApp] represents application of
    a relation operator to another relation, for example [ListRel R]. *)
Inductive RelationExpr : Type :=
| RRBound : nat -> RelationExpr
| RRFree : nat -> RelationExpr
| RRApp : RelationExpr -> RelationExpr -> RelationExpr.

(** [RFForallValue A body] binds one value of type [A].
    [RFForallType body] binds one type.
    [RFForallRelation A B body] binds one relation from [A] to [B]. *)
Inductive RelFormula : Type :=
| RFTop : RelFormula
| RFRel : RelationExpr -> ValueExpr -> ValueExpr -> RelFormula
| RFEqual : ValueExpr -> ValueExpr -> RelFormula
| RFAnd : RelFormula -> RelFormula -> RelFormula
| RFImplies : RelFormula -> RelFormula -> RelFormula
| RFForallValue : FormulaType -> RelFormula -> RelFormula
| RFForallType : RelFormula -> RelFormula
| RFForallRelation : FormulaType -> FormulaType ->
    RelFormula -> RelFormula.

(** ** Capture-avoiding weakening in the three namespaces *)

Definition lift_index (cutoff index : nat) : nat :=
  if index <? cutoff then index else S index.

Fixpoint formula_type_lift
    (cutoff : nat) (T : FormulaType) : FormulaType :=
  match T with
  | RTVar index => RTVar (lift_index cutoff index)
  | RTArrow T U =>
      RTArrow
        (formula_type_lift cutoff T)
        (formula_type_lift cutoff U)
  | RTForall T => RTForall (formula_type_lift (S cutoff) T)
  end.

Fixpoint value_lift (cutoff : nat) (value : ValueExpr) : ValueExpr :=
  match value with
  | RVBound index => RVBound (lift_index cutoff index)
  | RVFree name => RVFree name
  | RVApp function argument =>
      RVApp (value_lift cutoff function) (value_lift cutoff argument)
  | RVTypeApp function T => RVTypeApp (value_lift cutoff function) T
  end.

(** Type weakening inside a value expression is separate from value
    weakening because the namespaces do not interact. *)
Fixpoint value_type_lift
    (cutoff : nat) (value : ValueExpr) : ValueExpr :=
  match value with
  | RVBound index => RVBound index
  | RVFree name => RVFree name
  | RVApp function argument =>
      RVApp
        (value_type_lift cutoff function)
        (value_type_lift cutoff argument)
  | RVTypeApp function T =>
      RVTypeApp
        (value_type_lift cutoff function)
        (formula_type_lift cutoff T)
  end.

Fixpoint relation_lift
    (cutoff : nat) (relation : RelationExpr) : RelationExpr :=
  match relation with
  | RRBound index => RRBound (lift_index cutoff index)
  | RRFree name => RRFree name
  | RRApp constructor argument =>
      RRApp
        (relation_lift cutoff constructor)
        (relation_lift cutoff argument)
  end.

Fixpoint formula_value_lift
    (cutoff : nat) (formula : RelFormula) : RelFormula :=
  match formula with
  | RFTop => RFTop
  | RFRel relation lhs rhs =>
      RFRel relation (value_lift cutoff lhs) (value_lift cutoff rhs)
  | RFEqual lhs rhs =>
      RFEqual (value_lift cutoff lhs) (value_lift cutoff rhs)
  | RFAnd lhs rhs =>
      RFAnd
        (formula_value_lift cutoff lhs)
        (formula_value_lift cutoff rhs)
  | RFImplies premise conclusion =>
      RFImplies
        (formula_value_lift cutoff premise)
        (formula_value_lift cutoff conclusion)
  | RFForallValue T body =>
      RFForallValue T (formula_value_lift (S cutoff) body)
  | RFForallType body =>
      RFForallType (formula_value_lift cutoff body)
  | RFForallRelation T U body =>
      RFForallRelation T U (formula_value_lift cutoff body)
  end.

Fixpoint formula_type_lift_in
    (cutoff : nat) (formula : RelFormula) : RelFormula :=
  match formula with
  | RFTop => RFTop
  | RFRel relation lhs rhs =>
      RFRel relation
        (value_type_lift cutoff lhs)
        (value_type_lift cutoff rhs)
  | RFEqual lhs rhs =>
      RFEqual
        (value_type_lift cutoff lhs)
        (value_type_lift cutoff rhs)
  | RFAnd lhs rhs =>
      RFAnd
        (formula_type_lift_in cutoff lhs)
        (formula_type_lift_in cutoff rhs)
  | RFImplies premise conclusion =>
      RFImplies
        (formula_type_lift_in cutoff premise)
        (formula_type_lift_in cutoff conclusion)
  | RFForallValue T body =>
      RFForallValue
        (formula_type_lift cutoff T)
        (formula_type_lift_in cutoff body)
  | RFForallType body =>
      RFForallType (formula_type_lift_in (S cutoff) body)
  | RFForallRelation T U body =>
      RFForallRelation
        (formula_type_lift cutoff T)
        (formula_type_lift cutoff U)
        (formula_type_lift_in cutoff body)
  end.

Fixpoint formula_relation_lift
    (cutoff : nat) (formula : RelFormula) : RelFormula :=
  match formula with
  | RFTop => RFTop
  | RFRel relation lhs rhs =>
      RFRel (relation_lift cutoff relation) lhs rhs
  | RFEqual lhs rhs => RFEqual lhs rhs
  | RFAnd lhs rhs =>
      RFAnd
        (formula_relation_lift cutoff lhs)
        (formula_relation_lift cutoff rhs)
  | RFImplies premise conclusion =>
      RFImplies
        (formula_relation_lift cutoff premise)
        (formula_relation_lift cutoff conclusion)
  | RFForallValue T body =>
      RFForallValue T (formula_relation_lift cutoff body)
  | RFForallType body =>
      RFForallType (formula_relation_lift cutoff body)
  | RFForallRelation T U body =>
      RFForallRelation T U (formula_relation_lift (S cutoff) body)
  end.

(** ** Scope predicates *)

Fixpoint formula_type_scoped
    (type_depth : nat) (T : FormulaType) : Prop :=
  match T with
  | RTVar index => index < type_depth
  | RTArrow T U =>
      formula_type_scoped type_depth T /\
      formula_type_scoped type_depth U
  | RTForall T => formula_type_scoped (S type_depth) T
  end.

Fixpoint value_scoped
    (type_depth value_depth : nat) (value : ValueExpr) : Prop :=
  match value with
  | RVBound index => index < value_depth
  | RVFree _ => True
  | RVApp function argument =>
      value_scoped type_depth value_depth function /\
      value_scoped type_depth value_depth argument
  | RVTypeApp function T =>
      value_scoped type_depth value_depth function /\
      formula_type_scoped type_depth T
  end.

Fixpoint relation_scoped
    (relation_depth : nat) (relation : RelationExpr) : Prop :=
  match relation with
  | RRBound index => index < relation_depth
  | RRFree _ => True
  | RRApp constructor argument =>
      relation_scoped relation_depth constructor /\
      relation_scoped relation_depth argument
  end.

Fixpoint formula_scoped
    (type_depth relation_depth value_depth : nat)
    (formula : RelFormula) : Prop :=
  match formula with
  | RFTop => True
  | RFRel relation lhs rhs =>
      relation_scoped relation_depth relation /\
      value_scoped type_depth value_depth lhs /\
      value_scoped type_depth value_depth rhs
  | RFEqual lhs rhs =>
      value_scoped type_depth value_depth lhs /\
      value_scoped type_depth value_depth rhs
  | RFAnd lhs rhs | RFImplies lhs rhs =>
      formula_scoped type_depth relation_depth value_depth lhs /\
      formula_scoped type_depth relation_depth value_depth rhs
  | RFForallValue T body =>
      formula_type_scoped type_depth T /\
      formula_scoped type_depth relation_depth (S value_depth) body
  | RFForallType body =>
      formula_scoped (S type_depth) relation_depth value_depth body
  | RFForallRelation T U body =>
      formula_type_scoped type_depth T /\
      formula_type_scoped type_depth U /\
      formula_scoped type_depth (S relation_depth) value_depth body
  end.

(** A generated top-level theorem has no free de Bruijn indices.  Named
    [RVFree]/[RRFree] symbols remain allowed as part of the presentation
    language. *)
Definition closed_formula (formula : RelFormula) : Prop :=
  formula_scoped 0 0 0 formula.
