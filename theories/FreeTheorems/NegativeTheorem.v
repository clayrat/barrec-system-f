(** * A type variable in negative position

    In [forall a. (a -> a) -> a -> a], the quantified variable occurs on
    both sides of the argument endomorphism.  Relational translation therefore
    does not permit arbitrary functions on the two endpoints: it introduces
    the premise that they send related inputs to related outputs. *)

From Stdlib Require Import Bool List Lia.

From SystemF.F Require Import Syntax Scope.
From SystemF.FreeTheorems Require Import
  Formula Generate Correctness ListTheorem.

Definition negative_occurrence_type : type :=
  TForall
    (TArrow
      (TArrow (TVar 0) (TVar 0))
      (TArrow (TVar 0) (TVar 0))).

Theorem negative_occurrence_type_closed :
  closed 0 negative_occurrence_type.
Proof.
  cbn [negative_occurrence_type closed].
  lia.
Qed.

(** With endpoint functions [f] and [g] already bound, this is their
    compatibility condition:

      forall x y, R x y -> R (f x) (g y). *)
Definition endomorphisms_agree_formula : RelFormula :=
  RFForallValue (RTVar 1)
    (RFForallValue (RTVar 0)
      (RFImplies
        (RFRel (RRBound 0) (RVBound 1) (RVBound 0))
        (RFRel (RRBound 0)
          (RVApp (RVBound 3) (RVBound 1))
          (RVApp (RVBound 2) (RVBound 0))))).

Definition negative_occurrence_formula : RelFormula :=
  RFForallType
    (RFForallType
      (RFForallRelation (RTVar 1) (RTVar 0)
        (RFForallValue (RTArrow (RTVar 1) (RTVar 1))
          (RFForallValue (RTArrow (RTVar 0) (RTVar 0))
            (RFImplies endomorphisms_agree_formula
              (RFForallValue (RTVar 1)
                (RFForallValue (RTVar 0)
                  (RFImplies
                    (RFRel (RRBound 0) (RVBound 1) (RVBound 0))
                    (RFRel (RRBound 0)
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

(** Unlike the Church abbreviations in the list examples, this is literally
    the formula computed by the generic generator. *)
Theorem relgen_negative_occurrence :
  relgen negative_occurrence_type = negative_occurrence_formula.
Proof.
  reflexivity.
Qed.

Theorem negative_occurrence_formula_closed :
  closed_formula negative_occurrence_formula.
Proof.
  vm_compute.
  lia.
Qed.

Theorem negative_occurrence_formula_semantics : forall
    (model : RelModel) type_environment relation_environment
    value_environment free_values free_relations,
  formula_sem model type_environment relation_environment
      value_environment free_values free_relations
      negative_occurrence_formula <->
  forall (A B : SemanticType model) (R : SemanticRelation model),
    relation_between R A B ->
    forall left_function,
      (forall value,
        A value -> A (model_apply model left_function value)) ->
    forall right_function,
      (forall value,
        B value -> B (model_apply model right_function value)) ->
      (forall left_value,
        A left_value ->
        forall right_value,
          B right_value ->
          R left_value right_value ->
          R (model_apply model left_function left_value)
            (model_apply model right_function right_value)) ->
    forall left_value,
      A left_value ->
    forall right_value,
      B right_value ->
      R left_value right_value ->
      R
        (model_apply model
          (model_apply model
            (model_type_apply model (free_values 0) A)
            left_function)
          left_value)
        (model_apply model
          (model_apply model
            (model_type_apply model (free_values 0) B)
            right_function)
          right_value).
Proof.
  reflexivity.
Qed.

(** ** Familiar reading over ordinary functions *)

Definition EndomorphismsAgree {A B : Type}
    (R : A -> B -> Prop) (left : A -> A) (right : B -> B) : Prop :=
  forall x y, R x y -> R (left x) (right y).

Definition PolymorphicIterator : Type :=
  forall A : Type, (A -> A) -> A -> A.

Definition IteratorParametric (iterator : PolymorphicIterator) : Prop :=
  forall (A B : Type) (R : A -> B -> Prop)
      (left_function : A -> A) (right_function : B -> B),
    EndomorphismsAgree R left_function right_function ->
    forall left_value right_value,
      R left_value right_value ->
      R
        (iterator A left_function left_value)
        (iterator B right_function right_value).

Theorem endomorphisms_agree_graph_iff : forall
    (A B : Type) (mapping : A -> B)
    (left_function : A -> A) (right_function : B -> B),
  EndomorphismsAgree (relation_graph mapping)
      left_function right_function <->
  forall value,
    mapping (left_function value) = right_function (mapping value).
Proof.
  intros A B mapping left_function right_function.
  split.
  - intros Hagree value.
    apply (Hagree value (mapping value)).
    reflexivity.
  - intros Hcommutes x y Hgraph.
    unfold relation_graph in *.
    subst y.
    apply Hcommutes.
Qed.

(** Graph specialisation now needs the commuting-square premise.  This is
    precisely the extra hypothesis introduced by the negative occurrence. *)
Theorem negative_occurrence_naturality : forall
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
  intros iterator Hparametric A B mapping left_function right_function
    Hcommutes value.
  change
    (relation_graph mapping
      (iterator A left_function value)
      (iterator B right_function (mapping value))).
  apply Hparametric.
  - apply (proj2
      (endomorphisms_agree_graph_iff A B mapping
        left_function right_function)).
    exact Hcommutes.
  - reflexivity.
Qed.

(** Applying the supplied function once is a parametric inhabitant. *)
Definition apply_once : PolymorphicIterator :=
  fun A function value => function value.

Theorem apply_once_parametric : IteratorParametric apply_once.
Proof.
  intros A B R left_function right_function Hagree left right Hrelated.
  now apply Hagree.
Qed.

(** Dropping compatibility would make even [apply_once] false: [negb] and
    [id] disagree on related boolean inputs. *)
Theorem negative_premise_is_necessary :
  ~ EndomorphismsAgree (@eq bool) negb (fun value => value).
Proof.
  intro Hagree.
  specialize (Hagree false false eq_refl).
  discriminate.
Qed.

Example apply_once_fails_without_negative_premise :
  apply_once bool negb false <>
  apply_once bool (fun value => value) false.
Proof.
  discriminate.
Qed.
