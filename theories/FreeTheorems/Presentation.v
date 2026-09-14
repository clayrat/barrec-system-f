(** * Checked presentation rules for Church encodings

    The core generator always expands source System F types.  This module
    adds a separate executable presentation pass for the two lecture
    abbreviations:

      - [forall r. r -> r -> r] is printed as [Bool], and its relation as
        equality;
      - [forall r. r -> (a -> r -> r) -> r] is printed as [[a]], and its
        relation as [ListRel R].

    Type recognizers and relation rewrites are guarded by structural equality.
    Formula simplification remains explicitly conditional on the corresponding
    laws of the semantic model; [relate_presented_semantics] proves preservation
    for every source type, and no identity-extension axiom is hidden in the
    printer. *)

From Stdlib Require Import PeanoNat.

From SystemF.F Require Import Syntax Check.
From SystemF.FreeTheorems Require Import
  Formula Generate Correctness ListTheorem FilterTheorem.

Inductive ChurchTypeAbbreviation : Type :=
| CABool : ChurchTypeAbbreviation
| CAListVariable : nat -> ChurchTypeAbbreviation.

Definition expand_church_type
    (abbreviation : ChurchTypeAbbreviation) : type :=
  match abbreviation with
  | CABool => church_bool_type
  | CAListVariable index => church_list_type (TVar index)
  end.

Definition source_church_candidate (T : type) :
    option ChurchTypeAbbreviation :=
  match T with
  | TForall
      (TArrow (TVar 0)
        (TArrow (TVar 0) (TVar 0))) =>
      Some CABool
  | TForall
      (TArrow (TVar 0)
        (TArrow
          (TArrow (TVar (S index))
            (TArrow (TVar 0) (TVar 0)))
          (TVar 0))) =>
      Some (CAListVariable index)
  | _ => None
  end.

(** The equality guard makes the recognizer robust if the fast candidate
    matcher is extended later. *)
Definition recognize_church_type (T : type) :
    option ChurchTypeAbbreviation :=
  match source_church_candidate T with
  | Some abbreviation =>
      if type_eq_dec T (expand_church_type abbreviation)
      then Some abbreviation
      else None
  | None => None
  end.

Theorem recognize_church_type_sound : forall T abbreviation,
  recognize_church_type T = Some abbreviation ->
  T = expand_church_type abbreviation.
Proof.
  intros T abbreviation Hrecognized.
  unfold recognize_church_type in Hrecognized.
  destruct (source_church_candidate T) as [candidate |] eqn:Hcandidate;
    try discriminate.
  destruct (type_eq_dec T (expand_church_type candidate))
    as [Hequal | Hunequal]; try discriminate.
  inversion Hrecognized.
  now subst abbreviation.
Qed.

Example recognize_church_bool :
  recognize_church_type church_bool_type = Some CABool.
Proof. reflexivity. Qed.

Example recognize_church_list_variable : forall index,
  recognize_church_type (church_list_type (TVar index)) =
  Some (CAListVariable index).
Proof.
  intro index.
  assert (Hcandidate :
      source_church_candidate (church_list_type (TVar index)) =
      Some (CAListVariable index)).
  { destruct index; reflexivity. }
  unfold recognize_church_type.
  rewrite Hcandidate.
  destruct (type_eq_dec
      (church_list_type (TVar index))
      (expand_church_type (CAListVariable index)))
    as [Hequal | Hunequal].
  - reflexivity.
  - exfalso.
    apply Hunequal.
    reflexivity.
Qed.

Fixpoint formula_type_eq_dec (T U : FormulaType) : {T = U} + {T <> U}.
Proof.
  decide equality.
  apply Nat.eq_dec.
Defined.

Fixpoint value_expr_eq_dec (lhs rhs : ValueExpr) : {lhs = rhs} + {lhs <> rhs}.
Proof.
  decide equality; try apply formula_type_eq_dec; apply Nat.eq_dec.
Defined.

Fixpoint relation_expr_eq_dec (lhs rhs : RelationExpr) :
    {lhs = rhs} + {lhs <> rhs}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Fixpoint rel_formula_eq_dec (lhs rhs : RelFormula) :
    {lhs = rhs} + {lhs <> rhs}.
Proof.
  decide equality;
    try apply formula_type_eq_dec;
    try apply value_expr_eq_dec;
    try apply relation_expr_eq_dec.
Defined.

Definition expand_formula_church_type
    (abbreviation : ChurchTypeAbbreviation) : FormulaType :=
  formula_type_of_type (expand_church_type abbreviation).

Definition formula_church_candidate (T : FormulaType) :
    option ChurchTypeAbbreviation :=
  match T with
  | RTForall
      (RTArrow (RTVar 0)
        (RTArrow (RTVar 0) (RTVar 0))) =>
      Some CABool
  | RTForall
      (RTArrow (RTVar 0)
        (RTArrow
          (RTArrow (RTVar (S index))
            (RTArrow (RTVar 0) (RTVar 0)))
          (RTVar 0))) =>
      Some (CAListVariable index)
  | _ => None
  end.

Definition recognize_formula_church_type (T : FormulaType) :
    option ChurchTypeAbbreviation :=
  match formula_church_candidate T with
  | Some abbreviation =>
      if formula_type_eq_dec T (expand_formula_church_type abbreviation)
      then Some abbreviation
      else None
  | None => None
  end.

Theorem recognize_formula_church_type_sound : forall T abbreviation,
  recognize_formula_church_type T = Some abbreviation ->
  T = expand_formula_church_type abbreviation.
Proof.
  intros T abbreviation Hrecognized.
  unfold recognize_formula_church_type in Hrecognized.
  destruct (formula_church_candidate T) as [candidate |] eqn:Hcandidate;
    try discriminate.
  destruct (formula_type_eq_dec T
      (expand_formula_church_type candidate))
    as [Hequal | Hunequal]; try discriminate.
  inversion Hrecognized.
  now subst abbreviation.
Qed.

Example recognize_formula_church_bool :
  recognize_formula_church_type
    (formula_type_of_type church_bool_type) = Some CABool.
Proof. reflexivity. Qed.

Example recognize_formula_church_list_variable : forall index,
  recognize_formula_church_type
    (formula_type_of_type (church_list_type (TVar index))) =
  Some (CAListVariable index).
Proof.
  intro index.
  assert (Hcandidate :
      formula_church_candidate
        (formula_type_of_type (church_list_type (TVar index))) =
      Some (CAListVariable index)).
  { destruct index; reflexivity. }
  unfold recognize_formula_church_type.
  rewrite Hcandidate.
  destruct (formula_type_eq_dec
      (formula_type_of_type (church_list_type (TVar index)))
      (expand_formula_church_type (CAListVariable index)))
    as [Hequal | Hunequal].
  - reflexivity.
  - exfalso.
    apply Hunequal.
    reflexivity.
Qed.

(** ** Post-processing the core generator *)

(** [postprocess_relation] consumes an existing formula.  The source type and
    endpoint expressions are a traversal guide: a Church abbreviation is
    installed only when the current input is structurally equal to the core
    [relate] output for that guide.  On malformed or unrelated input the
    guarded rule leaves the node untouched. *)
Fixpoint postprocess_relation
    (T : type) (lhs rhs : ValueExpr) (formula : RelFormula) : RelFormula :=
  match recognize_church_type T with
  | Some abbreviation =>
      if rel_formula_eq_dec formula (relate T lhs rhs)
      then
        match abbreviation with
        | CABool => RFEqual lhs rhs
        | CAListVariable index =>
            RFRel (list_relation (RRBound index)) lhs rhs
        end
      else formula
  | None =>
      match T, formula with
      | TArrow A B,
          RFForallValue left_type
            (RFForallValue right_type
              (RFImplies premise conclusion)) =>
          RFForallValue left_type
            (RFForallValue right_type
              (RFImplies
                (postprocess_relation A
                  (RVBound 1) (RVBound 0) premise)
                (postprocess_relation B
                  (RVApp (value_weaken_twice lhs) (RVBound 1))
                  (RVApp (value_weaken_twice rhs) (RVBound 0))
                  conclusion)))
      | TForall body,
          RFForallType
            (RFForallType
              (RFForallRelation left_type right_type nested)) =>
          RFForallType
            (RFForallType
              (RFForallRelation left_type right_type
                (postprocess_relation body
                  (RVTypeApp
                    (value_type_weaken_twice lhs) (RTVar 1))
                  (RVTypeApp
                    (value_type_weaken_twice rhs) (RTVar 0))
                  nested)))
      | _, _ => formula
      end
  end.

Lemma postprocess_relation_recognized : forall T lhs rhs abbreviation,
  recognize_church_type T = Some abbreviation ->
  postprocess_relation T lhs rhs (relate T lhs rhs) =
  match abbreviation with
  | CABool => RFEqual lhs rhs
  | CAListVariable index =>
      RFRel (list_relation (RRBound index)) lhs rhs
  end.
Proof.
  intros T lhs rhs abbreviation Hrecognized.
  destruct T as [index | A B | body].
  - discriminate.
  - discriminate.
  - cbn [postprocess_relation].
    rewrite Hrecognized.
    destruct (rel_formula_eq_dec
        (relate (TForall body) lhs rhs)
        (relate (TForall body) lhs rhs)) as [Hequal | Hunequal].
    + reflexivity.
    + exfalso.
      apply Hunequal.
      reflexivity.
Qed.

Lemma postprocess_relation_unrecognized : forall T lhs rhs formula,
  recognize_church_type T = None ->
  postprocess_relation T lhs rhs formula =
  match T, formula with
  | TArrow A B,
      RFForallValue left_type
        (RFForallValue right_type
          (RFImplies premise conclusion)) =>
      RFForallValue left_type
        (RFForallValue right_type
          (RFImplies
            (postprocess_relation A (RVBound 1) (RVBound 0) premise)
            (postprocess_relation B
              (RVApp (value_weaken_twice lhs) (RVBound 1))
              (RVApp (value_weaken_twice rhs) (RVBound 0))
              conclusion)))
  | TForall body,
      RFForallType
        (RFForallType
          (RFForallRelation left_type right_type nested)) =>
      RFForallType
        (RFForallType
          (RFForallRelation left_type right_type
            (postprocess_relation body
              (RVTypeApp (value_type_weaken_twice lhs) (RTVar 1))
              (RVTypeApp (value_type_weaken_twice rhs) (RTVar 0))
              nested)))
  | _, _ => formula
  end.
Proof.
  intros T lhs rhs formula Hunrecognized.
  destruct T as [index | A B | body].
  - reflexivity.
  - reflexivity.
  - cbn [postprocess_relation].
    now rewrite Hunrecognized.
Qed.

(** The presentation layer is now definitionally a post-pass over the single
    authoritative generator. *)
Definition relate_presented
    (T : type) (lhs rhs : ValueExpr) : RelFormula :=
  postprocess_relation T lhs rhs (relate T lhs rhs).

Definition relgen_presented (T : type) : RelFormula :=
  postprocess_relation T (RVFree 0) (RVFree 0) (relgen T).

Theorem relate_presented_is_postprocessing : forall T lhs rhs,
  relate_presented T lhs rhs =
  postprocess_relation T lhs rhs (relate T lhs rhs).
Proof. reflexivity. Qed.

Theorem relgen_presented_is_postprocessing : forall T,
  relgen_presented T =
  postprocess_relation T (RVFree 0) (RVFree 0) (relgen T).
Proof. reflexivity. Qed.

Theorem presented_list_endomorphism_computes :
  relgen_presented polymorphic_list_endomorphism_type =
  list_endomorphism_formula.
Proof. reflexivity. Qed.

Theorem presented_filter_computes :
  relgen_presented polymorphic_filter_type = filter_formula.
Proof. reflexivity. Qed.

(** ** Semantic justification of the two relation reductions *)

Theorem bool_relation_print_rule_sound : forall
    (model : RelModel) formula_types left_types right_types relations
    values free_values free_relations lhs rhs,
  paired_type_environment formula_types left_types right_types ->
  ChurchBoolEqualityAbbreviation model ->
  (formula_sem model formula_types relations values
      free_values free_relations (RFEqual lhs rhs) <->
   formula_sem model formula_types relations values
      free_values free_relations (relate church_bool_type lhs rhs)).
Proof.
  intros model formula_types left_types right_types relations values
    free_values free_relations lhs rhs Hpaired Hbool.
  rewrite (relate_correct model church_bool_type formula_types
    left_types right_types relations values free_values free_relations
    lhs rhs Hpaired).
  cbn [formula_sem].
  apply iff_sym.
  apply Hbool.
Qed.

Theorem list_relation_print_rule_sound : forall
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
  intros model index formula_types left_types right_types relations values
    free_values free_relations lhs rhs Hpaired Hrelation Hlist.
  rewrite (relate_correct model (church_list_type (TVar index))
    formula_types left_types right_types relations values
    free_values free_relations lhs rhs Hpaired).
  cbn [formula_sem relation_sem list_relation semantic_list_relation].
  apply Hlist.
  exact Hrelation.
Qed.

(** Free relation variables must relate values from their corresponding
    endpoint types.  Generated [forall] binders preserve this invariant. *)
Definition relation_environment_between
    {model : RelModel}
    (left_types right_types : Environment (SemanticType model))
    (relations : Environment (SemanticRelation model)) : Prop :=
  forall index,
    relation_between (relations index)
      (left_types index) (right_types index).

Lemma relation_environment_between_extend : forall
    (model : RelModel)
    (left_types right_types : Environment (SemanticType model))
    (relations : Environment (SemanticRelation model))
    (left_type right_type : SemanticType model)
    (relation : SemanticRelation model),
  relation_environment_between left_types right_types relations ->
  relation_between relation left_type right_type ->
  relation_environment_between
    (env_extend left_type left_types)
    (env_extend right_type right_types)
    (env_extend relation relations).
Proof.
  intros model left_types right_types relations
    left_type right_type relation Henvironment Hrelation [| index].
  - exact Hrelation.
  - apply Henvironment.
Qed.

(** This is the general presentation theorem.  It is quantified over every
    source type, rather than only the list and [filter] demonstrations: the
    post-pass preserves the semantics of the core [relate] output whenever
    the two advertised Church abbreviation laws hold. *)
Theorem relate_presented_semantics : forall (model : RelModel) T
    formula_types left_types right_types relations
    values free_values free_relations lhs rhs,
  paired_type_environment formula_types left_types right_types ->
  relation_environment_between left_types right_types relations ->
  ChurchBoolEqualityAbbreviation model ->
  ChurchListRelationAbbreviation model (free_relations 0) ->
  (formula_sem model formula_types relations values
      free_values free_relations (relate_presented T lhs rhs) <->
   formula_sem model formula_types relations values
      free_values free_relations (relate T lhs rhs)).
Proof.
  intros model T.
  induction T as [index | A IHA B IHB | body IHbody];
    intros formula_types left_types right_types relations
      values free_values free_relations lhs rhs
      Hpaired Hrelations Hbool Hlist.
  - reflexivity.
  - cbn [relate_presented postprocess_relation relate
      recognize_church_type source_church_candidate formula_sem].
    split; intros H left_argument Hleft_argument
      right_argument Hright_argument Hargument.
    + apply (proj1
        (IHB formula_types left_types right_types relations
          (env_extend right_argument (env_extend left_argument values))
          free_values free_relations
          (RVApp (value_weaken_twice lhs) (RVBound 1))
          (RVApp (value_weaken_twice rhs) (RVBound 0))
          Hpaired Hrelations Hbool Hlist)).
      apply H; try assumption.
      apply (proj2
        (IHA formula_types left_types right_types relations
          (env_extend right_argument (env_extend left_argument values))
          free_values free_relations (RVBound 1) (RVBound 0)
          Hpaired Hrelations Hbool Hlist)).
      exact Hargument.
    + apply (proj2
        (IHB formula_types left_types right_types relations
          (env_extend right_argument (env_extend left_argument values))
          free_values free_relations
          (RVApp (value_weaken_twice lhs) (RVBound 1))
          (RVApp (value_weaken_twice rhs) (RVBound 0))
          Hpaired Hrelations Hbool Hlist)).
      apply H; try assumption.
      apply (proj1
        (IHA formula_types left_types right_types relations
          (env_extend right_argument (env_extend left_argument values))
          free_values free_relations (RVBound 1) (RVBound 0)
          Hpaired Hrelations Hbool Hlist)).
      exact Hargument.
  - unfold relate_presented.
    destruct (recognize_church_type (TForall body))
      as [abbreviation |] eqn:Hrecognized.
    + rewrite (postprocess_relation_recognized
        (TForall body) lhs rhs abbreviation Hrecognized).
      pose proof
        (recognize_church_type_sound
          (TForall body) abbreviation Hrecognized) as Hexpanded.
      destruct abbreviation as [| index].
      * rewrite Hexpanded.
        apply (bool_relation_print_rule_sound model
          formula_types left_types right_types relations
          values free_values free_relations lhs rhs Hpaired Hbool).
      * rewrite Hexpanded.
        apply (list_relation_print_rule_sound model index
          formula_types left_types right_types relations
          values free_values free_relations lhs rhs Hpaired
          (Hrelations index) Hlist).
    + rewrite (postprocess_relation_unrecognized
        (TForall body) lhs rhs (relate (TForall body) lhs rhs)
        Hrecognized).
      cbn [relate].
      cbn [formula_sem].
      split; intros H left_type right_type relation Hrelation.
      * apply (proj1
          (IHbody
            (env_extend right_type (env_extend left_type formula_types))
            (env_extend left_type left_types)
            (env_extend right_type right_types)
            (env_extend relation relations)
            values free_values free_relations
            (RVTypeApp (value_type_weaken_twice lhs) (RTVar 1))
            (RVTypeApp (value_type_weaken_twice rhs) (RTVar 0))
            (paired_type_environment_extend model formula_types
              left_types right_types left_type right_type Hpaired)
            (relation_environment_between_extend model
              left_types right_types relations
              left_type right_type relation Hrelations Hrelation)
            Hbool Hlist)).
        apply H.
        exact Hrelation.
      * apply (proj2
          (IHbody
            (env_extend right_type (env_extend left_type formula_types))
            (env_extend left_type left_types)
            (env_extend right_type right_types)
            (env_extend relation relations)
            values free_values free_relations
            (RVTypeApp (value_type_weaken_twice lhs) (RTVar 1))
            (RVTypeApp (value_type_weaken_twice rhs) (RTVar 0))
            (paired_type_environment_extend model formula_types
              left_types right_types left_type right_type Hpaired)
            (relation_environment_between_extend model
              left_types right_types relations
              left_type right_type relation Hrelations Hrelation)
            Hbool Hlist)).
        apply H.
        exact Hrelation.
Qed.

Corollary relgen_presented_semantics : forall (model : RelModel) T
    formula_types left_types right_types relations
    values free_values free_relations,
  paired_type_environment formula_types left_types right_types ->
  relation_environment_between left_types right_types relations ->
  ChurchBoolEqualityAbbreviation model ->
  ChurchListRelationAbbreviation model (free_relations 0) ->
  (formula_sem model formula_types relations values
      free_values free_relations (relgen_presented T) <->
   formula_sem model formula_types relations values
      free_values free_relations (relgen T)).
Proof.
  intros model T formula_types left_types right_types relations
    values free_values free_relations Hpaired Hrelations Hbool Hlist.
  unfold relgen_presented, relgen.
  apply (relate_presented_semantics model T
    formula_types left_types right_types relations
    values free_values free_relations (RVFree 0) (RVFree 0));
    assumption.
Qed.

Theorem presented_list_endomorphism_semantics : forall
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
  intros model type_environment relation_environment value_environment
    free_values free_relations Hlist.
  rewrite presented_list_endomorphism_computes.
  now apply list_relation_abbreviation_preserves_semantics.
Qed.

Theorem presented_filter_semantics : forall
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
  intros model type_environment relation_environment value_environment
    free_values free_relations Hbool Hlist.
  rewrite presented_filter_computes.
  now apply filter_abbreviations_preserve_semantics.
Qed.
