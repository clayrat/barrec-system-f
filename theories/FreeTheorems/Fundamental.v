(** * Fundamental theorem of relational parametricity

    This module is deliberately separate from [Correctness].  The latter
    says that [relate] prints the direct relational interpretation of a type;
    here we prove the abstraction lemma saying that every intrinsically typed
    System F term inhabits that interpretation.

    The realizability carrier is the one used by the formula semantics.  To
    interpret term and type abstraction we add abstraction operations and
    their beta laws.  No extensionality or global axiom is required. *)

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

From SystemF.F Require Import Syntax.
From SystemF.FreeTheorems Require Import Formula Generate Correctness.

Record ParametricModel : Type := {
  parametric_rel_model : RelModel;
  model_abstract :
    (model_value parametric_rel_model ->
      model_value parametric_rel_model) ->
    model_value parametric_rel_model;
  model_abstract_beta : forall body argument,
    model_apply parametric_rel_model (model_abstract body) argument =
    body argument;
  model_type_abstract :
    (SemanticType parametric_rel_model ->
      model_value parametric_rel_model) ->
    model_value parametric_rel_model;
  model_type_abstract_beta : forall body A,
    model_type_apply parametric_rel_model
      (model_type_abstract body) A = body A
}.

Coercion parametric_rel_model : ParametricModel >-> RelModel.

(** A logical relation carries the endpoint typing facts needed when a type
    variable occurs to the left of an arrow.  Its third component is exactly
    the direct relation used by [relate_correct]. *)
Definition logical_relation
    (model : RelModel)
    (T : type)
    (left_types right_types : Environment (SemanticType model))
    (relations : Environment (SemanticRelation model))
    (lhs rhs : model_value model) : Prop :=
  source_type_sem model left_types T lhs /\
  source_type_sem model right_types T rhs /\
  source_type_rel model T left_types right_types relations lhs rhs.

Lemma logical_relation_between : forall (model : RelModel) T
    left_types right_types relations,
  relation_between
    (logical_relation model T left_types right_types relations)
    (source_type_sem model left_types T)
    (source_type_sem model right_types T).
Proof.
  intros model T left_types right_types relations lhs rhs Hrelated.
  unfold logical_relation in Hrelated.
  tauto.
Qed.

(** ** Semantic weakening *)

Lemma source_type_sem_lift_correct : forall (model : RelModel) T cutoff
    new_environment old_environment,
  lifted_type_environment cutoff new_environment old_environment ->
  forall value,
    source_type_sem model new_environment (type_lift cutoff T) value <->
    source_type_sem model old_environment T value.
Proof.
  intros model T.
  induction T as [index | A IHA B IHB | body IHbody];
    intros cutoff new_environment old_environment Hlift value.
  - cbn [type_lift source_type_sem].
    specialize (Hlift index value).
    unfold lift_index in Hlift.
    destruct (index <? cutoff); exact Hlift.
  - cbn [type_lift source_type_sem].
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
  - cbn [type_lift source_type_sem].
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

Definition lifted_relation_environment
    {model : RelModel}
    (cutoff : nat)
    (new_environment old_environment :
      Environment (SemanticRelation model)) : Prop :=
  forall index lhs rhs,
    new_environment (lift_index cutoff index) lhs rhs <->
    old_environment index lhs rhs.

Lemma lifted_relation_environment_under_binder :
    forall (model : RelModel) cutoff
      (new_environment old_environment :
        Environment (SemanticRelation model))
      (relation : SemanticRelation model),
  lifted_relation_environment cutoff new_environment old_environment ->
  lifted_relation_environment (S cutoff)
    (env_extend relation new_environment)
    (env_extend relation old_environment).
Proof.
  intros model cutoff new_environment old_environment relation Hlift
    [| index] lhs rhs.
  - reflexivity.
  - unfold lift_index at 1.
    cbn [env_extend].
    change
      (env_extend relation new_environment
        (if index <? cutoff then S index else S (S index)) lhs rhs <->
       old_environment index lhs rhs).
    specialize (Hlift index lhs rhs).
    unfold lift_index in Hlift.
    destruct (index <? cutoff) eqn:Hindex;
      cbn [env_extend] in *; exact Hlift.
Qed.

Lemma source_type_rel_lift_correct : forall (model : RelModel) T cutoff
    new_left old_left new_right old_right new_relations old_relations,
  lifted_type_environment cutoff new_left old_left ->
  lifted_type_environment cutoff new_right old_right ->
  lifted_relation_environment cutoff new_relations old_relations ->
  forall lhs rhs,
    source_type_rel model (type_lift cutoff T)
      new_left new_right new_relations lhs rhs <->
    source_type_rel model T
      old_left old_right old_relations lhs rhs.
Proof.
  intros model T.
  induction T as [index | A IHA B IHB | body IHbody];
    intros cutoff new_left old_left new_right old_right
      new_relations old_relations Hleft Hright Hrelations lhs rhs.
  - cbn [type_lift source_type_rel].
    specialize (Hrelations index lhs rhs).
    unfold lift_index in Hrelations.
    destruct (index <? cutoff); exact Hrelations.
  - cbn [type_lift source_type_rel].
    split; intros H left_argument Hleft_argument
      right_argument Hright_argument Hrelated.
    + apply (proj1
        (IHB cutoff new_left old_left new_right old_right
          new_relations old_relations Hleft Hright Hrelations
          (model_apply model lhs left_argument)
          (model_apply model rhs right_argument))).
      apply H.
      * apply (proj2
          (source_type_sem_lift_correct model A cutoff
            new_left old_left Hleft left_argument)).
        exact Hleft_argument.
      * apply (proj2
          (source_type_sem_lift_correct model A cutoff
            new_right old_right Hright right_argument)).
        exact Hright_argument.
      * apply (proj2
          (IHA cutoff new_left old_left new_right old_right
            new_relations old_relations Hleft Hright Hrelations
            left_argument right_argument)).
        exact Hrelated.
    + apply (proj2
        (IHB cutoff new_left old_left new_right old_right
          new_relations old_relations Hleft Hright Hrelations
          (model_apply model lhs left_argument)
          (model_apply model rhs right_argument))).
      apply H.
      * apply (proj1
          (source_type_sem_lift_correct model A cutoff
            new_left old_left Hleft left_argument)).
        exact Hleft_argument.
      * apply (proj1
          (source_type_sem_lift_correct model A cutoff
            new_right old_right Hright right_argument)).
        exact Hright_argument.
      * apply (proj1
          (IHA cutoff new_left old_left new_right old_right
            new_relations old_relations Hleft Hright Hrelations
            left_argument right_argument)).
        exact Hrelated.
  - cbn [type_lift source_type_rel].
    split; intros H left_type right_type relation Hbetween.
    + apply (proj1
        (IHbody (S cutoff)
          (env_extend left_type new_left)
          (env_extend left_type old_left)
          (env_extend right_type new_right)
          (env_extend right_type old_right)
          (env_extend relation new_relations)
          (env_extend relation old_relations)
          (lifted_type_environment_under_binder model cutoff
            new_left old_left left_type Hleft)
          (lifted_type_environment_under_binder model cutoff
            new_right old_right right_type Hright)
          (lifted_relation_environment_under_binder model cutoff
            new_relations old_relations relation Hrelations)
          (model_type_apply model lhs left_type)
          (model_type_apply model rhs right_type))).
      apply H.
      exact Hbetween.
    + apply (proj2
        (IHbody (S cutoff)
          (env_extend left_type new_left)
          (env_extend left_type old_left)
          (env_extend right_type new_right)
          (env_extend right_type old_right)
          (env_extend relation new_relations)
          (env_extend relation old_relations)
          (lifted_type_environment_under_binder model cutoff
            new_left old_left left_type Hleft)
          (lifted_type_environment_under_binder model cutoff
            new_right old_right right_type Hright)
          (lifted_relation_environment_under_binder model cutoff
            new_relations old_relations relation Hrelations)
          (model_type_apply model lhs left_type)
          (model_type_apply model rhs right_type))).
      apply H.
      exact Hbetween.
Qed.

Lemma logical_relation_lift_correct : forall (model : RelModel) T cutoff
    new_left old_left new_right old_right new_relations old_relations,
  lifted_type_environment cutoff new_left old_left ->
  lifted_type_environment cutoff new_right old_right ->
  lifted_relation_environment cutoff new_relations old_relations ->
  forall lhs rhs,
    logical_relation model (type_lift cutoff T)
      new_left new_right new_relations lhs rhs <->
    logical_relation model T
      old_left old_right old_relations lhs rhs.
Proof.
  intros model T cutoff new_left old_left new_right old_right
    new_relations old_relations Hleft Hright Hrelations lhs rhs.
  unfold logical_relation.
  rewrite (source_type_sem_lift_correct model T cutoff
      new_left old_left Hleft lhs),
    (source_type_sem_lift_correct model T cutoff
      new_right old_right Hright rhs),
    (source_type_rel_lift_correct model T cutoff
      new_left old_left new_right old_right
      new_relations old_relations Hleft Hright Hrelations lhs rhs).
  reflexivity.
Qed.

(** ** Semantic type substitution *)

Definition substituted_type_environment
    {model : RelModel}
    (cutoff : nat)
    (new_environment : Environment (SemanticType model))
    (replacement : type)
    (old_environment : Environment (SemanticType model)) : Prop :=
  forall index value,
    (match index ?= cutoff with
     | Lt => new_environment index value
     | Eq => source_type_sem model new_environment replacement value
     | Gt => new_environment (pred index) value
     end) <-> old_environment index value.

Definition substituted_relation_environment
    {model : RelModel}
    (cutoff : nat)
    (new_environment : Environment (SemanticRelation model))
    (replacement : SemanticRelation model)
    (old_environment : Environment (SemanticRelation model)) : Prop :=
  forall index lhs rhs,
    (match index ?= cutoff with
     | Lt => new_environment index lhs rhs
     | Eq => replacement lhs rhs
     | Gt => new_environment (pred index) lhs rhs
     end) <-> old_environment index lhs rhs.

Lemma substituted_type_environment_under_binder : forall
    (model : RelModel) cutoff new_environment replacement old_environment
    (head : SemanticType model),
  substituted_type_environment cutoff
    new_environment replacement old_environment ->
  substituted_type_environment (S cutoff)
    (env_extend head new_environment) (type_lift 0 replacement)
    (env_extend head old_environment).
Proof.
  intros model cutoff new_environment replacement old_environment head
    Hsubstitution [| index] value.
  - reflexivity.
  - rewrite Nat.compare_succ.
    specialize (Hsubstitution index value).
    destruct (index ?= cutoff) eqn:Hcompare.
    + cbn [env_extend].
      rewrite (source_type_sem_lift_correct model replacement 0
        (env_extend head new_environment) new_environment).
      * exact Hsubstitution.
      * intros variable argument.
        rewrite env_extend_lift_zero.
        reflexivity.
    + exact Hsubstitution.
    + destruct index as [| index].
      * apply Nat.compare_gt_iff in Hcompare.
        lia.
      * exact Hsubstitution.
Qed.

Lemma substituted_relation_environment_under_binder : forall
    (model : RelModel) cutoff new_environment replacement old_environment
    (head : SemanticRelation model) lifted_replacement,
  substituted_relation_environment cutoff
    new_environment replacement old_environment ->
  (forall lhs rhs, lifted_replacement lhs rhs <-> replacement lhs rhs) ->
  substituted_relation_environment (S cutoff)
    (env_extend head new_environment) lifted_replacement
    (env_extend head old_environment).
Proof.
  intros model cutoff new_environment replacement old_environment head
    lifted_replacement Hsubstitution Hreplacement [| index] lhs rhs.
  - reflexivity.
  - rewrite Nat.compare_succ.
    specialize (Hsubstitution index lhs rhs).
    destruct (index ?= cutoff) eqn:Hcompare.
    + cbn [env_extend].
      rewrite Hreplacement.
      exact Hsubstitution.
    + exact Hsubstitution.
    + destruct index as [| index].
      * apply Nat.compare_gt_iff in Hcompare.
        lia.
      * exact Hsubstitution.
Qed.

Lemma source_type_sem_subst_correct : forall (model : RelModel) T cutoff
    new_environment replacement old_environment,
  substituted_type_environment cutoff
    new_environment replacement old_environment ->
  forall value,
    source_type_sem model new_environment
      (type_subst cutoff T replacement) value <->
    source_type_sem model old_environment T value.
Proof.
  intros model T.
  induction T as [index | A IHA B IHB | body IHbody];
    intros cutoff new_environment replacement old_environment
      Hsubstitution value.
  - cbn [type_subst source_type_sem].
    specialize (Hsubstitution index value).
    destruct (index ?= cutoff); exact Hsubstitution.
  - cbn [type_subst source_type_sem].
    split; intros H argument Hargument.
    + apply (proj1
        (IHB cutoff new_environment replacement old_environment
          Hsubstitution (model_apply model value argument))).
      apply H.
      apply (proj2
        (IHA cutoff new_environment replacement old_environment
          Hsubstitution argument)).
      exact Hargument.
    + apply (proj2
        (IHB cutoff new_environment replacement old_environment
          Hsubstitution (model_apply model value argument))).
      apply H.
      apply (proj1
        (IHA cutoff new_environment replacement old_environment
          Hsubstitution argument)).
      exact Hargument.
  - cbn [type_subst source_type_sem].
    split; intros H A.
    + apply (proj1
        (IHbody (S cutoff) (env_extend A new_environment)
          (type_lift 0 replacement) (env_extend A old_environment)
          (substituted_type_environment_under_binder model cutoff
            new_environment replacement old_environment A Hsubstitution)
          (model_type_apply model value A))).
      apply H.
    + apply (proj2
        (IHbody (S cutoff) (env_extend A new_environment)
          (type_lift 0 replacement) (env_extend A old_environment)
          (substituted_type_environment_under_binder model cutoff
            new_environment replacement old_environment A Hsubstitution)
          (model_type_apply model value A))).
      apply H.
Qed.

Lemma substituted_type_environment_zero : forall
    (model : RelModel) environment replacement,
  substituted_type_environment 0 environment replacement
    (env_extend (source_type_sem model environment replacement)
      environment).
Proof.
  intros model environment replacement [| index] value; reflexivity.
Qed.

Lemma substituted_relation_environment_zero : forall
    (model : RelModel)
    (environment : Environment (SemanticRelation model))
    (replacement : SemanticRelation model),
  substituted_relation_environment 0 environment replacement
    (env_extend replacement environment).
Proof.
  intros model environment replacement [| index] lhs rhs; reflexivity.
Qed.

(** The saturated logical relation commutes with type substitution.  The
    inserted relation is the logical relation of the replacement itself;
    this is the point that makes the arrow case work in both directions. *)
Theorem logical_relation_subst_correct : forall (model : RelModel) T cutoff
    new_left old_left new_right old_right
    new_relations old_relations replacement,
  substituted_type_environment cutoff
    new_left replacement old_left ->
  substituted_type_environment cutoff
    new_right replacement old_right ->
  substituted_relation_environment cutoff new_relations
    (logical_relation model replacement
      new_left new_right new_relations)
    old_relations ->
  forall lhs rhs,
    logical_relation model (type_subst cutoff T replacement)
      new_left new_right new_relations lhs rhs <->
    logical_relation model T
      old_left old_right old_relations lhs rhs.
Proof.
  intros model T.
  induction T as [index | A IHA B IHB | body IHbody];
    intros cutoff new_left old_left new_right old_right
      new_relations old_relations replacement
      Hleft Hright Hrelations lhs rhs.
  - unfold logical_relation.
    cbn [type_subst source_type_sem source_type_rel].
    specialize (Hleft index lhs).
    specialize (Hright index rhs).
    specialize (Hrelations index lhs rhs).
    destruct (index ?= cutoff) eqn:Hcompare;
      cbn [source_type_sem source_type_rel] in *;
      unfold logical_relation in Hrelations;
      tauto.
  - split; intro Hlogical.
    + destruct Hlogical as [Hlhs [Hrhs Hrelated]].
      split.
      * apply (proj1
          (source_type_sem_subst_correct model (TArrow A B) cutoff
            new_left replacement old_left Hleft lhs)).
        exact Hlhs.
      * split.
        -- apply (proj1
            (source_type_sem_subst_correct model (TArrow A B) cutoff
              new_right replacement old_right Hright rhs)).
           exact Hrhs.
        -- cbn [type_subst source_type_rel] in Hrelated |-.
           intros left_argument Hleft_argument
             right_argument Hright_argument Hargument_related.
           assert (Hargument_old :
               logical_relation model A old_left old_right old_relations
                 left_argument right_argument).
           { unfold logical_relation.
             tauto. }
           assert (Hargument_new :
               logical_relation model (type_subst cutoff A replacement)
                 new_left new_right new_relations
                 left_argument right_argument).
           { apply (proj2
               (IHA cutoff new_left old_left new_right old_right
                 new_relations old_relations replacement
                 Hleft Hright Hrelations
                 left_argument right_argument)).
             exact Hargument_old. }
           destruct Hargument_new as
             [Hleft_argument_new
               [Hright_argument_new Hargument_related_new]].
           specialize (Hrelated left_argument Hleft_argument_new
             right_argument Hright_argument_new Hargument_related_new).
           assert (Hresult_new :
               logical_relation model (type_subst cutoff B replacement)
                 new_left new_right new_relations
                 (model_apply model lhs left_argument)
                 (model_apply model rhs right_argument)).
           { unfold logical_relation.
             repeat split.
             - apply Hlhs.
               exact Hleft_argument_new.
             - apply Hrhs.
               exact Hright_argument_new.
             - exact Hrelated. }
           exact (proj2 (proj2
             (proj1
               (IHB cutoff new_left old_left new_right old_right
                 new_relations old_relations replacement
                 Hleft Hright Hrelations
                 (model_apply model lhs left_argument)
                 (model_apply model rhs right_argument)) Hresult_new))).
    + destruct Hlogical as [Hlhs [Hrhs Hrelated]].
      split.
      * apply (proj2
          (source_type_sem_subst_correct model (TArrow A B) cutoff
            new_left replacement old_left Hleft lhs)).
        exact Hlhs.
      * split.
        -- apply (proj2
            (source_type_sem_subst_correct model (TArrow A B) cutoff
              new_right replacement old_right Hright rhs)).
           exact Hrhs.
        -- cbn [type_subst source_type_rel].
           intros left_argument Hleft_argument
             right_argument Hright_argument Hargument_related.
           assert (Hargument_new :
               logical_relation model (type_subst cutoff A replacement)
                 new_left new_right new_relations
                 left_argument right_argument).
           { unfold logical_relation.
             tauto. }
           assert (Hargument_old :
               logical_relation model A old_left old_right old_relations
                 left_argument right_argument).
           { apply (proj1
               (IHA cutoff new_left old_left new_right old_right
                 new_relations old_relations replacement
                 Hleft Hright Hrelations
                 left_argument right_argument)).
             exact Hargument_new. }
           destruct Hargument_old as
             [Hleft_argument_old
               [Hright_argument_old Hargument_related_old]].
           cbn [source_type_rel] in Hrelated.
           specialize (Hrelated left_argument Hleft_argument_old
             right_argument Hright_argument_old Hargument_related_old).
           assert (Hresult_old :
               logical_relation model B old_left old_right old_relations
                 (model_apply model lhs left_argument)
                 (model_apply model rhs right_argument)).
           { unfold logical_relation.
             repeat split.
             - apply Hlhs.
               exact Hleft_argument_old.
             - apply Hrhs.
               exact Hright_argument_old.
             - exact Hrelated. }
           exact (proj2 (proj2
             (proj2
               (IHB cutoff new_left old_left new_right old_right
                 new_relations old_relations replacement
                 Hleft Hright Hrelations
                 (model_apply model lhs left_argument)
                 (model_apply model rhs right_argument)) Hresult_old))).
  - split; intro Hlogical.
    + destruct Hlogical as [Hlhs [Hrhs Hrelated]].
      split.
      * apply (proj1
          (source_type_sem_subst_correct model (TForall body) cutoff
            new_left replacement old_left Hleft lhs)).
        exact Hlhs.
      * split.
        -- apply (proj1
            (source_type_sem_subst_correct model (TForall body) cutoff
              new_right replacement old_right Hright rhs)).
           exact Hrhs.
        -- cbn [type_subst source_type_rel] in Hrelated |-.
           intros left_type right_type relation Hbetween.
           assert (Hleft' :
               substituted_type_environment (S cutoff)
                 (env_extend left_type new_left)
                 (type_lift 0 replacement)
                 (env_extend left_type old_left)).
           { apply substituted_type_environment_under_binder.
             exact Hleft. }
           assert (Hright' :
               substituted_type_environment (S cutoff)
                 (env_extend right_type new_right)
                 (type_lift 0 replacement)
                 (env_extend right_type old_right)).
           { apply substituted_type_environment_under_binder.
             exact Hright. }
           assert (Hrelations' :
               substituted_relation_environment (S cutoff)
                 (env_extend relation new_relations)
                 (logical_relation model (type_lift 0 replacement)
                   (env_extend left_type new_left)
                   (env_extend right_type new_right)
                   (env_extend relation new_relations))
                 (env_extend relation old_relations)).
           { apply substituted_relation_environment_under_binder
               with (replacement :=
                 logical_relation model replacement
                   new_left new_right new_relations).
             - exact Hrelations.
             - intros left_value right_value.
               apply logical_relation_lift_correct.
               + intros variable value.
                 rewrite env_extend_lift_zero.
                 reflexivity.
               + intros variable value.
                 rewrite env_extend_lift_zero.
                 reflexivity.
               + intros variable left_value' right_value'.
                 rewrite env_extend_lift_zero.
                 reflexivity. }
           specialize (Hrelated left_type right_type relation Hbetween).
           assert (Hresult_new :
               logical_relation model
                 (type_subst (S cutoff) body (type_lift 0 replacement))
                 (env_extend left_type new_left)
                 (env_extend right_type new_right)
                 (env_extend relation new_relations)
                 (model_type_apply model lhs left_type)
                 (model_type_apply model rhs right_type)).
           { unfold logical_relation.
             repeat split.
             - apply Hlhs.
             - apply Hrhs.
             - exact Hrelated. }
           exact (proj2 (proj2
             (proj1
               (IHbody (S cutoff)
                 (env_extend left_type new_left)
                 (env_extend left_type old_left)
                 (env_extend right_type new_right)
                 (env_extend right_type old_right)
                 (env_extend relation new_relations)
                 (env_extend relation old_relations)
                 (type_lift 0 replacement)
                 Hleft' Hright' Hrelations'
                 (model_type_apply model lhs left_type)
                 (model_type_apply model rhs right_type)) Hresult_new))).
    + destruct Hlogical as [Hlhs [Hrhs Hrelated]].
      split.
      * apply (proj2
          (source_type_sem_subst_correct model (TForall body) cutoff
            new_left replacement old_left Hleft lhs)).
        exact Hlhs.
      * split.
        -- apply (proj2
            (source_type_sem_subst_correct model (TForall body) cutoff
              new_right replacement old_right Hright rhs)).
           exact Hrhs.
        -- cbn [type_subst source_type_rel].
           intros left_type right_type relation Hbetween.
           assert (Hleft' :
               substituted_type_environment (S cutoff)
                 (env_extend left_type new_left)
                 (type_lift 0 replacement)
                 (env_extend left_type old_left)).
           { apply substituted_type_environment_under_binder.
             exact Hleft. }
           assert (Hright' :
               substituted_type_environment (S cutoff)
                 (env_extend right_type new_right)
                 (type_lift 0 replacement)
                 (env_extend right_type old_right)).
           { apply substituted_type_environment_under_binder.
             exact Hright. }
           assert (Hrelations' :
               substituted_relation_environment (S cutoff)
                 (env_extend relation new_relations)
                 (logical_relation model (type_lift 0 replacement)
                   (env_extend left_type new_left)
                   (env_extend right_type new_right)
                   (env_extend relation new_relations))
                 (env_extend relation old_relations)).
           { apply substituted_relation_environment_under_binder
               with (replacement :=
                 logical_relation model replacement
                   new_left new_right new_relations).
             - exact Hrelations.
             - intros left_value right_value.
               apply logical_relation_lift_correct.
               + intros variable value.
                 rewrite env_extend_lift_zero.
                 reflexivity.
               + intros variable value.
                 rewrite env_extend_lift_zero.
                 reflexivity.
               + intros variable left_value' right_value'.
                 rewrite env_extend_lift_zero.
                 reflexivity. }
           cbn [source_type_rel] in Hrelated.
           specialize (Hrelated left_type right_type relation Hbetween).
           assert (Hresult_old :
               logical_relation model body
                 (env_extend left_type old_left)
                 (env_extend right_type old_right)
                 (env_extend relation old_relations)
                 (model_type_apply model lhs left_type)
                 (model_type_apply model rhs right_type)).
           { unfold logical_relation.
             repeat split.
             - apply Hlhs.
             - apply Hrhs.
             - exact Hrelated. }
           exact (proj2 (proj2
             (proj2
               (IHbody (S cutoff)
                 (env_extend left_type new_left)
                 (env_extend left_type old_left)
                 (env_extend right_type new_right)
                 (env_extend right_type old_right)
                 (env_extend relation new_relations)
                 (env_extend relation old_relations)
                 (type_lift 0 replacement)
                 Hleft' Hright' Hrelations'
                 (model_type_apply model lhs left_type)
                 (model_type_apply model rhs right_type)) Hresult_old))).
Qed.

(** ** Interpretation of intrinsically typed terms *)

Fixpoint fterm_sem
    (model : ParametricModel)
    {context T} (term : fterm context T)
    (type_environment : Environment (SemanticType model))
    (value_environment : Environment (model_value model)) :
    model_value model :=
  match term with
  | FVar variable => value_environment (fvar_to_nat variable)
  | FAbs body =>
      model_abstract model (fun argument =>
        fterm_sem model body type_environment
          (env_extend argument value_environment))
  | FApp function argument =>
      model_apply model
        (fterm_sem model function type_environment value_environment)
        (fterm_sem model argument type_environment value_environment)
  | FTAbs body =>
      model_type_abstract model (fun A =>
        fterm_sem model body (env_extend A type_environment)
          value_environment)
  | FTApp function U =>
      model_type_apply model
        (fterm_sem model function type_environment value_environment)
        (source_type_sem model type_environment U)
  end.

Definition env_tail {A : Type}
    (environment : Environment A) : Environment A :=
  fun index => environment (S index).

Fixpoint term_environment_sem
    (model : RelModel)
    (context : list type)
    (types : Environment (SemanticType model))
    (values : Environment (model_value model)) : Prop :=
  match context with
  | [] => True
  | T :: context' =>
      source_type_sem model types T (values 0) /\
      term_environment_sem model context' types (env_tail values)
  end.

Fixpoint term_environment_rel
    (model : RelModel)
    (context : list type)
    (left_types right_types : Environment (SemanticType model))
    (relations : Environment (SemanticRelation model))
    (left_values right_values : Environment (model_value model)) : Prop :=
  match context with
  | [] => True
  | T :: context' =>
      source_type_rel model T left_types right_types relations
        (left_values 0) (right_values 0) /\
      term_environment_rel model context'
        left_types right_types relations
        (env_tail left_values) (env_tail right_values)
  end.

Lemma term_environment_sem_lookup : forall (model : RelModel)
    context T (variable : fvar context T) types values,
  term_environment_sem model context types values ->
  source_type_sem model types T
    (values (fvar_to_nat variable)).
Proof.
  intros model context T variable.
  induction variable as [context T | context T U variable IHvariable];
    intros types values Hcontext.
  - exact (proj1 Hcontext).
  - change (source_type_sem model types T
      ((env_tail values) (fvar_to_nat variable))).
    apply IHvariable.
    exact (proj2 Hcontext).
Qed.

Lemma term_environment_rel_lookup : forall (model : RelModel)
    context T (variable : fvar context T)
    left_types right_types relations left_values right_values,
  term_environment_rel model context left_types right_types relations
    left_values right_values ->
  source_type_rel model T left_types right_types relations
    (left_values (fvar_to_nat variable))
    (right_values (fvar_to_nat variable)).
Proof.
  intros model context T variable.
  induction variable as [context T | context T U variable IHvariable];
    intros left_types right_types relations left_values right_values Hcontext.
  - exact (proj1 Hcontext).
  - change (source_type_rel model T left_types right_types relations
      ((env_tail left_values) (fvar_to_nat variable))
      ((env_tail right_values) (fvar_to_nat variable))).
    apply IHvariable.
    exact (proj2 Hcontext).
Qed.

Lemma term_environment_sem_lift_zero : forall (model : RelModel)
    context types values head,
  term_environment_sem model context types values ->
  term_environment_sem model (map (type_lift 0) context)
    (env_extend head types) values.
Proof.
  intros model context.
  induction context as [| T context IHcontext];
    intros types values head Hcontext.
  - exact I.
  - cbn [map term_environment_sem] in *.
    destruct Hcontext as [HT Hcontext].
    split.
    + assert (Hlift : lifted_type_environment 0
          (env_extend head types) types).
      { intros index value.
        rewrite env_extend_lift_zero.
        reflexivity. }
      apply (proj2
        (source_type_sem_lift_correct model T 0
          (env_extend head types) types Hlift (values 0))).
      exact HT.
    + now apply IHcontext.
Qed.

Lemma term_environment_rel_lift_zero : forall (model : RelModel)
    context left_types right_types relations left_values right_values
    left_head right_head relation_head,
  term_environment_rel model context
    left_types right_types relations left_values right_values ->
  term_environment_rel model (map (type_lift 0) context)
    (env_extend left_head left_types)
    (env_extend right_head right_types)
    (env_extend relation_head relations)
    left_values right_values.
Proof.
  intros model context.
  induction context as [| T context IHcontext];
    intros left_types right_types relations left_values right_values
      left_head right_head relation_head Hcontext.
  - exact I.
  - cbn [map term_environment_rel] in *.
    destruct Hcontext as [HT Hcontext].
    split.
    + assert (Hleft : lifted_type_environment 0
          (env_extend left_head left_types) left_types).
      { intros index value.
        rewrite env_extend_lift_zero.
        reflexivity. }
      assert (Hright : lifted_type_environment 0
          (env_extend right_head right_types) right_types).
      { intros index value.
        rewrite env_extend_lift_zero.
        reflexivity. }
      assert (Hrelations : lifted_relation_environment 0
          (env_extend relation_head relations) relations).
      { intros index lhs rhs.
        rewrite env_extend_lift_zero.
        reflexivity. }
      apply (proj2
        (source_type_rel_lift_correct model T 0
          (env_extend left_head left_types) left_types
          (env_extend right_head right_types) right_types
          (env_extend relation_head relations) relations
          Hleft Hright Hrelations
          (left_values 0) (right_values 0))).
      exact HT.
    + now apply IHcontext.
Qed.

(** Ordinary semantic type soundness is recorded separately.  It supplies
    the endpoint-membership components used by the abstraction theorem. *)
Theorem fterm_sem_typed : forall (model : ParametricModel)
    context T (term : fterm context T) types values,
  term_environment_sem model context types values ->
  source_type_sem model types T
    (fterm_sem model term types values).
Proof.
  intros model context T term.
  induction term as
      [context T variable
       | context T U body IHbody
       | context T U function IHfunction argument IHargument
       | context T body IHbody
       | context T function IHfunction U];
    intros types values Hcontext.
  - apply term_environment_sem_lookup.
    exact Hcontext.
  - cbn [fterm_sem source_type_sem].
    intros argument Hargument.
    rewrite model_abstract_beta.
    apply IHbody.
    cbn [term_environment_sem env_extend env_tail].
    split.
    + exact Hargument.
    + exact Hcontext.
  - cbn [fterm_sem].
    apply (IHfunction types values Hcontext).
    apply IHargument.
    exact Hcontext.
  - cbn [fterm_sem source_type_sem].
    intros A.
    rewrite model_type_abstract_beta.
    apply IHbody.
    apply term_environment_sem_lift_zero.
    exact Hcontext.
  - cbn [fterm_sem].
    apply (proj2
      (source_type_sem_subst_correct model T 0
        types U
        (env_extend (source_type_sem model types U) types)
        (substituted_type_environment_zero model types U)
        (model_type_apply model
          (fterm_sem model function types values)
          (source_type_sem model types U)))).
    apply IHfunction.
    exact Hcontext.
Qed.

(** ** Fundamental theorem *)

Theorem fterm_parametricity : forall (model : ParametricModel)
    context T (term : fterm context T)
    left_types right_types relations left_values right_values,
  term_environment_sem model context left_types left_values ->
  term_environment_sem model context right_types right_values ->
  term_environment_rel model context
    left_types right_types relations left_values right_values ->
  logical_relation model T left_types right_types relations
    (fterm_sem model term left_types left_values)
    (fterm_sem model term right_types right_values).
Proof.
  intros model context T term.
  induction term as
      [context T variable
       | context T U body IHbody
       | context T U function IHfunction argument IHargument
       | context T body IHbody
       | context T function IHfunction U];
    intros left_types right_types relations left_values right_values
      Hleft_context Hright_context Hrelated_context.
  - unfold logical_relation.
    repeat split.
    + now apply term_environment_sem_lookup with
        (context := context) (variable := variable).
    + now apply term_environment_sem_lookup with
        (context := context) (variable := variable).
    + now apply term_environment_rel_lookup with
        (context := context) (variable := variable).
  - unfold logical_relation.
    split.
    + cbn [fterm_sem source_type_sem].
      intros argument Hargument.
      rewrite model_abstract_beta.
      apply fterm_sem_typed.
      cbn [term_environment_sem env_extend env_tail].
      tauto.
    + split.
      * cbn [fterm_sem source_type_sem].
        intros argument Hargument.
        rewrite model_abstract_beta.
        apply fterm_sem_typed.
        cbn [term_environment_sem env_extend env_tail].
        tauto.
      * cbn [fterm_sem source_type_rel].
        intros left_argument Hleft_argument
          right_argument Hright_argument Hargument_related.
        rewrite !model_abstract_beta.
        apply IHbody.
        -- cbn [term_environment_sem env_extend env_tail].
           tauto.
        -- cbn [term_environment_sem env_extend env_tail].
           tauto.
        -- cbn [term_environment_rel env_extend env_tail].
           tauto.
  - destruct (IHfunction left_types right_types relations
        left_values right_values
        Hleft_context Hright_context Hrelated_context)
      as [Hleft_function [Hright_function Hrelated_function]].
    destruct (IHargument left_types right_types relations
        left_values right_values
        Hleft_context Hright_context Hrelated_context)
      as [Hleft_argument [Hright_argument Hrelated_argument]].
    unfold logical_relation.
    repeat split.
    + apply Hleft_function.
      exact Hleft_argument.
    + apply Hright_function.
      exact Hright_argument.
    + apply Hrelated_function.
      * exact Hleft_argument.
      * exact Hright_argument.
      * exact Hrelated_argument.
  - unfold logical_relation.
    split.
    + cbn [fterm_sem source_type_sem].
      intros A.
      rewrite model_type_abstract_beta.
      apply fterm_sem_typed.
      apply term_environment_sem_lift_zero.
      exact Hleft_context.
    + split.
      * cbn [fterm_sem source_type_sem].
        intros A.
        rewrite model_type_abstract_beta.
        apply fterm_sem_typed.
        apply term_environment_sem_lift_zero.
        exact Hright_context.
      * cbn [fterm_sem source_type_rel].
        intros left_type right_type relation Hbetween.
        rewrite !model_type_abstract_beta.
        apply IHbody.
        -- apply term_environment_sem_lift_zero.
           exact Hleft_context.
        -- apply term_environment_sem_lift_zero.
           exact Hright_context.
        -- apply term_environment_rel_lift_zero.
           exact Hrelated_context.
  - destruct (IHfunction left_types right_types relations
        left_values right_values
        Hleft_context Hright_context Hrelated_context)
      as [Hleft_function [Hright_function Hrelated_function]].
    set (left_replacement := source_type_sem model left_types U).
    set (right_replacement := source_type_sem model right_types U).
    set (replacement_relation :=
      logical_relation model U left_types right_types relations).
    assert (Hbody :
        logical_relation model T
          (env_extend left_replacement left_types)
          (env_extend right_replacement right_types)
          (env_extend replacement_relation relations)
          (model_type_apply model
            (fterm_sem model function left_types left_values)
            left_replacement)
          (model_type_apply model
            (fterm_sem model function right_types right_values)
            right_replacement)).
    { unfold logical_relation.
      repeat split.
      - apply Hleft_function.
      - apply Hright_function.
      - apply Hrelated_function.
        apply logical_relation_between. }
    cbn [fterm_sem].
    apply (proj2
      (logical_relation_subst_correct model T 0
        left_types (env_extend left_replacement left_types)
        right_types (env_extend right_replacement right_types)
        relations (env_extend replacement_relation relations) U
        (substituted_type_environment_zero model left_types U)
        (substituted_type_environment_zero model right_types U)
        (substituted_relation_environment_zero model relations
          replacement_relation)
        (model_type_apply model
          (fterm_sem model function left_types left_values)
          left_replacement)
        (model_type_apply model
          (fterm_sem model function right_types right_values)
          right_replacement))).
    exact Hbody.
Qed.

Corollary closed_fterm_parametricity : forall (model : ParametricModel)
    T (term : fterm [] T) left_types right_types relations
    left_values right_values,
  logical_relation model T left_types right_types relations
    (fterm_sem model term left_types left_values)
    (fterm_sem model term right_types right_values).
Proof.
  intros model T term left_types right_types relations
    left_values right_values.
  apply fterm_parametricity; exact I.
Qed.

(** A conventional, searchable name for the abstraction lemma. *)
Corollary fundamental_theorem_of_parametricity :
  forall (model : ParametricModel)
    context T (term : fterm context T)
    left_types right_types relations left_values right_values,
  term_environment_sem model context left_types left_values ->
  term_environment_sem model context right_types right_values ->
  term_environment_rel model context
    left_types right_types relations left_values right_values ->
  logical_relation model T left_types right_types relations
    (fterm_sem model term left_types left_values)
    (fterm_sem model term right_types right_values).
Proof.
  exact fterm_parametricity.
Qed.

(** For a closed term interpreted at one outer type environment, the public
    generated formula is valid when its symbolic program denotes that term.
    The formula itself introduces the distinct endpoint types and relations
    at every source [forall]. *)
Corollary closed_fterm_satisfies_relgen : forall
    (model : ParametricModel) T (term : fterm [] T)
    formula_types types relations values term_values
    free_values free_relations,
  paired_type_environment formula_types types types ->
  free_values 0 = fterm_sem model term types term_values ->
  formula_sem model formula_types relations values
    free_values free_relations (relgen T).
Proof.
  intros model T term formula_types types relations values term_values
    free_values free_relations Hpaired Hprogram.
  apply (proj2
    (relgen_correct model T formula_types types types relations
      values free_values free_relations Hpaired)).
  rewrite Hprogram.
  exact (proj2 (proj2
    (closed_fterm_parametricity model T term
      types types relations term_values term_values))).
Qed.

(** ** Consistency witness for the model laws

    Every semantic statement above is generic over a [ParametricModel].  The
    one-point model shows that the record laws are satisfiable, so none of
    those statements is vacuous.  It carries no information about programs;
    a term or domain model would be needed to extract concrete consequences
    through the model, which the lecture does not require. *)

Definition unit_rel_model : RelModel :=
  {| model_value := unit;
     model_apply := fun _ _ => tt;
     model_type_apply := fun _ _ => tt;
     model_type_apply_ext := fun _ _ _ _ => eq_refl;
     model_relation_apply := fun _ _ _ _ => True |}.

Lemma unit_eta : forall value : unit, tt = value.
Proof.
  intros [].
  reflexivity.
Qed.

Definition unit_parametric_model : ParametricModel :=
  {| parametric_rel_model := unit_rel_model;
     model_abstract := fun _ => tt;
     model_abstract_beta := fun body argument => unit_eta (body argument);
     model_type_abstract := fun _ => tt;
     model_type_abstract_beta := fun body A => unit_eta (body A) |}.

Example unit_model_validates_relgen : forall T (term : fterm [] T)
    formula_types types relations values term_values
    free_values free_relations,
  paired_type_environment formula_types types types ->
  free_values 0 = fterm_sem unit_parametric_model term types term_values ->
  formula_sem unit_parametric_model formula_types relations values
    free_values free_relations (relgen T).
Proof.
  intros T term formula_types types relations values term_values
    free_values free_relations Hpaired Hprogram.
  exact (closed_fterm_satisfies_relgen unit_parametric_model T term
    formula_types types relations values term_values
    free_values free_relations Hpaired Hprogram).
Qed.
