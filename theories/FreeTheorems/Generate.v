(** * Relational translation of System F types

    [relate T lhs rhs] is the printable relational interpretation of [T]
    applied to two value expressions.  The public [relgen] specialises both
    endpoints to the same symbolic program [RVFree 0], as in the usual
    statement of a free theorem.

    Every source type variable gives rise to two formula-level type variables
    and one relation variable.  Under a source [forall], the left type is
    bound first, the right type second, and their relation third. *)

From Stdlib Require Import Lia PeanoNat.

From SystemF.F Require Import Syntax Scope.
From SystemF.FreeTheorems Require Import Formula.

Implicit Types
  (n type_depth value_depth : nat)
  (T U : type)
  (lhs rhs : ValueExpr).

Inductive Projection : Type :=
| ProjectLeft
| ProjectRight.

(** Extend a type-variable renaming underneath a formula-type binder. *)
Definition lift_type_renaming
    (rho : nat -> nat) (index : nat) : nat :=
  match index with
  | 0 => 0
  | S index => S (rho index)
  end.

Fixpoint project_type_with
    (rho : nat -> nat) (T : type) : FormulaType :=
  match T with
  | TVar index => RTVar (rho index)
  | TArrow T U =>
      RTArrow (project_type_with rho T) (project_type_with rho U)
  | TForall T =>
      RTForall (project_type_with (lift_type_renaming rho) T)
  end.

(** Direct embedding is used for the closed type of the symbolic program. *)
Definition formula_type_of_type (T : type) : FormulaType :=
  project_type_with (fun index => index) T.

(** In a relational environment, source variable [i] is represented by the
    adjacent pair [2*i+1] (left) and [2*i] (right). *)
Definition projection_index
    (projection : Projection) (index : nat) : nat :=
  match projection with
  | ProjectLeft => S (2 * index)
  | ProjectRight => 2 * index
  end.

Definition project_type
    (projection : Projection) (T : type) : FormulaType :=
  project_type_with (projection_index projection) T.

Definition value_weaken_twice (value : ValueExpr) : ValueExpr :=
  value_lift 0 (value_lift 0 value).

Definition value_type_weaken_twice (value : ValueExpr) : ValueExpr :=
  value_type_lift 0 (value_type_lift 0 value).

Fixpoint relate
    (T : type) (lhs rhs : ValueExpr) : RelFormula :=
  match T with
  | TVar index =>
      RFRel (RRBound index) lhs rhs
  | TArrow A B =>
      RFForallValue (project_type ProjectLeft A)
        (RFForallValue (project_type ProjectRight A)
          (RFImplies
            (relate A (RVBound 1) (RVBound 0))
            (relate B
              (RVApp (value_weaken_twice lhs) (RVBound 1))
              (RVApp (value_weaken_twice rhs) (RVBound 0)))))
  | TForall body =>
      RFForallType
        (RFForallType
          (RFForallRelation (RTVar 1) (RTVar 0)
            (relate body
              (RVTypeApp
                (value_type_weaken_twice lhs) (RTVar 1))
              (RVTypeApp
                (value_type_weaken_twice rhs) (RTVar 0)))))
  end.

(** Symbol zero is conventionally printed as the program whose free theorem
    is being generated. *)
Definition relgen (T : type) : RelFormula :=
  relate T (RVFree 0) (RVFree 0).

(** ** Scope infrastructure *)

Lemma project_type_with_scoped : forall T n type_depth rho,
  closed n T ->
  (forall index, index < n -> rho index < type_depth) ->
  formula_type_scoped type_depth (project_type_with rho T).
Proof.
  induction T as [index | T IHT U IHU | T IHT];
    intros n type_depth rho Hclosed Hrho;
    cbn [closed project_type_with formula_type_scoped] in *.
  - now apply Hrho.
  - destruct Hclosed as [HT HU].
    split.
    + now apply IHT with (n := n).
    + now apply IHU with (n := n).
  - apply IHT with (n := S n).
    + exact Hclosed.
    + intros [| index] Hindex;
        cbn [lift_type_renaming].
      * lia.
      * specialize (Hrho index).
        lia.
Qed.

Corollary formula_type_of_type_scoped : forall n T,
  closed n T ->
  formula_type_scoped n (formula_type_of_type T).
Proof.
  intros n T Hclosed.
  apply project_type_with_scoped with (n := n).
  - exact Hclosed.
  - intros index Hindex.
    exact Hindex.
Qed.

Corollary project_type_scoped : forall projection n T,
  closed n T ->
  formula_type_scoped (2 * n) (project_type projection T).
Proof.
  intros projection n T Hclosed.
  apply project_type_with_scoped with (n := n).
  - exact Hclosed.
  - intros index Hindex.
    destruct projection; cbn [projection_index]; lia.
Qed.

Lemma formula_type_lift_scoped : forall (formula_type : FormulaType)
    cutoff type_depth,
  cutoff <= type_depth ->
  formula_type_scoped type_depth formula_type ->
  formula_type_scoped (S type_depth)
    (formula_type_lift cutoff formula_type).
Proof.
  induction formula_type as [index | T IHT U IHU | T IHT];
    intros cutoff type_depth Hcutoff Hscoped;
    cbn [formula_type_scoped formula_type_lift] in *.
  - unfold lift_index.
    destruct (index <? cutoff) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      lia.
    + apply Nat.ltb_ge in Hlt.
      lia.
  - destruct Hscoped as [HT HU].
    split.
    + now apply IHT.
    + now apply IHU.
  - apply IHT.
    + lia.
    + exact Hscoped.
Qed.

Lemma value_lift_scoped : forall type_depth value_depth value,
  value_scoped type_depth value_depth value ->
  value_scoped type_depth (S value_depth) (value_lift 0 value).
Proof.
  intros type_depth value_depth value.
  induction value as
      [index | name | function IHfunction argument IHargument
       | function IHfunction T];
    intro Hscoped;
    cbn [value_scoped value_lift lift_index] in *.
  - unfold lift_index.
    destruct (index <? 0) eqn:Hindex; lia.
  - exact I.
  - destruct Hscoped as [Hfunction Hargument].
    split.
    + now apply IHfunction.
    + now apply IHargument.
  - destruct Hscoped as [Hfunction HT].
    split.
    + now apply IHfunction.
    + exact HT.
Qed.

Lemma value_type_lift_scoped : forall type_depth value_depth value,
  value_scoped type_depth value_depth value ->
  value_scoped (S type_depth) value_depth (value_type_lift 0 value).
Proof.
  intros type_depth value_depth value.
  induction value as
      [index | name | function IHfunction argument IHargument
       | function IHfunction T];
    intro Hscoped;
    cbn [value_scoped value_type_lift] in *.
  - exact Hscoped.
  - exact I.
  - destruct Hscoped as [Hfunction Hargument].
    split.
    + now apply IHfunction.
    + now apply IHargument.
  - destruct Hscoped as [Hfunction HT].
    split.
    + now apply IHfunction.
    + apply formula_type_lift_scoped.
      * lia.
      * exact HT.
Qed.

(** The three formula namespaces grow in lock-step with the source type
    context: two type variables and one relation variable per source
    variable. *)
Theorem relate_scoped : forall T n value_depth lhs rhs,
  closed n T ->
  value_scoped (2 * n) value_depth lhs ->
  value_scoped (2 * n) value_depth rhs ->
  formula_scoped (2 * n) n value_depth (relate T lhs rhs).
Proof.
  induction T as [index | A IHA B IHB | body IHbody];
    intros n value_depth lhs rhs Hclosed Hlhs Hrhs.
  - cbn [closed relate formula_scoped relation_scoped] in *.
    now repeat split.
  - cbn [closed] in Hclosed.
    destruct Hclosed as [HA HB].
    cbn [relate formula_scoped].
    repeat split.
    + now apply project_type_scoped.
    + now apply project_type_scoped.
    + apply IHA with (n := n).
      * exact HA.
      * cbn [value_scoped].
        lia.
      * cbn [value_scoped].
        lia.
    + apply IHB with (n := n).
      * exact HB.
      * cbn [value_scoped].
        split.
        -- unfold value_weaken_twice.
           apply value_lift_scoped.
           now apply value_lift_scoped.
        -- lia.
      * cbn [value_scoped].
        split.
        -- unfold value_weaken_twice.
           apply value_lift_scoped.
           now apply value_lift_scoped.
        -- lia.
  - cbn [closed] in Hclosed.
    cbn [relate formula_scoped].
    repeat split.
    + cbn [formula_type_scoped].
      lia.
    + cbn [formula_type_scoped].
      lia.
    + assert (Hlhs' :
          value_scoped (S (S (2 * n))) value_depth
            (value_type_weaken_twice lhs)).
      { unfold value_type_weaken_twice.
        apply value_type_lift_scoped.
        now apply value_type_lift_scoped. }
      assert (Hrhs' :
          value_scoped (S (S (2 * n))) value_depth
            (value_type_weaken_twice rhs)).
      { unfold value_type_weaken_twice.
        apply value_type_lift_scoped.
        now apply value_type_lift_scoped. }
      assert (Hlhs_app :
          value_scoped (2 * S n) value_depth
            (RVTypeApp (value_type_weaken_twice lhs) (RTVar 1))).
      { replace (2 * S n) with (S (S (2 * n))) by lia.
        cbn [value_scoped formula_type_scoped].
        split.
        - exact Hlhs'.
        - lia. }
      assert (Hrhs_app :
          value_scoped (2 * S n) value_depth
            (RVTypeApp (value_type_weaken_twice rhs) (RTVar 0))).
      { replace (2 * S n) with (S (S (2 * n))) by lia.
        cbn [value_scoped formula_type_scoped].
        split; [exact Hrhs' | lia]. }
      pose proof
        (IHbody (S n) value_depth
          (RVTypeApp (value_type_weaken_twice lhs) (RTVar 1))
          (RVTypeApp (value_type_weaken_twice rhs) (RTVar 0))
          Hclosed Hlhs_app Hrhs_app) as Hbody.
      replace (2 * S n) with (S (S (2 * n))) in Hbody by lia.
      exact Hbody.
Qed.

Theorem relgen_closed : forall T,
  closed 0 T -> closed_formula (relgen T).
Proof.
  intros T Hclosed.
  unfold closed_formula, relgen.
  apply relate_scoped with (n := 0).
  - exact Hclosed.
  - exact I.
  - exact I.
Qed.

Definition GeneratedFormula : Type :=
  {formula : RelFormula | closed_formula formula}.

Definition generateClosed
    (T : type) (Hclosed : closed 0 T) : GeneratedFormula :=
  exist _ (relgen T) (relgen_closed T Hclosed).
