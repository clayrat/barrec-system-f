(** * Type-level bridge from Algorithm W to System F

    A successful W result is first generalized with [gen_ty] in the
    substituted environment.  At the closed top level that environment is
    empty.  Generalized scheme variables become explicit outer [TForall]
    binders, free scheme variables are resolved in an ambient System F type
    context, and HM constants are interpreted by an explicit client-supplied
    map to closed System F types.

    Generalized variables are numbered by first occurrence from left to
    right.  Thus [sc_gen 0] becomes the outermost quantifier: in a body under
    [n] binders it is represented by de Bruijn index [n - 1].

    This file establishes the type bridge and connects it to [relgen].  Term
    elaboration, explicit type applications, and preservation of erasure are
    the separate next layer. *)

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

From SystemF.F Require Import Syntax Scope.
From SystemF.FreeTheorems Require Import Formula Generate.
From SystemF.HM Require Import Infer.
From SystemF.HM.WInCoq Require Import Gen Schemes.

Definition ConstantInterpretation : Type := id -> type.

Definition constants_closed
    (constants : ConstantInterpretation) : Prop :=
  forall name, closed 0 (constants name).

(** [free_variables_scoped depth resolve sigma] says that every [sc_var]
    has an ambient de Bruijn index below [depth].  [sc_gen] variables are
    checked separately because they are bound by the quantifiers introduced
    by this bridge. *)
Fixpoint free_variables_scoped
    (depth : nat) (resolve : id -> nat) (sigma : schm) : Prop :=
  match sigma with
  | sc_var variable => resolve variable < depth
  | sc_con _ => True
  | sc_gen _ => True
  | sc_arrow domain codomain =>
      free_variables_scoped depth resolve domain /\
      free_variables_scoped depth resolve codomain
  end.

Fixpoint generalized_variables_scoped
    (count : nat) (sigma : schm) : Prop :=
  match sigma with
  | sc_var _ => True
  | sc_con _ => True
  | sc_gen variable => variable < count
  | sc_arrow domain codomain =>
      generalized_variables_scoped count domain /\
      generalized_variables_scoped count codomain
  end.

Lemma generalized_variables_scoped_mono : forall sigma n m,
  n <= m ->
  generalized_variables_scoped n sigma ->
  generalized_variables_scoped m sigma.
Proof.
  induction sigma as
      [variable | name | variable | domain IHdomain codomain IHcodomain];
    intros n m Hnm Hscoped;
    cbn [generalized_variables_scoped] in *.
  - exact I.
  - exact I.
  - lia.
  - destruct Hscoped as [Hleft Hright].
    split.
    + now apply IHdomain with n.
    + now apply IHcodomain with n.
Qed.

Lemma generalized_variables_scoped_max : forall sigma,
  generalized_variables_scoped (max_gen_vars sigma) sigma.
Proof.
  induction sigma as
      [variable | name | variable | domain IHdomain codomain IHcodomain];
    cbn [generalized_variables_scoped max_gen_vars] in *.
  - exact I.
  - exact I.
  - lia.
  - split.
    + apply generalized_variables_scoped_mono
        with (n := max_gen_vars domain).
      * apply Nat.le_max_l.
      * exact IHdomain.
    + apply generalized_variables_scoped_mono
        with (n := max_gen_vars codomain).
      * apply Nat.le_max_r.
      * exact IHcodomain.
Qed.

(** Translate the body under all generalized binders.  Ambient free
    variables are shifted by [quantifier_count]; generalized variable [i]
    uses the reversed index [quantifier_count - S i] so that [0] denotes the
    first, outermost quantifier. *)
Fixpoint scheme_body_to_type
    (constants : ConstantInterpretation)
    (resolve : id -> nat)
    (quantifier_count : nat)
    (sigma : schm) : type :=
  match sigma with
  | sc_var variable => TVar (quantifier_count + resolve variable)
  | sc_con name => constants name
  | sc_gen variable => TVar (quantifier_count - S variable)
  | sc_arrow domain codomain =>
      TArrow
        (scheme_body_to_type constants resolve quantifier_count domain)
        (scheme_body_to_type constants resolve quantifier_count codomain)
  end.

Fixpoint quantify_scheme (count : nat) (body : type) : type :=
  match count with
  | 0 => body
  | S count => TForall (quantify_scheme count body)
  end.

Definition scheme_to_systemf
    (constants : ConstantInterpretation)
    (resolve : id -> nat)
    (sigma : schm) : type :=
  let count := max_gen_vars sigma in
  quantify_scheme count
    (scheme_body_to_type constants resolve count sigma).

(** ** Scope correctness *)

Lemma scheme_body_to_type_scoped : forall constants resolve sigma
    ambient_depth quantifier_count,
  constants_closed constants ->
  free_variables_scoped ambient_depth resolve sigma ->
  generalized_variables_scoped quantifier_count sigma ->
  closed (quantifier_count + ambient_depth)
    (scheme_body_to_type constants resolve quantifier_count sigma).
Proof.
  intros constants resolve sigma.
  induction sigma as
      [variable | name | variable | domain IHdomain codomain IHcodomain];
    intros ambient_depth quantifier_count Hconstants Hfree Hgeneralized;
    cbn [free_variables_scoped generalized_variables_scoped
      scheme_body_to_type closed] in *.
  - lia.
  - apply closed_mono with (n := 0).
    + lia.
    + apply Hconstants.
  - lia.
  - destruct Hfree as [Hfree_left Hfree_right].
    destruct Hgeneralized as [Hgen_left Hgen_right].
    split.
    + now apply IHdomain.
    + now apply IHcodomain.
Qed.

Lemma quantify_scheme_scoped : forall count ambient_depth body,
  closed (count + ambient_depth) body ->
  closed ambient_depth (quantify_scheme count body).
Proof.
  induction count as [| count IH]; intros ambient_depth body Hbody.
  - exact Hbody.
  - cbn [quantify_scheme closed].
    apply IH.
    replace (count + S ambient_depth)
      with (S count + ambient_depth) by lia.
    exact Hbody.
Qed.

Theorem scheme_to_systemf_scoped : forall constants resolve sigma
    ambient_depth,
  constants_closed constants ->
  free_variables_scoped ambient_depth resolve sigma ->
  closed ambient_depth (scheme_to_systemf constants resolve sigma).
Proof.
  intros constants resolve sigma ambient_depth Hconstants Hfree.
  unfold scheme_to_systemf.
  apply quantify_scheme_scoped.
  apply scheme_body_to_type_scoped.
  - exact Hconstants.
  - exact Hfree.
  - apply generalized_variables_scoped_max.
Qed.

(** Generalization in an empty HM context cannot leave an [sc_var]. *)
Lemma gen_ty_aux_empty_free_variables_scoped : forall tau variables,
  free_variables_scoped 0 (fun _ => 0)
    (fst (gen_ty_aux tau [] variables)).
Proof.
  induction tau as
      [variable | name | domain IHdomain codomain IHcodomain];
    intros variables;
    cbn [gen_ty_aux].
  - unfold FV_ctx.
    cbn [ListIds.in_list_id].
    destruct (ListIds.index_list_id variable variables); exact I.
  - exact I.
  - destruct (gen_ty_aux domain [] variables)
      as [domain_scheme domain_variables] eqn:Hdomain.
    destruct (gen_ty_aux codomain [] domain_variables)
      as [codomain_scheme codomain_variables] eqn:Hcodomain.
    cbn [free_variables_scoped].
    split.
    + specialize (IHdomain variables).
      rewrite Hdomain in IHdomain.
      exact IHdomain.
    + specialize (IHcodomain domain_variables).
      rewrite Hcodomain in IHcodomain.
      exact IHcodomain.
Qed.

Corollary gen_ty_empty_free_variables_scoped : forall tau,
  free_variables_scoped 0 (fun _ => 0) (gen_ty tau []).
Proof.
  intro tau.
  unfold gen_ty.
  apply gen_ty_aux_empty_free_variables_scoped.
Qed.

Definition hm_principal_scheme (tau : ty) : schm :=
  gen_ty tau [].

Definition hm_principal_type
    (constants : ConstantInterpretation) (tau : ty) : type :=
  scheme_to_systemf constants (fun _ => 0) (hm_principal_scheme tau).

Theorem hm_principal_type_closed : forall constants tau,
  constants_closed constants ->
  closed 0 (hm_principal_type constants tau).
Proof.
  intros constants tau Hconstants.
  unfold hm_principal_type, hm_principal_scheme.
  apply scheme_to_systemf_scoped.
  - exact Hconstants.
  - apply gen_ty_empty_free_variables_scoped.
Qed.

(** ** Public checked and executable W entry points *)

Definition infer_systemf_type_checked
    (constants : ConstantInterpretation) (expression : term) : option type :=
  match runW expression [] with
  | inl (tau, _) => Some (hm_principal_type constants tau)
  | inr _ => None
  end.

Definition infer_systemf_type_exec
    (constants : ConstantInterpretation) (expression : term) : option type :=
  match runW_exec expression [] with
  | inferred tau _ => Some (hm_principal_type constants tau)
  | inference_rejected => None
  end.

Theorem infer_systemf_type_correspondence : forall constants expression,
  infer_systemf_type_checked constants expression =
  infer_systemf_type_exec constants expression.
Proof.
  intros constants expression.
  unfold infer_systemf_type_checked, infer_systemf_type_exec.
  destruct (runW expression []) as [[tau substitution] | failure]
    eqn:Hrun.
  - pose proof
      (proj2
        (runW_exec_success_iff_checked_success
          expression [] tau substitution) Hrun) as Hexec.
    rewrite Hexec.
    reflexivity.
  - assert (Hexec : runW_exec expression [] = inference_rejected).
    { apply (proj2
        (runW_exec_rejected_iff_checked_rejected expression [])).
      now exists failure. }
    rewrite Hexec.
    reflexivity.
Qed.

Theorem infer_systemf_type_exec_closed : forall constants expression T,
  constants_closed constants ->
  infer_systemf_type_exec constants expression = Some T ->
  closed 0 T.
Proof.
  intros constants expression T Hconstants Hinfer.
  unfold infer_systemf_type_exec in Hinfer.
  destruct (runW_exec expression []) as [tau substitution |]
    eqn:Hrun; try discriminate.
  inversion Hinfer; subst T.
  now apply hm_principal_type_closed.
Qed.

Theorem infer_systemf_type_checked_closed : forall constants expression T,
  constants_closed constants ->
  infer_systemf_type_checked constants expression = Some T ->
  closed 0 T.
Proof.
  intros constants expression T Hconstants Hinfer.
  rewrite infer_systemf_type_correspondence in Hinfer.
  now apply infer_systemf_type_exec_closed
    with (constants := constants) (expression := expression).
Qed.

Definition BridgedType : Type :=
  {T : type | closed 0 T}.

Definition infer_systemf_type
    (constants : ConstantInterpretation)
    (Hconstants : constants_closed constants)
    (expression : term) : option BridgedType :=
  match runW_exec expression [] with
  | inferred tau _ =>
      Some (exist _ (hm_principal_type constants tau)
        (hm_principal_type_closed constants tau Hconstants))
  | inference_rejected => None
  end.

Definition infer_relational_formula_exec
    (constants : ConstantInterpretation)
    (expression : term) : option RelFormula :=
  match infer_systemf_type_exec constants expression with
  | Some T => Some (relgen T)
  | None => None
  end.

Theorem infer_relational_formula_exec_closed : forall constants expression T,
  constants_closed constants ->
  infer_systemf_type_exec constants expression = Some T ->
  closed_formula (relgen T).
Proof.
  intros constants expression T Hconstants Hinfer.
  apply relgen_closed.
  now apply infer_systemf_type_exec_closed
    with (constants := constants) (expression := expression).
Qed.
