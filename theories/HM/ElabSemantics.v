(** * Semantic interpretation of Algorithm W types

    This module interprets W monotypes, schemes, substitutions, generalized
    variables, instantiations, and contexts as System F types.  It contains
    no Church-term reifier and no public frontend: [HMElab] uses these laws
    to prove that its syntax construction preserves W typing. *)

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

From SystemF.F Require Import Syntax Scope TypeSubstitution RawTyping.
From SystemF.HM Require Import Erasure WElab.
From SystemF.HM.WInCoq Require Import Gen Schemes SimpleTypes Subst SubstSchm.
From SystemF.HM.WInCoq Require Import Context Disjoints ListIds.

Definition ConstantInterpretation : Type := id -> type.

Definition constants_closed
    (constants : ConstantInterpretation) : Prop :=
  forall name, closed 0 (constants name).

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

(** W may introduce unconstrained metavariables that occur only in an
    internal annotation and disappear from the principal result type.  Such
    variables have no top-level System F binder.  Instantiating all of them
    with one fixed closed type preserves every equality established by W and
    cannot capture a surrounding type binder. *)
Definition reification_default_type : type :=
  TForall (TArrow (TVar 0) (TVar 0)).

Definition reification_default_valuation : id -> type :=
  fun _ => reification_default_type.

Lemma reification_default_type_closed : forall n,
  closed n reification_default_type.
Proof.
  intro n.
  cbn [reification_default_type closed].
  lia.
Qed.

(** ** Semantic interpretation of W types

    A valuation gives a System F meaning to every globally fresh W type
    identifier.  Unlike the earlier stack-oriented translation, this view
    composes directly with W substitutions and is therefore convenient for
    the preservation proof. *)

Definition TypeValuation : Type := id -> type.

Definition valuation_scoped (depth : nat) (valuation : TypeValuation) : Prop :=
  forall variable, closed depth (valuation variable).

Lemma reification_default_valuation_scoped : forall depth,
  valuation_scoped depth reification_default_valuation.
Proof.
  intros depth variable.
  apply reification_default_type_closed.
Qed.

Fixpoint denote_monotype
    (constants : ConstantInterpretation)
    (valuation : TypeValuation)
    (tau : ty) : type :=
  match tau with
  | var variable => valuation variable
  | con name => constants name
  | arrow domain codomain =>
      TArrow
        (denote_monotype constants valuation domain)
        (denote_monotype constants valuation codomain)
  end.

Definition valuation_after_substitution
    (constants : ConstantInterpretation)
    (substitution : substitution)
    (valuation : TypeValuation) : TypeValuation :=
  fun variable =>
    denote_monotype constants valuation
      (apply_subst substitution (var variable)).

Lemma denote_monotype_after_substitution : forall
    constants substitution valuation tau,
  denote_monotype constants
    (valuation_after_substitution constants substitution valuation) tau =
  denote_monotype constants valuation (apply_subst substitution tau).
Proof.
  intros constants substitution valuation tau.
  induction tau as [variable | name | domain IHdomain codomain IHcodomain].
  - reflexivity.
  - reflexivity.
  - cbn [denote_monotype apply_subst].
    now rewrite IHdomain, IHcodomain.
Qed.

Lemma valuation_after_compose : forall
    constants first second valuation variable,
  valuation_after_substitution constants (compose_subst first second)
    valuation variable =
  valuation_after_substitution constants first
    (valuation_after_substitution constants second valuation) variable.
Proof.
  intros constants first second valuation variable.
  unfold valuation_after_substitution.
  rewrite apply_compose_equiv.
  symmetry.
  apply denote_monotype_after_substitution.
Qed.

Fixpoint denote_scheme_body
    (constants : ConstantInterpretation)
    (valuation : TypeValuation)
    (quantifier_count : nat)
    (sigma : schm) : type :=
  match sigma with
  | sc_var variable =>
      lift_type_by quantifier_count (valuation variable)
  | sc_con name => constants name
  | sc_gen variable => TVar (quantifier_count - S variable)
  | sc_arrow domain codomain =>
      TArrow
        (denote_scheme_body constants valuation quantifier_count domain)
        (denote_scheme_body constants valuation quantifier_count codomain)
  end.

Definition denote_scheme
    (constants : ConstantInterpretation)
    (valuation : TypeValuation)
    (sigma : schm) : type :=
  let count := max_gen_vars sigma in
  quantify_type count
    (denote_scheme_body constants valuation count sigma).

Lemma denote_monotype_valuation_ext : forall
    constants valuation valuation' tau,
  (forall variable, valuation variable = valuation' variable) ->
  denote_monotype constants valuation tau =
  denote_monotype constants valuation' tau.
Proof.
  intros constants valuation valuation' tau Hequal.
  induction tau as [variable | name | domain IHdomain codomain IHcodomain];
    cbn [denote_monotype].
  - apply Hequal.
  - reflexivity.
  - now rewrite IHdomain, IHcodomain.
Qed.

Lemma denote_scheme_body_valuation_ext : forall
    constants valuation valuation' sigma count,
  (forall variable, valuation variable = valuation' variable) ->
  denote_scheme_body constants valuation count sigma =
  denote_scheme_body constants valuation' count sigma.
Proof.
  intros constants valuation valuation' sigma.
  induction sigma as
      [variable | name | variable | domain IHdomain codomain IHcodomain];
    intros count Hequal; cbn [denote_scheme_body].
  - now rewrite Hequal.
  - reflexivity.
  - reflexivity.
  - now rewrite IHdomain, IHcodomain.
Qed.

Lemma denote_scheme_valuation_ext : forall
    constants valuation valuation' sigma,
  (forall variable, valuation variable = valuation' variable) ->
  denote_scheme constants valuation sigma =
  denote_scheme constants valuation' sigma.
Proof.
  intros constants valuation valuation' sigma Hequal.
  unfold denote_scheme.
  f_equal.
  now apply denote_scheme_body_valuation_ext.
Qed.

Lemma denote_monotype_scoped : forall constants valuation tau depth,
  constants_closed constants ->
  valuation_scoped depth valuation ->
  closed depth (denote_monotype constants valuation tau).
Proof.
  intros constants valuation tau.
  induction tau as [variable | name | domain IHdomain codomain IHcodomain];
    intros depth Hconstants Hvaluation; cbn [denote_monotype closed].
  - apply Hvaluation.
  - apply closed_mono with (n := 0).
    + lia.
    + apply Hconstants.
  - now split; [apply IHdomain | apply IHcodomain].
Qed.

Lemma valuation_after_substitution_scoped : forall
    constants substitution valuation depth,
  constants_closed constants ->
  valuation_scoped depth valuation ->
  valuation_scoped depth
    (valuation_after_substitution constants substitution valuation).
Proof.
  intros constants substitution valuation depth Hconstants Hvaluation variable.
  unfold valuation_after_substitution.
  now apply denote_monotype_scoped.
Qed.

Lemma quantify_type_scoped : forall count depth body,
  closed (count + depth) body ->
  closed depth (quantify_type count body).
Proof.
  induction count as [| count IH]; intros depth body Hbody.
  - exact Hbody.
  - cbn [quantify_type closed].
    apply IH.
    replace (count + S depth) with (S count + depth) by lia.
    exact Hbody.
Qed.

Lemma denote_scheme_body_scoped : forall
    constants valuation sigma depth count,
  constants_closed constants ->
  valuation_scoped depth valuation ->
  generalized_variables_scoped count sigma ->
  closed (count + depth)
    (denote_scheme_body constants valuation count sigma).
Proof.
  intros constants valuation sigma.
  induction sigma as
      [variable | name | variable | domain IHdomain codomain IHcodomain];
    intros depth count Hconstants Hvaluation Hgeneralized;
    cbn [denote_scheme_body generalized_variables_scoped closed] in *.
  - now apply lift_type_by_closed, Hvaluation.
  - apply closed_mono with (n := 0).
    + lia.
    + apply Hconstants.
  - lia.
  - destruct Hgeneralized as [Hdomain Hcodomain].
    split.
    + now apply IHdomain.
    + now apply IHcodomain.
Qed.

Lemma denote_scheme_scoped : forall
    constants valuation sigma depth,
  constants_closed constants ->
  valuation_scoped depth valuation ->
  closed depth (denote_scheme constants valuation sigma).
Proof.
  intros constants valuation sigma depth Hconstants Hvaluation.
  unfold denote_scheme.
  apply quantify_type_scoped.
  apply denote_scheme_body_scoped.
  - exact Hconstants.
  - exact Hvaluation.
  - apply generalized_variables_scoped_max.
Qed.

Lemma max_gen_vars_ty_to_schm : forall tau,
  max_gen_vars (ty_to_schm tau) = 0.
Proof.
  induction tau as [variable | name | domain IHdomain codomain IHcodomain];
    cbn [ty_to_schm max_gen_vars].
  - reflexivity.
  - reflexivity.
  - now rewrite IHdomain, IHcodomain.
Qed.

Lemma max_gen_vars_apply_subst_schm : forall substitution sigma,
  max_gen_vars (apply_subst_schm substitution sigma) =
  max_gen_vars sigma.
Proof.
  intros substitution sigma.
  induction sigma as
      [variable | name | variable | domain IHdomain codomain IHcodomain];
    cbn [apply_subst_schm max_gen_vars].
  - apply max_gen_vars_ty_to_schm.
  - reflexivity.
  - reflexivity.
  - now rewrite IHdomain, IHcodomain.
Qed.

Lemma denote_scheme_body_ty_to_schm : forall
    constants valuation tau count,
  constants_closed constants ->
  denote_scheme_body constants valuation count (ty_to_schm tau) =
  lift_type_by count (denote_monotype constants valuation tau).
Proof.
  intros constants valuation tau.
  induction tau as [variable | name | domain IHdomain codomain IHcodomain];
    intros count Hconstants;
    cbn [ty_to_schm denote_scheme_body denote_monotype].
  - reflexivity.
  - symmetry.
    now apply lift_type_by_closed_zero, Hconstants.
  - unfold lift_type_by.
    cbn [rename_type].
    now rewrite IHdomain, IHcodomain.
Qed.

Lemma denote_scheme_body_after_substitution : forall
    constants substitution valuation sigma count,
  constants_closed constants ->
  denote_scheme_body constants
    (valuation_after_substitution constants substitution valuation)
    count sigma =
  denote_scheme_body constants valuation count
    (apply_subst_schm substitution sigma).
Proof.
  intros constants substitution valuation sigma.
  induction sigma as
      [variable | name | variable | domain IHdomain codomain IHcodomain];
    intros count Hconstants;
    cbn [denote_scheme_body apply_subst_schm].
  - unfold valuation_after_substitution.
    symmetry.
    now apply denote_scheme_body_ty_to_schm.
  - reflexivity.
  - reflexivity.
  - now rewrite IHdomain, IHcodomain.
Qed.

Lemma denote_scheme_after_substitution : forall
    constants substitution valuation sigma,
  constants_closed constants ->
  denote_scheme constants
    (valuation_after_substitution constants substitution valuation) sigma =
  denote_scheme constants valuation
    (apply_subst_schm substitution sigma).
Proof.
  intros constants substitution valuation sigma Hconstants.
  unfold denote_scheme.
  rewrite max_gen_vars_apply_subst_schm.
  f_equal.
  now apply denote_scheme_body_after_substitution.
Qed.

Lemma denote_scheme_body_instantiation : forall
    constants valuation sigma instantiation instance,
  constants_closed constants ->
  apply_inst_subst instantiation sigma = Some instance ->
  substitute_type
    (closing_type_substitution
      (map (denote_monotype constants valuation) instantiation))
    (denote_scheme_body constants valuation
      (length instantiation) sigma) =
  denote_monotype constants valuation instance.
Proof.
  intros constants valuation sigma.
  induction sigma as
      [variable | name | variable | domain IHdomain codomain IHcodomain];
    intros instantiation instance Hconstants Hinstance;
    cbn [apply_inst_subst denote_scheme_body] in Hinstance |- *.
  - inversion Hinstance; subst instance.
    replace (length instantiation) with
      (length (map (denote_monotype constants valuation) instantiation))
      by apply map_length.
    apply closing_type_substitution_lift.
  - inversion Hinstance; subst instance.
    apply substitute_type_closed_zero.
    apply Hconstants.
  - destruct (nth_error instantiation variable)
      as [argument |] eqn:Hargument; try discriminate.
    inversion Hinstance; subst instance.
    cbn [substitute_type].
    replace (length instantiation) with
      (length (map (denote_monotype constants valuation) instantiation))
      by apply map_length.
    apply closing_type_substitution_nth.
    now rewrite nth_error_map, Hargument.
  - destruct (apply_inst_subst instantiation domain)
      as [domain' |] eqn:Hdomain; try discriminate.
    destruct (apply_inst_subst instantiation codomain)
      as [codomain' |] eqn:Hcodomain; try discriminate.
    inversion Hinstance; subst instance.
    cbn [substitute_type denote_monotype].
    now rewrite (IHdomain instantiation domain' Hconstants Hdomain),
      (IHcodomain instantiation codomain' Hconstants Hcodomain).
Qed.

Lemma denote_scheme_instantiation : forall
    constants valuation sigma instantiation instance,
  constants_closed constants ->
  length instantiation = max_gen_vars sigma ->
  apply_inst_subst instantiation sigma = Some instance ->
  instantiate_type (denote_scheme constants valuation sigma)
    (map (denote_monotype constants valuation) instantiation) =
  denote_monotype constants valuation instance.
Proof.
  intros constants valuation sigma instantiation instance
    Hconstants Hlength Hinstance.
  unfold denote_scheme.
  rewrite <- Hlength.
  replace (length instantiation) with
    (length (map (denote_monotype constants valuation) instantiation))
    by apply map_length.
  rewrite instantiate_quantified_type.
  rewrite map_length.
  now apply denote_scheme_body_instantiation.
Qed.


Definition generalized_valuation
    (generalized : list id)
    (valuation : TypeValuation) : TypeValuation :=
  fun variable =>
    match index_list_id variable generalized with
    | Some index => TVar (length generalized - S index)
    | None => lift_type_by (length generalized) (valuation variable)
    end.

Lemma generalized_valuation_scoped : forall
    generalized depth valuation,
  valuation_scoped depth valuation ->
  valuation_scoped (length generalized + depth)
    (generalized_valuation generalized valuation).
Proof.
  intros generalized depth valuation Hvaluation variable.
  unfold generalized_valuation.
  destruct (index_list_id variable generalized)
    as [index |] eqn:Hindex.
  - cbn [closed].
    apply index_lt in Hindex.
    lia.
  - now apply lift_type_by_closed, Hvaluation.
Qed.

Lemma index_list_id_none_of_not_member : forall variable variables,
  in_list_id variable variables = false ->
  index_list_id variable variables = None.
Proof.
  intros variable variables.
  unfold index_list_id.
  generalize 0 as offset.
  induction variables as [| head variables IH]; intros offset Hmember.
  - reflexivity.
  - cbn [in_list_id index_list_id_aux] in Hmember |- *.
    destruct (eq_id_dec head variable); [discriminate |].
    now apply IH.
Qed.

Lemma denote_scheme_body_generalized : forall
    constants valuation sigma quantifier_count generalized,
  constants_closed constants ->
  generalized_variables_scoped quantifier_count sigma ->
  are_disjoints (FV_schm sigma) generalized ->
  denote_scheme_body constants
    (generalized_valuation generalized valuation)
    quantifier_count sigma =
  rename_type
    (shift_type_variables quantifier_count (length generalized))
    (denote_scheme_body constants valuation quantifier_count sigma).
Proof.
  intros constants valuation sigma.
  induction sigma as
      [variable | name | variable | domain IHdomain codomain IHcodomain];
    intros quantifier_count generalized Hconstants Hscope Hdisjoint;
    cbn [generalized_variables_scoped FV_schm denote_scheme_body] in *.
  - unfold generalized_valuation.
    assert (Hmember : in_list_id variable generalized = false).
    { apply Hdisjoint.
      cbn [in_list_id].
      destruct (eq_id_dec variable variable); [reflexivity | contradiction]. }
    rewrite (index_list_id_none_of_not_member variable generalized Hmember).
    unfold lift_type_by.
    rewrite !rename_type_compose.
    apply rename_type_ext.
    intro index.
    unfold shift_type_variables.
    assert (Habove : quantifier_count + index <? quantifier_count = false).
    { apply Nat.ltb_ge. lia. }
    rewrite Habove.
    lia.
  - symmetry.
    apply rename_type_closed with (n := 0).
    + apply Hconstants.
    + intros index Hindex. lia.
  - cbn [rename_type].
    f_equal.
    unfold shift_type_variables.
    assert (Hbelow : quantifier_count - S variable <? quantifier_count = true).
    { apply Nat.ltb_lt. lia. }
    now rewrite Hbelow.
  - destruct Hscope as [Hscope_domain Hscope_codomain].
    assert (Hdisjoint_domain : are_disjoints (FV_schm domain) generalized).
    { unfold are_disjoints in *.
      intros variable Hmember.
      apply Hdisjoint.
      now apply in_list_id_append1. }
    assert (Hdisjoint_codomain : are_disjoints (FV_schm codomain) generalized).
    { unfold are_disjoints in *.
      intros variable Hmember.
      apply Hdisjoint.
      now apply in_list_id_append2. }
    now rewrite
      (IHdomain quantifier_count generalized Hconstants
        Hscope_domain Hdisjoint_domain),
      (IHcodomain quantifier_count generalized Hconstants
        Hscope_codomain Hdisjoint_codomain).
Qed.

Lemma denote_scheme_generalized : forall
    constants valuation sigma generalized,
  constants_closed constants ->
  are_disjoints (FV_schm sigma) generalized ->
  denote_scheme constants
    (generalized_valuation generalized valuation) sigma =
  lift_type_by (length generalized)
    (denote_scheme constants valuation sigma).
Proof.
  intros constants valuation sigma generalized Hconstants Hdisjoint.
  unfold denote_scheme.
  rewrite lift_type_by_quantify.
  f_equal.
  apply denote_scheme_body_generalized.
  - exact Hconstants.
  - apply generalized_variables_scoped_max.
  - exact Hdisjoint.
Qed.

Fixpoint denote_context
    (constants : ConstantInterpretation)
    (valuation : TypeValuation)
    (environment : ctx) : list type :=
  match environment with
  | [] => []
  | (_, sigma) :: environment' =>
      denote_scheme constants valuation sigma ::
      denote_context constants valuation environment'
  end.

Lemma denote_context_names : forall constants valuation environment,
  length (denote_context constants valuation environment) =
  length environment.
Proof.
  intros constants valuation environment.
  induction environment as [| [variable sigma] environment IH].
  - reflexivity.
  - cbn [denote_context].
    cbn [length].
    now f_equal.
Qed.

Lemma denote_context_scoped : forall
    constants valuation environment depth,
  constants_closed constants ->
  valuation_scoped depth valuation ->
  Forall (closed depth) (denote_context constants valuation environment).
Proof.
  intros constants valuation environment.
  induction environment as [| [variable sigma] environment IH];
    intros depth Hconstants Hvaluation.
  - constructor.
  - cbn [denote_context].
    constructor.
    + now apply denote_scheme_scoped.
    + now apply IH.
Qed.

Lemma denote_context_valuation_ext : forall
    constants valuation valuation' environment,
  (forall variable, valuation variable = valuation' variable) ->
  denote_context constants valuation environment =
  denote_context constants valuation' environment.
Proof.
  intros constants valuation valuation' environment Hequal.
  induction environment as [| [variable sigma] environment IH].
  - reflexivity.
  - cbn [denote_context].
    now rewrite (denote_scheme_valuation_ext
      constants valuation valuation' sigma Hequal), IH.
Qed.

Lemma denote_context_after_substitution : forall
    constants substitution valuation environment,
  constants_closed constants ->
  denote_context constants
    (valuation_after_substitution constants substitution valuation)
    environment =
  denote_context constants valuation
    (apply_subst_ctx substitution environment).
Proof.
  intros constants substitution valuation environment Hconstants.
  induction environment as [| [variable sigma] environment IH].
  - reflexivity.
  - cbn [denote_context apply_subst_ctx].
    rewrite denote_scheme_after_substitution by exact Hconstants.
    now rewrite IH.
Qed.

Lemma are_disjoints_append_left : forall left right other,
  are_disjoints (left ++ right) other ->
  are_disjoints left other /\ are_disjoints right other.
Proof.
  intros left right other Hdisjoint.
  split; unfold are_disjoints in *; intros variable Hmember;
    apply Hdisjoint.
  - now apply in_list_id_append1.
  - now apply in_list_id_append2.
Qed.

Lemma denote_context_generalized : forall
    constants valuation environment generalized,
  constants_closed constants ->
  are_disjoints (FV_ctx environment) generalized ->
  denote_context constants
    (generalized_valuation generalized valuation) environment =
  lift_type_context_by (length generalized)
    (denote_context constants valuation environment).
Proof.
  intros constants valuation environment.
  induction environment as [| [variable sigma] environment IH];
    intros generalized Hconstants Hdisjoint.
  - reflexivity.
  - change
      (are_disjoints (FV_schm sigma ++ FV_ctx environment) generalized)
      in Hdisjoint.
    destruct (are_disjoints_append_left
      (FV_schm sigma) (FV_ctx environment) generalized Hdisjoint)
      as [Hsigma Henvironment].
    cbn [denote_context lift_type_context_by map].
    rewrite (denote_scheme_generalized
      constants valuation sigma generalized Hconstants Hsigma).
    now rewrite (IH generalized Hconstants Henvironment).
Qed.

(** [gen_ty_aux] records generalized variables in first-occurrence order.
    Interpreting that final list as de Bruijn binders gives exactly the
    generated scheme body, including when a later traversal appends more
    binders. *)
Lemma gen_ty_aux_denotation : forall
    tau environment initial sigma generated,
  gen_ty_aux tau environment initial = (sigma, generated) ->
  are_disjoints (FV_ctx environment) initial ->
  forall suffix constants valuation,
    are_disjoints (FV_ctx environment) (generated ++ suffix) ->
    denote_monotype constants
      (generalized_valuation (generated ++ suffix) valuation) tau =
    denote_scheme_body constants valuation
      (length (generated ++ suffix)) sigma.
Proof.
  induction tau as
      [variable | name | domain IHdomain codomain IHcodomain];
    intros environment initial sigma generated
      Hgeneration Hinitial suffix constants valuation Hfinal;
    cbn [gen_ty_aux] in Hgeneration.
  - destruct (in_list_id variable (FV_ctx environment))
      eqn:Hfree.
    + inversion Hgeneration; subst sigma generated.
      cbn [denote_monotype denote_scheme_body].
      unfold generalized_valuation.
      assert (Hmember :
        in_list_id variable (initial ++ suffix) = false).
      { now apply Hfinal. }
      rewrite (index_list_id_none_of_not_member
        variable (initial ++ suffix) Hmember).
      reflexivity.
    + destruct (index_list_id variable initial)
        as [index |] eqn:Hindex.
      * inversion Hgeneration; subst sigma generated.
        cbn [denote_monotype denote_scheme_body].
        unfold generalized_valuation.
        rewrite (index_list_id_app initial suffix variable Hindex).
        reflexivity.
      * inversion Hgeneration; subst sigma generated.
        cbn [denote_monotype denote_scheme_body].
        unfold generalized_valuation.
        rewrite (index_list_id_app
          (initial ++ [variable]) suffix
          (n := length initial) variable).
        -- rewrite length_app.
           cbn [length].
           reflexivity.
        -- now apply index_list_id_cons.
  - inversion Hgeneration; subst sigma generated.
    reflexivity.
  - destruct (gen_ty_aux domain environment initial)
      as [domain_scheme domain_generated] eqn:Hdomain.
    destruct (gen_ty_aux codomain environment domain_generated)
      as [codomain_scheme codomain_generated] eqn:Hcodomain.
    inversion Hgeneration; subst sigma generated.
    cbn [denote_monotype denote_scheme_body].
    destruct (exists_snd_gen_aux_app
      environment codomain domain_generated)
      as [extra [Hextra Hextra_disjoint]].
    rewrite Hcodomain in Hextra.
    cbn [snd] in Hextra.
    subst codomain_generated.
    rewrite <- app_assoc in Hfinal |- *.
    f_equal.
    + apply (IHdomain environment initial domain_scheme
        domain_generated Hdomain Hinitial (extra ++ suffix)
        constants valuation).
      exact Hfinal.
    + rewrite app_assoc in Hfinal |- *.
      apply (IHcodomain environment domain_generated codomain_scheme
        (domain_generated ++ extra) Hcodomain).
      * pose proof
          (disjoint_snd_gen_aux environment initial domain Hinitial)
          as Hdomain_disjoint.
        rewrite Hdomain in Hdomain_disjoint.
        exact Hdomain_disjoint.
      * exact Hfinal.
Qed.

Lemma generalize_for_elaboration_denotation : forall
    tau environment sigma generalized constants valuation,
  generalize_for_elaboration tau environment = (sigma, generalized) ->
  denote_monotype constants
    (generalized_valuation generalized valuation) tau =
  denote_scheme_body constants valuation (length generalized) sigma.
Proof.
  intros tau environment sigma generalized constants valuation Hgeneralization.
  unfold generalize_for_elaboration in Hgeneralization.
  assert (Hgenerated : are_disjoints (FV_ctx environment) generalized).
  { pose proof
      (disjoint_snd_gen_aux environment [] tau (disjoints_nill1 _))
      as Hdisjoint.
    rewrite Hgeneralization in Hdisjoint.
    exact Hdisjoint. }
  pose proof
    (gen_ty_aux_denotation tau environment [] sigma generalized
      Hgeneralization (disjoints_nill1 _) [] constants valuation)
    as Hdenotation.
  rewrite !app_nil_r in Hdenotation.
  now apply Hdenotation.
Qed.

Lemma generalize_for_elaboration_disjoint : forall
    tau environment sigma generalized,
  generalize_for_elaboration tau environment = (sigma, generalized) ->
  are_disjoints (FV_ctx environment) generalized.
Proof.
  intros tau environment sigma generalized Hgeneralization.
  unfold generalize_for_elaboration in Hgeneralization.
  pose proof
    (disjoint_snd_gen_aux environment [] tau (disjoints_nill1 _))
    as Hdisjoint.
  rewrite Hgeneralization in Hdisjoint.
  exact Hdisjoint.
Qed.

Lemma generalize_for_elaboration_length : forall
    tau environment sigma generalized,
  generalize_for_elaboration tau environment = (sigma, generalized) ->
  length generalized = max_gen_vars sigma.
Proof.
  intros tau environment sigma generalized Hgeneralization.
  unfold generalize_for_elaboration in Hgeneralization.
  pose proof (length_snd_gen_aux environment tau []) as Hlength.
  rewrite Hgeneralization in Hlength.
  cbn [fst snd length Nat.max] in Hlength.
  exact Hlength.
Qed.

Lemma lookup_binder_denote_context : forall
    constants valuation environment variable sigma,
  in_ctx variable environment = Some sigma ->
  exists index,
    lookup_binder variable (map fst environment) = Some index /\
    nth_error (denote_context constants valuation environment) index =
      Some (denote_scheme constants valuation sigma).
Proof.
  intros constants valuation environment.
  induction environment as [| [name annotation] environment IH];
    intros variable sigma Hlookup; cbn [in_ctx] in Hlookup.
  - discriminate.
  - destruct (eq_id_dec name variable) as [Hequal | Hdifferent].
    + inversion Hlookup; subst annotation variable.
      exists 0.
      cbn [map lookup_binder denote_context nth_error fst].
      destruct (eq_id_dec name name); [now split | contradiction].
    + destruct (IH variable sigma Hlookup)
        as [index [Hbinder Htype]].
      exists (S index).
      cbn [map lookup_binder denote_context nth_error fst].
      destruct (eq_id_dec name variable); [contradiction |].
      rewrite Hbinder.
      now split.
Qed.

Lemma lookup_binder_denote_context_sig : forall
    constants valuation environment variable sigma,
  in_ctx variable environment = Some sigma ->
  { index : nat |
    lookup_binder variable (map fst environment) = Some index /\
    nth_error (denote_context constants valuation environment) index =
      Some (denote_scheme constants valuation sigma) }.
Proof.
  intros constants valuation environment.
  induction environment as [| [name annotation] environment IH];
    intros variable sigma Hlookup; cbn [in_ctx] in Hlookup.
  - discriminate.
  - destruct (eq_id_dec name variable) as [Hequal | Hdifferent].
    + inversion Hlookup; subst annotation variable.
      exists 0.
      cbn [map lookup_binder denote_context nth_error fst].
      destruct (eq_id_dec name name); [now split | contradiction].
    + destruct (IH variable sigma Hlookup)
        as [index [Hbinder Htype]].
      exists (S index).
      cbn [map lookup_binder denote_context nth_error fst].
      destruct (eq_id_dec name variable); [contradiction |].
      rewrite Hbinder.
      now split.
Qed.

Fixpoint denote_instantiation
    (constants : ConstantInterpretation)
    (valuation : TypeValuation)
    (instantiation : inst_subst) : list type :=
  match instantiation with
  | [] => []
  | argument :: instantiation' =>
      denote_monotype constants valuation argument ::
      denote_instantiation constants valuation instantiation'
  end.

Lemma denote_instantiation_is_map : forall constants valuation instantiation,
  denote_instantiation constants valuation instantiation =
  map (denote_monotype constants valuation) instantiation.
Proof.
  intros constants valuation instantiation.
  induction instantiation as [| argument instantiation IH].
  - reflexivity.
  - cbn [denote_instantiation map]. now rewrite IH.
Qed.

Lemma denote_context_after_compose : forall
    constants first second valuation environment,
  denote_context constants
    (valuation_after_substitution constants (compose_subst first second)
      valuation) environment =
  denote_context constants
    (valuation_after_substitution constants first
      (valuation_after_substitution constants second valuation))
    environment.
Proof.
  intros constants first second valuation environment.
  apply denote_context_valuation_ext.
  intro variable.
  apply valuation_after_compose.
Qed.
