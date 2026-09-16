(** * Checked System F normalization pipeline

    This module is the executable join point of the Church checker, Blot's
    repaired bar-recursive bound, and the independent weak-head reducer.
    [NormalizationResult] retains the checked intrinsic term; its erasure is
    computed from that same field and is the sole reducer input.  The strict
    path obtains fuel from [bound].  The exact-first path uses a successful
    capped evaluation as an exact bound and falls back to the strict path.

    The numerical adequacy of [bound] remains relative to the extracted
    [brec] implementation.  The theorems here establish the structural
    contracts of the pipeline: checker acceptance, identity of erasures, and
    use of the proposed bound as reducer fuel. *)

From Stdlib Require Import List.
Import ListNotations.

From SystemF.F Require Import Syntax Check OperationalSemantics.
From SystemF.BarRec Require Import Bound.
From SystemF.HM Require Import Erasure.
From SystemF.HM.W Require Import Typing.
From SystemF Require Import HMElab.

Inductive NormalizationBoundSource : Type :=
| exact_evaluation_bound
| bar_recursive_bound.

Record NormalizationResult : Type := {
  normalization_type : type;
  normalization_intrinsic : fderiv [] normalization_type;
  normalization_bound_source : NormalizationBoundSource;
  normalization_bound : nat;
  normalization_result : term
}.

Definition normalization_erasure
    (normalization : NormalizationResult) : term :=
  fderiv_to_term (normalization_intrinsic normalization).

Definition normalize_intrinsic {T : type}
    (intrinsic : fderiv [] T) : NormalizationResult :=
  let erased := fderiv_to_term intrinsic in
  let proposed_bound := bound T intrinsic in
  {| normalization_type := T;
     normalization_intrinsic := intrinsic;
     normalization_bound_source := bar_recursive_bound;
     normalization_bound := proposed_bound;
     normalization_result := run_fuel proposed_bound erased |}.

Lemma normalize_intrinsic_type : forall T (intrinsic : fderiv [] T),
  normalization_type (normalize_intrinsic intrinsic) = T.
Proof. reflexivity. Qed.

Lemma normalize_intrinsic_erasure : forall T (intrinsic : fderiv [] T),
  normalization_erasure (normalize_intrinsic intrinsic) =
  fderiv_to_term intrinsic.
Proof. reflexivity. Qed.

Lemma normalize_intrinsic_bound : forall T (intrinsic : fderiv [] T),
  normalization_bound (normalize_intrinsic intrinsic) = bound T intrinsic.
Proof. reflexivity. Qed.

Lemma normalize_intrinsic_bound_source : forall T (intrinsic : fderiv [] T),
  normalization_bound_source (normalize_intrinsic intrinsic) =
  bar_recursive_bound.
Proof. reflexivity. Qed.

Lemma normalize_intrinsic_result : forall T (intrinsic : fderiv [] T),
  normalization_result (normalize_intrinsic intrinsic) =
  run_fuel (bound T intrinsic) (fderiv_to_term intrinsic).
Proof. reflexivity. Qed.

(** Try a small exact evaluation before invoking BBC.  Success gives the
    strongest possible bound (the exact number of steps); failure means only
    that [cap] was insufficient, so the total bar-recursive path remains the
    fallback. *)
Definition normalize_intrinsic_with_cap {T : type}
    (cap : nat) (intrinsic : fderiv [] T) : NormalizationResult :=
  let erased := fderiv_to_term intrinsic in
  match eval_cap cap erased with
  | Some (steps, normal_form) =>
      {| normalization_type := T;
         normalization_intrinsic := intrinsic;
         normalization_bound_source := exact_evaluation_bound;
         normalization_bound := steps;
         normalization_result := normal_form |}
  | None => normalize_intrinsic intrinsic
  end.

Lemma normalize_intrinsic_with_cap_erasure : forall
    cap T (intrinsic : fderiv [] T),
  normalization_erasure (normalize_intrinsic_with_cap cap intrinsic) =
  fderiv_to_term intrinsic.
Proof.
  intros cap T intrinsic.
  unfold normalize_intrinsic_with_cap.
  destruct (eval_cap cap (fderiv_to_term intrinsic))
    as [[steps normal_form] |]; reflexivity.
Qed.

Lemma normalize_intrinsic_with_cap_result : forall
    cap T (intrinsic : fderiv [] T),
  normalization_result (normalize_intrinsic_with_cap cap intrinsic) =
  run_fuel
    (normalization_bound (normalize_intrinsic_with_cap cap intrinsic))
    (normalization_erasure (normalize_intrinsic_with_cap cap intrinsic)).
Proof.
  intros cap T intrinsic.
  unfold normalize_intrinsic_with_cap.
  destruct (eval_cap cap (fderiv_to_term intrinsic))
    as [[steps normal_form] |] eqn:Heval; simpl.
  - symmetry.
    now apply eval_cap_run_fuel with (fuel := cap).
  - apply normalize_intrinsic_result.
Qed.

Lemma normalize_intrinsic_with_cap_exact : forall
    cap T (intrinsic : fderiv [] T) steps normal_form,
  eval_cap cap (fderiv_to_term intrinsic) = Some (steps, normal_form) ->
  normalization_bound_source (normalize_intrinsic_with_cap cap intrinsic) =
    exact_evaluation_bound /\
  normalization_bound (normalize_intrinsic_with_cap cap intrinsic) = steps /\
  normalization_result (normalize_intrinsic_with_cap cap intrinsic) =
    normal_form.
Proof.
  intros cap T intrinsic steps normal_form Heval.
  unfold normalize_intrinsic_with_cap.
  now rewrite Heval.
Qed.

Definition normalize_checked {raw : fterm}
    (checked : Checked 0 [] raw) : NormalizationResult :=
  match checked with
  | existT _ _ (exist _ intrinsic _) => normalize_intrinsic intrinsic
  end.

Definition normalize_checked_with_cap {raw : fterm}
    (cap : nat) (checked : Checked 0 [] raw) : NormalizationResult :=
  match checked with
  | existT _ _ (exist _ intrinsic _) =>
      normalize_intrinsic_with_cap cap intrinsic
  end.

Lemma normalize_checked_result : forall raw (checked : Checked 0 [] raw),
  normalization_result (normalize_checked checked) =
  run_fuel
    (normalization_bound (normalize_checked checked))
    (normalization_erasure (normalize_checked checked)).
Proof.
  intros raw [T [intrinsic certificate]].
  reflexivity.
Qed.

Lemma normalize_checked_with_cap_result : forall
    cap raw (checked : Checked 0 [] raw),
  normalization_result (normalize_checked_with_cap cap checked) =
  run_fuel
    (normalization_bound (normalize_checked_with_cap cap checked))
    (normalization_erasure (normalize_checked_with_cap cap checked)).
Proof.
  intros cap raw [T [intrinsic certificate]].
  apply normalize_intrinsic_with_cap_result.
Qed.

Definition normalizeClosed
    (raw : fterm) : Result TypeError NormalizationResult :=
  match checkClosed raw with
  | Ok checked => Ok (normalize_checked checked)
  | Err error => Err error
  end.

Definition normalizeClosedWithCap
    (cap : nat) (raw : fterm) : Result TypeError NormalizationResult :=
  match checkClosed raw with
  | Ok checked => Ok (normalize_checked_with_cap cap checked)
  | Err error => Err error
  end.

Theorem normalizeClosed_result : forall raw normalization,
  normalizeClosed raw = Ok normalization ->
  normalization_result normalization =
  run_fuel
    (normalization_bound normalization)
    (normalization_erasure normalization).
Proof.
  intros raw normalization Hnormalization.
  unfold normalizeClosed in Hnormalization.
  destruct (checkClosed raw) as [checked | error] eqn:Hchecked;
    try discriminate.
  inversion Hnormalization; subst normalization.
  apply normalize_checked_result.
Qed.

Theorem normalizeClosedWithCap_result : forall cap raw normalization,
  normalizeClosedWithCap cap raw = Ok normalization ->
  normalization_result normalization =
  run_fuel
    (normalization_bound normalization)
    (normalization_erasure normalization).
Proof.
  intros cap raw normalization Hnormalization.
  unfold normalizeClosedWithCap in Hnormalization.
  destruct (checkClosed raw) as [checked | error] eqn:Hchecked;
    try discriminate.
  inversion Hnormalization; subst normalization.
  apply normalize_checked_with_cap_result.
Qed.

Definition normalize_checked_church
    (checked : CheckedChurchElaboration) : NormalizationResult :=
  normalize_checked (checked_church_certificate checked).

Definition normalize_checked_church_with_cap
    (cap : nat) (checked : CheckedChurchElaboration)
    : NormalizationResult :=
  normalize_checked_with_cap cap (checked_church_certificate checked).

Definition runWBarNormalization
    (constants : ConstantInterpretation)
    (expression : hmterm)
    : Result WChurchError NormalizationResult :=
  match runWChurchChecked constants expression with
  | Ok checked => Ok (normalize_checked_church checked)
  | Err error => Err error
  end.

Definition runWNormalizationWithCap
    (cap : nat)
    (constants : ConstantInterpretation)
    (expression : hmterm)
    : Result WChurchError NormalizationResult :=
  match runWChurchChecked constants expression with
  | Ok checked => Ok (normalize_checked_church_with_cap cap checked)
  | Err error => Err error
  end.

Definition default_normalization_cap : nat := 32.

(** The lecture frontend uses a cheap exact path for small programs and keeps
    [runWBarNormalization] available when the bar-recursive computation
    itself is the object of the experiment. *)
Definition runWNormalization :
    ConstantInterpretation -> hmterm ->
    Result WChurchError NormalizationResult :=
  runWNormalizationWithCap default_normalization_cap.

Lemma normalize_checked_church_type : forall checked,
  normalization_type (normalize_checked_church checked) =
  church_systemf_type (checked_church_elaboration checked).
Proof.
  intros [elaboration [T [intrinsic certificate]] Htype].
  exact Htype.
Qed.

Lemma normalize_checked_church_erasure : forall checked,
  normalization_erasure (normalize_checked_church checked) =
  checked_church_erasure checked.
Proof.
  intros [elaboration [T [intrinsic certificate]] Htype].
  reflexivity.
Qed.

Lemma normalize_checked_church_with_cap_erasure : forall cap checked,
  normalization_erasure (normalize_checked_church_with_cap cap checked) =
  checked_church_erasure checked.
Proof.
  intros cap [elaboration [T [intrinsic certificate]] Htype].
  apply normalize_intrinsic_with_cap_erasure.
Qed.

Lemma normalize_checked_church_erases_raw : forall checked,
  normalization_erasure (normalize_checked_church checked) =
  fterm_to_term
    (church_term (checked_church_elaboration checked)).
Proof.
  intro checked.
  rewrite normalize_checked_church_erasure.
  symmetry.
  apply checked_church_erasure_is_raw.
Qed.

Lemma normalize_checked_church_result : forall checked,
  normalization_result (normalize_checked_church checked) =
  run_fuel
    (normalization_bound (normalize_checked_church checked))
    (normalization_erasure (normalize_checked_church checked)).
Proof.
  intros [elaboration [T [intrinsic certificate]] Htype].
  reflexivity.
Qed.

Lemma normalize_checked_church_with_cap_result : forall cap checked,
  normalization_result (normalize_checked_church_with_cap cap checked) =
  run_fuel
    (normalization_bound (normalize_checked_church_with_cap cap checked))
    (normalization_erasure
      (normalize_checked_church_with_cap cap checked)).
Proof.
  intros cap [elaboration [T [intrinsic certificate]] Htype].
  apply normalize_intrinsic_with_cap_result.
Qed.

Theorem runWChurchChecked_normalization_erasure : forall
    constants expression checked,
  runWChurchChecked constants expression = Ok checked ->
  erase_hm_closed expression =
  Some (normalization_erasure (normalize_checked_church checked)).
Proof.
  intros constants expression checked Hchecked.
  rewrite normalize_checked_church_erasure.
  now apply runWChurchChecked_preserves_erasure
    with (constants := constants).
Qed.

Theorem runWNormalization_preserves_erasure : forall
    constants expression normalization,
  runWNormalization constants expression = Ok normalization ->
  erase_hm_closed expression = Some (normalization_erasure normalization).
Proof.
  intros constants expression normalization Hnormalization.
  unfold runWNormalization, runWNormalizationWithCap in Hnormalization.
  destruct (runWChurchChecked constants expression)
    as [checked | error] eqn:Hchecked; try discriminate.
  inversion Hnormalization; subst normalization.
  rewrite normalize_checked_church_with_cap_erasure.
  now apply runWChurchChecked_preserves_erasure
    with (constants := constants).
Qed.

Theorem runWNormalizationWithCap_preserves_erasure : forall
    cap constants expression normalization,
  runWNormalizationWithCap cap constants expression = Ok normalization ->
  erase_hm_closed expression = Some (normalization_erasure normalization).
Proof.
  intros cap constants expression normalization Hnormalization.
  unfold runWNormalizationWithCap in Hnormalization.
  destruct (runWChurchChecked constants expression)
    as [checked | error] eqn:Hchecked; try discriminate.
  inversion Hnormalization; subst normalization.
  rewrite normalize_checked_church_with_cap_erasure.
  now apply runWChurchChecked_preserves_erasure
    with (constants := constants).
Qed.

Theorem runWNormalization_result : forall
    constants expression normalization,
  runWNormalization constants expression = Ok normalization ->
  normalization_result normalization =
  run_fuel
    (normalization_bound normalization)
    (normalization_erasure normalization).
Proof.
  intros constants expression normalization Hnormalization.
  unfold runWNormalization, runWNormalizationWithCap in Hnormalization.
  destruct (runWChurchChecked constants expression)
    as [checked | error] eqn:Hchecked; try discriminate.
  inversion Hnormalization; subst normalization.
  apply normalize_checked_church_with_cap_result.
Qed.

Theorem runWNormalizationWithCap_result : forall
    cap constants expression normalization,
  runWNormalizationWithCap cap constants expression = Ok normalization ->
  normalization_result normalization =
  run_fuel
    (normalization_bound normalization)
    (normalization_erasure normalization).
Proof.
  intros cap constants expression normalization Hnormalization.
  unfold runWNormalizationWithCap in Hnormalization.
  destruct (runWChurchChecked constants expression)
    as [checked | error] eqn:Hchecked; try discriminate.
  inversion Hnormalization; subst normalization.
  apply normalize_checked_church_with_cap_result.
Qed.

Theorem runWBarNormalization_preserves_erasure : forall
    constants expression normalization,
  runWBarNormalization constants expression = Ok normalization ->
  erase_hm_closed expression = Some (normalization_erasure normalization).
Proof.
  intros constants expression normalization Hnormalization.
  unfold runWBarNormalization in Hnormalization.
  destruct (runWChurchChecked constants expression)
    as [checked | error] eqn:Hchecked; try discriminate.
  inversion Hnormalization; subst normalization.
  now apply runWChurchChecked_normalization_erasure
    with (constants := constants).
Qed.

Theorem runWBarNormalization_result : forall
    constants expression normalization,
  runWBarNormalization constants expression = Ok normalization ->
  normalization_result normalization =
  run_fuel
    (normalization_bound normalization)
    (normalization_erasure normalization).
Proof.
  intros constants expression normalization Hnormalization.
  unfold runWBarNormalization in Hnormalization.
  destruct (runWChurchChecked constants expression)
    as [checked | error] eqn:Hchecked; try discriminate.
  inversion Hnormalization; subst normalization.
  apply normalize_checked_church_result.
Qed.
