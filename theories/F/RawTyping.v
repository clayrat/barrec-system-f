(** * Extrinsic typing for raw Church terms

    [RawTyping] is a Type-valued, syntax-directed presentation of System F
    typing for [RawChurch].  It is independent of Algorithm W.  The central
    completeness theorem [raw_typing_check] turns any such derivation into
    the intrinsic certificate returned by the executable checker. *)

From Stdlib Require Import List Lia.
Import ListNotations.

From SystemF.F Require Import Syntax Scope TypeSubstitution Check.

(** ** Extrinsic Church typing and checker completeness *)

Inductive RawTyping :
    nat -> list type -> RawChurch -> type -> Type :=
| RawTypingVar : forall depth context index T,
    nth_error context index = Some T ->
    RawTyping depth context (RCVar index) T
| RawTypingAbs : forall depth context A body B,
    closed depth A ->
    RawTyping depth (A :: context) body B ->
    RawTyping depth context (RCAbs A body) (TArrow A B)
| RawTypingApp : forall depth context function argument A B,
    RawTyping depth context function (TArrow A B) ->
    RawTyping depth context argument A ->
    RawTyping depth context (RCApp function argument) B
| RawTypingTAbs : forall depth context body T,
    RawTyping (S depth) (map (type_lift 0) context) body T ->
    RawTyping depth context (RCTAbs body) (TForall T)
| RawTypingTApp : forall depth context function body argument,
    closed depth argument ->
    RawTyping depth context function (TForall body) ->
    RawTyping depth context (RCTApp function argument)
      (type_subst 0 body argument).

Lemma nth_error_fvar : forall context index T,
  nth_error context index = Some T ->
  { variable : fvar context T |
      fvar_to_nat variable = index }.
Proof.
  induction context as [| A context IH]; intros [| index] T Hlookup;
    cbn [nth_error] in Hlookup.
  - discriminate.
  - discriminate.
  - inversion Hlookup; subst T.
    exists (@FVar0 context A).
    reflexivity.
  - destruct (IH index T Hlookup) as [variable Hvariable].
    exists (@FVarS context T A variable).
    cbn [fvar_to_nat].
    now rewrite Hvariable.
Qed.

Lemma raw_typing_intrinsic : forall depth context raw T,
  RawTyping depth context raw T ->
  { intrinsic : fterm context T | forget intrinsic = raw }.
Proof.
  intros depth context raw T Htyping.
  induction Htyping as
      [depth context index T Hlookup
      | depth context A body B HA Hbody IHbody
      | depth context function argument A B
          Hfunction IHfunction Hargument IHargument
      | depth context body T Hbody IHbody
      | depth context function body argument
          Hargument Hfunction IHfunction].
  - destruct (nth_error_fvar context index T Hlookup)
      as [variable Hvariable].
    exists (FVar variable).
    cbn [forget].
    now rewrite Hvariable.
  - destruct IHbody as [body' Hbody'].
    exists (FAbs body').
    cbn [forget].
    now rewrite Hbody'.
  - destruct IHfunction as [function' Hfunction'].
    destruct IHargument as [argument' Hargument'].
    exists (FApp function' argument').
    cbn [forget].
    now rewrite Hfunction', Hargument'.
  - destruct IHbody as [body' Hbody'].
    exists (FTAbs body').
    cbn [forget].
    now rewrite Hbody'.
  - destruct IHfunction as [function' Hfunction'].
    exists (FTApp function' argument).
    cbn [forget].
    now rewrite Hfunction'.
Qed.

Lemma raw_typing_scope_and_type : forall depth context raw T,
  RawTyping depth context raw T ->
  Forall (closed depth) context ->
  closed depth T /\ scoped depth raw.
Proof.
  intros depth context raw T Htyping.
  induction Htyping as
      [depth context index T Hlookup
      | depth context A body B HA Hbody IHbody
      | depth context function argument A B
          Hfunction IHfunction Hargument IHargument
      | depth context body T Hbody IHbody
      | depth context function body argument
          Hargument Hfunction IHfunction];
    intro Hcontext.
  - split.
    + exact
        (closed_nth_error depth context index T Hcontext Hlookup).
    + exact I.
  - destruct (IHbody (Forall_cons A HA Hcontext))
      as [HB Hbody_scope].
    split.
    + cbn [closed]. now split.
    + cbn [scoped]. now split.
  - destruct (IHfunction Hcontext) as [Harrow Hfunction_scope].
    destruct (IHargument Hcontext) as [HA Hargument_scope].
    cbn [closed] in Harrow.
    destruct Harrow as [_ HB].
    split.
    + exact HB.
    + cbn [scoped]. now split.
  - destruct
      (IHbody (closed_context_lift depth context Hcontext))
      as [HT Hbody_scope].
    split.
    + exact HT.
    + exact Hbody_scope.
  - destruct (IHfunction Hcontext) as [Hforall Hfunction_scope].
    cbn [closed] in Hforall.
    split.
    + now apply closed_type_subst0.
    + cbn [scoped]. now split.
Qed.

Theorem raw_typing_check : forall
    depth context (Hcontext : Forall (closed depth) context) raw T,
  RawTyping depth context raw T ->
  exists checked : Checked depth context raw,
    check depth context Hcontext raw = Ok checked /\
    projT1 checked = T.
Proof.
  intros depth context Hcontext raw T Htyping.
  destruct (raw_typing_intrinsic depth context raw T Htyping)
    as [intrinsic Hforget].
  destruct (raw_typing_scope_and_type
      depth context raw T Htyping Hcontext)
    as [_ Hscoped].
  destruct (check_complete depth context Hcontext raw T intrinsic
      Hscoped Hforget) as [checked Hcheck].
  exists checked.
  split; [exact Hcheck |].
  destruct checked as [U [intrinsic' [HU [Hscoped' Hforget']]]].
  cbn.
  eapply church_typing_unique
    with (n := depth) (context := context)
      (t := intrinsic') (t' := intrinsic).
  - now rewrite Hforget'.
  - now rewrite Hforget', Hforget.
Qed.

Corollary raw_typing_checkClosed : forall raw T,
  RawTyping 0 [] raw T ->
  exists checked : Checked 0 [] raw,
    checkClosed raw = Ok checked /\
    projT1 checked = T.
Proof.
  intros raw T Htyping.
  unfold checkClosed.
  now apply raw_typing_check.
Qed.

Definition lift_type_context_by
    (count : nat) (context : list type) : list type :=
  map (lift_type_by count) context.

Lemma lift_type_context_by_zero : forall context,
  lift_type_context_by 0 context = context.
Proof.
  induction context as [| T context IH].
  - reflexivity.
  - unfold lift_type_context_by in *.
    cbn [map].
    rewrite lift_type_by_zero.
    now f_equal.
Qed.

Lemma lift_type_context_by_successor : forall count context,
  map (type_lift 0) (lift_type_context_by count context) =
  lift_type_context_by (S count) context.
Proof.
  intros count context.
  unfold lift_type_context_by.
  rewrite map_map.
  apply map_ext.
  intro T.
  now rewrite <- rename_type_successor, <- lift_type_by_successor.
Qed.

Lemma lift_type_context_by_after_lift : forall count context,
  lift_type_context_by count (map (type_lift 0) context) =
  lift_type_context_by (S count) context.
Proof.
  intros count context.
  unfold lift_type_context_by.
  rewrite map_map.
  apply map_ext.
  intro T.
  rewrite <- rename_type_successor.
  unfold lift_type_by.
  rewrite rename_type_compose.
  apply rename_type_ext.
  intro index.
  lia.
Qed.
