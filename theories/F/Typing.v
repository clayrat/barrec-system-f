(** * Extrinsic typing for Church-style [fterm] terms

    [Typing] is a Type-valued, syntax-directed presentation of System F
    typing for [fterm].  It is independent of Algorithm W.  The central
    completeness theorem [typing_check] turns any such derivation into
    the intrinsic certificate returned by the executable checker. *)

From Stdlib Require Import List Lia.
Import ListNotations.

From SystemF.F Require Import Syntax Scope TypeSubstitution Check.

(** ** Extrinsic Church typing and checker completeness *)

Inductive Typing :
    nat -> list type -> fterm -> type -> Type :=
| TypingVar : forall depth ctx index T,
    nth_error ctx index = Some T ->
    Typing depth ctx (FVar index) T
| TypingLam : forall depth ctx A body B,
    closed depth A ->
    Typing depth (A :: ctx) body B ->
    Typing depth ctx (FLam A body) (TArrow A B)
| TypingApp : forall depth ctx function argument A B,
    Typing depth ctx function (TArrow A B) ->
    Typing depth ctx argument A ->
    Typing depth ctx (FApp function argument) B
| TypingTLam : forall depth ctx body T,
    Typing (S depth) (map (type_lift 0) ctx) body T ->
    Typing depth ctx (FTLam body) (TForall T)
| TypingTApp : forall depth ctx function body argument,
    closed depth argument ->
    Typing depth ctx function (TForall body) ->
    Typing depth ctx (FTApp function argument)
      (type_subst 0 body argument).

Lemma nth_error_dvar : forall ctx index T,
  nth_error ctx index = Some T ->
  { variable : dvar ctx T |
      dvar_to_nat variable = index }.
Proof.
  induction ctx as [| A ctx IH]; intros [| index] T Hlookup;
    cbn [nth_error] in Hlookup.
  - discriminate.
  - discriminate.
  - inversion Hlookup; subst T.
    exists (@DVar0 ctx A).
    reflexivity.
  - destruct (IH index T Hlookup) as [variable Hvariable].
    exists (@DVarS ctx T A variable).
    cbn [dvar_to_nat].
    now rewrite Hvariable.
Qed.

Lemma typing_intrinsic : forall depth ctx raw T,
  Typing depth ctx raw T ->
  { intrinsic : fderiv ctx T | forget intrinsic = raw }.
Proof.
  intros depth ctx raw T Htyping.
  induction Htyping as
      [depth ctx index T Hlookup
      | depth ctx A body B HA Hbody IHbody
      | depth ctx function argument A B
          Hfunction IHfunction Hargument IHargument
      | depth ctx body T Hbody IHbody
      | depth ctx function body argument
          Hargument Hfunction IHfunction].
  - destruct (nth_error_dvar ctx index T Hlookup)
      as [variable Hvariable].
    exists (DVar variable).
    cbn [forget].
    now rewrite Hvariable.
  - destruct IHbody as [body' Hbody'].
    exists (DLam body').
    cbn [forget].
    now rewrite Hbody'.
  - destruct IHfunction as [function' Hfunction'].
    destruct IHargument as [argument' Hargument'].
    exists (DApp function' argument').
    cbn [forget].
    now rewrite Hfunction', Hargument'.
  - destruct IHbody as [body' Hbody'].
    exists (DTLam body').
    cbn [forget].
    now rewrite Hbody'.
  - destruct IHfunction as [function' Hfunction'].
    exists (DTApp function' argument).
    cbn [forget].
    now rewrite Hfunction'.
Qed.

Lemma typing_scope_and_type : forall depth ctx raw T,
  Typing depth ctx raw T ->
  Forall (closed depth) ctx ->
  closed depth T /\ scoped depth raw.
Proof.
  intros depth ctx raw T Htyping.
  induction Htyping as
      [depth ctx index T Hlookup
      | depth ctx A body B HA Hbody IHbody
      | depth ctx function argument A B
          Hfunction IHfunction Hargument IHargument
      | depth ctx body T Hbody IHbody
      | depth ctx function body argument
          Hargument Hfunction IHfunction];
    intro Hctx.
  - split.
    + exact
        (closed_nth_error depth ctx index T Hctx Hlookup).
    + exact I.
  - destruct (IHbody (Forall_cons A HA Hctx))
      as [HB Hbody_scope].
    split.
    + cbn [closed]. now split.
    + cbn [scoped]. now split.
  - destruct (IHfunction Hctx) as [Harrow Hfunction_scope].
    destruct (IHargument Hctx) as [HA Hargument_scope].
    cbn [closed] in Harrow.
    destruct Harrow as [_ HB].
    split.
    + exact HB.
    + cbn [scoped]. now split.
  - destruct
      (IHbody (closed_ctx_lift depth ctx Hctx))
      as [HT Hbody_scope].
    split.
    + exact HT.
    + exact Hbody_scope.
  - destruct (IHfunction Hctx) as [Hforall Hfunction_scope].
    cbn [closed] in Hforall.
    split.
    + now apply closed_type_subst0.
    + cbn [scoped]. now split.
Qed.

Theorem typing_check : forall
    depth ctx (Hctx : Forall (closed depth) ctx) raw T,
  Typing depth ctx raw T ->
  exists checked : Checked depth ctx raw,
    check depth ctx Hctx raw = Ok checked /\
    projT1 checked = T.
Proof.
  intros depth ctx Hctx raw T Htyping.
  destruct (typing_intrinsic depth ctx raw T Htyping)
    as [intrinsic Hforget].
  destruct (typing_scope_and_type
      depth ctx raw T Htyping Hctx)
    as [_ Hscoped].
  destruct (check_complete depth ctx Hctx raw T intrinsic
      Hscoped Hforget) as [checked Hcheck].
  exists checked.
  split; [exact Hcheck |].
  destruct checked as [U [intrinsic' [HU [Hscoped' Hforget']]]].
  cbn.
  eapply church_typing_unique
    with (n := depth) (ctx := ctx)
      (t := intrinsic') (t' := intrinsic).
  - now rewrite Hforget'.
  - now rewrite Hforget', Hforget.
Qed.

Corollary typing_checkClosed : forall raw T,
  Typing 0 [] raw T ->
  exists checked : Checked 0 [] raw,
    checkClosed raw = Ok checked /\
    projT1 checked = T.
Proof.
  intros raw T Htyping.
  unfold checkClosed.
  now apply typing_check.
Qed.

Definition lift_type_ctx_by
    (count : nat) (ctx : list type) : list type :=
  map (lift_type_by count) ctx.

Lemma lift_type_ctx_by_zero : forall ctx,
  lift_type_ctx_by 0 ctx = ctx.
Proof.
  induction ctx as [| T ctx IH].
  - reflexivity.
  - unfold lift_type_ctx_by in *.
    cbn [map].
    rewrite lift_type_by_zero.
    now f_equal.
Qed.

Lemma lift_type_ctx_by_successor : forall count ctx,
  map (type_lift 0) (lift_type_ctx_by count ctx) =
  lift_type_ctx_by (S count) ctx.
Proof.
  intros count ctx.
  unfold lift_type_ctx_by.
  rewrite map_map.
  apply map_ext.
  intro T.
  now rewrite <- rename_type_successor, <- lift_type_by_successor.
Qed.

Lemma lift_type_ctx_by_after_lift : forall count ctx,
  lift_type_ctx_by count (map (type_lift 0) ctx) =
  lift_type_ctx_by (S count) ctx.
Proof.
  intros count ctx.
  unfold lift_type_ctx_by.
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
