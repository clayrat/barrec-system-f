(** * Erasure of named Hindley--Milner terms

    Source variables carry numeric names, whereas the common untyped term
    syntax inherited from Blot uses de Bruijn indices.  [erase_hm] resolves a
    name against a nearest-binder-first stack.  It is partial because neither
    an unbound name nor an HM constant has a representation in the pure
    untyped lambda calculus used by the reducer.

    A non-recursive [let x = bound in body] is erased as
    [(lambda x. body) bound].  In particular, [x] is in scope in [body] but
    not in [bound]. *)

From Stdlib Require Import Lia List.
Import ListNotations.

From SystemF.F Require Import Syntax.
From SystemF.HM Require Import ElabScope.
From SystemF.HM.WInCoq Require Import SimpleTypes Typing.

(** Find the nearest binder with the requested source name. *)
Fixpoint lookup_binder
    (variable : id) (binders : list id) : option nat :=
  match binders with
  | [] => None
  | binder :: binders' =>
      if eq_id_dec binder variable
      then Some 0
      else option_map S (lookup_binder variable binders')
  end.

(** Syntactic term-variable scope, kept separate from the constant-free
    restriction.  Constants contain no term variables and are therefore
    scoped, even though [constant_free] excludes them from elaboration. *)
Fixpoint hm_names_scoped
    (binders : list id) (expression : Typing.term) : Prop :=
  match expression with
  | var_t variable => In variable binders
  | app_t function argument =>
      hm_names_scoped binders function /\
      hm_names_scoped binders argument
  | let_t variable bound body =>
      hm_names_scoped binders bound /\
      hm_names_scoped (variable :: binders) body
  | lam_t variable body =>
      hm_names_scoped (variable :: binders) body
  | const_t _ => True
  end.

Definition option_map2 {A B C : Type}
    (function : A -> B -> C) (left : option A) (right : option B)
    : option C :=
  match left, right with
  | Some left', Some right' => Some (function left' right')
  | _, _ => None
  end.

Fixpoint erase_hm
    (binders : list id) (expression : Typing.term)
    : option Syntax.term :=
  match expression with
  | var_t variable =>
      option_map Var (lookup_binder variable binders)
  | app_t function argument =>
      option_map2 App
        (erase_hm binders function)
        (erase_hm binders argument)
  | let_t variable bound body =>
      option_map2 (fun bound' body' => App (Abs body') bound')
        (erase_hm binders bound)
        (erase_hm (variable :: binders) body)
  | lam_t variable body =>
      option_map Abs (erase_hm (variable :: binders) body)
  | const_t _ => None
  end.

Definition erase_hm_closed (expression : Typing.term) : option Syntax.term :=
  erase_hm [] expression.

(** ** Exact domain of the partial erasure *)

Lemma option_map_success : forall (A B : Type) (function : A -> B) value,
  (exists result, option_map function value = Some result) <->
  exists input, value = Some input.
Proof.
  intros A B function [input |]; cbn.
  - split; intro H.
    + now exists input.
    + now exists (function input).
  - split; intros [result H]; discriminate.
Qed.

Lemma option_map2_success : forall (A B C : Type)
    (function : A -> B -> C) left right,
  (exists result, option_map2 function left right = Some result) <->
  (exists left', left = Some left') /\
  (exists right', right = Some right').
Proof.
  intros A B C function [left |] [right |]; cbn.
  - split; intro H.
    + split; [now exists left | now exists right].
    + now exists (function left right).
  - split.
    + intros [result H]. discriminate.
    + intros [_ [right' H]]. discriminate.
  - split.
    + intros [result H]. discriminate.
    + intros [[left' H] _]. discriminate.
  - split.
    + intros [result H]. discriminate.
    + intros [[left' H] _]. discriminate.
Qed.

Lemma lookup_binder_some_iff : forall variable binders,
  (exists index, lookup_binder variable binders = Some index) <->
  In variable binders.
Proof.
  intros variable binders.
  induction binders as [| binder binders IH].
  - cbn [lookup_binder].
    split; [intros [index H]; discriminate | contradiction].
  - cbn [lookup_binder].
    destruct (eq_id_dec binder variable) as [Hequal | Hdifferent].
    + subst binder.
      split.
      * intro H. now left.
      * intro H. now exists 0.
    + rewrite option_map_success, IH.
      cbn [In].
      tauto.
Qed.

Theorem erase_hm_success_iff : forall binders expression,
  (exists erased, erase_hm binders expression = Some erased) <->
  constant_free expression /\ hm_names_scoped binders expression.
Proof.
  intros binders expression.
  revert binders.
  induction expression as
      [variable
      | function IHfunction argument IHargument
      | variable bound IHbound body IHbody
      | variable body IHbody
      | constant];
    intro binders;
    cbn [erase_hm constant_free hm_names_scoped].
  - rewrite option_map_success, lookup_binder_some_iff.
    tauto.
  - rewrite option_map2_success, IHfunction, IHargument.
    tauto.
  - rewrite option_map2_success, IHbound, IHbody.
    tauto.
  - rewrite option_map_success, IHbody.
    tauto.
  - split; [intros [erased H]; discriminate | tauto].
Qed.

Corollary erase_hm_closed_success_iff : forall expression,
  (exists erased, erase_hm_closed expression = Some erased) <->
  constant_free expression /\ hm_names_scoped [] expression.
Proof.
  intro expression.
  apply erase_hm_success_iff.
Qed.

(** For a successful erasure, every produced variable index is relative to
    the current binder stack; [lookup_binder] cannot manufacture an index
    beyond that stack. *)
Lemma lookup_binder_lt : forall variable binders index,
  lookup_binder variable binders = Some index ->
  index < length binders.
Proof.
  intros variable binders.
  induction binders as [| binder binders IH]; intros index Hlookup.
  - discriminate.
  - cbn [lookup_binder] in Hlookup.
    destruct (eq_id_dec binder variable) as [Hequal | Hdifferent].
    + inversion Hlookup; subst index. cbn. lia.
    + destruct (lookup_binder variable binders) as [inner |] eqn:Hinner;
        cbn in Hlookup; try discriminate.
      inversion Hlookup; subst index.
      specialize (IH inner eq_refl).
      cbn. lia.
Qed.
