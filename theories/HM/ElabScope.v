(** * Source fragment for HM-to-System-F elaboration

    The term-level bridge elaborates the pure Hindley--Milner fragment:
    variables, abstraction, application, and non-recursive [let].  Constants
    are deliberately excluded because the current [ConstantInterpretation]
    supplies only their System F types, not System F terms realizing them.

    This restriction is independent of term-variable scope.  The internal
    elaborator will be parameterized by an HM environment; its public closed
    entry point will use the empty environment, so the existing Algorithm W
    lookup rejects unbound source variables.  Binder shadowing is allowed. *)

From Stdlib Require Import Bool.

From SystemF.HM.WInCoq Require Import Typing.

Fixpoint constant_free (expression : term) : Prop :=
  match expression with
  | var_t _ => True
  | app_t function argument =>
      constant_free function /\ constant_free argument
  | let_t _ bound body =>
      constant_free bound /\ constant_free body
  | lam_t _ body => constant_free body
  | const_t _ => False
  end.

(** Boolean view used by the extracted frontend before running [W_elab]. *)
Fixpoint constant_freeb (expression : term) : bool :=
  match expression with
  | var_t _ => true
  | app_t function argument =>
      constant_freeb function && constant_freeb argument
  | let_t _ bound body =>
      constant_freeb bound && constant_freeb body
  | lam_t _ body => constant_freeb body
  | const_t _ => false
  end.

Theorem constant_freeb_spec : forall expression,
  reflect (constant_free expression) (constant_freeb expression).
Proof.
  induction expression as
      [variable
      | function IHfunction argument IHargument
      | variable bound IHbound body IHbody
      | variable body IHbody
      | constant];
    cbn [constant_free constant_freeb].
  - constructor. exact I.
  - destruct IHfunction as [Hfunction | Hfunction];
      destruct IHargument as [Hargument | Hargument];
      constructor; intuition.
  - destruct IHbound as [Hbound | Hbound];
      destruct IHbody as [Hbody | Hbody];
      constructor; intuition.
  - exact IHbody.
  - constructor. exact (fun impossible => impossible).
Qed.

Corollary constant_freeb_true_iff : forall expression,
  constant_freeb expression = true <-> constant_free expression.
Proof.
  intro expression.
  destruct (constant_freeb_spec expression); split; intro H.
  - assumption.
  - reflexivity.
  - discriminate.
  - contradiction.
Qed.

Corollary constant_freeb_false_iff : forall expression,
  constant_freeb expression = false <-> ~ constant_free expression.
Proof.
  intro expression.
  destruct (constant_freeb_spec expression); split; intro H.
  - discriminate.
  - contradiction.
  - assumption.
  - reflexivity.
Qed.

Definition constant_free_dec (expression : term) :
    {constant_free expression} + {~ constant_free expression}.
Proof.
  destruct (constant_freeb_spec expression).
  - now left.
  - now right.
Defined.

(** A proof-carrying input for clients that want to make the restriction
    explicit at the API boundary. *)
Definition HMElaborationInput : Type :=
  {expression : term | constant_free expression}.

