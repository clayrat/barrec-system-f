(** * Weak-head reduction

    This module is the independent operational reference used to check
    normalization bounds.  It deliberately does not reuse the simultaneous
    substitution from Blot's artifact.

    The one-step rule contracts the first beta-redex on the left application
    spine:

      (lambda M) N Pi --> M[N] Pi.

    Reduction never proceeds under a lambda or into an argument. *)

From Stdlib Require Import Arith.
From SystemF.F Require Import Syntax.

(** [term_subst1 n body argument] removes the variable at index [n] from
    [body] and replaces it with [argument].  Going under a binder increments
    [n] and lifts the free variables of [argument], preventing capture. *)
Fixpoint term_subst1
    (n : nat) (body : term) (argument : term) : term :=
  match body with
  | Var m =>
      match m ?= n with
      | Lt => Var m
      | Eq => argument
      | Gt => Var (pred m)
      end
  | Lam body' =>
      Lam (term_subst1 (S n) body' (term_lift 0 argument))
  | App function argument' =>
      App (term_subst1 n function argument)
          (term_subst1 n argument' argument)
  end.

(** Executable weak-head reduction. *)
Fixpoint wh_step (t : term) : option term :=
  match t with
  | App (Lam body) argument => Some (term_subst1 0 body argument)
  | App function argument =>
      match wh_step function with
      | Some function' => Some (App function' argument)
      | None => None
      end
  | _ => None
  end.

(** Iterate at most [fuel] weak-head steps.  A term already in weak-head
    normal form is returned immediately, so an overestimate is harmless. *)
Fixpoint run_fuel (fuel : nat) (t : term) : term :=
  match fuel with
  | O => t
  | S fuel' =>
      match wh_step t with
      | Some t' => run_fuel fuel' t'
      | None => t
      end
  end.

(** A total test oracle.  [Some (steps, normal_form)] reports the exact
    number of weak-head steps when normalization finishes within [fuel].
    [None] means only that the supplied cap was insufficient. *)
Fixpoint eval_cap (fuel : nat) (t : term) : option (nat * term) :=
  match fuel with
  | O =>
      match wh_step t with
      | Some _ => None
      | None => Some (0, t)
      end
  | S fuel' =>
      match wh_step t with
      | Some t' =>
          match eval_cap fuel' t' with
          | Some (steps, normal_form) => Some (S steps, normal_form)
          | None => None
          end
      | None => Some (0, t)
      end
  end.

(** Relational specification of [wh_step]. *)
Inductive wh_reduces : term -> term -> Prop :=
| WhBeta : forall body argument,
    wh_reduces (App (Lam body) argument)
               (term_subst1 0 body argument)
| WhApp : forall function function' argument,
    wh_reduces function function' ->
    wh_reduces (App function argument) (App function' argument).

Definition whnf (t : term) : Prop :=
  forall t', ~ wh_reduces t t'.

Lemma wh_step_sound :
  forall t t', wh_step t = Some t' -> wh_reduces t t'.
Proof.
  induction t as [n | body IHbody | function IHfunction argument IHargument];
    intros t' Hstep; simpl in Hstep; try discriminate.
  destruct function as [n | body | left right].
  - discriminate.
  - inversion Hstep; subst. constructor.
  - destruct (wh_step (App left right)) as [function' |] eqn:Hfunction;
      try discriminate.
    inversion Hstep; subst.
    apply WhApp.
    apply IHfunction.
    reflexivity.
Qed.

Lemma wh_step_complete :
  forall t t', wh_reduces t t' -> wh_step t = Some t'.
Proof.
  intros t t' Hreduces.
  induction Hreduces as
      [body argument | function function' argument Hfunction IHfunction].
  - reflexivity.
  - destruct function as [n | body | left right]; simpl in IHfunction;
      try discriminate.
    simpl.
    rewrite IHfunction.
    reflexivity.
Qed.

Lemma wh_step_none_iff_whnf :
  forall t, wh_step t = None <-> whnf t.
Proof.
  intros t.
  split.
  - intros Hnone t' Hreduces.
    pose proof (wh_step_complete _ _ Hreduces) as Hstep.
    rewrite Hnone in Hstep.
    discriminate.
  - intros Hnormal.
    destruct (wh_step t) as [t' |] eqn:Hstep; [| reflexivity].
    exfalso.
    apply (Hnormal t').
    apply wh_step_sound.
    exact Hstep.
Qed.

(** Exactly [steps] weak-head reductions. *)
Inductive wh_steps : nat -> term -> term -> Prop :=
| WhStepsZero : forall t, wh_steps 0 t t
| WhStepsSucc : forall steps t t' normal_form,
    wh_reduces t t' ->
    wh_steps steps t' normal_form ->
    wh_steps (S steps) t normal_form.

Lemma run_fuel_sound :
  forall fuel t,
    exists steps,
      steps <= fuel /\ wh_steps steps t (run_fuel fuel t).
Proof.
  induction fuel as [| fuel IHfuel]; intros t.
  - exists 0.
    split; constructor.
  - simpl.
    destruct (wh_step t) as [t' |] eqn:Hstep.
    + destruct (IHfuel t') as [steps [Hle Hsteps]].
      exists (S steps).
      split.
      * now apply le_n_S.
      * apply WhStepsSucc with (t' := t').
        -- now apply wh_step_sound.
        -- exact Hsteps.
    + exists 0.
      split.
      * apply Nat.le_0_l.
      * constructor.
Qed.

Lemma eval_cap_sound :
  forall fuel t steps normal_form,
    eval_cap fuel t = Some (steps, normal_form) ->
    steps <= fuel /\
    wh_steps steps t normal_form /\
    whnf normal_form.
Proof.
  induction fuel as [| fuel IHfuel]; intros t steps normal_form Heval;
    simpl in Heval.
  - destruct (wh_step t) as [t' |] eqn:Hstep; try discriminate.
    inversion Heval; subst.
    repeat split.
    + constructor.
    + constructor.
    + apply wh_step_none_iff_whnf. exact Hstep.
  - destruct (wh_step t) as [t' |] eqn:Hstep.
    + destruct (eval_cap fuel t') as [[steps' normal_form'] |]
          eqn:Hrecursive; try discriminate.
      inversion Heval; subst.
      destruct (IHfuel _ _ _ Hrecursive) as [Hle [Hsteps Hnormal]].
      repeat split.
      * now apply le_n_S.
      * apply WhStepsSucc with (t' := t').
        -- now apply wh_step_sound.
        -- exact Hsteps.
      * exact Hnormal.
    + inversion Heval; subst.
      repeat split.
      * apply Nat.le_0_l.
      * constructor.
      * apply wh_step_none_iff_whnf. exact Hstep.
Qed.

(** A successful exact evaluation supplies not only a relational trace but
    also fuel that reproduces its reported weak-head normal form. *)
Lemma eval_cap_run_fuel :
  forall fuel t steps normal_form,
    eval_cap fuel t = Some (steps, normal_form) ->
    run_fuel steps t = normal_form.
Proof.
  induction fuel as [| fuel IHfuel];
    intros t steps normal_form Heval; simpl in Heval.
  - destruct (wh_step t) as [t' |] eqn:Hstep; try discriminate.
    inversion Heval; reflexivity.
  - destruct (wh_step t) as [t' |] eqn:Hstep.
    + destruct (eval_cap fuel t') as [[steps' normal_form'] |]
          eqn:Hrecursive; try discriminate.
      inversion Heval; subst.
      simpl.
      rewrite Hstep.
      now apply IHfuel.
    + inversion Heval; reflexivity.
Qed.
