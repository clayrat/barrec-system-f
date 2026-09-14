(** * Type-variable scope *)

From Stdlib Require Import List Lia PeanoNat Compare_dec.
Import ListNotations.

From SystemF.F Require Import Syntax.

Implicit Types
  (n m cutoff : nat)
  (T U : type)
  (context : list type).

(** [closed n T] means that every free de Bruijn index in [T] is
    strictly below [n].  Crossing [TForall] makes one additional type
    variable available. *)
Fixpoint closed (n : nat) (T : type) : Prop :=
  match T with
  | TVar k => k < n
  | TArrow T U => closed n T /\ closed n U
  | TForall T => closed (S n) T
  end.

(** Scope is decidable and therefore can be checked by the future
    Church-style elaborator. *)
Fixpoint closed_dec (n : nat) (T : type) :
    {closed n T} + {~ closed n T}.
Proof.
  destruct T as [k | T U | T]; cbn [closed].
  - exact (lt_dec k n).
  - destruct (closed_dec n T) as [HT | HT];
      destruct (closed_dec n U) as [HU | HU].
    + now left.
    + right. intros [_ H]. contradiction.
    + right. intros [H _]. contradiction.
    + right. intros [H _]. contradiction.
  - exact (closed_dec (S n) T).
Defined.

(** Increasing the number of available type variables preserves scope. *)
Lemma closed_mono : forall n m T,
  n <= m -> closed n T -> closed m T.
Proof.
  intros n m T.
  revert n m.
  induction T as [k | T IHT U IHU | T IHT];
    intros n m Hnm Hclosed; cbn [closed] in *.
  - lia.
  - destruct Hclosed as [HT HU].
    split.
    + now apply IHT with n.
    + now apply IHU with n.
  - apply IHT with (n := S n); try assumption.
    lia.
Qed.

(** Lifting below the current scope introduces one new available index.
    The general cutoff formulation is what is needed underneath nested
    universal quantifiers. *)
Lemma closed_type_lift : forall n cutoff T,
  cutoff <= n ->
  closed n T ->
  closed (S n) (type_lift cutoff T).
Proof.
  intros n cutoff T.
  revert n cutoff.
  induction T as [k | T IHT U IHU | T IHT];
    intros n cutoff Hcutoff Hclosed; cbn [closed type_lift] in *.
  - destruct (k <? cutoff) eqn:Hlt; cbn [closed].
    + apply Nat.ltb_lt in Hlt. lia.
    + apply Nat.ltb_ge in Hlt. lia.
  - destruct Hclosed as [HT HU].
    split.
    + now apply IHT.
    + now apply IHU.
  - apply IHT; try assumption.
    lia.
Qed.

Corollary closed_type_lift0 : forall n T,
  closed n T -> closed (S n) (type_lift 0 T).
Proof.
  intros n T Hclosed.
  apply closed_type_lift; try assumption.
  lia.
Qed.

(** Substitution removes one available type variable.  [cutoff <= n]
    permits the induction to cross binders while [type_subst] increments
    its cutoff and lifts the substituted type. *)
Lemma closed_type_subst : forall n cutoff T U,
  cutoff <= n ->
  closed (S n) T ->
  closed n U ->
  closed n (type_subst cutoff T U).
Proof.
  intros n cutoff T U.
  revert n cutoff U.
  induction T as [k | T IHT V IHV | T IHT];
    intros n cutoff U Hcutoff HT HU;
    cbn [closed type_subst] in *.
  - destruct (k ?= cutoff) eqn:Hcompare; cbn [closed].
    + apply Nat.compare_eq_iff in Hcompare.
      subst k. exact HU.
    + apply Nat.compare_lt_iff in Hcompare. lia.
    + apply Nat.compare_gt_iff in Hcompare. lia.
  - destruct HT as [HT HV].
    split.
    + now apply IHT.
    + now apply IHV.
  - apply IHT.
    + lia.
    + exact HT.
    + now apply closed_type_lift0.
Qed.

Corollary closed_type_subst0 : forall n T U,
  closed (S n) T ->
  closed n U ->
  closed n (type_subst 0 T U).
Proof.
  intros n T U HT HU.
  apply closed_type_subst; try assumption.
  lia.
Qed.

(** Under a type abstraction every type in the term-variable context is
    lifted in exactly the way required by [FTAbs]. *)
Lemma closed_context_lift : forall n context,
  Forall (closed n) context ->
  Forall (closed (S n)) (map (type_lift 0) context).
Proof.
  intros n context Hcontext.
  induction Hcontext as [| T context HT Hcontext IH]; cbn.
  - constructor.
  - constructor.
    + now apply closed_type_lift0.
    + exact IH.
Qed.

Lemma closed_nth_error : forall n context index T,
  Forall (closed n) context ->
  nth_error context index = Some T ->
  closed n T.
Proof.
  intros n context index T Hcontext Hlookup.
  apply (proj1 (Forall_forall (closed n) context) Hcontext T).
  eapply nth_error_In.
  exact Hlookup.
Qed.
