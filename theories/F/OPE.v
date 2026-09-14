(** * OPE renamings and parallel type substitutions

    This module presents the de Bruijn operations from [F.Syntax] in the
    drop/keep style used by ref-graphs.  The original Blot definitions stay
    unchanged; [ren_type_lift] and [sub_scons_ids] prove that the two
    presentations agree. *)

From Stdlib Require Import Arith Lia PeanoNat.

From SystemF.F Require Import Syntax.

Implicit Types
  (index cutoff : nat)
  (T U : type).

(** An OPE is built from the identity embedding by inserting an unused newest
    target variable ([OPEDrop]) or keeping the newest variable on both sides
    ([OPEKeep]). *)
Inductive ope : Type :=
| OPEId : ope
| OPEDrop : ope -> ope
| OPEKeep : ope -> ope.

Fixpoint apply_ope (rho : ope) (index : nat) : nat :=
  match rho with
  | OPEId => index
  | OPEDrop rho => S (apply_ope rho index)
  | OPEKeep rho =>
      match index with
      | 0 => 0
      | S index => S (apply_ope rho index)
      end
  end.

(** The constructors generate only order-preserving maps. *)
Lemma apply_ope_strict_mono : forall rho i j,
  i < j -> apply_ope rho i < apply_ope rho j.
Proof.
  induction rho as [| rho IH | rho IH]; intros i j Hij.
  - exact Hij.
  - cbn.
    specialize (IH i j Hij).
    lia.
  - destruct i as [| i], j as [| j]; cbn in *; try lia.
    assert (Hij' : i < j) by lia.
    specialize (IH i j Hij').
    lia.
Qed.

(** Weakening inserts a new variable at de Bruijn index zero. *)
Definition wk : ope := OPEDrop OPEId.

Fixpoint ren (rho : ope) (T : type) : type :=
  match T with
  | TVar index => TVar (apply_ope rho index)
  | TArrow T U => TArrow (ren rho T) (ren rho U)
  | TForall T => TForall (ren (OPEKeep rho) T)
  end.

(** [lift_ope cutoff] keeps the variables below [cutoff] and drops the next
    one.  It is the OPE presentation of Blot's cutoff-based lifting. *)
Fixpoint lift_ope (cutoff : nat) : ope :=
  match cutoff with
  | 0 => wk
  | S cutoff => OPEKeep (lift_ope cutoff)
  end.

Lemma ltb_succ_succ : forall n m,
  (S n <? S m) = (n <? m).
Proof.
  intros n m.
  destruct (S n <? S m) eqn:Hsucc;
    destruct (n <? m) eqn:H; try reflexivity.
  - apply Nat.ltb_lt in Hsucc.
    apply Nat.ltb_ge in H.
    lia.
  - apply Nat.ltb_ge in Hsucc.
    apply Nat.ltb_lt in H.
    lia.
Qed.

Lemma apply_lift_ope : forall cutoff index,
  apply_ope (lift_ope cutoff) index =
    if index <? cutoff then index else S index.
Proof.
  induction cutoff as [| cutoff IH]; intros [| index].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - change
      (S (apply_ope (lift_ope cutoff) index) =
       if S index <? S cutoff then S index else S (S index)).
    rewrite IH, ltb_succ_succ.
    destruct (index <? cutoff); reflexivity.
Qed.

(** OPE lifting agrees with the original operation at every cutoff. *)
Lemma ren_type_lift : forall cutoff T,
  ren (lift_ope cutoff) T = type_lift cutoff T.
Proof.
  intros cutoff T.
  revert cutoff.
  induction T as [index | T IHT U IHU | T IHT];
    intros cutoff; cbn [ren type_lift].
  - rewrite apply_lift_ope.
    destruct (index <? cutoff); reflexivity.
  - now rewrite IHT, IHU.
  - f_equal.
    exact (IHT (S cutoff)).
Qed.

Corollary ren_wk : forall T,
  ren wk T = type_lift 0 T.
Proof.
  exact (ren_type_lift 0).
Qed.

(** A parallel substitution assigns a type to every de Bruijn index. *)
Definition type_substitution : Type := nat -> type.

Definition ids : type_substitution := TVar.

Definition scons (U : type) (sigma : type_substitution) :
    type_substitution :=
  fun index =>
    match index with
    | 0 => U
    | S index => sigma index
    end.

Definition drop_sub (sigma : type_substitution) : type_substitution :=
  fun index => ren wk (sigma index).

(** Crossing a binder maps its newest variable to itself and weakens every
    older substitution image.  This is ref-graphs' [keep'_s]. *)
Definition keep_sub (sigma : type_substitution) : type_substitution :=
  scons (TVar 0) (drop_sub sigma).

Fixpoint sub (sigma : type_substitution) (T : type) : type :=
  match T with
  | TVar index => sigma index
  | TArrow T U => TArrow (sub sigma T) (sub sigma U)
  | TForall T => TForall (sub (keep_sub sigma) T)
  end.

Lemma sub_ext : forall sigma tau T,
  (forall index, sigma index = tau index) ->
  sub sigma T = sub tau T.
Proof.
  intros sigma tau T.
  revert sigma tau.
  induction T as [index | T IHT U IHU | T IHT];
    intros sigma tau Heq; cbn [sub].
  - apply Heq.
  - f_equal.
    + now apply IHT.
    + now apply IHU.
  - f_equal.
    apply IHT.
    intros [| index]; cbn [keep_sub scons].
    + reflexivity.
    + unfold drop_sub.
      now rewrite Heq.
Qed.

Lemma sub_ids : forall T,
  sub ids T = T.
Proof.
  induction T as [index | T IHT U IHU | T IHT]; cbn [sub ids].
  - reflexivity.
  - now rewrite IHT, IHU.
  - f_equal.
    transitivity (sub ids T).
    + apply sub_ext.
      intros [| index]; reflexivity.
    + exact IHT.
Qed.

(** The parallel substitution corresponding to Blot's single substitution
    at an arbitrary cutoff. *)
Definition single_substitution
    (cutoff : nat) (U : type) : type_substitution :=
  fun index =>
    match index ?= cutoff with
    | Lt => TVar index
    | Eq => U
    | Gt => TVar (pred index)
    end.

Lemma keep_single_substitution : forall cutoff U index,
  keep_sub (single_substitution cutoff U) index =
  single_substitution (S cutoff) (type_lift 0 U) index.
Proof.
  intros cutoff U [| index].
  - reflexivity.
  - cbn [keep_sub scons].
    unfold drop_sub, single_substitution.
    rewrite Nat.compare_succ.
    destruct (index ?= cutoff) eqn:Hcompare.
    + apply ren_wk.
    + reflexivity.
    + apply Nat.compare_gt_iff in Hcompare.
      cbn [ren wk apply_ope].
      f_equal.
      lia.
Qed.

Lemma sub_single_substitution : forall cutoff T U,
  sub (single_substitution cutoff U) T =
  type_subst cutoff T U.
Proof.
  intros cutoff T.
  revert cutoff.
  induction T as [index | T IHT V IHV | T IHT];
    intros cutoff U; cbn [sub type_subst].
  - reflexivity.
  - now rewrite IHT, IHV.
  - f_equal.
    transitivity
      (sub (single_substitution (S cutoff) (type_lift 0 U)) T).
    + apply sub_ext.
      apply keep_single_substitution.
    + apply IHT.
Qed.

Lemma scons_ids_single : forall U index,
  scons U ids index = single_substitution 0 U index.
Proof.
  intros U [| index]; reflexivity.
Qed.

(** Parallel substitution by [U] at zero agrees with Blot's operation. *)
Theorem sub_scons_ids : forall T U,
  sub (scons U ids) T = type_subst 0 T U.
Proof.
  intros T U.
  transitivity (sub (single_substitution 0 U) T).
  - apply sub_ext.
    apply scons_ids_single.
  - apply sub_single_substitution.
Qed.
