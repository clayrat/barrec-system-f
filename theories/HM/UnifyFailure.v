(** * Sound failure certificates for Hindley--Milner unification *)

From Stdlib Require Import Lia.
From SystemF.HM Require Export UnifySpec.
From SystemF.HM.WInCoq Require Export HoareMonad Occurs.

Fixpoint ty_size (t : ty) : nat :=
  match t with
  | arrow l r => 1 + ty_size l + ty_size r
  | _ => 1
  end.

Lemma occurs_ty_size_apply_subst_le : forall v t s,
    occurs v t ->
    ty_size (apply_subst s (var v)) <= ty_size (apply_subst s t).
Proof.
  intros v t.
  induction t as [i | c | l IHl r IHr]; intros s Hocc; simpl in *.
  - destruct (eq_id_dec i v); [subst; reflexivity | contradiction].
  - contradiction.
  - destruct Hocc as [Hocc | Hocc].
    + specialize (IHl s Hocc). lia.
    + specialize (IHr s Hocc). lia.
Qed.

Lemma occurs_ty_size_apply_subst_lt : forall v t s,
    t <> var v -> occurs v t ->
    ty_size (apply_subst s (var v)) < ty_size (apply_subst s t).
Proof.
  intros v t s Hneq Hocc.
  destruct t as [i | c | l r]; simpl in *.
  - destruct (eq_id_dec i v); [subst; contradiction | contradiction].
  - contradiction.
  - destruct Hocc as [Hocc | Hocc].
    + pose proof (occurs_ty_size_apply_subst_le v l s Hocc).
      change (ty_size (apply_subst s (var v)) <
              S (ty_size (apply_subst s l) + ty_size (apply_subst s r))).
      lia.
    + pose proof (occurs_ty_size_apply_subst_le v r s Hocc).
      change (ty_size (apply_subst s (var v)) <
              S (ty_size (apply_subst s l) + ty_size (apply_subst s r))).
      lia.
Qed.

(** Every failure certificate rules out every substitution, including the
    recursive right-arrow case whose certificate records factorization of the
    already-computed left unifier. *)
Theorem unify_failure_no_unifier : forall t1 t2,
    UnifyFailure t1 t2 -> forall s,
      apply_subst s t1 <> apply_subst s t2.
Proof.
  intros t1 t2 failure.
  induction failure; intros theta Heq.
  - pose proof (occurs_ty_size_apply_subst_lt v t theta n o).
    apply (f_equal ty_size) in Heq. lia.
  - pose proof (occurs_ty_size_apply_subst_lt v t theta n o).
    apply (f_equal ty_size) in Heq. lia.
  - simpl in Heq. inversion Heq. contradiction.
  - discriminate.
  - discriminate.
  - simpl in Heq. inversion Heq.
    apply (IHfailure theta). assumption.
  - simpl in Heq. inversion Heq.
    destruct (e0 theta H0) as [delta Hdelta].
    apply (IHfailure delta).
    repeat rewrite <- apply_compose_equiv.
    rewrite <-
      (ext_subst_var_ty theta (compose_subst s delta) Hdelta r).
    rewrite <-
      (ext_subst_var_ty theta (compose_subst s delta) Hdelta r').
    exact H1.
Qed.
