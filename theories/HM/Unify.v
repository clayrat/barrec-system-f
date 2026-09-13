(** * Executable Hindley--Milner unification

    [run_unify] erases the dependent proof payload from the adapted W-in-Coq
    algorithm while the following lemmas recover its checked contract. *)

From Stdlib Require Import Program.
From SystemF.HM Require Export
  UnifySpec UnifyFailure UnifyExec UnifyExecCorrect.
From SystemF.HM.WInCoq Require Import WellFormed.
From SystemF.HM.WInCoq Require Import Unify.

Definition run_unify (t1 t2 : ty) : unify_result :=
  match SystemF.HM.WInCoq.Unify.unify'' t1 t2 with
  | existT _ _ (inl (exist _ s _)) => unified s
  | existT _ _ (inr _) => rejected
  end.

Theorem run_unify_sound : forall t1 t2 s,
    run_unify t1 t2 = unified s -> is_unifier t1 t2 s.
Proof.
  intros t1 t2 s Hrun.
  unfold run_unify in Hrun.
  destruct (SystemF.HM.WInCoq.Unify.unify'' t1 t2) as [variables result].
  destruct result as [[candidate properties] | failure]; try discriminate.
  inversion Hrun; subst.
  exact (proj1 properties).
Qed.

Theorem run_unify_principal : forall t1 t2 s,
    run_unify t1 t2 = unified s -> is_principal_unifier t1 t2 s.
Proof.
  intros t1 t2 s Hrun.
  unfold run_unify in Hrun.
  destruct (SystemF.HM.WInCoq.Unify.unify'' t1 t2) as [variables result].
  destruct result as [[candidate properties] | failure]; try discriminate.
  inversion Hrun; subst; clear Hrun.
  destruct properties as [Hunify [_ [_ Hprincipal]]].
  split; [exact Hunify |].
  intros s' Hs'.
  destruct (Hprincipal s' Hs') as [residual Hresidual].
  exists residual. exact Hresidual.
Qed.

Theorem run_unify_preserves_freshness : forall t1 t2 s,
    run_unify t1 t2 = unified s -> preserves_freshness t1 t2 s.
Proof.
  intros t1 t2 s Hrun.
  unfold run_unify in Hrun.
  destruct (SystemF.HM.WInCoq.Unify.unify'' t1 t2) as [variables result].
  destruct result as [[candidate properties] | failure]; try discriminate.
  inversion Hrun; subst; clear Hrun.
  exact (proj1 (proj2 (proj2 properties))).
Qed.

Theorem run_unify_rejected_no_unifier : forall t1 t2,
    run_unify t1 t2 = rejected -> forall s,
      apply_subst s t1 <> apply_subst s t2.
Proof.
  intros t1 t2 Hrun.
  unfold run_unify in Hrun.
  destruct (SystemF.HM.WInCoq.Unify.unify'' t1 t2) as [variables result].
  destruct result as [[candidate properties] | failure]; try discriminate.
  apply unify_failure_no_unifier. exact failure.
Qed.

(** ** Correspondence with the proof-free core *)

Theorem unify_exec_rejected_iff_run_unify_rejected : forall t1 t2,
    unify_exec t1 t2 = rejected <-> run_unify t1 t2 = rejected.
Proof.
  intros t1 t2. split; intro Hrejected.
  - destruct (run_unify t1 t2) as [checked |] eqn:Hchecked.
    + exfalso.
      apply (unify_exec_rejected_no_unifier t1 t2 Hrejected checked).
      apply run_unify_sound. exact Hchecked.
    + reflexivity.
  - destruct (unify_exec t1 t2) as [computed |] eqn:Hcomputed.
    + exfalso.
      apply (run_unify_rejected_no_unifier t1 t2 Hrejected computed).
      apply unify_exec_success_sound. exact Hcomputed.
    + reflexivity.
Qed.

(** Successful substitutions returned by both implementations are mutually
    most general.  They need not be syntactically identical because variable
    elimination order is an implementation detail. *)
Theorem unify_exec_checked_correspondence : forall t1 t2 computed checked,
    unify_exec t1 t2 = unified computed ->
    run_unify t1 t2 = unified checked ->
    is_unifier t1 t2 computed /\
    is_unifier t1 t2 checked /\
    factors_through computed checked /\
    factors_through checked computed.
Proof.
  intros t1 t2 computed checked Hcomputed Hchecked.
  pose proof
    (unify_exec_success_principal t1 t2 computed Hcomputed)
    as [Hcomputed_sound Hcomputed_principal].
  pose proof
    (run_unify_principal t1 t2 checked Hchecked)
    as [Hchecked_sound Hchecked_principal].
  repeat split; try assumption.
  - now apply Hcomputed_principal.
  - now apply Hchecked_principal.
Qed.

Theorem unify_exec_success_iff_run_unify_success : forall t1 t2,
    (exists computed, unify_exec t1 t2 = unified computed) <->
    (exists checked, run_unify t1 t2 = unified checked).
Proof.
  intros t1 t2. split; intros [candidate Hcandidate].
  - destruct (run_unify t1 t2) as [checked |] eqn:Hchecked.
    + now exists checked.
    + exfalso.
      apply (proj2 (unify_exec_rejected_iff_run_unify_rejected t1 t2))
        in Hchecked.
      now rewrite Hcandidate in Hchecked.
  - destruct (unify_exec t1 t2) as [computed |] eqn:Hcomputed.
    + now exists computed.
    + exfalso.
      apply (proj1 (unify_exec_rejected_iff_run_unify_rejected t1 t2))
        in Hcomputed.
      now rewrite Hcandidate in Hcomputed.
Qed.

(** The interface consumed by the original [W] proof.  Its raw result is
    named separately so clients can erase the Hoare proof without reducing
    through a dependent [Program] match.  Rejection is reported without a
    certificate: [unify_exec_rejected_no_unifier] already proves that no
    unifier exists, so the dependent [unify''] is never executed by [W]. *)
Definition unify_exec_hoare_raw (tau1 tau2 : ty) (st : id)
    : (substitution * id + InferFailure)%type :=
  match unify_exec tau1 tau2 with
  | unified mu => inl (mu, st)
  | rejected => inr (UnifyRejected' tau1 tau2)
  end.

Program Definition unify_exec_hoare (tau1 tau2 : ty) :
  @Infer (@top id) substitution (fun i mu f =>
    i = f /\
    (forall s', apply_subst s' tau1 = apply_subst s' tau2 ->
      exists s'', forall tau,
        apply_subst s' tau =
        apply_subst (compose_subst mu s'') tau) /\
    ((new_tv_ty tau1 i /\ new_tv_ty tau2 i) ->
      new_tv_subst mu i) /\
    apply_subst mu tau1 = apply_subst mu tau2) :=
  fun input =>
    exist _
      (unify_exec_hoare_raw tau1 tau2 (proj1_sig input)) _.
Next Obligation.
  unfold unify_exec_hoare_raw.
  destruct (unify_exec tau1 tau2) as [mu |] eqn:Hexec.
  - pose proof (unify_exec_success_principal tau1 tau2 mu Hexec)
      as [Hsound Hprincipal].
    split; [reflexivity |].
    split.
    + intros candidate Hcandidate.
      destruct (Hprincipal candidate Hcandidate)
        as [residual Hfactor].
      exists residual.
      intro tau.
      apply substitution_equiv_ty.
      exact Hfactor.
    + split.
      * intro Hfresh.
        exact (unify_exec_preserves_freshness
          tau1 tau2 mu Hexec input Hfresh).
      * exact Hsound.
  - exact I.
Defined.
