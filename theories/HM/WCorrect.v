(** * Successful contract of the checked Algorithm W *)

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

From SystemF.HM.W Require Import
  Context Infer NewTypeVariable SimpleTypes Subst Typing.

(** [runW] deliberately erases the final fresh-variable state carried by
    [W].  Its successful postcondition therefore quantifies that state
    existentially. *)
Definition runW_success_spec
    (e : hmterm) (G : hmctx) (tau : ty) (s : substitution) : Prop :=
  exists final_state,
    proj1_sig (computeInitialState G) <= final_state /\
    new_tv_subst s final_state /\
    new_tv_ty tau final_state /\
    new_tv_ctx (apply_subst_ctx s G) final_state /\
    has_type (apply_subst_ctx s G) e tau /\
    completeness e G tau s (proj1_sig (computeInitialState G)).

(** A successful [runW] result retains the complete checked postcondition
    of [W]: state monotonicity, freshness, declarative soundness, and the
    principal-result completeness property. *)
Theorem runW_success_contract : forall e G tau s,
    runW e G = inl (tau, s) ->
    runW_success_spec e G tau s.
Proof.
  intros e G tau s Hrun.
  unfold runW in Hrun.
  destruct (W e G (computeInitialState G)) as [result Hresult].
  destruct result as [[[tau' s'] final_state] | failure].
  - cbn in Hrun.
    inversion Hrun; subst tau' s'.
    exists final_state.
    exact Hresult.
  - discriminate.
Qed.

Corollary runW_success_sound : forall e G tau s,
    runW e G = inl (tau, s) ->
    has_type (apply_subst_ctx s G) e tau.
Proof.
  intros e G tau s Hrun.
  destruct (runW_success_contract e G tau s Hrun)
    as [final_state [_ [_ [_ [_ [Htyping _]]]]]].
  exact Htyping.
Qed.

Corollary runW_success_complete : forall e G tau s,
    runW e G = inl (tau, s) ->
    completeness e G tau s (proj1_sig (computeInitialState G)).
Proof.
  intros e G tau s Hrun.
  destruct (runW_success_contract e G tau s Hrun)
    as [final_state [_ [_ [_ [_ [_ Hcomplete]]]]]].
  exact Hcomplete.
Qed.
