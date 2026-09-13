(** * Observational correspondence of checked and proof-free W *)

From Stdlib Require Import
  List Lia PeanoNat Program ProofIrrelevance.
Import ListNotations.

From SystemF.HM Require Import WExec WExecCorrect WCorrect Unify.
From SystemF.HM.WInCoq Require Import
  Context HoareMonad Infer NewTypeVariable SimpleTypes Subst Typing.

(** Hoare computations may receive different proofs of the same
    precondition.  Their observable result cannot depend on that proof. *)
Lemma run_hoare_proof_irrelevant :
  forall (state error : Set) (A : Type)
    (P : Pre state) (Q : Post state A)
    (m : @HoareState state error P A Q)
    st (p q : P st),
  proj1_sig (m (exist _ st p)) =
  proj1_sig (m (exist _ st q)).
Proof.
  intros state error A P Q m st p q.
  pose proof (proof_irrelevance (P st) p q) as Heq.
  dependent rewrite Heq.
  reflexivity.
Qed.

Lemma computeInitialState_observe : forall G,
  proj1_sig (computeInitialState G) = initial_state_exec G.
Proof.
  induction G as [| [x sigma] G IH].
  - reflexivity.
  - cbn [computeInitialState initial_state_exec proj1_sig].
    destruct (Compare_dec.lt_dec
      (Schemes.max_vars_schm sigma) (proj1_sig (computeInitialState G)))
      as [Hlt | Hnlt]; cbn [proj1_sig].
    + rewrite IH in Hlt |-.
      apply Nat.ltb_lt in Hlt.
      rewrite Hlt.
      exact IH.
    + rewrite IH in Hnlt |-.
      assert (Hb :
        (Schemes.max_vars_schm sigma <? initial_state_exec G) = false).
      { apply Nat.ltb_ge. lia. }
      rewrite Hb.
      reflexivity.
Qed.

Section ObserveBind.

Context {state error : Set}.
Context {A B : Type}.
Context {P : Pre state} {Pnext : A -> Pre state}.
Context {Q : Post state A} {Qnext : A -> Post state B}.

Variable first : @HoareState state error P A Q.
Variable next : forall x,
  @HoareState state error (Pnext x) B (Qnext x).

Lemma observe_bind_failure :
  forall (input : { st : state |
    P st /\ forall x st', Q st x st' -> Pnext x st' })
    failure,
  proj1_sig
    (first (exist _ (proj1_sig input) (proj1 (proj2_sig input)))) =
    inr failure ->
  proj1_sig ((bind first next) input) = inr failure.
Proof.
  intros [st [Hp Hcontinue]] failure Hfirst.
  unfold bind in *.
  cbn in *.
  pose proof
    (proof_irrelevance (P st) (proj1 (conj Hp Hcontinue)) Hp) as Heq.
  dependent rewrite Heq in Hfirst.
  destruct (first (exist (fun t : state => P t) st Hp))
    as [[[x st'] | actual_failure] Hpost] eqn:Hcall;
    cbn in Hfirst |-; try discriminate.
  inversion Hfirst.
  reflexivity.
Qed.

Lemma observe_bind_success :
  forall (input : { st : state |
    P st /\ forall x st', Q st x st' -> Pnext x st' })
    x st',
  proj1_sig
    (first (exist _ (proj1_sig input) (proj1 (proj2_sig input)))) =
    inl (x, st') ->
  exists next_pre : Pnext x st',
    proj1_sig ((bind first next) input) =
    proj1_sig (next x (exist _ st' next_pre)).
Proof.
  intros [st [Hp Hcontinue]] x st' Hfirst.
  unfold bind in *.
  cbn in *.
  pose proof
    (proof_irrelevance (P st) (proj1 (conj Hp Hcontinue)) Hp) as Heq.
  dependent rewrite Heq in Hfirst.
  destruct (first (exist (fun t : state => P t) st Hp))
    as [[[actual actual_st] | failure] Hpost] eqn:Hcall;
    cbn in Hfirst |-; try discriminate.
  inversion Hfirst; subst actual actual_st.
  eexists.
  cbn.
  reflexivity.
Qed.

End ObserveBind.

Section ObserveBindRet.

Context {state error : Set}.
Context {A B : Type}.
Context {P : Pre state} {Q : Post state A}.

Variable first : @HoareState state error P A Q.
Variable f : A -> B.

(** The most common bind in [W] only transforms a successful value and
    leaves the state and failures untouched.  Stating that fact once keeps
    the dependent proof arguments out of the branch equations below. *)
Lemma observe_bind_ret :
  forall (input : { st : state |
    P st /\ forall x st', Q st x st' -> @top state st' }),
  proj1_sig ((bind first (fun x => ret (f x))) input) =
  match proj1_sig
    (first (exist _ (proj1_sig input) (proj1 (proj2_sig input)))) with
  | inl (x, st') => inl (f x, st')
  | inr failure => inr failure
  end.
Proof.
  intros input.
  destruct (proj1_sig
    (first (exist _ (proj1_sig input) (proj1 (proj2_sig input)))))
    as [[x st'] | failure] eqn:Hfirst.
  - destruct (observe_bind_success first (fun x => ret (f x))
      input x st' Hfirst) as [next_pre Hbind].
    rewrite Hbind.
    reflexivity.
  - rewrite (observe_bind_failure first (fun x => ret (f x))
      input failure Hfirst).
    reflexivity.
Qed.

End ObserveBindRet.

Lemma look_dep_observe : forall x G st (p : top st),
  proj1_sig (look_dep x G (exist _ st p)) =
  match in_ctx x G with
  | Some sigma => inl (sigma, st)
  | None => inr (MissingVar' (missingVar x))
  end.
Proof.
  intros x G st p.
  unfold look_dep.
  destruct (in_ctx x G); reflexivity.
Qed.

Lemma apply_inst_subst_hoare_observe : forall is sigma st (p : top st),
  proj1_sig (apply_inst_subst_hoare is sigma (exist _ st p)) =
  match SubstSchm.apply_inst_subst is sigma with
  | Some tau => inl (tau, st)
  | None => inr (SubstFailure' substFail)
  end.
Proof.
  intros is sigma st p.
  unfold apply_inst_subst_hoare.
  destruct (SubstSchm.apply_inst_subst is sigma); reflexivity.
Qed.

Lemma schm_inst_dep_observe : forall sigma st (p : top st),
  proj1_sig (schm_inst_dep sigma (exist _ st p)) =
  match SubstSchm.apply_inst_subst
    (SubstSchm.compute_inst_subst st (Schemes.max_gen_vars sigma)) sigma with
  | Some tau => inl (tau, st + Schemes.max_gen_vars sigma)
  | None => inr (SubstFailure' substFail)
  end.
Proof.
  intros sigma st p.
  unfold schm_inst_dep.
  cbn.
  match goal with
  | |- proj1_sig ((bind ?first ?next) ?input) = _ =>
      pose proof (observe_bind_ret first (fun x => x) input) as Hbind
  end.
  cbn in Hbind.
  rewrite Hbind.
  match goal with
  | |- context [proj1_sig
      (apply_inst_subst_hoare ?is ?sigma (exist _ ?state ?pre))] =>
      pose proof
        (apply_inst_subst_hoare_observe is sigma state pre) as Happly
  end.
  assert (Heta : forall z : (ty * id + InferFailure)%type,
    match z with
    | inl (x, st') => inl (x, st')
    | inr failure => inr failure
    end = z).
  { intros [[x final] | failure]; reflexivity. }
  etransitivity.
  - apply Heta.
  - exact Happly.
Qed.

(** Forget only the proof-carrying failure certificate.  Successful data,
    including the final fresh-variable state, stays observable. *)
Definition observe_checked_state_result
    (result : ((ty * substitution) * id + InferFailure)%type)
    : w_state_result :=
  match result with
  | inl ((tau, s), final_state) =>
      w_state_success tau s final_state
  | inr _ => w_state_rejected
  end.

Definition observe_value_state_result {A : Type}
    (f : A -> ty * substitution)
    (result : (A * id + InferFailure)%type) : w_state_result :=
  match result with
  | inl (value, final_state) =>
      w_state_success (fst (f value)) (snd (f value)) final_state
  | inr _ => w_state_rejected
  end.

(** A value-transforming bind, seen through the W observer, is just [map]
    over the successful result of its first computation. *)
Lemma observe_bind_ret_W :
  forall {A : Type} {P : Pre id} {Q : Post id A}
    (first : @HoareState id InferFailure P A Q)
    (f : A -> ty * substitution)
    (input : { st : id |
      P st /\ forall x st', Q st x st' -> top st' }),
  observe_checked_state_result
    (proj1_sig ((bind first (fun x => ret (f x))) input)) =
  observe_value_state_result f
    (proj1_sig
      (first (exist _ (proj1_sig input) (proj1 (proj2_sig input))))).
Proof.
  intros A P Q first f input.
  destruct (proj1_sig
    (first (exist _ (proj1_sig input) (proj1 (proj2_sig input)))))
    as [[x st'] | failure] eqn:Hfirst.
  - destruct (observe_bind_success first (fun x => ret (f x))
      input x st' Hfirst) as [next_pre Hbind].
    etransitivity.
    + exact (f_equal observe_checked_state_result Hbind).
    + cbn [ret observe_checked_state_result
        observe_value_state_result proj1_sig].
      destruct (f x); reflexivity.
  - pose proof
      (observe_bind_failure first (fun x => ret (f x))
        input failure Hfirst) as Hbind.
    etransitivity.
    + exact (f_equal observe_checked_state_result Hbind).
    + reflexivity.
Qed.

Lemma observe_instantiation_result :
  forall (f : ty -> ty * substitution) st result,
  observe_value_state_result f
    match result with
    | Some tau => inl (tau, st)
    | None => inr (SubstFailure' substFail)
    end =
  match result with
  | Some tau =>
      w_state_success (fst (f tau)) (snd (f tau)) st
  | None => w_state_rejected
  end.
Proof.
  intros f st [tau |]; reflexivity.
Qed.

Lemma look_result_success : forall x G st sigma final_state,
  @inl (Schemes.schm * id) InferFailure (sigma, final_state) =
    match in_ctx x G with
    | Some found => inl (found, st)
    | None => inr (MissingVar' (missingVar x))
    end ->
  in_ctx x G = Some sigma /\ final_state = st.
Proof.
  intros x G st sigma final_state Hresult.
  destruct (in_ctx x G) as [found |] eqn:Hlookup;
    inversion Hresult; subst; auto.
Qed.

Lemma look_result_failure : forall x G st failure,
  @inr (Schemes.schm * id) InferFailure failure =
    match in_ctx x G with
    | Some found => inl (found, st)
    | None => inr (MissingVar' (missingVar x))
    end ->
  in_ctx x G = None.
Proof.
  intros x G st failure Hresult.
  destruct (in_ctx x G) as [found |] eqn:Hlookup;
    inversion Hresult; auto.
Qed.

Lemma observe_unify_exec_hoare :
  forall (f : substitution -> ty * substitution)
    tau1 tau2 st (p : top st),
  observe_value_state_result f
    (proj1_sig (unify_exec_hoare tau1 tau2 (exist _ st p))) =
  match unify_exec tau1 tau2 with
  | unified s =>
      w_state_success (fst (f s)) (snd (f s)) st
  | rejected => w_state_rejected
  end.
Proof.
  intros f tau1 tau2 st p.
  cbn [unify_exec_hoare proj1_sig].
  unfold unify_exec_hoare_raw.
  destruct (unify_exec tau1 tau2) as [s |] eqn:Hexec.
  - cbn [observe_value_state_result].
    destruct (f s); reflexivity.
  - reflexivity.
Qed.

Definition observe_checked_W
    (e : term) (G : ctx) (st : id) (fresh : new_tv_ctx G st)
    : w_state_result :=
  observe_checked_state_result
    (proj1_sig (W e G (exist _ st fresh))).

(** The checked and proof-free implementations take exactly the same
    observable branch, return the same successful type/substitution, and
    advance the fresh-variable state by the same amount. *)
Theorem W_exec_checked_correspondence : forall e G st fresh,
  observe_checked_W e G st fresh = W_exec e G st.
Proof.
  induction e as [x | l IHl r IHr | x e1 IH1 e2 IH2 |
                  x body IHbody | c];
    intros G st fresh;
    unfold observe_checked_W;
    simpl W_exec.
  - cbn [W proj1_sig].
    match goal with
    | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
        let initial := constr:(exist _ (proj1_sig input)
          (proj1 (proj2_sig input))) in
        destruct (proj1_sig (first initial))
          as [[sigma st'] | failure] eqn:Hfirst
    end.
    + match goal with
      | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
          destruct (observe_bind_success first next input sigma st' Hfirst)
            as [next_pre Hbind]
      end.
      refine (eq_trans (f_equal observe_checked_state_result Hbind) _).
      cbn [proj1_sig] in Hfirst.
      match type of Hfirst with
      | proj1_sig (look_dep _ _ (exist _ _ ?pre)) = _ =>
          pose proof (look_dep_observe x G st pre) as Hlook
      end.
      pose proof (eq_trans (eq_sym Hfirst) Hlook) as Hlook_result.
      destruct (look_result_success x G st sigma st' Hlook_result)
        as [Hlookup Hstate].
      subst st'.
      rewrite Hlookup.
      match goal with
      | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
          pose proof
            (observe_bind_ret_W first
              (fun tau => (tau, ([] : substitution))) input) as Hinner
      end.
      refine (eq_trans Hinner _).
      match type of Hinner with
      | _ = observe_value_state_result _
          (proj1_sig (schm_inst_dep _ (exist _ _ ?pre))) =>
          pose proof (schm_inst_dep_observe sigma st pre) as Hschm
      end.
      refine (eq_trans
        (f_equal
          (observe_value_state_result
            (fun tau => (tau, ([] : substitution)))) Hschm) _).
      apply observe_instantiation_result.
    + match goal with
      | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
          pose proof
            (observe_bind_failure first next input failure Hfirst) as Hbind
      end.
      refine (eq_trans (f_equal observe_checked_state_result Hbind) _).
      cbn [observe_checked_state_result proj1_sig] in Hfirst |-.
      match type of Hfirst with
      | proj1_sig (look_dep _ _ (exist _ _ ?pre)) = _ =>
          pose proof (look_dep_observe x G st pre) as Hlook
      end.
      pose proof (eq_trans (eq_sym Hfirst) Hlook) as Hlook_result.
      pose proof (look_result_failure x G st failure Hlook_result)
        as Hlookup.
      rewrite Hlookup.
      reflexivity.
  - cbn [W proj1_sig].
    match goal with
    | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
        let initial := constr:(exist _ (proj1_sig input)
          (proj1 (proj2_sig input))) in
        destruct (proj1_sig (first initial))
          as [[[tau1 s1] st1] | failure] eqn:Hfirst
    end.
    + match goal with
      | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
          destruct
            (observe_bind_success first next input (tau1, s1) st1 Hfirst)
            as [next_pre Hbind]
      end.
      refine (eq_trans (f_equal observe_checked_state_result Hbind) _).
      cbn [proj1_sig] in Hfirst.
      match type of Hfirst with
      | proj1_sig (W l G (exist _ st ?pre)) = _ =>
          pose proof (IHl G st pre) as Hleft
      end.
      unfold observe_checked_W in Hleft.
      pose proof
        (eq_trans (eq_sym Hleft)
          (f_equal observe_checked_state_result Hfirst)) as Hleft_exec.
      rewrite Hleft_exec.
      cbn [fst snd].
      match goal with
      | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
          let initial := constr:(exist _ (proj1_sig input)
            (proj1 (proj2_sig input))) in
          destruct (proj1_sig (first initial))
            as [[[tau2 s2] st2] | failure2] eqn:Hsecond
      end.
      * match goal with
        | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
            destruct
              (observe_bind_success first next input (tau2, s2) st2 Hsecond)
              as [next_pre2 Hbind2]
        end.
        refine (eq_trans (f_equal observe_checked_state_result Hbind2) _).
        cbn [fst snd proj1_sig] in Hsecond |-.
        match type of Hsecond with
        | proj1_sig
            (W r (apply_subst_ctx s1 G) (exist _ st1 ?pre)) = _ =>
            pose proof (IHr (apply_subst_ctx s1 G) st1 pre) as Hright
        end.
        unfold observe_checked_W in Hright.
        pose proof
          (eq_trans (eq_sym Hright)
            (f_equal observe_checked_state_result Hsecond)) as Hright_exec.
        rewrite Hright_exec.
        match goal with
        | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
            let initial := constr:(exist _ (proj1_sig input)
              (proj1 (proj2_sig input))) in
            destruct (proj1_sig (first initial))
              as [[alpha st3] | impossible] eqn:Hfresh
        end.
        -- cbn [proj1_sig Infer.fresh] in Hfresh.
           inversion Hfresh; subst alpha st3.
           match goal with
           | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
               destruct
                 (observe_bind_success first next input st2 (S st2) Hfresh)
                 as [next_pre3 Hbind3]
           end.
           refine (eq_trans
             (f_equal observe_checked_state_result Hbind3) _).
           match goal with
           | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
               pose proof
                 (observe_bind_ret_W first
                   (fun s =>
                     (apply_subst s (var st2),
                      compose_subst s1 (compose_subst s2 s))) input)
                 as Hunify
           end.
           refine (eq_trans Hunify _).
           match type of Hunify with
           | _ = observe_value_state_result _
               (proj1_sig
                 (unify_exec_hoare ?left ?right (exist _ _ ?pre))) =>
               exact (observe_unify_exec_hoare
                 (fun s =>
                   (apply_subst s (var st2),
                    compose_subst s1 (compose_subst s2 s)))
                 left right (S st2) pre)
           end.
        -- cbn [proj1_sig Infer.fresh] in Hfresh.
           discriminate.
      * match goal with
        | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
            pose proof
              (observe_bind_failure first next input failure2 Hsecond)
              as Hbind2
        end.
        refine (eq_trans
          (f_equal observe_checked_state_result Hbind2) _).
        cbn [fst snd proj1_sig] in Hsecond |-.
        match type of Hsecond with
        | proj1_sig
            (W r (apply_subst_ctx s1 G) (exist _ st1 ?pre)) = _ =>
            pose proof (IHr (apply_subst_ctx s1 G) st1 pre) as Hright
        end.
        unfold observe_checked_W in Hright.
        pose proof
          (eq_trans (eq_sym Hright)
            (f_equal observe_checked_state_result Hsecond)) as Hright_exec.
        rewrite Hright_exec.
        reflexivity.
    + match goal with
      | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
          pose proof
            (observe_bind_failure first next input failure Hfirst) as Hbind
      end.
      refine (eq_trans (f_equal observe_checked_state_result Hbind) _).
      cbn [proj1_sig] in Hfirst |-.
      match type of Hfirst with
      | proj1_sig (W l G (exist _ st ?pre)) = _ =>
          pose proof (IHl G st pre) as Hleft
      end.
      unfold observe_checked_W in Hleft.
      pose proof
        (eq_trans (eq_sym Hleft)
          (f_equal observe_checked_state_result Hfirst)) as Hleft_exec.
      rewrite Hleft_exec.
      reflexivity.
  - cbn [W proj1_sig].
    match goal with
    | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
        let initial := constr:(exist _ (proj1_sig input)
          (proj1 (proj2_sig input))) in
        destruct (proj1_sig (first initial))
          as [[[tau1 s1] st1] | failure] eqn:Hfirst
    end.
    + match goal with
      | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
          destruct
            (observe_bind_success first next input (tau1, s1) st1 Hfirst)
            as [next_pre Hbind]
      end.
      refine (eq_trans (f_equal observe_checked_state_result Hbind) _).
      cbn [proj1_sig] in Hfirst.
      match type of Hfirst with
      | proj1_sig (W e1 G (exist _ st ?pre)) = _ =>
          pose proof (IH1 G st pre) as Hbound
      end.
      unfold observe_checked_W in Hbound.
      pose proof
        (eq_trans (eq_sym Hbound)
          (f_equal observe_checked_state_result Hfirst)) as Hbound_exec.
      rewrite Hbound_exec.
      cbn [fst snd].
      match goal with
      | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
          let initial := constr:(exist _ (proj1_sig input)
            (proj1 (proj2_sig input))) in
          destruct (proj1_sig (first initial))
            as [[[tau2 s2] st2] | failure2] eqn:Hsecond
      end.
      * match goal with
        | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
            destruct
              (observe_bind_success first next input (tau2, s2) st2 Hsecond)
              as [next_pre2 Hbind2]
        end.
        refine (eq_trans (f_equal observe_checked_state_result Hbind2) _).
        cbn [fst snd proj1_sig] in Hsecond |-.
        match type of Hsecond with
        | proj1_sig
            (W e2
              ((x, Gen.gen_ty tau1 (apply_subst_ctx s1 G)) ::
                apply_subst_ctx s1 G)
              (exist _ st1 ?pre)) = _ =>
            pose proof
              (IH2
                ((x, Gen.gen_ty tau1 (apply_subst_ctx s1 G)) ::
                  apply_subst_ctx s1 G)
                st1 pre) as Hbody
        end.
        unfold observe_checked_W in Hbody.
        pose proof
          (eq_trans (eq_sym Hbody)
            (f_equal observe_checked_state_result Hsecond)) as Hbody_exec.
        rewrite Hbody_exec.
        reflexivity.
      * match goal with
        | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
            pose proof
              (observe_bind_failure first next input failure2 Hsecond)
              as Hbind2
        end.
        refine (eq_trans
          (f_equal observe_checked_state_result Hbind2) _).
        cbn [fst snd proj1_sig] in Hsecond |-.
        match type of Hsecond with
        | proj1_sig
            (W e2
              ((x, Gen.gen_ty tau1 (apply_subst_ctx s1 G)) ::
                apply_subst_ctx s1 G)
              (exist _ st1 ?pre)) = _ =>
            pose proof
              (IH2
                ((x, Gen.gen_ty tau1 (apply_subst_ctx s1 G)) ::
                  apply_subst_ctx s1 G)
                st1 pre) as Hbody
        end.
        unfold observe_checked_W in Hbody.
        pose proof
          (eq_trans (eq_sym Hbody)
            (f_equal observe_checked_state_result Hsecond)) as Hbody_exec.
        rewrite Hbody_exec.
        reflexivity.
    + match goal with
      | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
          pose proof
            (observe_bind_failure first next input failure Hfirst) as Hbind
      end.
      refine (eq_trans (f_equal observe_checked_state_result Hbind) _).
      cbn [proj1_sig] in Hfirst |-.
      match type of Hfirst with
      | proj1_sig (W e1 G (exist _ st ?pre)) = _ =>
          pose proof (IH1 G st pre) as Hbound
      end.
      unfold observe_checked_W in Hbound.
      pose proof
        (eq_trans (eq_sym Hbound)
          (f_equal observe_checked_state_result Hfirst)) as Hbound_exec.
      rewrite Hbound_exec.
      reflexivity.
  - cbn [W proj1_sig].
    match goal with
    | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
        let initial := constr:(exist _ (proj1_sig input)
          (proj1 (proj2_sig input))) in
        destruct (proj1_sig (first initial))
          as [[alpha st1] | impossible] eqn:Hfresh
    end.
    + cbn [proj1_sig Infer.fresh] in Hfresh.
      inversion Hfresh; subst alpha st1.
      match goal with
      | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
          destruct
            (observe_bind_success first next input st (S st) Hfresh)
            as [next_pre Hbind]
      end.
      refine (eq_trans (f_equal observe_checked_state_result Hbind) _).
      match goal with
      | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
          let initial := constr:(exist _ (proj1_sig input)
            (proj1 (proj2_sig input))) in
          destruct (proj1_sig (first initial))
            as [[G' st2] | impossible2] eqn:Hadd
      end.
      * cbn [addFreshCtx ret proj1_sig] in Hadd.
        inversion Hadd; subst G' st2.
        match goal with
        | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
            destruct
              (observe_bind_success first next input
                ((x, Schemes.ty_to_schm (var st)) :: G) (S st) Hadd)
              as [next_pre2 Hbind2]
        end.
        refine (eq_trans (f_equal observe_checked_state_result Hbind2) _).
        cbn [Schemes.ty_to_schm] in *.
        match goal with
        | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
            let initial := constr:(exist _ (proj1_sig input)
              (proj1 (proj2_sig input))) in
            destruct (proj1_sig (first initial))
              as [[[tau s] st'] | failure] eqn:Hbody
        end.
        -- match goal with
           | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
               destruct
                 (observe_bind_success first next input (tau, s) st' Hbody)
                 as [next_pre3 Hbind3]
           end.
           refine (eq_trans
             (f_equal observe_checked_state_result Hbind3) _).
           cbn [fst snd proj1_sig] in Hbody |-.
           match type of Hbody with
           | proj1_sig
               (W body ((x, Schemes.sc_var st) :: G)
                 (exist _ (S st) ?pre)) = _ =>
               pose proof
                 (IHbody ((x, Schemes.sc_var st) :: G) (S st) pre)
                 as Hrecursive
           end.
           unfold observe_checked_W in Hrecursive.
           pose proof
             (eq_trans (eq_sym Hrecursive)
               (f_equal observe_checked_state_result Hbody)) as Hbody_exec.
           rewrite Hbody_exec.
           reflexivity.
        -- match goal with
           | |- context [proj1_sig ((bind ?first ?next) ?input)] =>
               pose proof
                 (observe_bind_failure first next input failure Hbody)
                 as Hbind3
           end.
           refine (eq_trans
             (f_equal observe_checked_state_result Hbind3) _).
           cbn [proj1_sig] in Hbody |-.
           match type of Hbody with
           | proj1_sig
               (W body ((x, Schemes.sc_var st) :: G)
                 (exist _ (S st) ?pre)) = _ =>
               pose proof
                 (IHbody ((x, Schemes.sc_var st) :: G) (S st) pre)
                 as Hrecursive
           end.
           unfold observe_checked_W in Hrecursive.
           pose proof
             (eq_trans (eq_sym Hrecursive)
               (f_equal observe_checked_state_result Hbody)) as Hbody_exec.
           rewrite Hbody_exec.
           reflexivity.
      * cbn [addFreshCtx ret proj1_sig] in Hadd.
        discriminate.
    + cbn [Infer.fresh proj1_sig] in Hfresh.
      discriminate.
  - reflexivity.
Qed.

(** Erase the final state after correspondence has established it. *)
Definition erase_w_state_result (result : w_state_result) : w_result :=
  match result with
  | w_state_success tau s _ => inferred tau s
  | w_state_rejected => inference_rejected
  end.

Definition observe_checked_result
    (result : (ty * substitution + InferFailure)%type) : w_result :=
  match result with
  | inl (tau, s) => inferred tau s
  | inr _ => inference_rejected
  end.

Lemma observe_runW : forall e G,
  observe_checked_result (runW e G) =
  erase_w_state_result
    (observe_checked_W e G
      (proj1_sig (computeInitialState G))
      (proj2_sig (computeInitialState G))).
Proof.
  intros e G.
  destruct (computeInitialState G) as [st fresh] eqn:Hinitial.
  cbn [proj1_sig proj2_sig].
  unfold runW, observe_checked_result, erase_w_state_result,
    observe_checked_W, observe_checked_state_result.
  rewrite Hinitial.
  destruct (W e G (exist _ st fresh)) as [result Hresult].
  destruct result as [[[tau s] final_state] | failure]; reflexivity.
Qed.

(** Public bridge: after erasing the checked failure certificate, [runW]
    and the extracted proof-free reducer are extensionally identical. *)
Theorem runW_exec_checked_correspondence : forall e G,
  observe_checked_result (runW e G) = runW_exec e G.
Proof.
  intros e G.
  rewrite observe_runW.
  rewrite W_exec_checked_correspondence.
  unfold runW_exec.
  rewrite computeInitialState_observe.
  reflexivity.
Qed.

Corollary runW_exec_success_iff_checked_success : forall e G tau s,
  runW_exec e G = inferred tau s <->
  runW e G = inl (tau, s).
Proof.
  intros e G tau s.
  pose proof (runW_exec_checked_correspondence e G) as Hbridge.
  destruct (runW e G) as [[tau' s'] | failure] eqn:Hchecked;
    cbn [observe_checked_result] in Hbridge.
  - split; intro Hresult.
    + rewrite <- Hbridge in Hresult.
      inversion Hresult; subst.
      reflexivity.
    + inversion Hresult; subst.
      symmetry.
      exact Hbridge.
  - split; intro Hresult.
    + rewrite <- Hbridge in Hresult.
      discriminate.
    + discriminate.
Qed.

Corollary runW_exec_rejected_iff_checked_rejected : forall e G,
  runW_exec e G = inference_rejected <->
  exists failure, runW e G = inr failure.
Proof.
  intros e G.
  pose proof (runW_exec_checked_correspondence e G) as Hbridge.
  destruct (runW e G) as [[tau s] | failure] eqn:Hchecked;
    cbn [observe_checked_result] in Hbridge.
  - split; intro Hresult.
    + rewrite <- Hbridge in Hresult.
      discriminate.
    + destruct Hresult as [failure Hfailure].
      discriminate.
  - split; intro Hresult.
    + exists failure.
      reflexivity.
    + symmetry.
      exact Hbridge.
Qed.

(** Thus the checked wrapper inherits the executable core's proved
    rejection contract. *)
Corollary runW_checked_rejected_no_typing : forall e G failure,
  runW e G = inr failure ->
  forall tau, ~ has_type G e tau.
Proof.
  intros e G failure Hchecked.
  apply runW_exec_rejected_no_typing.
  apply (proj2 (runW_exec_rejected_iff_checked_rejected e G)).
  now exists failure.
Qed.

(** Conversely, a successful executable result carries the full dependent
    soundness/completeness contract already established for [runW]. *)
Corollary runW_exec_success_contract : forall e G tau s,
  runW_exec e G = inferred tau s ->
  runW_success_spec e G tau s.
Proof.
  intros e G tau s Hexec.
  apply runW_success_contract.
  apply (proj1 (runW_exec_success_iff_checked_success e G tau s)).
  exact Hexec.
Qed.
