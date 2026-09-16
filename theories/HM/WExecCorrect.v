(** * Correctness of every rejection produced by the executable W core *)

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

From SystemF.HM Require Import WExec Unify.
From SystemF.HM.W Require Import
  Context Gen Infer MoreGeneral NewTypeVariable Subst SubstSchm Typing.

(** The successful half of the invariant is deliberately strong.  In
    particular, [completeness] is what lets a later failing branch transport
    an arbitrary declarative typing through the substitutions already
    computed by earlier branches. *)
Definition w_success_spec
    (e : hmterm) (G : hmctx) (st : id)
    (tau : ty) (s : substitution) (st' : id) : Prop :=
  st <= st' /\
  new_tv_subst s st' /\
  new_tv_ty tau st' /\
  new_tv_ctx (apply_subst_ctx s G) st' /\
  completeness e G tau s st.

Definition w_result_spec
    (e : hmterm) (G : hmctx) (st : id)
    (result : w_state_result) : Prop :=
  match result with
  | w_state_success tau s st' => w_success_spec e G st tau s st'
  | w_state_rejected =>
      forall phi tau, ~ has_type (apply_subst_ctx phi G) e tau
  end.

Lemma length_compute_inst_subst : forall st count,
    length (compute_inst_subst st count) = count.
Proof.
  intros st count.
  revert st.
  induction count; intros st; simpl; [reflexivity |].
  now rewrite IHcount.
Qed.

Lemma computed_instantiation_succeeds : forall st sigma,
    exists tau,
      apply_inst_subst
        (compute_inst_subst st (Schemes.max_gen_vars sigma)) sigma =
      Some tau.
Proof.
  intros st sigma.
  apply apply_inst_subst_succeeds.
  rewrite length_compute_inst_subst.
  apply le_n.
Qed.

Lemma missing_variable_no_typing : forall x G,
    in_ctx x G = None ->
    forall phi tau,
      ~ has_type (apply_subst_ctx phi G) (var_t x) tau.
Proof.
  intros x G Hmissing phi tau Htyping.
  inversion Htyping; subst.
  destruct (assoc_subst_exists G x phi H0)
    as [sigma' [Hlookup Heq]].
  rewrite Hmissing in Hlookup.
  discriminate.
Qed.

Theorem W_exec_correct : forall e G st,
    new_tv_ctx G st ->
    w_result_spec e G st (W_exec e G st).
Proof.
  induction e as [x | l IHl r IHr | x e1 IH1 e2 IH2 |
                  x body IHbody | c];
    intros G st Hfresh; simpl W_exec.
  - destruct (in_ctx x G) as [sigma |] eqn:Hlookup.
    + destruct (apply_inst_subst
          (compute_inst_subst st (Schemes.max_gen_vars sigma)) sigma)
        as [tau |] eqn:Hinst.
      * unfold w_result_spec, w_success_spec.
        repeat split.
        -- lia.
        -- simpl. discriminate.
        -- eapply new_tv_schm_to_new_tv_ty; [| exact Hinst].
           eapply new_tv_ctx_implies_new_tv_schm; eauto.
        -- rewrite apply_subst_ctx_nil.
           now apply new_tv_ctx_plus.
        -- unfold completeness.
           intros tau' phi Htyping.
           inversion Htyping; subst.
           destruct (assoc_subst_exists G x phi H0)
             as [sigma' [Hlookup' Hsigma]].
           rewrite Hlookup in Hlookup'. inversion Hlookup'; subst sigma'.
           unfold is_schm_instance in H2.
           destruct H2 as [is Hinstance].
           exists (compute_subst st is ++ phi).
           split.
           ++ eapply new_tv_schm_compute_inst_subst
                with (sigma := sigma)
                     (p := Schemes.max_gen_vars sigma); eauto.
              rewrite <- Hsigma. exact Hinstance.
           ++ intros y Hy.
              simpl.
              symmetry.
              apply find_subst_some_apply_app_compute_subst.
              exact Hy.
      * exfalso.
        destruct (computed_instantiation_succeeds st sigma)
          as [tau Hsome].
        rewrite Hinst in Hsome. discriminate.
    + unfold w_result_spec.
      now apply missing_variable_no_typing.

  - specialize (IHl G st Hfresh).
    destruct (W_exec l G st) as [tau1 s1 st1 |] eqn:Hwl;
      simpl in IHl |-.
    + unfold w_success_spec in IHl.
      destruct IHl as [Hst1 [Hs1 [Htau1 [HG1 HCl]]]].
      specialize (IHr (apply_subst_ctx s1 G) st1 HG1).
      destruct (W_exec r (apply_subst_ctx s1 G) st1)
        as [tau2 s2 st2 |] eqn:Hwr;
        simpl in IHr |-.
      * unfold w_success_spec in IHr.
        destruct IHr as [Hst2 [Hs2 [Htau2 [HG2 HCr]]]].
        destruct (unify_exec (apply_subst s2 tau1)
                    (arrow tau2 (var st2))) as [su |] eqn:Hu;
          simpl.
        -- pose proof (unify_exec_success_principal _ _ _ Hu)
             as [_ Huprincipal].
           assert (Htau1s2 : new_tv_ty (apply_subst s2 tau1) st2).
           { apply new_tv_apply_subst_ty.
             - eapply new_tv_ty_trans_le; eauto.
             - exact Hs2. }
           assert (Hinputs :
             new_tv_ty (apply_subst s2 tau1) (S st2) /\
             new_tv_ty (arrow tau2 (var st2)) (S st2)).
           { split.
             - eapply new_tv_ty_trans_le; eauto.
             - constructor; eauto. }
           assert (Hsu : new_tv_subst su (S st2)).
           { eapply unify_exec_preserves_freshness; eauto. }
           assert (Hsall :
             new_tv_subst
               (comp_subst s1 (comp_subst s2 su)) (S st2)).
           { apply new_tv_comp_subst.
             - eapply new_tv_subst_trans; eauto.
             - apply new_tv_comp_subst.
               + eapply new_tv_subst_trans; eauto.
               + exact Hsu. }
           unfold w_success_spec.
           repeat split.
           ++ lia.
           ++ inversion Hsall; assumption.
           ++ change (new_tv_ty (apply_subst su (var st2)) (S st2)).
              apply new_tv_apply_subst_ty; [constructor; lia | exact Hsu].
           ++ apply new_tv_s_ctx.
              ** eapply new_tv_ctx_trans; eauto. lia.
              ** exact Hsall.
           ++ unfold completeness.
              intros tauout phi Htyping.
              inversion Htyping; subst.
              rename tau into tau_arg.
              rename H2 into HTleft.
              rename H4 into HTright.
              destruct (HCl _ _ HTleft)
                as [psi1 [Hpsi1 Hfactor1]].
              assert (Hright_for_W :
                has_type
                  (apply_subst_ctx psi1 (apply_subst_ctx s1 G))
                  r tau_arg).
              { erewrite <- new_tv_comp_subst_ctx; eauto. }
              destruct (HCr _ _ Hright_for_W)
                as [psi2 [Hpsi2 Hfactor2]].
              set (candidate := (st2, tauout) :: psi2).
              assert (Hcandidate :
                is_unifier (apply_subst s2 tau1)
                  (arrow tau2 (var st2)) candidate).
              { unfold is_unifier, candidate.
                simpl.
                destruct (eq_id_dec st2 st2) as [_ | Hneq];
                  [|contradiction].
                rewrite add_subst_new_tv_ty.
                2: exact Htau1s2.
                rewrite add_subst_new_tv_ty by exact Htau2.
                rewrite <- Hpsi2.
                erewrite <- (@new_tv_comp_subst_type
                  psi1 s2 psi2 st1 tau1); eauto. }
              destruct (Huprincipal candidate Hcandidate)
                as [residual Hresidual].
              exists residual.
              split.
              ** specialize (Hresidual st2).
                 unfold candidate in Hresidual.
                 simpl in Hresidual.
                 destruct (eq_id_dec st2 st2) as [_ | Hneq];
                   [|contradiction].
                 change (tauout =
                   apply_subst (comp_subst su residual) (var st2))
                   in Hresidual.
                 rewrite apply_compose_equiv in Hresidual.
                 exact Hresidual.
              ** intros y Hy.
                 repeat rewrite apply_compose_equiv.
                 rewrite <- apply_compose_equiv.
                 rewrite <- (@substitution_equiv_ty candidate
                   (comp_subst su residual) Hresidual
                   (apply_subst s2 (apply_subst s1 (var y)))).
                 unfold candidate.
                 rewrite add_subst_new_tv_ty.
                 --- rewrite (Hfactor1 y Hy).
                     eapply (@new_tv_comp_subst_type
                       psi1 s2 psi2 st1 (apply_subst s1 (var y))).
                     +++ intros z Hz. apply Hfactor2. exact Hz.
                     +++ apply new_tv_apply_subst_ty.
                         *** constructor. lia.
                         *** exact Hs1.
                 --- apply new_tv_apply_subst_ty.
                     +++ eapply new_tv_ty_trans_le.
                         *** apply new_tv_apply_subst_ty.
                             ---- constructor.
                                  exact (Nat.lt_le_trans _ _ _ Hy Hst1).
                             ---- exact Hs1.
                         *** exact Hst2.
                     +++ exact Hs2.
        -- intros phi tauout Htyping.
           inversion Htyping; subst.
           rename tau into tau_arg.
           rename H2 into HTleft.
           rename H4 into HTright.
           destruct (HCl _ _ HTleft)
             as [psi1 [Hpsi1 Hfactor1]].
           assert (Hright_for_W :
             has_type (apply_subst_ctx psi1 (apply_subst_ctx s1 G))
               r tau_arg).
           { erewrite <- new_tv_comp_subst_ctx; eauto. }
           destruct (HCr _ _ Hright_for_W)
             as [psi2 [Hpsi2 Hfactor2]].
           set (candidate := (st2, tauout) :: psi2).
           apply (unify_exec_rejected_no_unifier _ _ Hu candidate).
           unfold is_unifier, candidate.
           simpl.
           destruct (eq_id_dec st2 st2) as [_ | Hneq];
             [|contradiction].
           rewrite add_subst_new_tv_ty.
           2: apply new_tv_apply_subst_ty;
              [eapply new_tv_ty_trans_le; eauto | exact Hs2].
           rewrite add_subst_new_tv_ty by exact Htau2.
           rewrite <- Hpsi2.
           erewrite <- (@new_tv_comp_subst_type
             psi1 s2 psi2 st1 tau1); eauto.
      * unfold w_result_spec in IHr |-.
        intros phi tauout Htyping.
        inversion Htyping; subst.
        rename tau into tau_arg.
        rename H2 into HTleft.
        rename H4 into HTright.
        destruct (HCl _ _ HTleft) as [psi1 [Hpsi1 Hfactor1]].
        apply (IHr psi1 tau_arg).
        erewrite <- new_tv_comp_subst_ctx; eauto.
    + unfold w_result_spec in IHl |-.
      intros phi tauout Htyping.
      inversion Htyping; subst.
      eapply IHl; eauto.

  - specialize (IH1 G st Hfresh).
    destruct (W_exec e1 G st) as [tau1 s1 st1 |] eqn:Hw1;
      simpl in IH1 |-.
    + unfold w_success_spec in IH1.
      destruct IH1 as [Hst1 [Hs1 [Htau1 [HG1 HC1]]]].
      assert (HGbody : new_tv_ctx
        ((x, Gen.gen_ty tau1 (apply_subst_ctx s1 G)) ::
         apply_subst_ctx s1 G) st1).
      { constructor; [exact HG1 |].
        now apply new_tv_gen_ty. }
      specialize (IH2 _ st1 HGbody).
      destruct (W_exec e2
        ((x, Gen.gen_ty tau1 (apply_subst_ctx s1 G)) ::
         apply_subst_ctx s1 G) st1)
        as [tau2 s2 st2 |] eqn:Hw2;
        simpl in IH2 |-.
      * unfold w_success_spec in IH2.
        destruct IH2 as [Hst2 [Hs2 [Htau2 [HG2 HC2]]]].
        assert (Hsall : new_tv_subst (comp_subst s1 s2) st2).
        { apply new_tv_comp_subst.
          - eapply new_tv_subst_trans; eauto.
          - exact Hs2. }
        unfold w_success_spec.
        repeat split.
        -- lia.
        -- inversion Hsall; assumption.
        -- exact Htau2.
        -- apply new_tv_s_ctx.
           ++ eapply new_tv_ctx_trans; eauto. lia.
           ++ exact Hsall.
        -- unfold completeness.
           intros tauout phi Htyping.
           inversion Htyping; subst.
           rename tau into tau1'.
           rename H4 into HT1'.
           rename H5 into HT2'.
           destruct (HC1 _ _ HT1') as [psi1 [Hpsi1 Hfactor1]].
           assert (HT2_for_W :
             has_type
               (apply_subst_ctx psi1
                 ((x, Gen.gen_ty tau1 (apply_subst_ctx s1 G)) ::
                  apply_subst_ctx s1 G))
               e2 tauout).
           { rewrite subst_add_type_scheme.
             eapply typing_in_a_more_general_ctx with
               (G2 :=
                 (x, Gen.gen_ty (apply_subst psi1 tau1)
                      (apply_subst_ctx psi1 (apply_subst_ctx s1 G))) ::
                 apply_subst_ctx psi1 (apply_subst_ctx s1 G)).
             - apply more_general_ctx_cons.
               + apply more_general_ctx_refl.
               + apply more_general_gen_ty_before_apply_subst.
             - rewrite <- Hpsi1.
               erewrite <- new_tv_comp_subst_ctx; eauto. }
           destruct (HC2 _ _ HT2_for_W)
             as [psi2 [Hpsi2 Hfactor2]].
           exists psi2.
           split; [exact Hpsi2 |].
           intros y Hy.
           rewrite apply_compose_equiv.
           rewrite (Hfactor1 y Hy).
           eapply (@new_tv_comp_subst_type psi1 s2 psi2 st1
             (apply_subst s1 (var y))).
           ++ intros z Hz. apply Hfactor2. exact Hz.
           ++ apply new_tv_apply_subst_ty.
              ** constructor. lia.
              ** exact Hs1.
      * unfold w_result_spec in IH2 |-.
        intros phi tauout Htyping.
        inversion Htyping; subst.
        rename tau into tau1'.
        rename H4 into HT1'.
        rename H5 into HT2'.
        destruct (HC1 _ _ HT1') as [psi1 [Hpsi1 Hfactor1]].
        apply (IH2 psi1 tauout).
        eapply typing_in_a_more_general_ctx with
          (G2 :=
            (x, Gen.gen_ty (apply_subst psi1 tau1)
                 (apply_subst_ctx psi1 (apply_subst_ctx s1 G))) ::
            apply_subst_ctx psi1 (apply_subst_ctx s1 G)).
        -- apply more_general_ctx_cons.
           ++ apply more_general_ctx_refl.
           ++ apply more_general_gen_ty_before_apply_subst.
        -- rewrite <- Hpsi1.
           erewrite <- new_tv_comp_subst_ctx; eauto.
    + unfold w_result_spec in IH1 |-.
      intros phi tauout Htyping.
      inversion Htyping; subst.
      eapply IH1; eauto.

  - assert (HGbody : new_tv_ctx ((x, Schemes.sc_var st) :: G) (S st)).
    { constructor.
      - apply new_tv_ctx_Succ. exact Hfresh.
      - constructor. lia. }
    specialize (IHbody _ (S st) HGbody).
    destruct (W_exec body ((x, Schemes.sc_var st) :: G) (S st))
      as [tau s st' |] eqn:Hw;
      simpl in IHbody |-.
    + unfold w_success_spec in IHbody.
      destruct IHbody as [Hst' [Hs [Htau [HG' HC]]]].
      unfold w_success_spec.
      repeat split.
      * lia.
      * inversion Hs; assumption.
      * change (new_tv_ty (arrow (apply_subst s (var st)) tau) st').
        constructor.
        -- apply new_tv_apply_subst_ty.
           ++ constructor. lia.
           ++ exact Hs.
        -- exact Htau.
      * inversion HG'; subst. assumption.
      * unfold completeness.
        intros tauout phi Htyping.
        inversion Htyping; subst.
        assert (Hbody :
          has_type
            (apply_subst_ctx ((st, tau0) :: phi)
              ((x, Schemes.sc_var st) :: G)) body tau').
        { rewrite add_subst_add_ctx by exact Hfresh.
          exact H3. }
        destruct (HC tau' ((st, tau0) :: phi) Hbody)
          as [residual [Hresult Hfactor]].
        exists residual.
        split.
        -- change (arrow tau0 tau' =
             apply_subst residual
               (arrow (apply_subst s (var st)) tau)).
           simpl.
           rewrite Hresult.
           specialize (Hfactor st (Nat.lt_succ_diag_r st)).
           simpl in Hfactor.
           destruct (eq_id_dec st st) as [_ | Hneq]; [|contradiction].
           now rewrite Hfactor.
        -- intros y Hy.
           rewrite <- (Hfactor y) by lia.
           symmetry.
           apply add_subst_rewrite_for_unmodified_id.
           lia.
    + unfold w_result_spec in IHbody |-.
      intros phi tauout Htyping.
      inversion Htyping; subst.
      apply (IHbody ((st, tau) :: phi) tau').
      change (has_type
        (apply_subst_ctx ((st, tau) :: phi)
          ((x, Schemes.sc_var st) :: G)) body tau').
      rewrite add_subst_add_ctx by exact Hfresh.
      exact H3.

  - unfold w_result_spec, w_success_spec.
    repeat split.
    + lia.
    + simpl. discriminate.
    + constructor.
    + rewrite apply_subst_ctx_nil. exact Hfresh.
    + unfold completeness.
      intros tau' phi Htyping.
      inversion Htyping; subst.
      exists phi.
      split; [reflexivity |].
      intros y Hy.
      now rewrite apply_subst_nil.
Qed.

Lemma initial_state_exec_fresh : forall G,
    new_tv_ctx G (initial_state_exec G).
Proof.
  induction G as [| [x sigma] G IH].
  - simpl. constructor.
  - simpl.
    destruct (Nat.ltb (Schemes.max_vars_schm sigma)
      (initial_state_exec G)) eqn:Hlt.
    + constructor.
      * exact IH.
      * eapply new_tv_schm_trans.
        -- apply new_tv_schm_max_vars.
        -- apply Nat.ltb_lt in Hlt. lia.
    + constructor.
      * eapply new_tv_ctx_trans; eauto.
        apply Nat.ltb_ge in Hlt. lia.
      * apply new_tv_schm_max_vars.
Qed.

(** Every rejection is semantic: it rules out every typing, even after an
    arbitrary substitution of the input context. *)
Theorem W_exec_rejected_no_typing : forall e G st,
    new_tv_ctx G st ->
    W_exec e G st = w_state_rejected ->
    forall phi tau,
      ~ has_type (apply_subst_ctx phi G) e tau.
Proof.
  intros e G st Hfresh Hrejected.
  pose proof (W_exec_correct e G st Hfresh) as Hcorrect.
  rewrite Hrejected in Hcorrect.
  exact Hcorrect.
Qed.

Theorem runW_exec_rejected_no_typing : forall e G,
    runW_exec e G = inference_rejected ->
    forall tau, ~ has_type G e tau.
Proof.
  intros e G Hrun tau Htyping.
  unfold runW_exec in Hrun.
  destruct (W_exec e G (initial_state_exec G))
    as [inferred_ty inferred_subst final_state |] eqn:Hw;
    try discriminate.
  pose proof
    (W_exec_rejected_no_typing e G (initial_state_exec G)
      (initial_state_exec_fresh G) Hw [] tau) as Hnot.
  rewrite apply_subst_ctx_nil in Hnot.
  exact (Hnot Htyping).
Qed.

Print Assumptions W_exec_rejected_no_typing.
Print Assumptions runW_exec_rejected_no_typing.
