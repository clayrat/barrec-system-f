(** * Correctness of the proof-free unification core *)

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

From SystemF.HM Require Import UnifySpec UnifyFailure UnifyExec.

Definition equation_unifier (s : substitution) (e : equation) : Prop :=
  apply_subst s (fst e) = apply_subst s (snd e).

Definition equations_unifier
    (equations : list equation) (s : substitution) : Prop :=
  Forall (equation_unifier s) equations.

Definition scan_result_spec
    (equations : list equation) (result : scan_result) : Prop :=
  match result with
  | equations_solved => forall s, equations_unifier equations s
  | equations_failed => forall s, ~ equations_unifier equations s
  | equation_binding v t rest =>
      t <> var v /\ ~ occurs v t /\
      forall s,
        equations_unifier equations s <->
        is_unifier (var v) t s /\ equations_unifier rest s
  | scan_fuel_exhausted => False
  end.

Lemma equations_unifier_equal_head : forall t rest s,
    equations_unifier ((t, t) :: rest) s <->
    equations_unifier rest s.
Proof.
  intros. split; intro H.
  - inversion H. assumption.
  - constructor; [reflexivity | assumption].
Qed.

Lemma equations_unifier_arrow_head : forall l r l' r' rest s,
    equations_unifier ((arrow l r, arrow l' r') :: rest) s <->
    equations_unifier ((l, l') :: (r, r') :: rest) s.
Proof.
  intros. split; intro H.
  - inversion H as [| equation equations Hhead Hrest]; subst.
    unfold equation_unifier in Hhead. simpl in Hhead.
    inversion Hhead.
    repeat constructor; assumption.
  - inversion H as [| equation equations Hl Htail]; subst.
    inversion Htail as [| equation equations Hr Hrest]; subst.
    constructor; [|assumption].
    unfold equation_unifier in *. simpl in *.
    now rewrite Hl, Hr.
Qed.

Lemma equations_size_arrow_decompose : forall l r l' r' rest,
    equations_size ((l, l') :: (r, r') :: rest) <
    equations_size ((arrow l r, arrow l' r') :: rest).
Proof.
  intros.
  simpl.
  unfold equation_size.
  cbn.
  lia.
Qed.

Lemma scan_result_spec_equal_head : forall t rest result,
    scan_result_spec rest result ->
    scan_result_spec ((t, t) :: rest) result.
Proof.
  intros t rest result Hspec.
  destruct result; simpl in *.
  - intros. apply equations_unifier_equal_head. apply Hspec.
  - intros s Hfull. apply (Hspec s).
    apply equations_unifier_equal_head in Hfull. exact Hfull.
  - destruct Hspec as [Hneq [Hocc Hspec]].
    split; [exact Hneq |].
    split; [exact Hocc |].
    intros theta. rewrite equations_unifier_equal_head. apply Hspec.
  - tauto.
Qed.

Lemma scan_result_spec_arrow_head : forall l r l' r' rest result,
    scan_result_spec ((l, l') :: (r, r') :: rest) result ->
    scan_result_spec ((arrow l r, arrow l' r') :: rest) result.
Proof.
  intros l r l' r' rest result Hspec.
  destruct result; simpl in *.
  - intros. apply equations_unifier_arrow_head. apply Hspec.
  - intros s Hfull. apply (Hspec s).
    apply equations_unifier_arrow_head in Hfull. exact Hfull.
  - destruct Hspec as [Hneq [Hocc Hspec]].
    split; [exact Hneq |].
    split; [exact Hocc |].
    intros theta. rewrite equations_unifier_arrow_head. apply Hspec.
  - contradiction.
Qed.

Lemma scan_equations_correct : forall fuel equations,
    equations_size equations <= fuel ->
    scan_result_spec equations (scan_equations fuel equations).
Proof.
  induction fuel as [| fuel IH]; intros equations Hfuel.
  - destruct equations as [| equation rest]; simpl in *.
    + intros s. constructor.
    + lia.
  - destruct equations as [| [t1 t2] rest].
    + simpl. intros s. constructor.
    + simpl scan_equations.
      destruct (eq_ty_dec t1 t2) as [Heq | Hneq].
      * subst t2. apply scan_result_spec_equal_head.
        apply IH. simpl in Hfuel. lia.
      * destruct t1 as [v | c | l r];
          destruct t2 as [v' | c' | l' r']; cbn -[occurs_dec].
        -- destruct (occurs_dec v (var v')) as [Hocc | Hocc].
           ++ intros s Hunifier.
              inversion Hunifier as [| equation equations Hhead Hrest]; subst.
              apply (@unify_failure_no_unifier
                (var v) (var v')
                (occ_fail (not_eq_sym Hneq) Hocc) s).
              exact Hhead.
           ++ split; [exact (not_eq_sym Hneq) |].
              split; [exact Hocc |].
              intros s. split; intro H.
              { inversion H; subst. split; assumption. }
              { destruct H. constructor; assumption. }
        -- destruct (occurs_dec v (con c')) as [Hocc | Hocc].
           ++ contradiction.
           ++ split; [exact (not_eq_sym Hneq) |].
              split; [exact Hocc |].
              intros s. split; intro H.
              { inversion H; subst. split; assumption. }
              { destruct H. constructor; assumption. }
        -- destruct (occurs_dec v (arrow l' r')) as [Hocc | Hocc].
           ++ intros s Hunifier.
              inversion Hunifier as [| equation equations Hhead Hrest]; subst.
              apply (@unify_failure_no_unifier
                (var v) (arrow l' r')
                (occ_fail (not_eq_sym Hneq) Hocc) s).
              exact Hhead.
           ++ split; [exact (not_eq_sym Hneq) |].
              split; [exact Hocc |].
              intros s. split; intro H.
              { inversion H; subst. split; assumption. }
              { destruct H. constructor; assumption. }
        -- destruct (occurs_dec v' (con c)) as [Hocc | Hocc].
           ++ contradiction.
           ++ split; [exact Hneq |].
              split; [exact Hocc |].
              intros s. split; intro H.
              { inversion H; subst. split; [symmetry; assumption | assumption]. }
              { destruct H. constructor; [symmetry; assumption | assumption]. }
        -- intros s Hunifier.
           inversion Hunifier as [| equation equations Hhead Hrest]; subst.
           unfold equation_unifier in Hhead. simpl in Hhead.
           inversion Hhead. contradiction.
        -- intros s Hunifier.
           inversion Hunifier as [| equation equations Hhead Hrest]; subst.
           discriminate.
        -- destruct (occurs_dec v' (arrow l r)) as [Hocc | Hocc].
           ++ intros s Hunifier.
              inversion Hunifier as [| equation equations Hhead Hrest]; subst.
              apply (@unify_failure_no_unifier
                (arrow l r) (var v')
                (occ_fail' Hneq Hocc) s).
              exact Hhead.
           ++ split; [exact Hneq |].
              split; [exact Hocc |].
              intros s. split; intro H.
              { inversion H; subst. split; [symmetry; assumption | assumption]. }
              { destruct H. constructor; [symmetry; assumption | assumption]. }
        -- intros s Hunifier.
           inversion Hunifier as [| equation equations Hhead Hrest]; subst.
           discriminate.
        -- apply scan_result_spec_arrow_head.
           apply IH.
           pose proof
             (equations_size_arrow_decompose l r l' r' rest) as Hsize.
           pose proof (Nat.lt_le_trans _ _ _ Hsize Hfuel) as Hbound.
           exact (proj1 (Nat.lt_succ_r _ _) Hbound).
Qed.

(** ** Scope invariant for the structural fuel *)

Definition ty_scoped (variables : list id) (t : ty) : Prop :=
  forall v, occurs v t -> In v variables.

Definition equation_scoped (variables : list id) (e : equation) : Prop :=
  ty_scoped variables (fst e) /\ ty_scoped variables (snd e).

Definition equations_scoped
    (variables : list id) (equations : list equation) : Prop :=
  Forall (equation_scoped variables) equations.

Lemma occurs_in_ids_ty : forall v t,
    occurs v t -> In v (ids_ty t).
Proof.
  intros v t. induction t as [i | c | l IHl r IHr]; simpl.
  - destruct (eq_id_dec i v); [intros; subst; auto | contradiction].
  - contradiction.
  - intros [Hocc | Hocc]; apply in_or_app;
      [left; apply IHl | right; apply IHr]; assumption.
Qed.

Lemma ty_scoped_initial_left : forall t1 t2,
    ty_scoped (initial_variables t1 t2) t1.
Proof.
  intros t1 t2 v Hocc.
  unfold initial_variables.
  apply nodup_In.
  apply in_or_app. left.
  now apply occurs_in_ids_ty.
Qed.

Lemma ty_scoped_initial_right : forall t1 t2,
    ty_scoped (initial_variables t1 t2) t2.
Proof.
  intros t1 t2 v Hocc.
  unfold initial_variables.
  apply nodup_In.
  apply in_or_app. right.
  now apply occurs_in_ids_ty.
Qed.

Lemma occurs_apply_subst_single : forall x v t u,
    occurs x (apply_subst [(v, t)] u) ->
    occurs x u \/ occurs x t.
Proof.
  intros x v t u.
  induction u as [i | c | l IHl r IHr]; simpl.
  - destruct (eq_id_dec v i) as [Heq | Hneq].
    + subst i. intro Hocc. right. exact Hocc.
    + intro Hocc. left. exact Hocc.
  - contradiction.
  - intros [Hocc | Hocc].
    + destruct (IHl Hocc); [left; left | right]; assumption.
    + destruct (IHr Hocc); [left; right | right]; assumption.
Qed.

Lemma subst_single_removes_self : forall v t u,
    ~ occurs v t -> ~ occurs v (apply_subst [(v, t)] u).
Proof.
  intros v t u Hnot.
  induction u as [i | c | l IHl r IHr]; simpl.
  - destruct (eq_id_dec v i) as [Heq | Hneq].
    + subst i. exact Hnot.
    + unfold occurs.
      destruct (eq_id_dec i v); [congruence | tauto].
  - tauto.
  - intros [Hocc | Hocc]; [now apply IHl | now apply IHr].
Qed.

Lemma ty_scoped_subst_single_remove : forall variables v t u,
    ty_scoped variables t ->
    ty_scoped variables u ->
    ~ occurs v t ->
    ty_scoped (remove eq_id_dec v variables)
      (apply_subst [(v, t)] u).
Proof.
  intros variables v t u Ht Hu Hnot x Hocc.
  destruct (occurs_apply_subst_single x v t u Hocc) as [Hu' | Ht'].
  - apply in_in_remove; [|now apply Hu].
    intro Heq; subst x.
    exact (subst_single_removes_self v t u Hnot Hocc).
  - apply in_in_remove; [|now apply Ht].
    intro Heq; subst x. contradiction.
Qed.

Lemma equations_scoped_map_subst_remove : forall variables v t equations,
    ty_scoped variables t ->
    equations_scoped variables equations ->
    ~ occurs v t ->
    equations_scoped (remove eq_id_dec v variables)
      (map (apply_subst_equation [(v, t)]) equations).
Proof.
  intros variables v t equations Ht Hequations Hnot.
  induction Hequations as [| [left right] rest Hhead Hrest IH]; simpl.
  - constructor.
  - constructor.
    + destruct Hhead as [Hleft Hright]. split;
        apply ty_scoped_subst_single_remove; assumption.
    + apply IH.
Qed.

Lemma occurs_same_variable : forall v, occurs v (var v).
Proof.
  intros v. simpl.
  destruct (eq_id_dec v v); [constructor | contradiction].
Qed.

Lemma ty_scoped_arrow_left : forall variables l r,
    ty_scoped variables (arrow l r) -> ty_scoped variables l.
Proof.
  intros variables l r Hscope v Hocc.
  apply Hscope. simpl. now left.
Qed.

Lemma ty_scoped_arrow_right : forall variables l r,
    ty_scoped variables (arrow l r) -> ty_scoped variables r.
Proof.
  intros variables l r Hscope v Hocc.
  apply Hscope. simpl. now right.
Qed.

Lemma scan_binding_scope : forall fuel equations v t rest variables,
    scan_equations fuel equations = equation_binding v t rest ->
    equations_scoped variables equations ->
    In v variables /\
    ty_scoped variables t /\
    equations_scoped variables rest.
Proof.
  induction fuel as [| fuel IH];
    intros equations target body pending variables Hscan Hscope.
  - destruct equations as [| [left right] equations];
      simpl scan_equations in Hscan; discriminate.
  - destruct equations as [| [left right] equations]; [discriminate |].
    simpl scan_equations in Hscan.
    inversion Hscope as [| equation rest Hhead Htail]; subst.
    destruct (eq_ty_dec left right) as [Heq | Hneq].
    + eapply IH; eauto.
    + destruct left as [v | c | l r];
        destruct right as [v' | c' | l' r'];
        cbn -[occurs_dec] in Hscan.
      * destruct (occurs_dec v (var v')); try discriminate.
        inversion Hscan; subst.
        destruct Hhead as [Hleft Hright].
        repeat split; try assumption.
        apply Hleft. apply occurs_same_variable.
      * destruct (occurs_dec v (con c')); try discriminate.
        inversion Hscan; subst.
        destruct Hhead as [Hleft Hright].
        repeat split; try assumption.
        apply Hleft. apply occurs_same_variable.
      * destruct (occurs_dec v (arrow l' r')); try discriminate.
        inversion Hscan; subst.
        destruct Hhead as [Hleft Hright].
        repeat split; try assumption.
        apply Hleft. apply occurs_same_variable.
      * destruct (occurs_dec v' (con c)); try discriminate.
        inversion Hscan; subst.
        destruct Hhead as [Hleft Hright].
        repeat split; try assumption.
        apply Hright. apply occurs_same_variable.
      * discriminate.
      * discriminate.
      * destruct (occurs_dec v' (arrow l r)); try discriminate.
        inversion Hscan; subst.
        destruct Hhead as [Hleft Hright].
        repeat split; try assumption.
        apply Hright. apply occurs_same_variable.
      * discriminate.
      * eapply IH; [exact Hscan |].
        destruct Hhead as [Hleft Hright].
        constructor.
        -- split.
           ++ now apply ty_scoped_arrow_left with (r := r).
           ++ now apply ty_scoped_arrow_left with (r := r').
        -- constructor.
           ++ split.
              ** now apply ty_scoped_arrow_right with (l := l).
              ** now apply ty_scoped_arrow_right with (l := l').
           ++ exact Htail.
Qed.

(** Applying a substitution to the worklist and then solving it is the same
    equation semantics as solving under the composed substitution. *)
Lemma equations_unifier_map_compose : forall first second equations,
    equations_unifier
      (map (apply_subst_equation first) equations) second <->
    equations_unifier equations (compose_subst first second).
Proof.
  intros first second equations.
  induction equations as [| [left right] rest IH]; simpl.
  - split; constructor.
  - split; intro H.
    + inversion H as [| equation equations Hhead Hrest]; subst.
      constructor.
      * unfold equation_unifier in *. simpl in *.
        repeat rewrite apply_compose_equiv. exact Hhead.
      * apply IH. exact Hrest.
    + inversion H as [| equation equations Hhead Hrest]; subst.
      constructor.
      * unfold equation_unifier in *. simpl in *.
        repeat rewrite <- apply_compose_equiv. exact Hhead.
      * apply IH. exact Hrest.
Qed.

Lemma singleton_binding_absorbed : forall v t s,
    is_unifier (var v) t s -> forall u,
      apply_subst s u = apply_subst (compose_subst [(v, t)] s) u.
Proof.
  intros v t s Hunifier u.
  unfold is_unifier in Hunifier.
  rewrite apply_compose_equiv.
  induction u as [i | c | l IHl r IHr]; simpl in *.
  - destruct (eq_id_dec v i); [subst; exact Hunifier | reflexivity].
  - reflexivity.
  - now rewrite IHl, IHr.
Qed.

Lemma equations_unifier_extensional : forall equations s s',
    (forall t, apply_subst s t = apply_subst s' t) ->
    equations_unifier equations s -> equations_unifier equations s'.
Proof.
  intros equations s s' Heq Hunifier.
  induction Hunifier as [| [left right] rest Hhead Hrest IH].
  - constructor.
  - constructor.
    + unfold equation_unifier in *. now rewrite <- !Heq.
    + apply IH.
Qed.

(** ** Correctness of the substitution phase *)

Definition solve_result_spec
    (equations : list equation) (result : solve_result) : Prop :=
  match result with
  | solution s => equations_unifier equations s
  | unsatisfiable => forall s, ~ equations_unifier equations s
  | solver_fuel_exhausted => False
  end.

Lemma solve_equations_correct : forall fuel variables equations,
    length variables <= fuel ->
    equations_scoped variables equations ->
    solve_result_spec equations
      (solve_equations fuel variables equations).
Proof.
  induction fuel as [| fuel IH]; intros variables equations Hlength Hscope.
  - simpl solve_equations.
    remember (scan_equations (equations_size equations) equations)
      as scan eqn:Hscan.
    pose proof
      (scan_equations_correct (equations_size equations) equations
        (le_n _)) as Hscan_spec.
    rewrite <- Hscan in Hscan_spec.
    destruct scan.
    + exact (Hscan_spec []).
    + exact Hscan_spec.
    + exfalso.
      destruct (@scan_binding_scope
        (equations_size equations) equations i t l variables
        (eq_sym Hscan) Hscope) as [Hin _].
      destruct variables as [| head tail]; simpl in *; [contradiction | lia].
    + contradiction.
  - simpl solve_equations.
    remember (scan_equations (equations_size equations) equations)
      as scan eqn:Hscan.
    pose proof
      (scan_equations_correct (equations_size equations) equations
        (le_n _)) as Hscan_spec.
    rewrite <- Hscan in Hscan_spec.
    destruct scan as [| | v t rest |].
    + exact (Hscan_spec []).
    + exact Hscan_spec.
    + destruct Hscan_spec as [Hneq [Hocc Hscan_spec]].
      destruct (@scan_binding_scope
        (equations_size equations) equations v t rest variables
        (eq_sym Hscan) Hscope)
        as [Hin [Ht_scoped Hrest_scoped]].
      destruct (in_dec eq_id_dec v variables) as [Hin' | Hnotin].
      * assert (Hremove : length (remove eq_id_dec v variables) <= fuel).
        { pose proof (remove_length_lt eq_id_dec variables v Hin) as Hlt.
          pose proof (Nat.lt_le_trans _ _ _ Hlt Hlength) as Hbound.
          exact (proj1 (Nat.lt_succ_r _ _) Hbound). }
        pose proof
          (@equations_scoped_map_subst_remove variables v t rest
            Ht_scoped Hrest_scoped Hocc) as Hmapped_scope.
        specialize (IH
          (remove eq_id_dec v variables)
          (map (apply_subst_equation [(v, t)]) rest)
          Hremove Hmapped_scope).
        remember
          (solve_equations fuel (remove eq_id_dec v variables)
            (map (apply_subst_equation [(v, t)]) rest))
          as recursive eqn:Hrecursive.
        destruct recursive as [s | |].
        -- apply Hscan_spec. split.
           ++ unfold is_unifier.
              repeat rewrite apply_compose_equiv.
              simpl.
              destruct (eq_id_dec v v); [|contradiction].
              rewrite occurs_not_apply_subst_single by exact Hocc.
              reflexivity.
           ++ apply equations_unifier_map_compose. exact IH.
        -- intros candidate Hunifier.
           apply (IH candidate).
           apply equations_unifier_map_compose.
           destruct (Hscan_spec candidate) as [Hforward _].
           destruct (Hforward Hunifier) as [Hbinding Hrest].
           eapply equations_unifier_extensional; [|exact Hrest].
           intros u. apply singleton_binding_absorbed. exact Hbinding.
        -- contradiction.
      * contradiction.
    + contradiction.
Qed.

Lemma initial_equations_scoped : forall t1 t2,
    equations_scoped (initial_variables t1 t2) [(t1, t2)].
Proof.
  intros. constructor; [|constructor].
  split; [apply ty_scoped_initial_left | apply ty_scoped_initial_right].
Qed.

Theorem unify_exec_result_correct : forall t1 t2,
    solve_result_spec [(t1, t2)] (unify_exec_result t1 t2).
Proof.
  intros t1 t2.
  unfold unify_exec_result.
  apply solve_equations_correct.
  - reflexivity.
  - apply initial_equations_scoped.
Qed.

Theorem unify_exec_success_sound : forall t1 t2 s,
    unify_exec t1 t2 = unified s -> is_unifier t1 t2 s.
Proof.
  intros t1 t2 s Hexec.
  unfold unify_exec in Hexec.
  pose proof (unify_exec_result_correct t1 t2) as Hcorrect.
  destruct (unify_exec_result t1 t2) as [candidate | |];
    try discriminate; simpl in Hcorrect.
  inversion Hexec; subst.
  inversion Hcorrect; subst.
  exact H1.
Qed.

Theorem unify_exec_rejected_no_unifier : forall t1 t2,
    unify_exec t1 t2 = rejected -> forall s,
      apply_subst s t1 <> apply_subst s t2.
Proof.
  intros t1 t2 Hexec.
  unfold unify_exec in Hexec.
  pose proof (unify_exec_result_correct t1 t2) as Hcorrect.
  destruct (unify_exec_result t1 t2) as [candidate | |];
    try discriminate; simpl in Hcorrect.
  - intros s Hunifier.
    apply (Hcorrect s).
    constructor; [exact Hunifier | constructor].
  - contradiction.
Qed.

Theorem unify_exec_never_exhausts : forall t1 t2,
    unify_exec_result t1 t2 <> solver_fuel_exhausted.
Proof.
  intros t1 t2 Hexhausted.
  pose proof (unify_exec_result_correct t1 t2) as Hcorrect.
  now rewrite Hexhausted in Hcorrect.
Qed.

(** ** Principality *)

Definition equations_principal
    (equations : list equation) (s : substitution) : Prop :=
  equations_unifier equations s /\
  forall s', equations_unifier equations s' ->
    factors_through s s'.

Lemma substitution_equiv_ty : forall s s',
    substitution_equiv s s' ->
    forall t, apply_subst s t = apply_subst s' t.
Proof.
  intros s s' Hequiv.
  apply ext_subst_var_ty.
  exact Hequiv.
Qed.

Lemma singleton_binding_factors : forall v t candidate s residual,
    is_unifier (var v) t candidate ->
    substitution_equiv candidate (compose_subst s residual) ->
    substitution_equiv candidate
      (compose_subst (compose_subst [(v, t)] s) residual).
Proof.
  intros v t candidate s residual Hbinding Hfactor x.
  rewrite apply_compose_assoc_var.
  rewrite apply_compose_equiv.
  rewrite <- (substitution_equiv_ty candidate (compose_subst s residual)
    Hfactor (apply_subst [(v, t)] (var x))).
  rewrite <- apply_compose_equiv.
  apply singleton_binding_absorbed.
  exact Hbinding.
Qed.

Lemma solve_equations_principal : forall fuel variables equations,
    length variables <= fuel ->
    equations_scoped variables equations ->
    forall s,
      solve_equations fuel variables equations = solution s ->
      equations_principal equations s.
Proof.
  induction fuel as [| fuel IH]; intros variables equations Hlength Hscope.
  - simpl solve_equations.
    remember (scan_equations (equations_size equations) equations)
      as scan eqn:Hscan.
    pose proof
      (scan_equations_correct (equations_size equations) equations
        (le_n _)) as Hscan_spec.
    rewrite <- Hscan in Hscan_spec.
    destruct scan as [| | v t rest |].
    + intros s Hsolution. inversion Hsolution; subst.
      split.
      * apply Hscan_spec.
      * intros candidate Hunifier.
        exists candidate.
        unfold substitution_equiv.
        intro x.
        now rewrite compose_subst_nil_l.
    + intros s Hsolution. discriminate.
    + intros s Hsolution. discriminate.
    + contradiction.
  - simpl solve_equations.
    remember (scan_equations (equations_size equations) equations)
      as scan eqn:Hscan.
    pose proof
      (scan_equations_correct (equations_size equations) equations
        (le_n _)) as Hscan_spec.
    rewrite <- Hscan in Hscan_spec.
    destruct scan as [| | v t rest |].
    + intros s Hsolution. inversion Hsolution; subst.
      split.
      * apply Hscan_spec.
      * intros candidate Hunifier.
        exists candidate.
        unfold substitution_equiv.
        intro x.
        now rewrite compose_subst_nil_l.
    + intros s Hsolution. discriminate.
    + destruct Hscan_spec as [Hneq [Hocc Hscan_spec]].
      destruct (@scan_binding_scope
        (equations_size equations) equations v t rest variables
        (eq_sym Hscan) Hscope)
        as [Hin [Ht_scoped Hrest_scoped]].
      destruct (in_dec eq_id_dec v variables) as [Hin' | Hnotin].
      * assert (Hremove : length (remove eq_id_dec v variables) <= fuel).
        { pose proof (remove_length_lt eq_id_dec variables v Hin) as Hlt.
          pose proof (Nat.lt_le_trans _ _ _ Hlt Hlength) as Hbound.
          exact (proj1 (Nat.lt_succ_r _ _) Hbound). }
        pose proof
          (@equations_scoped_map_subst_remove variables v t rest
            Ht_scoped Hrest_scoped Hocc) as Hmapped_scope.
        specialize (IH
          (remove eq_id_dec v variables)
          (map (apply_subst_equation [(v, t)]) rest)
          Hremove Hmapped_scope).
        remember
          (solve_equations fuel (remove eq_id_dec v variables)
            (map (apply_subst_equation [(v, t)]) rest))
          as recursive eqn:Hrecursive.
        destruct recursive as [recursive_subst | |].
        -- intros result Hsolution.
           inversion Hsolution; subst result.
           specialize (IH recursive_subst eq_refl).
           destruct IH as [IHunifier IHprincipal].
           split.
           ++ apply Hscan_spec. split.
              ** unfold is_unifier.
                 repeat rewrite apply_compose_equiv.
                 simpl.
                 destruct (eq_id_dec v v); [|contradiction].
                 rewrite occurs_not_apply_subst_single by exact Hocc.
                 reflexivity.
              ** apply equations_unifier_map_compose.
                 exact IHunifier.
           ++ intros candidate Hunifier.
              assert (Hmapped :
                equations_unifier
                  (map (apply_subst_equation [(v, t)]) rest)
                  candidate).
              { apply equations_unifier_map_compose.
                destruct (Hscan_spec candidate) as [Hforward _].
                destruct (Hforward Hunifier) as [Hbinding Hrest].
                eapply equations_unifier_extensional; [|exact Hrest].
                intros u.
                apply singleton_binding_absorbed.
                exact Hbinding. }
              destruct (IHprincipal candidate Hmapped)
                as [residual Hfactor].
              exists residual.
              destruct (Hscan_spec candidate) as [Hforward _].
              destruct (Hforward Hunifier) as [Hbinding _].
              eapply singleton_binding_factors; eauto.
        -- intros result Hsolution. discriminate.
        -- intros result Hsolution. discriminate.
      * intros result Hsolution. discriminate.
    + contradiction.
Qed.

Theorem unify_exec_success_principal : forall t1 t2 s,
    unify_exec t1 t2 = unified s ->
    is_principal_unifier t1 t2 s.
Proof.
  intros t1 t2 s Hexec.
  unfold unify_exec in Hexec.
  destruct (unify_exec_result t1 t2) eqn:Hresult;
    try discriminate.
  inversion Hexec; subst.
  unfold unify_exec_result in Hresult.
  pose proof
    (solve_equations_principal
      (length (initial_variables t1 t2))
      (initial_variables t1 t2)
      [(t1, t2)]
      (le_n _)
      (initial_equations_scoped t1 t2)
      s Hresult) as Hprincipal.
  destruct Hprincipal as [Hunifier Hprincipal].
  split.
  - inversion Hunifier as [| equation equations Hhead Htail]; subst.
    exact Hhead.
  - intros candidate Hcandidate.
    apply Hprincipal.
    constructor; [exact Hcandidate | constructor].
Qed.

(** ** Freshness *)

Definition variables_below (variables : list id) (st : id) : Prop :=
  Forall (fun v => v < st) variables.

Lemma new_tv_ty_occurs_lt : forall t st,
    new_tv_ty t st -> forall v, occurs v t -> v < st.
Proof.
  intros t st Hfresh.
  induction Hfresh; intros v Hocc; simpl in Hocc.
  - contradiction.
  - destruct (eq_id_dec i v); [subst; assumption | contradiction].
  - destruct Hocc as [Hocc | Hocc];
      [apply IHHfresh1 | apply IHHfresh2]; assumption.
Qed.

Lemma ids_ty_occurs : forall v t,
    In v (ids_ty t) -> occurs v t.
Proof.
  intros v t.
  induction t as [i | c | l IHl r IHr]; simpl.
  - intros [Heq | Hfalse]; [subst | contradiction].
    destruct (eq_id_dec v v); [constructor | contradiction].
  - contradiction.
  - intros Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin]; simpl;
      [left; apply IHl | right; apply IHr]; assumption.
Qed.

Lemma ty_scoped_new_tv : forall variables t st,
    variables_below variables st ->
    ty_scoped variables t ->
    new_tv_ty t st.
Proof.
  intros variables t st Hbelow Hscope.
  induction t as [i | c | l IHl r IHr].
  - apply new_tv_var.
    unfold variables_below in Hbelow.
    rewrite Forall_forall in Hbelow.
    apply Hbelow.
    apply Hscope.
    apply occurs_same_variable.
  - constructor.
  - constructor.
    + apply IHl.
      now apply ty_scoped_arrow_left with (r := r).
    + apply IHr.
      now apply ty_scoped_arrow_right with (l := l).
Qed.

Lemma variables_below_remove : forall variables st v,
    variables_below variables st ->
    variables_below (remove eq_id_dec v variables) st.
Proof.
  intros variables st v Hbelow.
  unfold variables_below in *.
  rewrite Forall_forall in *.
  intros x Hin.
  apply Hbelow.
  exact (proj1 (in_remove eq_id_dec variables x v Hin)).
Qed.

Lemma initial_variables_below : forall t1 t2 st,
    new_tv_ty t1 st ->
    new_tv_ty t2 st ->
    variables_below (initial_variables t1 t2) st.
Proof.
  intros t1 t2 st Hfresh1 Hfresh2.
  unfold variables_below.
  rewrite Forall_forall.
  intros v Hin.
  unfold initial_variables in Hin.
  apply nodup_In in Hin.
  apply in_app_or in Hin.
  destruct Hin as [Hin | Hin].
  - eapply new_tv_ty_occurs_lt; [exact Hfresh1 |].
    now apply ids_ty_occurs.
  - eapply new_tv_ty_occurs_lt; [exact Hfresh2 |].
    now apply ids_ty_occurs.
Qed.

Lemma solve_equations_fresh : forall fuel variables equations st,
    length variables <= fuel ->
    equations_scoped variables equations ->
    variables_below variables st ->
    forall s,
      solve_equations fuel variables equations = solution s ->
      new_tv_subst s st.
Proof.
  induction fuel as [| fuel IH];
    intros variables equations st Hlength Hscope Hbelow.
  - simpl solve_equations.
    destruct (scan_equations (equations_size equations) equations);
      intros s Hsolution; try discriminate.
    inversion Hsolution; subst.
    apply new_tv_subst_nil.
  - simpl solve_equations.
    remember (scan_equations (equations_size equations) equations)
      as scan eqn:Hscan.
    destruct scan as [| | v t rest |].
    + intros s Hsolution.
      inversion Hsolution; subst.
      apply new_tv_subst_nil.
    + intros s Hsolution. discriminate.
    + destruct (@scan_binding_scope
        (equations_size equations) equations v t rest variables
        (eq_sym Hscan) Hscope)
        as [Hin [Ht_scoped Hrest_scoped]].
      destruct (in_dec eq_id_dec v variables) as [Hin' | Hnotin].
      * assert (Hremove : length (remove eq_id_dec v variables) <= fuel).
        { pose proof (remove_length_lt eq_id_dec variables v Hin) as Hlt.
          pose proof (Nat.lt_le_trans _ _ _ Hlt Hlength) as Hbound.
          exact (proj1 (Nat.lt_succ_r _ _) Hbound). }
        assert (Hbelow_remove :
          variables_below (remove eq_id_dec v variables) st).
        { now apply variables_below_remove. }
        pose proof
          (scan_equations_correct (equations_size equations) equations
            (le_n _)) as Hscan_spec.
        rewrite <- Hscan in Hscan_spec.
        destruct Hscan_spec as [Hneq [Hocc Hscan_spec]].
        pose proof
          (@equations_scoped_map_subst_remove variables v t rest
            Ht_scoped Hrest_scoped Hocc) as Hmapped_scope.
        specialize (IH
          (remove eq_id_dec v variables)
          (map (apply_subst_equation [(v, t)]) rest)
          st Hremove Hmapped_scope Hbelow_remove).
        remember
          (solve_equations fuel (remove eq_id_dec v variables)
            (map (apply_subst_equation [(v, t)]) rest))
          as recursive eqn:Hrecursive.
        destruct recursive as [recursive_subst | |].
        -- intros result Hsolution.
           inversion Hsolution; subst result.
           specialize (IH recursive_subst eq_refl).
           apply new_tv_compose_subst.
           ++ apply new_ty_to_cons_new_tv_subst.
              ** unfold variables_below in Hbelow.
                 rewrite Forall_forall in Hbelow.
                 now apply Hbelow.
              ** now apply ty_scoped_new_tv with (variables := variables).
              ** apply new_tv_subst_nil.
           ++ exact IH.
        -- intros result Hsolution. discriminate.
        -- intros result Hsolution. discriminate.
      * intros result Hsolution. discriminate.
    + intros result Hsolution. discriminate.
Qed.

Theorem unify_exec_preserves_freshness : forall t1 t2 s,
    unify_exec t1 t2 = unified s ->
    preserves_freshness t1 t2 s.
Proof.
  intros t1 t2 s Hexec st [Hfresh1 Hfresh2].
  unfold unify_exec in Hexec.
  destruct (unify_exec_result t1 t2) eqn:Hresult;
    try discriminate.
  inversion Hexec; subst.
  unfold unify_exec_result in Hresult.
  eapply (@solve_equations_fresh
    (length (initial_variables t1 t2))
    (initial_variables t1 t2)
    [(t1, t2)] st).
  - reflexivity.
  - apply initial_equations_scoped.
  - apply initial_variables_below; assumption.
  - exact Hresult.
Qed.
