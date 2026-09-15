(** * Algebra of parallel de Bruijn type substitutions

    [Syntax] exposes Blot's cutoff operations and [OPE] exposes parallel
    substitutions.  Type preservation for the HM elaborator additionally
    needs their functor and monad laws.  They are proved here for arbitrary
    renamings; the final lemmas connect the presentation back to
    [type_lift], [type_subst], and [OPE.sub]. *)

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

From SystemF.F Require Import Syntax OPE Scope.

Definition type_renaming : Type := nat -> nat.

Definition keep_renaming (rho : type_renaming) : type_renaming :=
  fun index =>
    match index with
    | 0 => 0
    | S index => S (rho index)
    end.

Fixpoint rename_type (rho : type_renaming) (T : type) : type :=
  match T with
  | TVar index => TVar (rho index)
  | TArrow A B => TArrow (rename_type rho A) (rename_type rho B)
  | TForall body => TForall (rename_type (keep_renaming rho) body)
  end.

Definition keep_type_substitution
    (sigma : type_substitution) : type_substitution :=
  fun index =>
    match index with
    | 0 => TVar 0
    | S index => rename_type S (sigma index)
    end.

Fixpoint substitute_type
    (sigma : type_substitution) (T : type) : type :=
  match T with
  | TVar index => sigma index
  | TArrow A B =>
      TArrow (substitute_type sigma A) (substitute_type sigma B)
  | TForall body =>
      TForall (substitute_type (keep_type_substitution sigma) body)
  end.

Lemma rename_type_ext : forall rho rho' T,
  (forall index, rho index = rho' index) ->
  rename_type rho T = rename_type rho' T.
Proof.
  intros rho rho' T.
  revert rho rho'.
  induction T as [index | A IHA B IHB | body IHbody];
    intros rho rho' Hequal; cbn [rename_type].
  - now rewrite Hequal.
  - now rewrite (IHA rho rho'), (IHB rho rho').
  - f_equal.
    apply IHbody.
    intros [| index]; cbn [keep_renaming].
    + reflexivity.
    + now rewrite Hequal.
Qed.

Lemma substitute_type_ext : forall sigma sigma' T,
  (forall index, sigma index = sigma' index) ->
  substitute_type sigma T = substitute_type sigma' T.
Proof.
  intros sigma sigma' T.
  revert sigma sigma'.
  induction T as [index | A IHA B IHB | body IHbody];
    intros sigma sigma' Hequal; cbn [substitute_type].
  - apply Hequal.
  - now rewrite (IHA sigma sigma'), (IHB sigma sigma').
  - f_equal.
    apply IHbody.
    intros [| index]; cbn [keep_type_substitution].
    + reflexivity.
    + now rewrite Hequal.
Qed.

Lemma keep_renaming_compose : forall rho rho' index,
  keep_renaming (fun index => rho' (rho index)) index =
  keep_renaming rho' (keep_renaming rho index).
Proof.
  intros rho rho' [| index]; reflexivity.
Qed.

Lemma rename_type_compose : forall rho rho' T,
  rename_type rho' (rename_type rho T) =
  rename_type (fun index => rho' (rho index)) T.
Proof.
  intros rho rho' T.
  revert rho rho'.
  induction T as [index | A IHA B IHB | body IHbody];
    intros rho rho'; cbn [rename_type].
  - reflexivity.
  - now rewrite IHA, IHB.
  - f_equal.
    rewrite IHbody.
    apply rename_type_ext.
    intro index.
    symmetry.
    apply keep_renaming_compose.
Qed.

Lemma rename_type_identity : forall T,
  rename_type (fun index => index) T = T.
Proof.
  induction T as [index | A IHA B IHB | body IHbody];
    cbn [rename_type].
  - reflexivity.
  - now rewrite IHA, IHB.
  - f_equal.
    transitivity (rename_type (fun index => index) body).
    + apply rename_type_ext.
      intros [| index]; reflexivity.
    + exact IHbody.
Qed.

Lemma keep_rename_substitution : forall rho index,
  keep_type_substitution (fun index => TVar (rho index)) index =
  TVar (keep_renaming rho index).
Proof.
  intros rho [| index]; reflexivity.
Qed.

Lemma substitute_rename_type : forall sigma rho T,
  substitute_type sigma (rename_type rho T) =
  substitute_type (fun index => sigma (rho index)) T.
Proof.
  intros sigma rho T.
  revert sigma rho.
  induction T as [index | A IHA B IHB | body IHbody];
    intros sigma rho; cbn [rename_type substitute_type].
  - reflexivity.
  - now rewrite IHA, IHB.
  - f_equal.
    rewrite IHbody.
    apply substitute_type_ext.
    intros [| index]; cbn [keep_renaming keep_type_substitution].
    + reflexivity.
    + reflexivity.
Qed.

Lemma rename_substitute_type : forall rho sigma T,
  rename_type rho (substitute_type sigma T) =
  substitute_type (fun index => rename_type rho (sigma index)) T.
Proof.
  intros rho sigma T.
  revert rho sigma.
  induction T as [index | A IHA B IHB | body IHbody];
    intros rho sigma; cbn [rename_type substitute_type].
  - reflexivity.
  - now rewrite IHA, IHB.
  - f_equal.
    rewrite IHbody.
    apply substitute_type_ext.
    intros [| index]; cbn [keep_renaming keep_type_substitution].
    + reflexivity.
    + rewrite !rename_type_compose.
      apply rename_type_ext.
      intros index'.
      reflexivity.
Qed.

Definition compose_type_substitution
    (sigma tau : type_substitution) : type_substitution :=
  fun index => substitute_type tau (sigma index).

Lemma keep_type_substitution_compose : forall sigma tau index,
  keep_type_substitution (compose_type_substitution sigma tau) index =
  compose_type_substitution
    (keep_type_substitution sigma) (keep_type_substitution tau) index.
Proof.
  intros sigma tau [| index].
  - reflexivity.
  - unfold compose_type_substitution.
    cbn [keep_type_substitution].
    transitivity
      (substitute_type
        (fun index => rename_type S (tau index)) (sigma index)).
    + apply rename_substitute_type.
    + rewrite substitute_rename_type.
      apply substitute_type_ext.
      intro index'.
      reflexivity.
Qed.

Lemma substitute_type_compose : forall sigma tau T,
  substitute_type tau (substitute_type sigma T) =
  substitute_type (compose_type_substitution sigma tau) T.
Proof.
  intros sigma tau T.
  revert sigma tau.
  induction T as [index | A IHA B IHB | body IHbody];
    intros sigma tau; cbn [substitute_type compose_type_substitution].
  - reflexivity.
  - now rewrite IHA, IHB.
  - f_equal.
    rewrite IHbody.
    apply substitute_type_ext.
    intro index.
    symmetry.
    apply keep_type_substitution_compose.
Qed.

Lemma substitute_type_identity : forall T,
  substitute_type (fun index => TVar index) T = T.
Proof.
  induction T as [index | A IHA B IHB | body IHbody];
    cbn [substitute_type].
  - reflexivity.
  - now rewrite IHA, IHB.
  - f_equal.
    transitivity
      (substitute_type (fun index => TVar index) body).
    + apply substitute_type_ext.
      intros [| index]; reflexivity.
    + exact IHbody.
Qed.

Lemma keep_renaming_ope : forall rho index,
  keep_renaming (apply_ope rho) index =
  apply_ope (OPEKeep rho) index.
Proof.
  intros rho [| index]; reflexivity.
Qed.

Lemma rename_type_ope : forall rho T,
  rename_type (apply_ope rho) T = ren rho T.
Proof.
  intros rho T.
  revert rho.
  induction T as [index | A IHA B IHB | body IHbody];
    intro rho; cbn [rename_type ren].
  - reflexivity.
  - now rewrite IHA, IHB.
  - f_equal.
    transitivity
      (rename_type (apply_ope (OPEKeep rho)) body).
    + apply rename_type_ext.
      apply keep_renaming_ope.
    + apply IHbody.
Qed.

Lemma rename_type_successor : forall T,
  rename_type S T = type_lift 0 T.
Proof.
  intro T.
  change (rename_type (apply_ope wk) T = type_lift 0 T).
  rewrite rename_type_ope.
  apply ren_wk.
Qed.

Lemma keep_type_substitution_is_ope_keep : forall sigma index,
  keep_type_substitution sigma index = keep_sub sigma index.
Proof.
  intros sigma [| index]; cbn [keep_type_substitution keep_sub scons].
  - reflexivity.
  - unfold drop_sub.
    now rewrite ren_wk, <- rename_type_successor.
Qed.

Lemma substitute_type_is_ope_sub : forall sigma T,
  substitute_type sigma T = sub sigma T.
Proof.
  intros sigma T.
  revert sigma.
  induction T as [index | A IHA B IHB | body IHbody];
    intro sigma; cbn [substitute_type sub].
  - reflexivity.
  - now rewrite IHA, IHB.
  - f_equal.
    rewrite IHbody.
    apply sub_ext.
    apply keep_type_substitution_is_ope_keep.
Qed.

Theorem substitute_type_single : forall T U,
  substitute_type (scons U ids) T = type_subst 0 T U.
Proof.
  intros T U.
  rewrite substitute_type_is_ope_sub.
  apply sub_scons_ids.
Qed.

(** ** Eliminating a block of outer quantifiers *)

Fixpoint keep_type_substitution_n
    (count : nat) (sigma : type_substitution) : type_substitution :=
  match count with
  | 0 => sigma
  | S count =>
      keep_type_substitution (keep_type_substitution_n count sigma)
  end.

Fixpoint quantify_type (count : nat) (body : type) : type :=
  match count with
  | 0 => body
  | S count => TForall (quantify_type count body)
  end.

Definition lift_type_by (count : nat) (T : type) : type :=
  rename_type (fun index => count + index) T.

Definition shift_type_variables
    (cutoff count index : nat) : nat :=
  if index <? cutoff then index else count + index.

Lemma keep_shift_type_variables : forall cutoff count index,
  keep_renaming (shift_type_variables cutoff count) index =
  shift_type_variables (S cutoff) count index.
Proof.
  intros cutoff count [| index].
  - reflexivity.
  - unfold shift_type_variables.
    cbn [keep_renaming].
    rewrite ltb_succ_succ.
    destruct (index <? cutoff); cbn; lia.
Qed.

Lemma rename_type_quantify_shift : forall
    cutoff count quantifiers body,
  rename_type (shift_type_variables cutoff count)
    (quantify_type quantifiers body) =
  quantify_type quantifiers
    (rename_type
      (shift_type_variables (quantifiers + cutoff) count) body).
Proof.
  intros cutoff count quantifiers.
  revert cutoff.
  induction quantifiers as [| quantifiers IH]; intros cutoff body.
  - cbn [quantify_type].
    apply rename_type_ext.
    intro index.
    now replace (0 + cutoff) with cutoff by lia.
  - cbn [quantify_type rename_type].
    f_equal.
    transitivity
      (rename_type (shift_type_variables (S cutoff) count)
        (quantify_type quantifiers body)).
    + apply rename_type_ext.
      apply keep_shift_type_variables.
    + rewrite (IH (S cutoff) body).
      now replace (quantifiers + S cutoff)
        with (S quantifiers + cutoff) by lia.
Qed.

Lemma lift_type_by_quantify : forall count quantifiers body,
  lift_type_by count (quantify_type quantifiers body) =
  quantify_type quantifiers
    (rename_type
      (shift_type_variables quantifiers count) body).
Proof.
  intros count quantifiers body.
  unfold lift_type_by.
  transitivity
    (rename_type (shift_type_variables 0 count)
      (quantify_type quantifiers body)).
  - apply rename_type_ext.
    intro index.
    reflexivity.
  - rewrite rename_type_quantify_shift.
    replace (quantifiers + 0) with quantifiers by lia.
    reflexivity.
Qed.

Lemma lift_type_by_compose : forall first second T,
  lift_type_by first (lift_type_by second T) =
  lift_type_by (first + second) T.
Proof.
  intros first second T.
  unfold lift_type_by.
  rewrite rename_type_compose.
  apply rename_type_ext.
  intro index.
  lia.
Qed.

Lemma lift_type_by_zero : forall T,
  lift_type_by 0 T = T.
Proof.
  intro T.
  unfold lift_type_by.
  transitivity (rename_type (fun index => index) T).
  - apply rename_type_ext. intro index. lia.
  - apply rename_type_identity.
Qed.

Lemma lift_type_by_successor : forall count T,
  lift_type_by (S count) T = rename_type S (lift_type_by count T).
Proof.
  intros count T.
  unfold lift_type_by.
  rewrite rename_type_compose.
  apply rename_type_ext.
  intro index.
  lia.
Qed.

Lemma keep_type_substitution_n_lookup : forall count sigma index,
  keep_type_substitution_n count sigma index =
  if index <? count then TVar index
  else lift_type_by count (sigma (index - count)).
Proof.
  induction count as [| count IH]; intros sigma [| index].
  - cbn [keep_type_substitution_n].
    now rewrite lift_type_by_zero.
  - cbn [keep_type_substitution_n].
    now rewrite lift_type_by_zero.
  - reflexivity.
  - cbn [keep_type_substitution_n keep_type_substitution].
    rewrite IH.
    rewrite ltb_succ_succ.
    destruct (index <? count) eqn:Hindex.
    + apply Nat.ltb_lt in Hindex.
      cbn [rename_type].
      f_equal.
    + apply Nat.ltb_ge in Hindex.
      rewrite <- lift_type_by_successor.
      f_equal.
Qed.

Lemma keep_type_substitution_n_successor : forall count sigma index,
  keep_type_substitution_n count (keep_type_substitution sigma) index =
  keep_type_substitution_n (S count) sigma index.
Proof.
  induction count as [| count IH]; intros sigma [| index];
    cbn [keep_type_substitution_n keep_type_substitution].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - now rewrite IH.
Qed.

Fixpoint instantiate_type (T : type) (arguments : list type) : type :=
  match arguments with
  | [] => T
  | argument :: arguments' =>
      match T with
      | TForall body =>
          instantiate_type (type_subst 0 body argument) arguments'
      | _ => T
      end
  end.

Definition closing_type_substitution
    (arguments : list type) : type_substitution :=
  fun index =>
    if index <? length arguments then
      nth (length arguments - S index) arguments (TVar 0)
    else
      TVar (index - length arguments).

Lemma substitute_type_quantify : forall count sigma body,
  substitute_type sigma (quantify_type count body) =
  quantify_type count
    (substitute_type (keep_type_substitution_n count sigma) body).
Proof.
  induction count as [| count IH]; intros sigma body.
  - reflexivity.
  - cbn [quantify_type substitute_type].
    f_equal.
    rewrite IH.
    f_equal.
    apply substitute_type_ext.
    apply keep_type_substitution_n_successor.
Qed.

Lemma nth_cons_positive : forall (A : Type) (default : A)
    (head : A) tail index,
  0 < index ->
  nth index (head :: tail) default = nth (pred index) tail default.
Proof.
  intros A default head tail [| index] Hpositive; try lia.
  reflexivity.
Qed.

Lemma closing_type_substitution_cons : forall argument arguments index,
  compose_type_substitution
    (keep_type_substitution_n (length arguments)
      (scons argument ids))
    (closing_type_substitution arguments)
    index =
  closing_type_substitution (argument :: arguments) index.
Proof.
  intros argument arguments index.
  unfold compose_type_substitution, closing_type_substitution.
  rewrite keep_type_substitution_n_lookup.
  destruct (index <? length arguments) eqn:Hbelow.
  - assert (Hlt : index < length arguments).
    { apply Nat.ltb_lt. exact Hbelow. }
    cbn [substitute_type].
    rewrite Hbelow.
    assert (Hbelow' : index <? length (argument :: arguments) = true).
    { apply Nat.ltb_lt. cbn [length]. lia. }
    rewrite Hbelow'.
    replace (length (argument :: arguments) - S index)
      with (S (length arguments - S index)) by
        (cbn [length]; lia).
    reflexivity.
  - assert (Hge : length arguments <= index).
    { apply Nat.ltb_ge. exact Hbelow. }
    destruct (Nat.eq_dec index (length arguments)) as [Hequal | Hdifferent].
    + subst index.
      replace (length arguments - length arguments) with 0 by lia.
      cbn [scons].
      unfold lift_type_by.
      rewrite substitute_rename_type.
      transitivity
        (substitute_type (fun index => TVar index) argument).
      * apply substitute_type_ext.
        intro index.
        unfold closing_type_substitution.
        assert (Hindex :
          length arguments + index <? length arguments = false).
        { apply Nat.ltb_ge. lia. }
        rewrite Hindex.
        cbn [rename_type].
        f_equal.
        lia.
      * rewrite substitute_type_identity.
        assert (Hlast :
          length arguments <? length (argument :: arguments) = true).
        { apply Nat.ltb_lt. cbn [length]. lia. }
        rewrite Hlast.
        cbn [length].
        replace (S (length arguments) - S (length arguments)) with 0 by lia.
        reflexivity.
    + assert (Habove : length arguments < index) by lia.
      replace (index - length arguments) with
        (S (index - S (length arguments))) by lia.
      cbn [scons ids].
      unfold lift_type_by, ids.
      cbn [rename_type substitute_type].
      assert (Hshift :
        length arguments + (index - S (length arguments))
          <? length arguments = false).
      { apply Nat.ltb_ge. lia. }
      rewrite Hshift.
      assert (Habove' : index <? length (argument :: arguments) = false).
      { apply Nat.ltb_ge. cbn [length]. lia. }
      rewrite Habove'.
      f_equal.
      cbn [length].
      rewrite Nat.add_sub_swap by lia.
      replace (length arguments - length arguments) with 0 by lia.
      cbn.
      lia.
Qed.

Theorem instantiate_quantified_type : forall arguments body,
  instantiate_type
    (quantify_type (length arguments) body) arguments =
  substitute_type (closing_type_substitution arguments) body.
Proof.
  induction arguments as [| argument arguments IH]; intro body.
  - cbn [instantiate_type quantify_type].
    transitivity
      (substitute_type (fun index => TVar index) body).
    + symmetry. apply substitute_type_identity.
    + apply substitute_type_ext.
      intro index.
      unfold closing_type_substitution.
      cbn.
      f_equal.
      lia.
  - cbn [length quantify_type instantiate_type].
    rewrite <- substitute_type_single.
    rewrite substitute_type_quantify.
    rewrite IH.
    rewrite substitute_type_compose.
    apply substitute_type_ext.
    apply closing_type_substitution_cons.
Qed.

Lemma substitute_type_closed : forall n T sigma,
  closed n T ->
  (forall index, index < n -> sigma index = TVar index) ->
  substitute_type sigma T = T.
Proof.
  intros n T.
  revert n.
  induction T as [index | A IHA B IHB | body IHbody];
    intros n sigma Hclosed Hfixed;
    cbn [closed substitute_type] in Hclosed |- *.
  - now apply Hfixed.
  - destruct Hclosed as [HA HB].
    now rewrite (IHA n sigma HA Hfixed), (IHB n sigma HB Hfixed).
  - f_equal.
    apply IHbody with (n := S n).
    + exact Hclosed.
    + intros [| index] Hindex.
      * reflexivity.
      * cbn [keep_type_substitution].
        rewrite Hfixed by lia.
        reflexivity.
Qed.

Lemma rename_type_closed : forall n T rho,
  closed n T ->
  (forall index, index < n -> rho index = index) ->
  rename_type rho T = T.
Proof.
  intros n T.
  revert n.
  induction T as [index | A IHA B IHB | body IHbody];
    intros n rho Hclosed Hfixed;
    cbn [closed rename_type] in Hclosed |- *.
  - now rewrite Hfixed.
  - destruct Hclosed as [HA HB].
    now rewrite (IHA n rho HA Hfixed), (IHB n rho HB Hfixed).
  - f_equal.
    apply IHbody with (n := S n).
    + exact Hclosed.
    + intros [| index] Hindex.
      * reflexivity.
      * cbn [keep_renaming].
        now rewrite Hfixed by lia.
Qed.

Corollary lift_type_by_closed_zero : forall count T,
  closed 0 T -> lift_type_by count T = T.
Proof.
  intros count T Hclosed.
  unfold lift_type_by.
  apply rename_type_closed with (n := 0).
  - exact Hclosed.
  - intros index Hindex. lia.
Qed.

Lemma lift_type_by_closed : forall count depth T,
  closed depth T -> closed (count + depth) (lift_type_by count T).
Proof.
  induction count as [| count IH]; intros depth T Hclosed.
  - rewrite lift_type_by_zero.
    exact Hclosed.
  - rewrite lift_type_by_successor.
    rewrite rename_type_successor.
    replace (S count + depth) with (S (count + depth)) by lia.
    apply closed_type_lift0.
    now apply IH.
Qed.

Corollary substitute_type_closed_zero : forall T sigma,
  closed 0 T -> substitute_type sigma T = T.
Proof.
  intros T sigma Hclosed.
  apply substitute_type_closed with (n := 0).
  - exact Hclosed.
  - intros index Hindex. lia.
Qed.

Lemma closing_type_substitution_lift : forall arguments T,
  substitute_type (closing_type_substitution arguments)
    (lift_type_by (length arguments) T) = T.
Proof.
  intros arguments T.
  unfold lift_type_by.
  rewrite substitute_rename_type.
  transitivity
    (substitute_type (fun index => TVar index) T).
  - apply substitute_type_ext.
    intro index.
    unfold closing_type_substitution.
    assert (Hbelow :
      length arguments + index <? length arguments = false).
    { apply Nat.ltb_ge. lia. }
    rewrite Hbelow.
    cbn [rename_type].
    f_equal.
    rewrite Nat.add_sub_swap by lia.
    replace (length arguments - length arguments) with 0 by lia.
    cbn.
    reflexivity.
  - apply substitute_type_identity.
Qed.

Lemma closing_type_substitution_nth : forall arguments index argument,
  nth_error arguments index = Some argument ->
  closing_type_substitution arguments
    (length arguments - S index) = argument.
Proof.
  intros arguments index argument Hnth.
  assert (Hindex : index < length arguments).
  { apply (proj1 (nth_error_Some arguments index)).
    rewrite Hnth.
    discriminate. }
  unfold closing_type_substitution.
  assert (Hbelow :
    length arguments - S index <? length arguments = true).
  { apply Nat.ltb_lt. lia. }
  rewrite Hbelow.
  replace
    (length arguments - S (length arguments - S index))
    with index by lia.
  now apply nth_error_nth with (d := TVar 0) in Hnth.
Qed.
