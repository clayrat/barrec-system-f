(** * The Disjoint tail
      This file contains defintions and lemmas about [is_disjoint_with_some_tail]. 
      This definition is used in the lemmas 
      [inst_subst_to_subst_aux] and [more_general_ctx_disjoint_prefix_apply_inst] 
      in the Moregeneral file. *)

Set Implicit Arguments.

From SystemF.HM.W Require Import SubstSchm.
Require Import List.
From SystemF.HM.W Require Import ListIds.
From SystemF.HM.W Require Import Context.
From SystemF.HM.W Require Import Disjoints.
From SystemF.HM.W Require Import Gen.
From SystemF.HM.W Require Import SimpleTypes.
From SystemF.HM.W Require Import Subst.
From SystemF.HM.W Require Import Context.
From SystemF.HM.W Require Import MyLtacs.
From SystemF.HM.W Require Import NthErrorTools.
From SystemF.HM.W Require Import LibTactics.


(** * Disjoint tail *)
(** If [l] is a prefix of [L], then there is a postfix [l1] of [L] that is disjoint
    with some given [C]. *)
Inductive is_disjoint_with_some_tail : list id -> list id -> list id -> Prop :=
|  prefixe_free_intro : forall C l L : list id,
    {l1 : list id | L = l ++ l1 /\ are_disjoints C l1} -> is_disjoint_with_some_tail C l L.

Hint Constructors is_disjoint_with_some_tail:core.

(** ** Lemmas about disjoint tail *)

Lemma is_prefixe_gen_aux : forall (l L : list id) (tau : ty) (G : hmctx),
    is_disjoint_with_some_tail (FV_ctx G) (snd (gen_ty_aux tau G l)) L ->
    is_disjoint_with_some_tail (FV_ctx G) l L.
Proof.
  intros l L tau G Htail.
  destruct (exists_snd_gen_aux_app G tau l) as [extra [Heq Hextra]].
  rewrite Heq in Htail.
  inversion Htail as [C prefix whole witness]; subst.
  destruct witness as [tail [HL Hdisjoint_tail]].
  econstructor.
  exists (extra ++ tail).
  split.
  - rewrite app_assoc. exact HL.
  - unfold are_disjoints in *.
    intros z Hz.
    apply Bool.not_true_is_false.
    intro Happ.
    apply in_list_id_or_append_inversion in Happ.
    destruct Happ as [Hextra_member | Htail_member].
    + rewrite (Hextra z Hz) in Hextra_member. discriminate.
    + rewrite (Hdisjoint_tail z Hz) in Htail_member. discriminate.
Qed.

Hint Resolve is_prefixe_gen_aux:core.

Lemma is_prefixe_reflexivity : forall C L : list id, is_disjoint_with_some_tail C L L.
intros C L.
econstructor.
exists (nil: list id).
 split; auto.
 apply app_nil_end.
Qed.

Hint Resolve is_prefixe_reflexivity:core.
