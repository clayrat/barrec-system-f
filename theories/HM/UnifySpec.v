(** * Specification of Hindley--Milner unification

    This module states the successful-result contract independently from the
    executable unifier.  The adapted W-in-Coq implementation supplies exactly
    these properties in the dependent result of [unify'']. *)

From SystemF.HM.W Require Export SimpleTypes Subst NewTypeVariable.

Definition is_unifier (t1 t2 : ty) (s : substitution) : Prop :=
  apply_subst s t1 = apply_subst s t2.

Definition substitution_equiv (s1 s2 : substitution) : Prop :=
  forall v,
    apply_subst s1 (var v) = apply_subst s2 (var v).

Definition factors_through (general specific : substitution) : Prop :=
  exists residual,
    substitution_equiv specific (comp_subst general residual).

Definition is_principal_unifier
    (t1 t2 : ty) (s : substitution) : Prop :=
  is_unifier t1 t2 s /\
  forall s', is_unifier t1 t2 s' -> factors_through s s'.

Definition preserves_freshness
    (t1 t2 : ty) (s : substitution) : Prop :=
  forall st,
    new_tv_ty t1 st /\ new_tv_ty t2 st -> new_tv_subst s st.
