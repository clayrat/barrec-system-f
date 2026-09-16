(** * Shared examples

    Keep the identifiers used by the existing bound experiment.
    [term1] and [term2] reproduce the examples in Blot's artifact.
    [term3] and [term4] are the one-beta-step regression inputs described
    in the plan.  The repaired implementation now lives in [BarRec.Bound];
    its potentially slow numerical runs remain in the separate benchmark
    harness. *)

From Stdlib Require Import List.
Import ListNotations.
From SystemF.F Require Import Syntax Check.

(** forall X. X -> X *)
Definition type1 : type := TForall (TArrow (TVar 0) (TVar 0)).

(** Lambda X. lambda x:X. x *)
Definition term1 : fderiv [] type1 :=
  DTLam (DLam (DVar (DVar0 (TVar 0)))).

(** lambda x:type1. x[type1] x *)
Definition type2 : type := TArrow type1 type1.
Definition term2 : fderiv [] type2 :=
  DLam (DApp (DTApp (DVar (DVar0 type1)) type1)
             (DVar (DVar0 type1))).

(** term1[type1] term1 *)
Definition term3 : fderiv [] type1 :=
  DApp (DTApp term1 type1) term1.

(** (lambda x:type1. x) term1 *)
Definition term4 : fderiv [] type1 :=
  DApp (DLam (DVar (DVar0 type1))) term1.

(** The same four inputs before intrinsic type checking. *)
Definition raw_term1 : fterm :=
  FTLam (FLam (TVar 0) (FVar 0)).

Definition raw_term2 : fterm :=
  FLam type1
    (FApp (FTApp (FVar 0) type1) (FVar 0)).

Definition raw_term3 : fterm :=
  FApp (FTApp raw_term1 type1) raw_term1.

Definition raw_term4 : fterm :=
  FApp (FLam type1 (FVar 0)) raw_term1.

Definition erased_examples : list term :=
  [fderiv_to_term term1; fderiv_to_term term2;
   fderiv_to_term term3; fderiv_to_term term4].
