(** * Shared examples

    Keep the identifiers used by the existing bound experiment.
    [term1] and [term2] reproduce the examples in Blot's artifact.
    [term3] and [term4] are the one-beta-step regression inputs described
    in the plan. Their bounds have not been repaired or recomputed here. *)

From Stdlib Require Import List.
Import ListNotations.
From SystemF.F Require Import Syntax Check.

(** forall X. X -> X *)
Definition type1 : type := TForall (TArrow (TVar 0) (TVar 0)).

(** Lambda X. lambda x:X. x *)
Definition term1 : fterm [] type1 :=
  FTAbs (FAbs (FVar (FVar0 (TVar 0)))).

(** lambda x:type1. x[type1] x *)
Definition type2 : type := TArrow type1 type1.
Definition term2 : fterm [] type2 :=
  FAbs (FApp (FTApp (FVar (FVar0 type1)) type1)
             (FVar (FVar0 type1))).

(** term1[type1] term1 *)
Definition term3 : fterm [] type1 :=
  FApp (FTApp term1 type1) term1.

(** (lambda x:type1. x) term1 *)
Definition term4 : fterm [] type1 :=
  FApp (FAbs (FVar (FVar0 type1))) term1.

(** The same four inputs before intrinsic type checking. *)
Definition raw_term1 : RawChurch :=
  RCTAbs (RCAbs (TVar 0) (RCVar 0)).

Definition raw_term2 : RawChurch :=
  RCAbs type1
    (RCApp (RCTApp (RCVar 0) type1) (RCVar 0)).

Definition raw_term3 : RawChurch :=
  RCApp (RCTApp raw_term1 type1) raw_term1.

Definition raw_term4 : RawChurch :=
  RCApp (RCAbs type1 (RCVar 0)) raw_term1.

Definition erased_examples : list term :=
  [fterm_to_term term1; fterm_to_term term2;
   fterm_to_term term3; fterm_to_term term4].
