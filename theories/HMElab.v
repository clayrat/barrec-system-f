(** * From HM inference to explicit System F — planned

    Translate generalized schemes and preserve the computational choices
    of W: instantiation lists, lambda argument types, and generalization
    order. Build RawChurch, check it with F.Check, and prove agreement
    with runW and preservation of erasure after desugaring let.

    Start with the constant-free example: let id = lambda x.x in id id. *)

From SystemF.F Require Import Check.
From SystemF.HM Require Import Infer.
