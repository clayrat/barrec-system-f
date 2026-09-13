(** * Hindley--Milner inference

    Public facade for the Rocq-9.1 adaptation of W-in-Coq.  It preserves the
    upstream [term], [ty], [schm], [ctx], and [runW] interfaces.  The public
    unifier facade additionally separates its specification, executable
    result, and sound failure theorem. *)

From SystemF.HM Require Export
  Unify WExec WExecCorrect WCorrect WCorrespondence.
From SystemF.HM.WInCoq Require Export Schemes Context Typing.
From SystemF.HM.WInCoq Require Export Infer.
