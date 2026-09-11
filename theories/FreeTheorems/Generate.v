(** * Relational translation of a type — planned

    Recurse on System F types, following Atkey's variable, arrow, and
    universal-quantification clauses. The public input is a closed type.
    Keep formula generation separate from simplification to familiar laws. *)

From SystemF.F Require Import Syntax Scope.
From SystemF.FreeTheorems Require Import Formula.
