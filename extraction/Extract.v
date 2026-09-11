(** * Extraction driver

    Syntax, erasure, the independent weak-head reducer, and shared examples
    are currently exported. Add the checker, inference, relational generator,
    and finally the repaired bound as their implementations become available.

    Keep natural numbers as Peano data for now. Any later native numeric
    mapping must preserve truncated subtraction and predecessor, and
    address overflow for bounds. *)

From Stdlib Require Import Extraction ExtrOcamlBasic.
From SystemF.F Require Import Syntax OperationalSemantics.
From SystemF Require Import Examples.

Extraction Language OCaml.
Set Extraction Output Directory ".".

Extraction "systemf.ml"
  type_lift type_subst term_equal term_lift fterm_to_term
  term_subst1 wh_step run_fuel eval_cap
  type1 term1 type2 term2 term3 term4 erased_examples.
