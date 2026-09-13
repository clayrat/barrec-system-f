(** * Extraction driver

    Syntax, erasure, the independent weak-head reducer, the proof-free HM
    inference ([unify_exec], [runW_exec]), and shared examples are exported.
    The dependent W-in-Coq [runW] and [unify''] stay inside Rocq as the
    reference proof; their equivalence with the extracted code is the
    theorem [runW_exec_checked_correspondence]. Add the checker, relational
    generator, and finally the repaired bound as they become available.

    Keep natural numbers as Peano data for now. Any later native numeric
    mapping must preserve truncated subtraction and predecessor, and
    address overflow for bounds. *)

From Stdlib Require Import Extraction ExtrOcamlBasic.
From SystemF.F Require Import Syntax OperationalSemantics.
From SystemF.HM Require Import Infer Unify Examples.
From SystemF Require Import Examples.

Extraction Language OCaml.
Set Extraction Output Directory ".".

Extraction "systemf.ml"
  type_lift type_subst term_equal term_lift fterm_to_term
  term_subst1 wh_step run_fuel eval_cap
  type1 term1 type2 term2 term3 term4 erased_examples
  unify_exec runW_exec
  repeated_application infer_exec_succeeds.
