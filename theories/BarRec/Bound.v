(** * Bar-recursive normalization bound — external repair validated

    The untouched input artifact is vendor/blot/Coq/f.v. Its reported
    underestimation on Examples.term4 is reproduced by the saved experiment
    in bench/blot-baseline/: the independent reducer takes one step while the
    extracted baseline returns zero. The reviewed repair is kept as
    patches/blot-f.v-bound.patch and validated in bench/blot-repair/: it gives
    bound 2 for that one-step term. The source remains external here until the
    logic and realizers are factored into the SystemF namespace.

    The executable BBC implementation is an extraction boundary. Neither
    a passing Rocq build nor a finite benchmark proves its adequacy.
    Record those assumptions separately from the checked syntax and W.

    There is intentionally no replacement bound or placeholder axiom here. *)

From SystemF.F Require Import Syntax.
