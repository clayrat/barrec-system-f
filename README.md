# System F through three algorithms

Rocq/OCaml companion to [plan-systemf.md](plan-systemf.md): Hindley-Milner
inference, a free-theorem generator, and normalization bounds through
bar recursion.

The project follows the layout of the preceding strictness-pcf lecture.
This checkout currently contains a buildable scaffold, the syntax and
erasure definitions from Blot's artifact, and four shared typed examples.

## Status

| Component | Current status |
| --- | --- |
| F type/term syntax, lifting, type substitution, erasure | Copied from Blot; compiled in the new namespace |
| Shared examples term1–term4 | Defined in Rocq; erasures and weak-head evaluations printed by the OCaml driver |
| Type-variable scope and Church checker | Module scaffolds |
| W and its corrected unifier | Module scaffold; upstream archive retained |
| Relational formulas and generator | Module scaffolds |
| Independent WH-reducer | Implemented with a capped exact-step oracle and Rocq correspondence proofs |
| HM elaboration | Module scaffold |
| Repaired bound and BBC experiment | Pending; original baseline and compatibility patch retained |
| Surface parser | Scaffold only |
| Benchmark runner | Executes a command with a timeout and saves its output |

The scaffold introduces no substitute axioms or admitted proofs.
The future correctness claims must distinguish checked theorems, semantic
assumptions used for parametricity, and the external BBC implementation.

## Build

Requires Rocq 9.1, OCaml, GNU Make, dune 3, and Python 3 for experiments.

~~~sh
make              # compile the Rocq modules
make demo         # compile, extract, and print the shared examples
make check        # current fast check: the build and scaffold demo
make bench-help   # options for the separate experiment runner
~~~

make check checks the build pipeline and the current kernel-checked
weak-head reduction regressions. It does not claim algorithmic coverage
for the remaining planned components. Add further regression proofs to
theories/Tests.v as those algorithms become available.
make clean removes compiler and extraction output; recorded experiment
results are preserved.

The root Makefile generates Makefile.coq from _CoqProject. That project
maps theories/ to the logical prefix SystemF. extraction/Extract.v stays
outside _CoqProject and is compiled by its own Makefile before dune runs.

## Layout

~~~text
theories/
  F/                 syntax, scope, Church checking, WH-semantics
  HM/                W and unification
  FreeTheorems/      formulas, generation, correctness
  BarRec/            repaired realizers and bound
  HMElab.v           bridge from W to Church F
  Examples.v         common inputs for proofs, extraction, and experiments
  Tests.v            fast algorithmic regressions
extraction/
  Extract.v          extraction entry points
  parser.ml          planned unverified surface front end
  main.ml            executable lecture demo
  Makefile, dune
bench/
  run.py             time-limited runs and result recording
  results/           local logs; selected reference runs can be committed
vendor/blot/         untouched source baseline and original license
patches/             compatibility and, later, semantic fixes
~~~

Source files marked planned contain explanatory comments and imports,
not implementations. The OCaml demo currently prints erased terms, exact
weak-head step counts, and the resulting normal forms under a finite cap.

## First implementation milestone

Make the reported bound failure reproducible using the original baseline,
a saved driver, shared fixtures, and a minimal independent WH-reducer.
The rule is fixed by Blot's specification: reduce a head beta-redex along
the application spine and stop at weak-head normal form.

Repair bound against that reference, then connect the Church checker.
W and the relational generator can be developed independently.

## Extraction boundary

Natural numbers currently remain Peano data. A future native mapping
must preserve truncated predecessor/subtraction and handle overflow.
Intrinsic terms and type-directed realizers may introduce casts in
extracted code; the PCF project's blanket rejection of Obj.magic is not
copied here. Inspect any casts and custom extraction constants explicitly.

The hand-written parser will produce raw syntax; acceptance belongs to
the extracted checker. Actual bound/BBC runs are kept out of the fast
test target; see [bench/README.md](bench/README.md).

## Sources and licensing

[Blot's baseline](vendor/blot/README.md) is retained unchanged, with its
original GPL license. F/Syntax.v reuses definitions from that artifact.
The W archive and both reference PDFs remain at the project root.
The plan records the exact role of W-in-Coq, Atkey, ref-graphs, and
unification-cm; only the Blot syntax has been imported at this stage.
