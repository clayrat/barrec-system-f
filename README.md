# System F through three algorithms

Rocq/OCaml companion to [plan-systemf.md](plan-systemf.md): Hindley-Milner
inference, a free-theorem generator, and normalization bounds through
bar recursion.

The project follows the layout of the preceding strictness-pcf lecture.
This checkout currently contains a buildable scaffold, the syntax and erasure
definitions from Blot's artifact, four shared typed examples, and a Rocq 9.1
adaptation of W-in-Coq.

## Status

| Component | Current status |
| --- | --- |
| F type/term syntax, lifting, type substitution, erasure | Copied from Blot; OPE `drop`/`keep` renaming and parallel substitution are proved equivalent to the original operations |
| Shared examples term1–term4 | Defined in Rocq; erasures and weak-head evaluations printed by the OCaml driver |
| Type-variable scope and Church checker | Complete: scope and OPE lemmas, computational `check_core`, proof-carrying `Checked`, `check`/`checkClosed`, success/completeness/rejection theorems, and kernel regressions |
| W and its corrected unifier | Complete Rocq 9.1 adaptation: proof-free `unify_exec`/`W_exec`, checked success and rejection contracts, universal checked/executable correspondence, and an extracted event trace whose erasure is proved equal to `runW_exec` |
| Relational formulas and generator | Complete: `relate_correct` proves generator correspondence, the separate abstraction lemma proves every intrinsic `fterm` logically related to itself, and `closed_fterm_satisfies_relgen` connects typed terms to generated formulas; `relate_presented` is a guarded post-pass over `relate`, with a general semantics-preservation theorem, and prints Church encodings as `Bool`, `[A]`, and `ListRel` |
| Independent WH-reducer | Implemented with a capped exact-step oracle and Rocq correspondence proofs |
| HM elaboration | Type level complete: W principal schemes are translated to closed System F types with explicit constant interpretation and checked/executable correspondence; term elaboration remains |
| Repaired bound and BBC experiment | Root cause patched; term1 and term4 satisfy the independent oracle, term3 remains a slow acceptance run |
| Surface parser | HM lecture fragment implemented: complete-input parsing, lexical name resolution, integer/`true` markers, and Church-pair expansion; explicit Church F input remains planned |
| Benchmark runner | Saves baseline/repaired runs and full differential BBC traces |

The new project code introduces no substitute axioms or admitted proofs.
Adapted W retains its explicit standard `Eqdep.Eq_rect_eq.eq_rect_eq`
dependency inherited from dependent inversion in the upstream development;
the observational bridge additionally uses standard proof irrelevance to
erase Hoare precondition witnesses.
Generator correctness is generic over an explicit `RelModel`; the separate
fundamental theorem is generic over its `ParametricModel` extension with
explicit abstraction beta laws. Neither introduces global axioms, and both
remain distinct from claims about the external BBC implementation. No
informative model is constructed: the one-point `unit_parametric_model` only
witnesses that the record laws are satisfiable, so the semantic theorems are
statements relative to any such model. The concrete `map`/`filter` laws are
stated directly over Rocq types from the generated relational contract.

## Build

Requires Rocq 9.1, OCaml, GNU Make, dune 3, and Python 3 for experiments.

~~~sh
make              # compile the Rocq modules
make demo         # compile, extract, and print the shared examples
make check        # current fast check: Rocq regressions and extracted demo
make bench-help   # options for the separate experiment runner
~~~

make check checks the build pipeline, audits the generated OCaml interface,
kernel-checked weak-head, unification,
proof-free W regressions, the universal checked/executable W bridge, the
proof-carrying Church checker, the relational generator, and the W-to-System-F
type bridge. The extracted demo checks the four shared Church inputs, one
rejection, proof-free W, prints its successful Church-pair trace and failing
occurs-check trace from parsed surface HM input, translates its principal
type, and prints the generated theorem for `forall X. X -> X` both directly
and through W. It also prints the readable free theorem for
`forall a. [a] -> [a]`; Rocq proves that specialising `ListRel` to the graph
of a function yields `map f (g xs) = g (map f xs)`. The demo also prints the
`filter` formula with its necessary premise `R x y -> p x = q y`; Rocq derives
the corresponding `filter`/`map` law when the predicates commute with the
mapping. The negative-occurrence example shows the additional commuting-square
premise and includes a checked counterexample to dropping it. Kernel
regressions also instantiate the separate fundamental theorem for the
intrinsic polymorphic identity and connect it to its generated formula.
The extraction audit requires all public W/checker/generator entry points and
all six trace events, rejects impossible generated stubs, checks that the
instrumented W does not rerun `runW_exec`, and reports the current cast count.
make clean removes compiler and extraction output; recorded experiment
results are preserved.

The root Makefile generates Makefile.coq from _CoqProject. That project
maps theories/ to the logical prefix SystemF. extraction/Extract.v stays
outside _CoqProject and is compiled by its own Makefile before dune runs.

## Layout

~~~text
theories/
  F/                 syntax, scope, Church checking, WH-semantics
  HM/                public W/unification facade and adapted W-in-Coq sources
  FreeTheorems/      formulas, generation, correctness
  BarRec/            repaired realizers and bound
  HMElab.v           principal-scheme/type bridge from W to Church F
  Examples.v         common inputs for proofs, extraction, and experiments
  Tests.v            fast algorithmic regressions
extraction/
  Extract.v          extraction entry points
  parser.ml          unverified HM surface parser and Church-pair expansion
  main.ml            executable lecture demo
  audit.py           structural checks for the generated OCaml boundary
  Makefile, dune
bench/
  run.py             time-limited runs and result recording
  results/           local logs; selected reference runs can be committed
vendor/blot/         untouched Blot baseline and original license
vendor/w-in-coq/     untouched W-in-Coq baseline and adaptation notes
patches/             compatibility and, later, semantic fixes
~~~

Source files marked planned contain explanatory comments and imports,
not implementations. The OCaml demo currently prints erased terms, exact
weak-head step counts, the resulting normal forms under a finite cap, the
identity theorem generated both directly and through W, and the readable
free theorems for lists, `filter`, and a negative type occurrence.

## Normalization-bound milestone

The original failure remains reproducible from the untouched vendored source:
term4 computes one weak-head step but returns bound 0 after roughly five
minutes. Differential tracing localized the defect to the inner `elim` in the
`TForall` branch of `isrc`: an open `rc T` formula was not instantiated with
the run-time term, so `repl` manufactured a spurious `(#0 #0)` BBC key.

The semantic patch in `patches/blot-f.v-bound.patch` also fixes simultaneous
substitution and context use under `FAbs`, while guarding a
dependent-extraction projection. It preserves Blot's reversed Coq spine
convention (`t :: p` under a right fold); JavaScript's append is paired with a
left fold. Recorded repaired runs give `term1: 0 <= 1`
and `term4: 1 <= 2`; term4 now takes about seven seconds. The original source,
baseline logs, repaired logs, and compressed traces are all retained. See
`bench/blot-baseline/`, `bench/blot-repair/`, and `bench/blot-trace/`.

The remaining numerical acceptance claim for term3 is unresolved: the
independent evaluator confirms one step, but the repaired bound exceeded a
recorded 30-minute timeout. Type application and nested-arrow inputs therefore
remain subject to the original combinatorial blow-up in both Coq/OCaml and
JavaScript; the patch is a correctness repair, not a general performance fix.
These inputs are excluded from the live demo. The W-in-Coq adaptation and the
proof-carrying Church checker are complete and remain independent of this slow
benchmark.

## Extraction boundary

Natural numbers currently remain Peano data. A future native mapping
must preserve truncated predecessor/subtraction and handle overflow.
Intrinsic terms and type-directed realizers may introduce casts in
extracted code; the PCF project's blanket rejection of Obj.magic is not
copied here. Inspect any casts and custom extraction constants explicitly.

The hand-written HM parser consumes complete input, resolves lexical names,
and sends its result to W; it remains outside Rocq's trusted kernel. A future
explicit Church F parser will produce `RawChurch`, whose acceptance belongs to
the extracted checker. The proof-free `unify_exec`/`runW_exec` and `runWTrace`
are extracted and used by the OCaml driver; the dependent W-in-Coq `runW` and
`unify''` stay inside Rocq as the reference proof. Rocq proves universal
observational correspondence for W, including the final fresh-variable state
before `runW` erases it, and proves that erasing the event list from
`runWTrace` returns exactly `runW_exec`. The adapted dependent W reaches
unification through a Hoare adapter over `unify_exec` with the original
contract; a rejection is reported as the certificate-free `UnifyRejected'`,
justified by `unify_exec_rejected_no_unifier`, so the dependent unifier is
never executed by `W`. Actual bound/BBC runs are kept out of the fast test
target; see [bench/README.md](bench/README.md).

## Sources and licensing

[Blot's baseline](vendor/blot/README.md) is retained unchanged, with its
original GPL license. F/Syntax.v reuses definitions from that artifact.
The untouched W-in-Coq snapshot is retained with its GPL license; its Rocq 9.1
adaptation is built under `SystemF.HM.WInCoq`. The plan records the distinct
reference roles of Atkey/ref-graphs and unification-cm; their code is not linked
into the executable.
