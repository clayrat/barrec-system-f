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
| F type/term syntax, lifting, type substitution, erasure | Copied from Blot, with Blot's intrinsic `fterm` renamed to the typing derivation `fderiv` (`fterm` is the annotated Church syntax); OPE `drop`/`keep` renaming and parallel substitution are proved equivalent to the original operations |
| Shared examples term1–term4 | Defined in Rocq; erasures and weak-head evaluations printed by the OCaml driver |
| Type-variable scope and Church checker | Complete: scope and OPE lemmas, computational `check_core`, proof-carrying `Checked`, `check`/`checkClosed`, success/completeness/rejection theorems, and kernel regressions |
| W and its corrected unifier | Complete Rocq 9.1 adaptation: proof-free `unify_exec`/`W_exec`, checked success and rejection contracts, universal checked/executable correspondence, an extracted event trace, and generated monomorphic/let-polymorphic `let x_(n+1) = (x_n, x_n)` stress families |
| Relational formulas and generator | Complete: `relate_correct` proves generator correspondence, the separate abstraction lemma proves every intrinsic `fderiv` logically related to itself, and `closed_fderiv_satisfies_relgen` connects typed terms to generated formulas; `relate_presented` is a guarded post-pass over `relate`, with a general semantics-preservation theorem, and prints Church encodings as `Bool`, `[A]`, and `ListRel` |
| Independent WH-reducer | Implemented with a capped exact-step oracle and Rocq correspondence proofs |
| HM elaboration | Complete: semantic tree reification preserves W typing, dead internal variables default to `forall X. X -> X`, every constructed term is accepted by `checkClosed` exactly at `hm_principal_type`, and public `runWChurch` succeeds iff `W_elab` succeeds |
| Repaired bound and BBC experiment | Repaired `term_subst`/`isrc`/`adeq`/`bound` are ported to `BarRec/Bound.v` over the shared syntax and extracted with the reviewed `brec`; the ordinary demo consumes live `query`/`hit`/`miss`/`update` events, term1 and term4 satisfy the independent oracle, while term3 remains a slow acceptance run |
| Surface parsers | HM lecture fragment and full explicit Church-style F implemented; both consume complete input and resolve names, while only verified `checkClosed` decides Church typing |
| Benchmark runner | Builds the separate project normalization oracle and saves baseline/repaired runs and full differential BBC traces |

The only project-level parameter is Blot's explicit `BarRec.Bound.brec`
extraction boundary; no theorem claims adequacy of its supplied OCaml
implementation. The remaining new project code introduces no substitute
axioms or admitted proofs.
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
make hm HM_SOURCE='let id = fun x -> x in id id'
make church CHURCH_SOURCE='Lambda X. fun (x : X) -> x'
make brec-demo    # print only the concise live BBC demand trace
make reference    # run the hand-written readable OCaml counterpart
make check        # current fast check: Rocq regressions and extracted demo
make hm-evil      # measure the generated Algorithm W stress family
make bench-help   # options for the separate experiment runner
~~~

The HM frontend accepts variables, application, `fun x -> term`, non-recursive
`let x = bound in body`, non-negative integer markers, `true`, and pairs. The
interactive `--hm` route resolves names, prints a single-pass W trace, its
principal HM/System F types, and the generated free theorem. Pure successful
inputs additionally pass through the checked W-to-Church bridge and a capped
exact weak-head evaluation; inputs containing constants still show inference
but skip term reification because constants have no runtime interpretation.

The Church frontend accepts variables, application, explicit type application,
typed lambdas, type abstractions, right-associative arrows, and universal
types. For example:

~~~text
Lambda X. fun (f : X -> X) -> fun (x : X) -> f x
(Lambda X. fun (x : X) -> x) [forall X. X -> X]
~~~

Both `fun (x : A) -> body` and the compact `fun x : A. body` binder forms are
accepted. `Lambda X. body` introduces a type variable and `forall X. A`
introduces a universal type.

make check checks the build pipeline, audits the generated OCaml interface,
kernel-checked weak-head, unification,
proof-free W regressions, the universal checked/executable W bridge, the
structural W elaborator and its source/type/result contracts,
proof-carrying Church checker, the relational generator, and the W-to-System-F
type and term bridges. The extracted demo checks the four shared Church inputs,
one rejection and proof-free W.  Its Curry/Church boundary block exhibits two
checker-accepted Church identities with the same erased lambda term but
different System F types, shows an explicit type application disappearing,
and then uses W to restore the principal rank-1 Church identity.  It runs the main
`let id = fun x -> x in id id` input through its retained Church certificate,
exact two-step weak-head evaluation, and free-theorem branch; then prints its
successful Church-pair trace and failing occurs-check trace from parsed surface
HM input and translates its principal type. It also prints the readable free theorem for
`forall a. [a] -> [a]`; Rocq proves that specialising `ListRel` to the graph
of a function yields `map f (g xs) = g (map f xs)`. The demo also prints the
`filter` formula with its necessary premise `R x y -> p x = q y`; Rocq derives
the corresponding `filter`/`map` law when the predicates commute with the
mapping. The negative-occurrence example shows the additional commuting-square
premise and includes a checked counterexample to dropping it. Kernel
regressions also instantiate the separate fundamental theorem for the
intrinsic polymorphic identity and connect it to its generated formula.
The demo also measures the classic pair-duplication family without printing
its rapidly expanding types.  In addition to ordinary tree size it constructs
an explicit maximally shared DAG whose `arrow` nodes contain child identifiers.
A fixed-result monomorphic control has tree sizes 1, 7, 19, 43, 91 but DAG
sizes 1, 5, 8, 11, 14.  For the actual W terms at depths 0 through 3, the
lambda-bound-base variant has tree/DAG sizes 3/2, 9/6, 21/14, 45/30; the
let-polymorphic variant has 3/2, 11/8, 27/20, 59/44.  The real language has no
primitive products: its Church pair contains a result variable that is itself
generalized, so even the first W family loses some of the control's ideal
sharing, and fresh let instantiation loses more.  Both source families remain
linear in the depth. These observations are regression measurements, not a
complexity lower-bound theorem.
Choose the other base or a larger family without printing the expanded type:

~~~sh
make hm-evil HM_EVIL_ARGS='--variant mono --depth 8'
make hm-evil HM_EVIL_ARGS='--variant poly --depth 8'
~~~

The extraction audit requires all public W/checker/generator entry points and
all six trace events, rejects impossible generated stubs, checks that the
instrumented W does not rerun `runW_exec`, verifies the opt-in live `brec`
hooks, checks the native-integer natural-number boundary, and reports the
current cast count.
make clean removes compiler and extraction output; recorded experiment
results are preserved.

The root Makefile generates Makefile.coq from _CoqProject. That project
maps theories/ to the logical prefix SystemF. extraction/Extract.v stays
outside _CoqProject and is compiled by its own Makefile before dune runs.

## Layout

~~~text
theories/
  F/                 syntax, scope, Church checking, WH-semantics
  F/Typing.v         extrinsic Church typing and checker completeness
  HM/                public W/unification facade and adapted W-in-Coq sources
  HM/W/              adapted W-in-Coq sources, logical prefix SystemF.HM.W
  FreeTheorems/      formulas, generation, correctness
  BarRec/            repaired realizers and bound
  HMElab.v           principal-type bridge and W-tree reification to fterm
  CurryChurchBoundary.v  checked many-to-one erasure and rank-1 recovery demo
  Normalization.v    checked intrinsic term to bound-driven WH reduction
  HM/ElabScope.v      decidable constant-free source fragment for W elaboration
  HM/ElabSemantics.v  interpretation of W types, schemes, and substitutions
  HM/Erasure.v        named HM scope and erasure to the common untyped term
  HM/TypeDAG.v        unique hash-consed HM nodes and verified DAG decoding
  HM/WElab.v          structural W tree and correspondence with checked W
  Examples.v         common inputs for proofs, extraction, and experiments
  Tests.v            fast algorithmic regressions
extraction/
  Extract.v          extraction entry points
  parser.ml          unverified HM surface parser and Church-pair expansion
  church_parser.ml   full explicit Church F parser with de Bruijn resolution
  main.ml            executable lecture demo
  hm_evil.ml         tree/DAG-size CLI for the generated Algorithm W family
  audit.py           structural checks for the generated OCaml boundary
  Makefile, dune
reference/
  systemf_native.ml  hand-written native view of W, relgen, brec, checker/reducer
  README.md          correspondence and trust-boundary notes
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
The same reviewed repair is now materialized in `theories/BarRec/Bound.v`
against the project's shared `F.Syntax` definitions; the isolated patching
runner remains the reproducibility oracle for the port.
The pre-optimization project normalization trace for `term1` contains the
same 75 BBC invocations and 45,300 ordered events as that isolated repaired
build, which checks the custom extraction boundary and the port together.
The current custom extraction memoizes repeated pure oracle calls within one
`brec_aux` state: the same bound now needs 14 invocations and 1,736 recorded
events, while `term4` drops from about 7.5 seconds to about 0.03 seconds.
The production extraction also exposes silent-by-default observation hooks.
`make demo` installs a handwritten consumer around `bound type1 term1`, prints
the first 16 live `query`/`hit(state)`/`hit(cache)`/`miss`/`update` events and
then summarizes the full run. Setting `BLOT_TRACE_FILE` retains the historical
nine-column TSV format; the resulting term1 trace is byte-for-byte identical
to the previously instrumented copy.
The live summary counts every requested key as a `query` before lookup
(1,400 for term1); the historical TSV folds the outcome into its phase, so it
reports 700 underlying state queries plus 700 cache hits.

For the third-block slide without the preceding W/free-theorem output:

~~~sh
make brec-demo
~~~

The remaining numerical acceptance claim for term3 is unresolved. On the
final memoized native-`int` project extraction, independent 10- and 30-minute
runs both report one exact step immediately and then time out before `bound`
returns; their metadata, logs, tool versions, and input hashes are retained in
`bench/results`. Type application and nested-arrow inputs therefore remain
subject to the original combinatorial blow-up in both Coq/OCaml and JavaScript;
the patch is a correctness repair, not a general performance fix.
These inputs are excluded from the live demo. The W-in-Coq adaptation and the
proof-carrying Church checker are complete and remain independent of this slow
benchmark.

The public W normalization frontend is exact-first: a successful
`eval_cap 32` supplies an exact fuel bound and is proved to reproduce the
reported WHNF; only cap exhaustion falls back to BBC. Thus `w-let-id` now
returns bound 2 and `lambda. #0` immediately. `runWBarNormalization` remains
the explicit strict Blot path for timeout-controlled experiments, so the
performance limitation is visible rather than silently attributed to BBC.

## Extraction boundary

Natural numbers are extracted through `ExtrOcamlNatInt`, so public counters,
indices, fuel and bounds are ordinary OCaml `int` values. The standard mapping
keeps `pred 0 = 0` and truncated subtraction; both properties are checked by
the extraction audit and the executable demo. Inputs are rejected when
negative, while overflow above `max_int` remains an explicit extraction trust
boundary (the frontend also prevents its binder counter from wrapping).
Intrinsic terms and type-directed realizers introduce 68 reviewed casts in
the extracted repaired bound. The audit fixes that count, localizes the two
impossible branches to `adeq_var`, and checks the shape of the custom `brec`
implementation; any drift requires explicit review.

The hand-written HM parser consumes complete input, resolves lexical names,
and sends its result to W. The separate Church parser handles the complete
explicit F grammar, resolves term and type names in independent de Bruijn
namespaces, and produces `fterm`; syntax accepted by it is still accepted
or rejected only by verified `checkClosed`. Both parsers remain outside Rocq's
trusted kernel. The
verified-side `runWChurchChecked` now reifies W's structural decisions into
`fterm`, validates the result through `checkClosed`, and retains its
intrinsic `fderiv`; its success theorem equates the checked type, W's
translated principal type, and the type exposed by the bridge. The general
erasure theorem identifies that intrinsic term with `erase_hm_closed` of the
source. Internal W metavariables absent from the principal result are
consistently instantiated with the fixed closed type `forall X. X -> X`;
Rocq proves that structural reification then succeeds exactly when `W_elab`
succeeds. The universal theorem
`runWChurch_unchecked_checkClosed_principal` proves that every constructed raw
term is accepted by `checkClosed` exactly at `hm_principal_type`; consequently
the public `runWChurch` succeeds iff `W_elab` succeeds (for a closed constant
interpretation). The proof-free
`unify_exec`/`runW_exec` and `runWTrace`
are extracted and used by the OCaml driver; the dependent W-in-Coq `runW` and
`unify''` stay inside Rocq as the reference proof. Rocq proves universal
observational correspondence for W, including the final fresh-variable state
before `runW` erases it, and proves that erasing the event list from
`runWTrace` returns exactly `runW_exec`. The adapted dependent W reaches
unification through a Hoare adapter over `unify_exec` with the original
contract; a rejection is reported as the certificate-free `UnifyRejected'`,
justified by `unify_exec_rejected_no_unifier`, so the dependent unifier is
never executed by `W`. Actual bound/BBC runs are kept out of the fast test
target. The separately built normalization oracle checks that the public
wrapper preserves its erasure, that the exact weak-head step count does not
exceed its bound, and that bound-fuel reduction reaches the independently
computed WHNF. It reports whether that bound came from exact evaluation or
bar recursion; see [bench/README.md](bench/README.md).

## Sources and licensing

[Blot's baseline](vendor/blot/README.md) is retained unchanged, with its
original GPL license. F/Syntax.v reuses definitions from that artifact.
The untouched W-in-Coq snapshot is retained with its GPL license; its Rocq 9.1
adaptation is built under `SystemF.HM.W`. Upstream is
[rafaelcgs10/W-in-Coq](https://github.com/rafaelcgs10/W-in-Coq); the vendored
snapshot is revision `a579e188b402a462840250e6f454fd6752b116bc`. The plan
records the distinct reference roles of Atkey/ref-graphs and unification-cm;
their code is not linked into the executable.
