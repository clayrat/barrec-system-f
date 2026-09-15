# Native OCaml reference

[`systemf_native.ml`](systemf_native.ml) is the hand-written, readable
counterpart of the generated `extraction/systemf.ml`, following the convention
used by `strictness-pcf/reference/pcf_native.ml`.

It is deliberately a reference implementation, not a second verified
artifact.  The Rocq definitions and extracted module remain authoritative.
The file keeps the executable ideas needed to read the lecture end to end:

| Native section | Rocq/generated counterpart |
| --- | --- |
| explicit Church checker | `F.Checker.checkClosed` |
| weak-head reducer | `F.OperationalSemantics.eval_cap` |
| Algorithm W and its trace | `HM.W.runW_exec`, `HM.Trace.runWTrace` |
| shared HM type DAG | `HM.TypeDAG` |
| relational formula generator | `FreeTheorems.Generator.relgen` |
| memoising bar-recursion boundary | custom extraction of `BarRec.Bound.brec` |

The native relational AST uses generated names instead of de Bruijn indices;
`Bool` and `[A]` are presentation abbreviations only.  The full proof-carrying
W-to-Church elaborator, parser frontends, logical-relation proofs, and the
dependent `isrc`/`adeq`/`bound` network are not duplicated.  Their erased
generated code contains casts whose safety comes from Rocq typing, so rewriting
them as apparently ordinary native OCaml would obscure rather than explain the
trust boundary.  The native file does include the exact memoisation/update
shape supplied for the `brec` parameter and a small observable demand trace.

Regenerate and audit the authoritative extraction, then run the native smoke
tests with:

```sh
make extract
make reference
```

The second command invokes the OCaml toplevel directly and produces no build
artifacts.  `make check` runs both the extracted demo and this native reference.
