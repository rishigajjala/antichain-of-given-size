# Native check diagnostics

The [27 October native `/check` output](native-check-20261027.txt) reports
successful compilation, standard axioms for all 37 registered declarations,
no proof placeholders or added axioms, and passing closure and layout checks.
Its overall result is **FAILED** for `surface-states` and
`hypothesis-is-in-the-bundle`.

The first heuristic counts indented lines after a declaration starts, including
its multiline type. The seven affected wrappers each have a single `exact`
proof. The CLI displays the first five of those diagnostics. Their proofs live
in the corresponding `Analysis` modules.

The second heuristic treats the two defining constraints of `BoundedProfile`
as borrowed results. `empty_zero` removes ground-set points in no generator;
`load_le` expresses the paper's generator-size bound. The proved
`Paper.mem_attainableValues_iff` and the expanded
`Model.attainableValues_membership` identify this representation with arbitrary
finite generating families allowed by the paper. These constraints do not add
an assumption to the counting theorem. `Prior` remains field-free.

Separate CLI messages about proved modules outside a selected theorem concern
that theorem's import closure. The repository contains other results as well;
the independent axiom audit covers all 124 library modules and their source
files. Those modules are retained.

The diagnostics are preserved. The two native heuristics were not changed,
and their failed result is not presented as a native check pass. Mathematical
verification and paper-to-Lean correspondence review are recorded separately.
