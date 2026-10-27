# Native check diagnostics

The [current native `/check` output](compatibility/logs/native-check-after-helper-20261027.txt)
was recorded after the helper relocation, on source fingerprint `197605d3…`
(commit `420d09b`). It reports successful compilation, standard axioms for all
37 registered declarations, no proof placeholders or added axioms, and passing
closure and layout checks. Its overall result is **FAILED** for `surface-states`
and `hypothesis-is-in-the-bundle`. The [earlier native output](native-check-20261027.txt)
is preserved as historical evidence.

The first heuristic counts indented lines after a declaration starts, including
its multiline type. Reproducing the unchanged native functions on the current
four Model files finds **six** affected wrappers, each with a single `exact`
proof: `attainableValues_membership`, `attainable_count`, `alpha_eventual_upper`,
`alpha_lower_density_one`, `alpha_maximum_order`, and `alpha_asymptotic_order`.
The CLI displays only the first five diagnostics. The [hash-pinned reproduction](compatibility/heuristic/reproduction.json)
records all six; their proofs live in the corresponding `Analysis` modules.
The earlier count of seven included `alpha_simultaneous_density_one`, which now
lives in Analysis with its statement and proof unchanged.

The second heuristic flags four lemmas with a `BoundedProfile K B` parameter:
`paper_headers`, `paper_exceptional_bound_and_agreement`, `paper_record_counts`,
and `paper_tail_bounds`. Its two defining constraints describe the paper's
allowed families: `empty_zero` removes ground-set points in no generator, and
`load_le` expresses the generator-size bound. The proved
`Paper.mem_attainableValues_iff` and the expanded
`Model.attainableValues_membership` identify this representation with arbitrary
finite generating families allowed by the paper. These constraints do not add
an assumption to the counting theorem. `Prior` remains field-free.

A separate CLI warning reports 104 proved declarations in eight files outside
the selected capstone's 117-file import closure. This is a statement about that
capstone's reachability in a repository containing several results and audit
tests. The independent axiom audit covers all 124 library modules and their
source files. The warning and those modules are retained.

Neither heuristic was changed or suppressed. Their failed result is not
presented as a native check pass. Mathematical verification and paper-to-Lean
correspondence review are recorded separately; successful certificates or
handoffs do not change the mechanical result above.
