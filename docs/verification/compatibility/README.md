# Tex2Lean compatibility evidence

This package records the local compatibility work used with Tex2Lean 1.0.2.
It contains build manifests and preserved JavaScript regression results, not a
CLI bundle, credentials, review-authority records, or a Lean proof certificate.
The installed Tex2Lean executable was not modified.

The reproduction source is `scripts/tex2lean-compat/` in the repository.
`manifest.json` records the exact tested source hashes. The v17 candidate passed
eight regression suites and 18 syntax checks on 27 October 2026; its manifest and
eight output logs are retained. The prior v16 seven-suite/17-syntax record is
also preserved. All tested sources match commit `8b661a7` and the current
repository source. No tests were rerun during this packaging update.

The earlier selected-target certificates and exports are **historical for
source `0d23ccef…`**. Counting had 11 verified mathematical rows and two excluded
metadata rows; main had seven verified rows, but its 06:27:01 handoff raised a
blocking placement issue for an internal helper on the Model surface. That
report is preserved and is not presented as a clean final handoff.

The helper was moved with the same name, type, proof body and individual closure
check into its Analysis proof file; the main dependency and global audit remain.
Eight scratch Lean files were moved outside the deliverable. Fresh strict checks passed on source `197605d3…` (commit `420d09b`). The actual
native `/check` rerun still failed the two heuristics described below, while build,
37 axiom roots, no-sorry, closure and layout checks passed. Main received a fresh
native certificate (generation 91) and its handoff completed at 06:57:31.876Z.
Counting generation 141 and its 07:19:21.488Z handoff are also exported. Splitting generation 9 and its 07:31:33.355Z handoff are exported too. All three
ordinary workflows finished in v17-main session 6885, which exited cleanly. None of the
older exports establishes current-source completion. See
`manifests/helper-relocation-source-transition.json`.

The build chain is pinned exactly:

| Artifact | SHA-256 |
| --- | --- |
| Installed upstream executable | `3beb95c9c3973589febe7ea44c778269fe291cc23652b5f935ffe630b18e3a08` |
| Extracted upstream 1.0.2 bundle | `ae68bb68d8b7d1333660add1a39474e007d43136b8ddab923850594ff79bc99d` |
| Base compatibility build v8 | `93d40c1b5465f43c456a0a46c63995a2d5f4439027fccbd57c3ecfee877af4b7` |
| Splitting task build v16 | `9237f86a4cfb4eccbcac971aca3c4e31784b24ddc2f5f723db48ba62d9d5fde5` |

The main and counting v17 builds retain their separately pinned authorities.
Their bundle SHA-256 values are respectively
`3ad5d8e73e524e1f24618c01718857e4d0aba12eacab6ad7979bfbb5e62f2ed0` and
`f3c83567f9b8d50dcc8aaa935024a6a264ca1dda519420f5a29d6c02106bbee6`.
Their complete manifests also pin copied support modules; the bundle hash alone
does not identify those modules. Main v17 has the same CLI bundle as v15, with
only its separately loaded adapter updated.

The v8 repairs cover import generation, provider effort propagation, two-process
diagnostic scheduling, transient helper-file inventory, complete handoff source
access, placement of whole-model checks, and safe transaction recovery. Two
ModelClosure fixes strengthen its treatment of private project constants and
project structure/constructor constraints; ModelClosure is therefore **not**
claimed unchanged from upstream. The v8 manifest records those changes and the
unchanged check regions separately.

The extension adds Codex-specific read-only source-inspection instructions.
Its optional ledger review and optional lifecycle/UI repairs default off;
both were explicitly enabled for v16 and v17. The lifecycle changes preserve
repeated
choice requests and attach only correctly targeted, currently certified handoff
progress. They do not create certificates. Its manifest records exact unchanged
certification, graph-construction, claim-evaluation, validation/store, and seal
regions. The optional inspection branch exposes complete elaborated types and
semantic bodies; the normal native interface-certification path and native
binding-validator loop remain intact.

The ledger adapter records **Codex assistant review under the user's authorized
formalization task; it does not assert human review**. It requires independently
pinned authority, source/configuration/toolchain evidence, current ledger heads,
explicit semantic review, and exact claim coverage. It uses the native immutable
review/publication APIs. The reviewed v17 addition supports only bindings
already marked stale by the
native validator for changed types or semantic roots. It preserves the old
record as superseded, creates a new proposed successor for exactly the same
obligation/declaration/file/module/role, and records fresh semantic approval.
Every publication rechecks the head and complete source pins. Interrupted
prefixes retain history without duplicate active bindings. It rejects verified
state shortcuts and identity changes, and it does not assign `verified`/`proved`
status or fabricate receipts/certificates. Subsequent ordinary Tex2Lean proof
reconciliation performs
native interface validation, binding verification, and certified-snapshot
publication. Target-specific native evidence belongs in the separate exported
workflow records, not in these JavaScript test results.

The actual current-source native `/check` result is **FAILED** for `surface-states`
and `hypothesis-is-in-the-bundle`. The unchanged proof-length heuristic counts
multiline theorem headers as proof lines. The CLI displays the first five entries;
isolated execution of the same hash-pinned native functions finds **six** affected
wrappers, each with a one-line `exact` proof. The older seven-wrapper count is
historical: the relocated helper is no longer in Model. The other heuristic flags
four lemmas with `BoundedProfile` domain data (`empty_zero` and `load_le`). These
encode removal of unused ground elements and the generating-set size bound;
the proved membership equivalence connects that representation to the paper.
This explanation does not change or suppress either native failure.

The fresh log, all eight raw terminal chunks, and the isolated reproduction are
in `logs/native-check-after-helper-20261027.txt`,
`manifests/current-native-check.json`, and `heuristic/`. The raw chunks match the
log after documented terminal newline normalization. The retained warning about
104 proved declarations outside the selected capstone's 117-file import closure
is separate from full-project checking. Kernel, axiom, closure and native
correspondence results are reported separately; they do not make `/check` pass.

`REPRODUCE.txt` gives the build and isolated test commands. The build manifests'
`cliExecuted: false` fields describe bundle construction, not whether that
constructed bundle was subsequently used for the native workflow. Test fixture
bundle hashes can differ from v16 because optional features and authority pins
are intentionally varied by the tests.

`RUNTIME-RECOVERY.md` records the explicit launch flags, the source-based stale
graph diagnosis, and the reversible cache recovery. The earlier default-Claude
handoff is retained externally as non-final evidence; it is not a successful
completion report. `manifests/counting-runtime-recovery.json` records the archive
hashes and restarted session. Its follow-up reference records the subsequently
historical counting certificate and handoff without changing the original recovery
record or accepting the earlier default-Claude report.

`manifests/main-runtime-provenance.json` records the seven native reviewed
successor proposals, the preserved already-exported counting graph, and the
explicit main launch flags. A mismatched configuration pin from an external
preparation script was corrected to the recomputed main-specific value; no
runtime or validator patch was made. That earlier main certificate belongs to the historical source; its handoff
completed with the preserved blocking finding. The new-source generation-91
certificate is separately retained as `manifests/main-current-certified-snapshot.json`;
the completed main and counting exports are referenced separately in
`manifests/main-current-export-reference.json` and
`manifests/counting-current-export-reference.json`; the final splitting record is
`manifests/splitting-current-export-reference.json`.

The current main report has seven proved/certified mathematical rows and retains
two explicit verification limitations: the read-only reviewer used saved strict
logs rather than launching a new build, did not independently hash dependency
checkout contents, and did not treat the empty statement-check stdout as proof
evidence by itself. Both native strings are preserved without clearing them.
Counting has 11 proved/certified mathematical rows and no unknowns; two reviewed
nonmathematical metadata rows remain excluded, so its native aggregate
`complete` and `whollyProved` fields are still false. All three refreshes use the
same v17-main process through ordinary native target selection. Authority pinning
restricts the optional review command, not normal selected-target verification.

The compatibility package contains no full review prompts, authority records,
credentials, or runtime bundles. Absolute paths retained in build/export
provenance identify the workspace, executables and external evidence locations;
reproduction instructions explicitly allow replacement on another machine.

Splitting has one proved/certified mathematical row, no unknowns, and both
native completion flags true. This package records completion of these three
selected native workflows, not separate native certificates for all 18 numbered
results. The full project proof audit and the unchanged two-failure mechanical
check remain distinct evidence.
