# Tex2Lean 1.0.2 compatibility fixes

These scripts build a **local patched copy**, not an upstream release. They
extract the exact bundled CommonJS source from the installed Node SEA executable;
they do not modify the installed CLI, Codex app, settings, or workflow records.
The reviewed source SHA-256 is
`ae68bb68d8b7d1333660add1a39474e007d43136b8ddab923850594ff79bc99d`.
The builder refuses a different bundle until its source is reviewed.

Twelve replacements address integration bugs, strengthen one check, and reduce
peak memory use:

- Restrict generated `Meta.Audit` imports to the selected library's modules,
  preventing a cycle through `scripts.CheckAxioms`. The separate axiom audit
  still imports and checks the library, including Meta modules.
- Supply configured effort to the structured Codex provider and emit its
  request/configured effort argument.
- Use configured effort when a proof worker has no explicit tier effort.
- Apply `Lean.privateToUserName` when deciding whether a constant belongs to
  the project namespace in ModelClosure. A private project definition has an
  internal `_private...` name that otherwise bypasses this filter. The original
  name remains the key for environment lookup and defining-module checks.
- Reduce concurrent Lean diagnostic processes from four to two for this
  16 GB machine. The file list, checks, and result processing are unchanged;
  every selected file is still checked. This does not change model worker
  concurrency. This CLI version exposes no configuration for this limit.
- Traverse constructor types of project inductives in ModelClosure, so
  structure field constraints are checked. Their names use the same private
  name classification; Mathlib inductive constructors remain unexpanded.
- At a planning boundary, regenerate Meta using the union of the current
  claims and `capstones.txt`. This preserves earlier claims when adding a
  result, so the whole-project surplus check evaluates the complete registered
  claim set. Every current claim remains included; duplicates are removed.
- Exclude the tool's transient Lean helpers from the source inventory only
  when they are at the project root and have an exact reserved basename:
  `.tex2lean-{inspection,axioms,public-refutation,refutation,interfaces,interface-values}-<32 lowercase hex digits>.lean`
  or `.tex2lean-side.lean`. These files are separately executed by the tool;
  including them in concurrent source scans changes the fingerprint despite
  unchanged author sources. Ordinary hidden Lean files, lookalike names, and
  all nested Lean files remain subject to the existing inventory rules.
- Give the three independent handoff readers absolute workspace, Lean project,
  and complete paper paths, plus a dynamic inventory of files actually present
  under the configured output directory's `verification/`. The Codex
  structured provider keeps its temporary working directory and read-only
  sandbox. The context asks readers to inspect relevant complete sources and
  actual log contents, flags empty/unavailable logs honestly, and preserves
  unknown findings when evidence is missing. Steering notes alone do not reach
  these gates in this CLI version.

Model selection is unchanged. The existing Codex effort mapping is preserved:
low and medium pass through; other configured levels map to high. Thus the
configured high is explicit rather than inheriting an unrelated global setting.
No proof, target status, or workflow verdict is patched. ModelClosure's
namespace predicate and project constructor traversal are strengthened as
described below; its other logic is unchanged.

## Build and test

From the repository root, choose an output directory outside the repository:

```sh
python3 scripts/tex2lean-compat/build_compat.py --output /tmp/antichain-tex2lean-compat
node --check /tmp/antichain-tex2lean-compat/out/cli.cjs
node scripts/tex2lean-compat/test_compat.cjs /tmp/antichain-tex2lean-compat/out/cli.cjs
```

Use the available Node executable in place of `node`; the builder accepts
`--node /absolute/path/to/node` and `--installed /absolute/path/to/tex2lean`.
Its default Node path is the Codex desktop runtime used for this project.
The generated launcher is `/tmp/antichain-tex2lean-compat/tex2lean`.
Output includes the bundle, exact replacement list, diff, and hash manifest;
do not commit those generated files.

The isolated tests execute the actual import selector, argument helpers, and
structured-provider method with mocked filesystem and process operations.
They check retained library modules, excluded audit consumers, configured and
explicit effort, preserved model selection, and unchanged sandbox arguments.
They also inspect the generated ModelClosure source for the corrected private
name classification, traversal of project constructor types, and unchanged
environment lookup keys, and run the actual diagnostic scheduler with mocked
Lean processes to verify that all files are
checked with peak concurrency two. They execute the planning-boundary helper
with mocked registry reads and regeneration to verify that registered and
current claims are both retained. Mocked filesystem tests run the actual
collector against every reserved helper family and check that authored and
nested Lean files are retained. The actual shared handoff runner is exercised
with mocked providers: every independent gate receives the absolute paths and
read-only access instructions, missing/empty logs are not described as passes,
and `unknown` verdicts remain unchanged. They neither run Lean, launch a model, nor
start a Tex2Lean workflow. After switching to this copy, re-run the Lean check
controls and the complete project validation.

Stop the existing workflow and its workers before resuming through the local
launcher with the same project and target arguments. Keep using that launcher
for subsequent gates; the unpatched CLI would regenerate the import cycle.
Do not add a model override unless one is intended.

## Project setup

`formalize.json` keeps the repository's Lean and Mathlib v4.32.0 pins. Run
`setup` through the patched launcher before resuming a workflow if that base
environment is not already available. The `lean.useArlib: never` setting
selects a Mathlib-only setup environment: this paper has no program or
resource-cost claim. The repository still pins Arlib for the generated
CostSeal checker and its tests. Those required modules compile under the
repository's fixed Lean version; the setup does not remove that dependency.

The ordinary Lean build and audits verify the saved formalization without
running Tex2Lean or this launcher.

## Unchanged check implementations

The builder verifies byte equality against the original bundle and records
these SHA-256 hashes in its output manifest:

| Source generator | SHA-256 |
| --- | --- |
| CostSeal permission lists | `30a2031f6b77551a827ae0dcfb94a44bc2522cb4677c728b9c489345820e80b5` |
| CostSeal checker | `dc3f2b931729a7a4348d0ce82365fc47c4aa8edee37c8ca3b0fb101e18a3156d` |
| Meta phase regeneration | `c15368cae42210d1bf457a5bb666c329300be08dbf69164c5a45c7bbdbf84d9a` |
| Audit template | `c3baa7968dcd43cc1b5b15915d94648e70b6ace1d8a91504914aed25df3424bf` |

The audit template receives a corrected module list; its checks and regeneration
remain unchanged.

The builder separately records the collector's original and patched hashes
under `source_inventory` and verifies that its only change is the narrow
root-helper filter. The complete before/after-build and inspection source
fingerprint checks are byte-identical to the original bundle and are also
recorded in `unchanged_check_sha256`.

## Handoff source evidence

The handoff patch does not add a new command-line option. Keep the normal
project, Lean-directory, and output-directory arguments. Before handoff, place
captured verification results in `<output directory>/verification/` with
commands, exit codes, timestamps, and source hashes where available. The
locator lists what exists when the handoff runs; it does not create logs,
assume named files exist, or certify their freshness or contents. Empty logs
can be interpreted alongside a separate recorded exit status, but are not
success evidence on their own.

The builder verifies that the complete handoff runner differs only by appending
this source-access context to the existing shared prompt. The independent
requests, schemas, verdict aggregation, and final writer's instructions remain
unchanged. Before/after runner and locator hashes are recorded under
`handoff_evidence` in the manifest. The provider's sandbox and temporary
working-directory behavior are unchanged.

## Strengthened ModelClosure check

The original ModelClosure generator SHA-256 is
`09e04c01c1dd639b7ecd1422c0f833e95ca3353b11313bccdf9b0e02287c4625`.
The strengthened generator SHA-256 is
`4decc75f0f568076797d0d2878a7aab2b5e91795bc65c34ffdef79859b7bfaa0`.
The builder verifies that the entire generator differs only in the namespace
predicate and project constructor traversal above and records its original
and new hashes under
`strengthened_check_sha256` in the manifest. This supersedes the earlier
four-patch version's claim that ModelClosure was byte-identical.

The builder also verifies that the diagnostics function differs only in its
concurrency argument and records the before/after hashes under
`resource_tuning`.

The corresponding Lean negative control is a private definition outside
`Model/` used in a public theorem statement: `#modelClosureOfType` must reject
it. Another control must reach an external definition through a project
structure's field type, and require that definition in the rejection
diagnostic. This detects the previous omission of constructor types even when
the structure itself is already reported. A Mathlib-only statement and a
theorem whose proof, but not statement,
uses an external definition must still pass. The JavaScript tests do not
substitute for these Lean controls.

The public release repository does not contain the matching TypeScript
development source, so this narrowly patches the reviewed installed bundle.
