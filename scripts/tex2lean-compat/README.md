# Tex2Lean 1.0.2 compatibility fixes

These scripts build a **local patched copy**, not an upstream release. They
extract the exact bundled CommonJS source from the installed Node SEA executable;
they do not modify the installed CLI, Codex app, settings, or workflow records.
The reviewed source SHA-256 is
`ae68bb68d8b7d1333660add1a39474e007d43136b8ddab923850594ff79bc99d`.
The builder refuses a different bundle until its source is reviewed.

Exact replacements address integration bugs, strengthen one check, and reduce
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
- Stop the missing-invocation repair from adding a whole-`Model` surplus check
  seeded only by the current theorem file. In a project with multiple results,
  that incorrectly flags definitions used by other registered claims. Each
  theorem retains its `#modelClosureOfType` and existing `#print axioms` checks.
  The global surplus check remains in `Meta/Audit`, imports the full library,
  and uses the union of all registered and current claims. The default root
  still imports that audit, and the mandatory seal check still rejects a
  project with no surplus invocation. Existing source commands are not deleted
  by this patch; it only suppresses the redundant generated insertion.
- Protect transaction recovery from concurrent checkpoint refresh and snapshot
  failures. A missing child file cannot be mistaken for a missing project;
  live transactions cannot be recovered as interrupted runs; and an old empty
  unscoped journal is rejected before deleting any files. The details and
  regression coverage are below.

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

The per-file repair test covers two theorem claims, preserving their closure
and axiom commands without inserting a global surplus command. It also checks
the actual global Audit and root templates, the registry/current-claim union,
and the unchanged mechanical check's rejection when surplus checking is absent.

The recovery tests execute the actual snapshot, open, prepare, commit, rollback,
recovery, and checkpoint-refresh functions against an in-memory filesystem.
They reproduce descendant `ENOENT`, an atomic-write temporary disappearing,
recovery during journal publication, concurrent recovery callers, and opening
a new transaction while old recovery is pending. They check that bogus empty
journals fail before mutation, ordinary files and completed work survive,
valid scoped and verified empty/missing-project rollback still work, and only
missing-file deletion errors are tolerated. They also test preservation of live
protection after failed publication/rollback, and reject restoration of stale
atomic temporaries or transaction journals recorded in a legacy snapshot.

Stop the existing workflow and its workers before resuming through the local
launcher with the same project and target arguments. Keep using that launcher
for subsequent gates; the unpatched CLI would regenerate the import cycle.
Do not add a model override unless one is intended.

## Transaction recovery

The original `rf` catches errors from both the root-directory check and the
entire snapshot in one `try`. If a temporary checkpoint file disappears during
that snapshot, its `ENOENT` is treated as an absent project and an empty journal
is written. Restoring that unscoped journal would delete project files. The
patched function catches missing-root errors only around the root check;
descendant snapshot errors abort before journal creation.

The original checkpoint refresh calls recovery before checking whether a run
is active. Recovery can therefore restore a live planning snapshot. The patch
returns early while workers or a transaction are active, registers each live
transaction before journal publication, and releases it only after successful
commit or rollback cleanup. Recovery runs once at a time per project; opening
a transaction waits for pending recovery. This coordination is process-local;
the CLI's existing project lease remains responsible for excluding another CLI.

Full snapshots omit only native `*.writing-<milliseconds>-<hex>` atomic-write
temporaries and the configured transaction directory. Other output files are
still covered by rollback. Legacy snapshots cannot restore these temporary or
journal paths either. A disappearance during deletion is harmless only for
`ENOENT`/`FileNotFound`; permission and other I/O errors still abort.

Empty unscoped snapshots require an explicit `emptySnapshotReason` recorded by
a successful root check/snapshot (`project-missing` or `project-empty`). That
reason survives preparation and reload. Unmarked legacy empty journals are
preserved and rejected before mutation; scoped empty snapshots retain their
ordinary meaning. These guards change recovery bookkeeping, not proof status,
mathematical checks, correspondence decisions, or completion criteria.

If an earlier CLI already produced an invalid journal, stop its process and
workers and preserve the working tree first. Review the journal against that
backup. Move a confirmed invalid journal intact to a separate recovery backup,
record its SHA-256 and the reason, and verify the destination before restarting.
Do not fabricate a replacement baseline or mark a theorem complete. This
builder does not move, repair, or delete any existing workflow record.

The output manifest records before/after hashes for every changed recovery
function under `transaction_recovery`. All previously listed mathematical
checker hashes and source-fingerprint checks remain unchanged by these fixes.

## Project setup

Resolve directory symlinks before starting a run. From the repository checkout,
use `project_dir="$(pwd -P)"`, then `cd "$project_dir"` and pass
`--project "$project_dir"` to the launcher. The working directory and project
argument must identify the same physical directory: a symlink alias can be
rejected by a nested Codex worker's writable-root check.

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

The root-module template and mandatory seal-invocation check are also verified
byte-identical. `surface_check_placement` records the sole change to the
per-file invocation generator. No surplus-check implementation or global
coverage is removed.

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


## v9 source-inspection extension

The self-contained [`extensions/`](extensions/README.md) package applies one
additional default fix to the exact v8 output above. Codex inspection workers
can use equivalent read-only file/search tools instead of being required to
have Claude-specific tool names. They must actually inspect the sources; the
existing prohibitions on builds, network, Git and source changes remain.
Claude prompts and ordinary proof prompts are unchanged.

From the repository root, using new output directories:

```sh
python3 scripts/tex2lean-compat/build_compat.py --output /tmp/antichain-tex2lean-compat-v8
node scripts/tex2lean-compat/extensions/extend.cjs \
  --input /tmp/antichain-tex2lean-compat-v8/out/cli.cjs \
  --output /tmp/antichain-tex2lean-compat-v9
node --check /tmp/antichain-tex2lean-compat-v9/out/cli.cjs
for test in test-inspection-prompt test-extension test-integration test-adapter; do
  node "scripts/tex2lean-compat/extensions/$test.cjs" /tmp/antichain-tex2lean-compat-v8/out/cli.cjs
done
```

The default v9 bundle SHA-256 is
`4268db0fdda61deb1e3be7d52879d8952e67caaf4931e6c1a9fdbfdff39327d6`.
The extension requires the exact reviewed v8 hash and asserts unchanged
ModelClosure, CostSeal, native ledger store/replay and binding-validator code.
Stop any existing workflow before switching launchers; the physical-project
path requirements above still apply.

The optional ledger-review command is **off by default and unconfigured**.
A separate build can enable it with
`--ledger-authority-pin sha256-<independently-reviewed-authority-file-hash>`.
It then provides `/ledger-review {"inspect":true,...}`, a default dry-run with a
reviewed manifest, and an explicit `"apply":true` operation. See the extension
README for complete commands, authority schema, source/type review requirements
and tests. Review provenance identifies the Codex assistant, never an
authenticated human. Only native evidence/binding/disposition decisions may be
published; ordinary `/prove` and `/handoff` remain mandatory. No authority
record, binding manifest or ledger decision is supplied by this package.
