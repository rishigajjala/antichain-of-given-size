# Tex2Lean v9 extension and optional ledger review

This package extends the exact v8 bundle produced by the sibling
`../build_compat.py`; that original builder is unchanged. The required v8 SHA-256
is `93d40c1b5465f43c456a0a46c63995a2d5f4439027fccbd57c3ecfee877af4b7`.
The extension fails closed on another input. Its generated bundle, launcher and
manifest must go to a new directory under `/tmp`, outside the repository.
It does not alter the installed CLI or launch a workflow.

The optional ledger host is disabled by default. No real authority record or
review manifest is configured in this package. Tests evaluate selected actual
native functions with mocked I/O and provider/compiler calls; they do not run
the CLI bootstrap, Lean, providers, or a real ledger.


## Default build: Codex inspection prompt repair

The confirmed bug is in `ste`/`dte`: the inspection prompt was chosen before
provider dispatch and required Claude tool names `Read`, `Glob`, and `Grep`, while
forbidding Codex's equivalent read-only exec tool. The repaired Codex branch
requires actual source inspection, permits only equivalent read-only file/search
operations in authorized paths, and retains the sole authorized JSON-output write
exception. Lean/Lake, builds, probes, network, Git, installs and source edits stay
forbidden. The configured tool list is unchanged; `Bash` is not added. Claude's
prompt/whitelist and the ordinary proof-worker prompts are unchanged.

`extend.cjs` is the single reproducible entry point. Its default output contains
**only this bug fix on top of v8**. The optional ledger host is off unless an
independently reviewed authority pin is explicitly supplied.

```sh
node scripts/tex2lean-compat/extensions/extend.cjs \
  --input /tmp/antichain-tex2lean-compat-v8/out/cli.cjs \
  --output /tmp/antichain-tex2lean-compat-v9
node --check /tmp/antichain-tex2lean-compat-v9/out/cli.cjs
```

The default v9 bundle SHA-256 is
`4268db0fdda61deb1e3be7d52879d8952e67caaf4931e6c1a9fdbfdff39327d6`.

The following sections describe the separately optional ledger integration.

## Scope and recommendation

No public or hidden source-only command in the installed CLI provides arbitrary
obligation-to-declaration review. `/remap` updates legacy source-marker links; the
native initial author gate approves its existing proposed capstone binding only.
The optional `ledger-review` command exposes the existing immutable
publication API under explicit assistant review. Keep it optional and off by
default. The ordinary author gate, proof certifier, validator, and handoff remain
unchanged.

`adapter.cjs` publishes only through the native immutable decision API. `native-host.cjs`
connects it to actual source inventory, native `cr` build/proof-fact inspection,
`o4` interface evidence, `wd` publication and the native lease schema/class.
`cli-helpers.js` supplies the lexical native API bridge. `patch.cjs` has exact,
fail-closed source anchors against the reviewed v8 bundle and generates a separate
bundle, never modifying its input. `extend.cjs` is the supported build entry point.

The only change to `o4` is optional read-only return material when
`includeReviewMaterial:true`: exact elaborated types and the semantic-root types,
values and canonical value digests already obtained by its native Lean probes.
Ordinary calls return identical receipt data. No Lean probe or receipt policy is
changed. Duplicate public declaration names are rejected in inspection mode.

## Inspection precedes any semantic review

Once the actual project sources and workflow are stable, the command's `inspect`
mode obtains current native evidence and exports an artifact in a fresh temporary
directory. It contains:

- exact current ledger claims and obligations, without guessed bindings;
- the full elaborated types and native semantic-root definition bodies/digests;
- **all source files in the selected capstone's module closure**, including full
  structure fields and constructors, for manual semantic review;
- the paper source, packet digest, complete Lean-source fingerprint and
  configuration/toolchain pins;
- the unchanged native interface receipts, which are evidence rather than proof
  status or automatic semantic approval.

The native receipt's older project-type closure does not expand every inductive
constructor. Therefore the inspection includes complete reachable source files;
the reviewer must inspect the relevant structure fields/constructor constraints
as well as the listed root values. The whole source fingerprint is pinned through
application. Do not mistake the listed roots alone for all semantic structure.

The reviewer must inspect the paper quotes, exact types, and all reached definition
bodies before constructing a manifest. Inspection never proposes or approves a
binding by declaration name or list position.

## Independently pinned authority

A separate authority record describes the user's already-authorized task. It is
created from the trusted conversation context and reviewed separately from the
binding manifest. Its exact byte SHA256 is compiled into the optional host build.
A caller cannot override that pin through a command, manifest, or environment
variable. An unconfigured candidate refuses execution.

This is a provenance record of the assistant acting within the user's authorized
formalization task, **not an authenticated human semantic-review signature**.
No additional user confirmation is required by this design. Every publication
retains the literal statement:

> Codex assistant review under user-authorized formalization; no human review asserted

Authority-record template, to be filled from the actual authorized task later:

```json
{
  "schema": "tex2lean.delegated-authority-record/1",
  "scope": "formalization-and-correspondence-review",
  "recordedBy": "Codex assistant",
  "noHumanSemanticReviewAsserted": true,
  "userRequest": "<exact authorized user request and its relevant context>",
  "projectRoot": "<absolute physical checkout path from pwd -P>",
  "blueprint": ".blueprint/<the-target>/blueprint.json",
  "targetIds": ["<the exact current native target ID>"]
}
```

Do not create a binding manifest against moving sources. No real authority record
or real review manifest was generated in this preparation task.

## Optional commands after independent review

Build the separately reviewed host with the authority file's independently
reviewed digest (the `sha256-` prefix is required):

```sh
node scripts/tex2lean-compat/extensions/extend.cjs \
  --input /tmp/antichain-tex2lean-compat-v8/out/cli.cjs \
  --output /tmp/new-reviewed-host \
  --ledger-authority-pin "sha256-<authority-file-SHA256>"
```

Use the physical project directory (`pwd -P`). After normal CLI boot and after all
workers/transactions are idle, request actual source/type evidence:

```text
/ledger-review {"inspect":true,"authority":"/absolute/authority.json","declarations":["<exact fully qualified declaration>"]}
```

The command logs the path of its temporary `evidence.json` artifact. Read that
artifact and the included complete source bodies. Create a manifest manually
only after comparing every proposed binding with its exact paper obligation.
Then run the default dry-run:

```text
/ledger-review {"authority":"/absolute/authority.json","manifest":"/absolute/review-manifest.json"}
```

Review the resulting `dry-run.json`. Only an explicit boolean requests application:

```text
/ledger-review {"authority":"/absolute/authority.json","manifest":"/absolute/review-manifest.json","apply":true}
```

Application publishes only native `put-evidence`, `put-binding` with
`status:"proposed"`, semantic approval decisions, and the two specifically allowed
metadata exclusions. The first eleven mathematical counting rows cannot be
excluded. All receipt membership, mathematical obligations and immutable history
remain. No proof status, verified binding, or certified snapshot is assigned by
this command.

Finish through the normal native `/prove <target-id>` and `/handoff` workflows.
They must obtain fresh actual receipts and compute the final proof/mapping result.

## Idle, lease, freshness and cache safeguards

The normal command's `no-run`/batch guards remain. Additional guards reject any
worker/control, live transaction, recovery operation, pending transaction journal,
or another process lease. The command atomically creates the native lease file
with `wx`, using the native lease data/class. Any existing file—including stale,
unknown-schema, or malformed content—is refused and preserved. There is no force
or takeover prompt. Cleanup checks ownership and never removes a replacement
owner's lease. The native control is disposed even if cleanup throws.

While the review is active, another registered command cannot enter. A native
control also keeps background checkpoint recovery from entering. This command
alone is exempted from T8's post-handler `Oi` reconciliation: that ordinary refresh
writes theorem records, so allowing it after a dry-run would be incorrect. All
other commands retain their original post-handler behavior.

Before its one full native certification, the command drops only this project's
`Fl` proof-fact and `Hc` diagnostics cache entries. Those native keys omit compiler
and configuration inputs, so unknown historical entries are not safe review
evidence. Other projects' caches are untouched. After fresh certification, the
command reuses its exact evidence only while the full source, configuration and
toolchain pins stay fixed. Every publication rereads the ledger head, source pins
and exact quoted files. This may cost a full native diagnostic pass per inspection
or apply command; it avoids falsely claiming current certification from an older
configuration.

Inspect/dry-run creates only normal build/probe caches, a temporary native lease,
and the external evidence artifact; it does not publish ledger decisions or
reconcile theorem/status records. The native validator loop is correct and is
not patched. An earlier diagnosis that the validator failed to refresh its head
between bindings was incorrect: the actual bundled loop already refreshes inside each
iteration. `validator-loop.cjs` extracts that complete unchanged loop. The tests
verify multiple bindings and reproduce the failure only in a test-only mutant
that removes the existing refresh.

## Tests and limits

Run from the repository root with the exact v8 bundle as an explicit argument:

```sh
v8_bundle=/tmp/antichain-tex2lean-compat-v8/out/cli.cjs
for test in test-inspection-prompt test-extension test-integration test-adapter; do
  node "scripts/tex2lean-compat/extensions/$test.cjs" "$v8_bundle"
done
```

Use the available Node executable in place of `node`. `extend.cjs` also accepts
`--node /absolute/path/to/node` for its generated launcher. All tests require
exactly one bundle-path argument; no temporary prototype paths are embedded.
`validator-loop.cjs` and all runtime support modules are included in this
package. The generated optional bundle copies only `adapter.cjs` and
`native-host.cjs`, with their hashes recorded in its manifest.

The inspection test evaluates actual `dte`/`ste` generation and mocked provider
invocation. The composition test checks the default bug-fix-only and explicit
optional-ledger builds. The integration test evaluates the actual native `o4`
and registration wrapper, checks
ordinary receipt equivalence, successful/failing dry-run cleanup paths, retained
entry guards, authority mismatch, exclusive lease behavior, exact cache prefixes,
and an inspection flow with current type/body/source output and no publication.
The adapter test checks the actual native ledger store/replay and unchanged
multi-binding validator, plus the adapter's full negative controls.

These tests do not constitute a successful real-project inspection. Before
applying any ledger decisions, the optional host must capture current evidence
from the actual project, and the reviewer must compare exact types, all relevant
source definitions and paper quotations. Normal native proof and handoff
validation remains required after application.

`extend.cjs` asserts byte equality of the entire ModelClosure generator, the
CostSeal block, native ledger replay/validation/store, and native binding-validator
loop before writing output; their SHA-256 values appear under `unchanged` in the
manifest. It preserves model selection, sandbox policy and ordinary gate verdicts.
The optional branch changes only review-evidence exposure and guarded review
command integration. It never assigns proof completion or verified status.
