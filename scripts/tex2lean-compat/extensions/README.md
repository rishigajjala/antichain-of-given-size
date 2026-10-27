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

## Optional UI lifecycle repairs

`--lifecycle-ui-fixes true` enables a separate `lifecycle-ui.cjs` transformation.
It is off by default; the default v9 bundle and installed CLI are unchanged.
The option composes with the independently pinned ledger host but does not require
or configure authority, and does not publish any ledger decisions.

Three narrowly related defects are addressed:

- A second native choice with the same public ID was never displayed because the
  terminal retained `lastChoice`. Each request now carries a process-local sequence;
  repeated renders of that request are still answered once. Public IDs, action
  order, approval policy, and answers are unchanged.
- Display projection rebuilt an otherwise identical certified graph with a fresh
  `updatedAt`, then rejected its full hash. The native graph is still freshly
  derived. The previous graph is reused only if canonical JSON agrees in every
  field except the **top-level** `updatedAt`. Nested timestamps and all mathematical,
  source, dependency, target, ledger, node, edge and status data must agree. The
  existing strict native full-hash certificate test then runs unchanged.
- Handoff copied session-global progress even for another selected target. It now
  attaches progress only when its ephemeral native certificate identity belongs
  to the selected target and matches the current head, certified snapshot, full
  persisted graph, current paper target and fresh source fingerprint. It rechecks
  the full saved graph and head after the source scan. Missing, changed, unvalidated or other-target
  progress is omitted. Standalone handoff without a matching session projection
  does not claim complete certified correspondence; this option does not invent
  or cache per-target progress.

The original native graph constructor, proof certification, interface receipts,
claim projection, ledger validation/replay/store, ModelClosure and CostSeal remain
byte-identical across this transformation. Build output records their hashes.
Ordinary native proof reconciliation and handoff are still required; no proof or
binding status is assigned by these UI changes.

```sh
node scripts/tex2lean-compat/extensions/extend.cjs \
  --input /tmp/antichain-tex2lean-compat-v8/out/cli.cjs \
  --output /tmp/new-lifecycle-host \
  --lifecycle-ui-fixes true
node scripts/tex2lean-compat/extensions/test-lifecycle-ui.cjs \
  /tmp/antichain-tex2lean-compat-v8/out/cli.cjs
node scripts/tex2lean-compat/extensions/test-extension.cjs \
  /tmp/antichain-tex2lean-compat-v8/out/cli.cjs
```

Tests run extracted actual native request/projection methods with isolated mock
I/O. They reproduce the old candidate-closed result, verify the matching certified
result, reject semantic/source/ledger/nested-timestamp changes, and reject handoff
head/source/target changes. They launch no native workflow, provider or compiler.

## Scope and recommendation

No public or hidden source-only command in the installed CLI provides arbitrary
obligation-to-declaration review. `/remap` updates legacy source-marker links; the
native initial author gate approves its existing proposed capstone binding only.
The optional `ledger-review` command exposes the existing immutable
publication API under explicit assistant review. Keep it optional and off by
default. The ordinary author gate, proof certifier and validator remain unchanged.
The ledger option alone does not change handoff; the separately optional UI
repairs above add a conservative progress-attachment guard.

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
changed. Repeated normalized rows are accepted only when their full type and dependency
records agree exactly; repeated selected values must also agree exactly.
A duplicated selected value with no body is also rejected, since equal types
without bodies cannot establish identity. Conflicting records fail closed with
the declaration name and both records in
the diagnostic. This handles generated equations that Lean enumerates more than
once, without choosing between different declarations sharing a display name.

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

Binding-review application uses native `put-evidence`, proposed bindings, semantic
approval decisions, and the two specifically allowed metadata exclusions. The
explicit stale-refresh mode below additionally supersedes an exact old stale
binding before proposing its reviewed successor. The first eleven mathematical counting rows cannot be
excluded. All receipt membership, mathematical obligations and immutable history
remain. No proof status, verified binding, or certified snapshot is assigned by
this command.

Native certification and handoff remain mandatory after publication. In this
CLI build `/prove [id]` forwards to a handler that ignores the ID and uses only
the current session blueprint; it is not a target selector. Select the exact
saved run through the native workflow and verify the displayed capstone before
starting proof reconciliation. `/handoff` opens its own paper-target chooser.

### Correcting an unapproved proposal

When an earlier planner associated an obligation with the wrong declaration,
the review may correct that proposal without changing a Lean statement. The
existing binding must still be `proposed`, with no semantic approval, receipt,
evidence-snapshot ID, verification decision, or stale reason. The binding ID,
obligation ID and `proposed` status are retained. Ordinary bindings need no
additional field; a differing existing proposal requires this explicit block
inside its manifest binding:

```json
"replaceUnapprovedProposal": {
  "expectedBinding": {"id": "<exact existing record, including all fields>"},
  "expectedBindingDigest": "<native digest of that complete record>",
  "reason": "<why the reviewed declaration replaces the earlier unapproved proposal>"
}
```

The inspection artifact's `unapprovedProposals` array supplies the complete old
record and its digest. The digest uses the native canonical hash
`Pt("delegated-binding-proposal/1", binding)`, not a hash of arbitrarily formatted
JSON. Both the quoted record and digest must equal the current native record.
The new declaration's exact type, complete semantic-definition list, source
quote and semantic-review reason remain required. An empty replacement reason,
changed old record, no-op replacement, missing old proposal, protected binding
state, or duplicate resulting declaration binding is rejected. Publication
order is checked before writing: a correction must free its old declaration
before another binding uses it. Unsafe ordering is rejected without reordering
the manifest, so an interruption cannot leave a temporary duplicate.

Dry-run lists each replacement with its old record, new declaration and reason.
Apply publishes the correction and subsequent semantic approval as **separate
native immutable `put-binding` decisions**, both still `proposed`; the original
planner decision is retained. Every decision uses a freshly checked head and
source pins. It never rejects/supersedes a verified binding, changes an
obligation, or bypasses native proof certification. Reusing one capstone for two
headline bindings is not a workaround: the native certified-surface validator
requires exactly one verified binding per surface declaration and role.

### Refreshing an interface that native verification marked stale

This mode is only for `status:"stale"` with the exact native reason
`elaborated type or semantic roots changed`, an earlier applied semantic approval
and verification decision, and its historical receipt. A currently `verified`
binding cannot use it: first run ordinary native reconciliation, which either
refreshes an unchanged receipt or marks a changed receipt stale. Inspection
alone does not change statuses. Replanning is unnecessary: use `/plan` with no
argument, select only the completed result in the picker, and confirm its exact
saved capstone. The explicit `/plan <id>` route instead invokes planning.

Read a fresh `/ledger-review` inspection of every relevant declaration. Review
its full current types and semantic-definition lists against the frozen paper
and previous evidence. Keep the same claim and obligation, declaration, file,
module and role; use fresh source/configuration/toolchain/paper/head pins. Add
this explicit block to each stale binding's newly reviewed manifest row:

```json
"refreshStaleBinding": {
  "expectedBinding": {"id": "<complete exact current stale record>"},
  "expectedBindingDigest": "<native digest of that complete record>",
  "reason": "<why the complete current semantics still match this exact paper obligation>"
}
```

The digest is `Pt("delegated-stale-binding/1", binding)` using the native
canonical hash, also exposed by `staleBindingDigest` in `adapter.cjs`. Obtain the
record from the fresh inspection's ledger. It is distinct from the unapproved
proposal digest. Do not carry an old `replaceUnapprovedProposal` block into a
refresh, and do not repeat metadata exclusions already applied.

Native replay forbids a same-ID `stale → proposed` transition. Application
therefore records source evidence, changes only the old binding's status to
`superseded`, creates a **new** proposed binding with `supersedes:[oldId]`, and
records its new semantic approval. The old receipt and decisions remain in
immutable history. The successor has exactly the old mathematical identity;
it inherits no receipt, verified status, verification decision or stale reason.
Every event uses a fresh checked ledger head and source pins. There is no moment
with two active bindings for the declaration. A failure after superseding can
leave a safe, incomplete state that needs a fresh review; the adapter does not
pretend the operation completed. If interrupted after the unapproved successor
exists, ordinary fresh proposal approval preserves its `supersedes` lineage.

Dry-run lists `staleRefreshes` with exact old records and successor IDs. Neither
dry-run nor application creates proof verification. The normal native validator
must subsequently verify successor receipts and certify the unchanged complete
target inventory. Same-ID reopening, verified-state shortcuts, identity changes,
missing history, other stale reasons and stale review pins are rejected.

`test-stale-refresh.cjs` uses the actual native store/replay and unchanged
validator. It checks every interrupted publication prefix, historical-record
preservation, no active duplicates, exact-identity/state rejection, semantic and
source pins, preserved successor lineage, and failure of certified-surface
validation until ordinary native verification supplies fresh receipts.

### Reviewing the target's declaration inventory

The native planner records every theorem in the shared `Model/Theorem.lean` as
part of each new target's inventory. This can include an earlier target or a
conditional helper, and omit a target's separately defined semantic equivalences.
The optional `surface-review.cjs` corrects that ownership record through native
`put-surface-inventory` and author-authorized `select-surface-inventory` decisions.
It does not edit a Lean file, change any claim or binding, or certify a proof.

This operation is deliberately limited to the two reviewed targets. Main must
retain exactly seven mathematical obligation bindings; its only permitted
removals are `attainable_count` (owned by the separate counting target) and
`alpha_simultaneous_density_one` (a proved conditional helper directly used by
the unconditional main capstone). Counting must expand from its one headline
to all eleven mathematical bindings, after the two exact metadata rows already
have their separately reviewed exclusions. Every claim and original receipt
remains recorded. No mathematical claim may be excluded by this operation.

Obtain a fresh `inspect` artifact after binding review and after the sources
settle. For main, inspect the seven bound names **and** the two removed names.
For counting, inspect all eleven bound names. The artifact now also includes:

- `activeInventory.inventory` and `activeInventory.expectedInventoryDigest`;
- `expectedPreservedStateDigest`, pinning every claim, plan, obligation, binding
  status, claim-set receipt, and relation;
- native `cr` declaration references under `proofFacts`, tied to the complete
  source fingerprint;
- for main, `relatedCountingTarget`, read from the sole finalized counting
  blueprint and its current native ledger, including its actual reviewed counting
  binding, headline obligation, formalize plan, active claim/version and receipt
  membership. Its historical binding status and receipt are preserved as reported;
  current verification is not inferred. This is read-only evidence; the
  authority scope still permits publication only to the selected target.

The separate manifest has this shape:

```json
{
  "schema": "tex2lean.delegated-surface-review/1",
  "targetId": "<current target>",
  "targetVersionId": "<current target version>",
  "baseLedgerDigest": "<current ledgerDigest>",
  "pins": {"paperPacket": "...", "leanSources": "...", "configuration": "...", "toolchain": "..."},
  "review": {"authority": "user-delegated-author", "authorizationDigest": "...", "provenance": "Codex assistant review under user-authorized formalization; no human review asserted"},
  "expectedInventory": {"id": "<complete exact old inventory record>"},
  "expectedInventoryDigest": "<artifact value>",
  "expectedPreservedStateDigest": "<artifact value>",
  "declarations": [
    {"declaration": "<bound name>", "role": "headline", "file": "...", "module": "...", "elaboratedType": "...", "semanticDefinitions": [], "sourceQuote": {"file": "...", "from": 1, "to": 1, "text": "...", "fileDigest": "..."}, "reason": "<exact statement/ownership review>"}
  ],
  "changes": {
    "additions": [{"declaration": "<each added name>", "reason": "<review reason>"}],
    "removals": []
  },
  "reason": "<why the old shared-file inventory differs from this paper target>"
}
```

Use complete artifact values, not the placeholder values above. Every declaration
must have a complete exact type/definition review and paper quote. Each main
removal carries the same declaration fields plus `category`: either
`separate-counting-target` with `ownership` equal to the artifact's complete
`relatedCountingTarget`, or `proved-conditional-helper` with no ownership field.
The host rechecks the counting ownership and the compiler-reported direct edges
`attainable_count → Analysis.AttainableCountProof.attainableCount` and
`alpha_asymptotic_order → alpha_simultaneous_density_one`. It does not assert
that the public counting wrapper itself is a dependency of the main theorem.

Pass this manifest to the same default-dry-run `/ledger-review` command. Review
its complete before/after inventory before explicitly applying. Application
publishes exactly three fresh-head decisions: source evidence, the new inventory,
then its selection. The new origin is truthfully `author-reviewed-target-scope`;
the old sealed inventory and its original blueprint digest remain immutable.
An interruption before selection leaves the old inventory active. Native
publication invalidates any earlier certified snapshot pointer. The unchanged
native validator continues to reject certification until every selected binding
has a valid verified receipt. Ordinary proof reconciliation and handoff remain
mandatory; this command does not publish a certified snapshot or a Lean relation.

## Optional scope review for later numbered targets

`future-surface-review.cjs` is a separate, fail-closed path. It refuses
`thm:main` and `thm:attainable-count`; their original fixed rules are unchanged.
It accepts only frozen LaTeX theorem/lemma/corollary/claim targets; definitions,
remarks and Lean aliases are rejected. It uses the same single-target,
independently pinned authority and idle lease.
Related target records are read-only and never broaden publication authority.
There is no automatic owner selection or automatic semantic approval.

Before review, let the ordinary planner append the new target and review/bind
its mathematical obligations. Do not move existing declarations or overwrite
shared Model files to obtain a smaller inventory. The future operation requires
every active reportable claim to have a `formalize` plan with one exact headline
obligation and one semantically approved proposed/verified binding. The active
claim-set receipt must contain precisely all those claim versions. Exclusions,
assumptions, unsupported dispositions, alternative obligation groups and missing
bindings are rejected. It does not create a native helper/subgoal role.

For an inspection, supply `futureSurface` explicitly:

```json
{
  "inspect": true,
  "authority": "/absolute/reviewed-authority.json",
  "declarations": ["<retained and removed declarations to review>"],
  "futureSurface": {
    "relatedTargets": [{
      "targetId": "<explicit existing owner target>",
      "targetVersionId": "<active version>",
      "ledgerDigest": "<exact current native head>",
      "blueprint": ".blueprint/<owner>/blueprint.json",
      "blueprintDigest": "sha256-<exact blueprint bytes>",
      "activeInventoryId": "<currently selected inventory>",
      "bindingIds": ["<explicit owned binding ID>"]
    }],
    "helperPaths": [{
      "declaration": "<removed internal helper>",
      "path": ["<retained mathematical binding>", "<compiler dependency>", "<removed internal helper>"]
    }]
  }
}
```

Empty arrays are allowed when no owner/path is needed. A path rooted in a
related theorem additionally supplies `ownerTargetId` and `ownerBindingId`.
The host does not infer either. Every selected related binding must already be
natively verified with applied semantic/proof decisions and its original proof
receipt; its mathematical formalize plan, active claim receipt membership and
selected inventory entry must still exist. The exact head, target version,
blueprint bytes, source and inventory are checked on every snapshot.

Inspection extends read-only module inspection to the explicitly selected
owners and path nodes. For every owner, removed helper and path node it calls
the unchanged native `yr` inspector: build that module, then ask Lean for its
complete transitive `Lean.collectAxioms` result. Unknown answers, `sorryAx` or
axioms outside `propext`, `Classical.choice`, `Quot.sound` fail closed. The
actual compiler graph must contain every edge on the explicit acyclic path.
Roots, owned endpoints and removed helpers must have compiler theorem/lemma
kind; intermediate dependencies may be definitions.
`cr.hasSorry = false` alone is insufficient. Full axiom results, raw outputs and
complete source/configuration/toolchain pins appear in `fullAxiomEvidence`;
they are obtained freshly on each inspection/dry-run/apply invocation and
reused inside that invocation only while the pins remain unchanged.

The future manifest has schema `tex2lean.delegated-future-surface-review/1`.
Use the same target/head/pins/review/expected-inventory/protected-state fields
as a fixed surface manifest, plus the exact `targetLabel`, `inspection`
(selection above), `relatedTargets` and `axiomEvidence` from fresh evidence.
Its `declarations` must equal all mathematical obligation bindings exactly.
Its `owners` array must review every explicitly selected owner with the same
complete declaration/type/definition/paper-quote fields, plus `targetId` and
`bindingId`. Every addition and removal needs an explicit reason and exact
before/after identity. Allowed removal categories are:

- `separate-reviewed-target`, with `ownerTargetId` and `ownerBindingId` pointing
  to that exact declaration in a reviewed related target;
- `proved-internal-helper`, with exactly one reviewed dependency path. Its root
  must be a retained mathematical binding or an explicitly selected related
  owner. A binding for this target's own mathematical claim cannot be removed.

Pass the completed manifest to the ordinary `/ledger-review` dry-run and review
the full result before explicit apply. Publication uses only the native immutable
source-evidence, put-inventory and select-inventory operations. All prior
inventories, mathematical claims/plans/binding statuses and claim receipts remain
unchanged; related targets receive no writes. The new inventory cannot certify
anything: the unchanged native validator still requires verified binding
receipts, followed by ordinary proof reconciliation and handoff.

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
for test in test-inspection-prompt test-extension test-integration test-adapter test-surface-review test-future-surface-review test-lifecycle-ui; do
  node "scripts/tex2lean-compat/extensions/$test.cjs" "$v8_bundle"
done
```

Use the available Node executable in place of `node`. `extend.cjs` also accepts
`--node /absolute/path/to/node` for its generated launcher. All tests require
exactly one bundle-path argument; no temporary prototype paths are embedded.
`validator-loop.cjs` and all runtime support modules are included in this
package. The generated optional bundle copies `adapter.cjs`, `surface-review.cjs`,
`future-surface-review.cjs` and `native-host.cjs`, with their hashes recorded in its manifest.

The inspection test evaluates actual `dte`/`ste` generation and mocked provider
invocation. The composition test checks the default bug-fix-only and explicit
optional-ledger builds. The integration test evaluates the actual native `o4`
and registration wrapper, checks
ordinary receipt equivalence, identical-row/value repeats, conflicting type,
dependency and value rejection, successful/failing dry-run cleanup paths, retained
entry guards, authority mismatch, exclusive lease behavior, exact cache prefixes,
and an inspection flow with current type/body/source output and no publication.
The adapter test checks the actual native ledger store/replay and unchanged
multi-binding validator, plus the adapter's full negative controls. Replacement
regressions use the actual native store/replay and validator, retaining original
events, rejecting changed records/heads and protected states, preserving the
ordinary existing-proposal flow, and checking the final certified surface.
The surface-review test exercises native immutable inventory publication,
exact seven/eleven-claim coverage, unchanged claims/receipts/statuses, fixed
justified removals, fresh proof references, interruption safety and authority
rejection. The unchanged native validator fails on the selected inventory until
the ordinary verification loop supplies all corresponding receipts. The future-target
suite also tests exact active receipt coverage, explicit related-owner selection,
full native axiom evidence pins, open/transitive/custom-axiom rejection, immutable
related state, native dependency paths, mid-publication drift and interrupted
selection. The host integration suite verifies the actual `yr` bridge and its
unchanged implementation; its test axiom responses are mocked, with no compiler
or workflow execution.

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
