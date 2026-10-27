# Runtime selection and saved-graph recovery

Launch the reviewed task-local runtime with explicit provider and resource
settings. Resolve the project to its physical directory; do not use its symlink
alias. The historical counting recovery used these settings:

```sh
/tmp/antichain-tex2lean-compat-20261027-v17-counting/tex2lean targets \
  --project '/Users/sg9396/Desktop/boxicity/Documents New project/research/antichain-of-given-size' \
  --lean . --output .blueprint \
  --provider codex-cli --agents 3 --effort high --no-commit
```

At the prompt, use `/plan` with **no argument**, select only the saved counting
result, and check the displayed capstone. This loads the finalized plan and
performs ordinary proof reconciliation; `/plan <id>` instead invokes planning.
Omitting the explicit provider flags previously selected default Claude, whose
handoff workers lacked file-reading access. That incomplete report is archived
and is not accepted as final evidence.

After reviewed binding changes, compare the saved graph's `mappingDigest` with
the current target ledger head. In this CLI version, `Oue` starts with its local
mapping variable `Ge` undefined; `Xg` permits reuse when that optional expected
digest is undefined. The opening `wt` path can therefore reuse a same-source
old graph before `ai` loads the new ledger and validates its bindings. There is
no exposed force-refresh command. Adding a dirty marker alone is unreliable,
because the resume path reads the previous graph with `ignoreDirty=true`.

The recovery used here was to quit the idle CLI, preserve the exact graph and
non-final handoff externally with hashes, and move **only** generated
`.tex2lean/proof-graph.json` out of the project. The original graph SHA-256 is
`a825c202acfc5f454de42bad8f6f809f55a23d7b75663db3b0c3ba9c47c20b4c`.
The archive is `/tmp/antichain-counting-stale-graph-handoff-20261027`.
Mappings, checkpoints, sources, receipts and certified-snapshot histories were
left intact. The optional sidecar `.tex2lean/proof-graph.dirty.json` was absent;
if one exists, preserve it and let native reconciliation clear it after a
successful graph rebuild.

With no cached graph, native `ts` returns no previous graph and `wt` enters
`ai`, which reads the current ledger, rebuilds the proof graph, obtains current
interface receipts, runs the unchanged validator, and may publish a certified
snapshot. Moving the cache does not itself verify a binding or certify a target.
Session `42597` restarted that normal workflow with the explicit settings above.
Its final graph digest, current ledger head and certified-snapshot reference
must be checked before a successful completion is reported. No final certificate
or handoff result is claimed in this recovery record.

The corrected run subsequently produced the counting certificate at
`2026-10-27T05:38:05.956Z` and the Codex handoff at
`2026-10-27T05:42:20.946Z`. Its final export records 11 mathematical rows proved,
two metadata rows excluded, and no unknowns. The aggregate native completion
flags remain false because of those exclusions. See
`manifests/counting-final-export-reference.json`; the prior default-Claude
handoff remains non-final.

Before the final main run, the shared generated graph still represented the
already-exported counting target. It was preserved separately at
`/tmp/antichain-main-final-graph-refresh-20261027`, with raw SHA-256
`a72a0e3fc83a6c119c8e5180eb7bc1390342557f73d6910b9c9d46ca5ededda0`,
then only the generated cache path was removed. Seven main successor bindings
were proposed through the reviewed native adapter (generation 75); they were
not thereby verified. Session `40094` then ran normal main reconciliation and
handoff with the same explicit Codex flags. Main's native certificate was then
issued at `2026-10-27T06:21:14.022Z`, with seven active verified bindings; its
06:27:01 handoff subsequently reported the helper-placement issue below. See `manifests/main-runtime-provenance.json`.

**Source transition after the main handoff:** the 06:27:01 report found the
conditional simultaneous-density helper correctly used by the headline but
misplaced on the Model surface. The helper and its individual closure check
were moved unchanged to its Analysis proof file, and scratch Lean files were
moved outside the deliverable. All certificates/exports described above now
refer to historical source `0d23ccef…`; the fresh current-source evidence described next supersedes them for
current-source reporting. The compatibility runtime was not patched
for this correction. The full old report, graph and source files are preserved
outside the project; see `manifests/helper-relocation-source-transition.json`.

After the source correction, session `6885` used the **v17-main** executable with
the same explicit project/provider/agent/effort flags above. Ordinary `/plan`
selection loaded main, counting and splitting sequentially, exporting each
before switching the shared graph. Optional main-authority ledger review was
not invoked for another target. The new source fingerprint invalidated the
historical cached graph through normal native checks. All three runs produced
current-source certificates and handoffs; the CLI then exited with code 0.
See the three `*-current-export-reference.json` files for exact generations,
digests, times and retained qualifications. No additional cache or validator
patch was introduced for these final runs.
