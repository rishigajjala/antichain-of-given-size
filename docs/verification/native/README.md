# Evidence for the selected Tex2Lean runs

All three selected workflows have current checked exports: main generation 91,
counting generation 141, and splitting generation 9. They share the same Lean
source fingerprint. Main preserves two verification limitations; counting
preserves two metadata exclusions and its native false aggregate-completion flags.

These records cover three selected workflows: the main theorem, the counting
theorem, and a splitting-lemma pilot. The Lean audit covers all 18 numbered
manuscript results; the other 15 have no separate native plan. The
[correspondence document](../../current-paper.md) identifies their statements,
proof reuse, alternative arguments, and assistant review provenance.

| Selected result | Exact archive | Readable record |
| --- | --- | --- |
| Main theorem (generation 91) | [Archive](thm-main.tar.gz) | [Summary](thm-main.summary.json) |
| Counting theorem (generation 141) | [Archive](thm-attainable-count.tar.gz) | [Summary](thm-attainable-count.summary.json) |
| Splitting lemma (generation 9) | [Archive](lem-splitting.tar.gz) | [Summary](lem-splitting.summary.json) |

[index.json](index.json) records target generations, the shared source fingerprint,
and archive/summary hashes. [SHA256SUMS](SHA256SUMS) lists the archive hashes.
Each archive preserves original relative paths and exact bytes for its graph,
head, ledger, certificate, Lean evidence and interface receipts, blueprint,
handoff, selected paper/configuration inputs, and `EXPORT.json`. Its graph was
captured before the next run could replace the shared graph file.

The complete immutable decision, publication, object, receipt and snapshot history
remains in [`.tex2lean/mapping`](../../../.tex2lean/mapping). Archives include all
Lean source hashes, **not every Lean source file**. Pair them with the repository
source tree identified by the final export manifests. Their source fingerprints,
individual Lean hashes, generations, and handoff times are recorded in the index
and summaries. The package contains only these three final exports. Earlier
certificates remain in the repository's immutable mapping history, and the
[pre-relocation main handoff](../history/main-before-helper-relocation/HANDOFF.md)
is preserved separately. Earlier working exports are not included here.

The [strict verification report](../../../.blueprint/verification/checks.json)
records command results, execution times, and exact input hashes. Its logs give
the declaration/module counts and expanded statement checks. Closure checks cover
27 declarations in Model and the relocated conditional helper in Analysis.
These are source checks, not a new validation performed by the archive checker.
The native `/check` report separately remains `FAIL` for
[two explained heuristic findings](../native-check-explanation.md).

The main archive retains the exact strict logs cited by its handoff review.
The repository's `checks.json` records the final integration check after
publication-document edits. All 129 Lean source files remain tied to the
[helper-relocation commit](https://github.com/rishigajjala/antichain-of-given-size/commit/420d09b23a8449bf144b3a0d391331e899292e5f),
but the archived 138-input verification manifest includes handoff-time document
versions. It is not a claim that all 138 files equal the final checkout.

The main handoff's two top-level verification limitations remain verbatim in
`observedHandoff.unknowns`. Its readable summary includes the limitations-review
SHA-256 and purpose; the complete review text, its exact evidence citations, and
the native report remain in the archive. Packaging does not clear unknowns or
change native verdicts, proof counts, or completion flags.

The current counting handoff reports eleven proved mathematical rows and no unknowns.
Its two excluded metadata notes retain `complete=false` and
`whollyProved=false`; neither packaging nor summaries changes those flags or
counts the notes as proofs. Ten superseded bindings remain in its ledger.
Splitting's generation-9 handoff reports one proved mathematical row, no unknowns,
and both completion flags true.

Readable binding summaries retain declaration, binding and approval IDs, receipt
digests, and the assistant-review provenance sentence. Full review payloads remain
verbatim in `EXPORT.json` and the native decision records. No human review
signature is asserted. Private conversations, UI transcripts, generated runtime
bundles, dependency caches, and temporary probes are not added by this package.

To check the archives from the repository root:

```sh
python3 docs/verification/native/package.py check docs/verification/native
```

The standard-library checker validates archive and summary hashes, rejects unsafe
or duplicate paths and nonregular members, and checks each preserved file against
`EXPORT.json`'s byte count and raw SHA-256. It reads without extracting. This checks
packaging integrity; it does not rerun Lean, Tex2Lean, or semantic review.

The current export helper checks native domain-separated canonical hashes for
ledgers, certificates, graphs, Lean evidence, paper packets and interface receipts,
and requires agreement with the current Lean source fingerprint. The reviewed
producer source is preserved exactly and was used for all three final exports:

| Export producer | Targets | SHA-256 |
| --- | --- | --- |
| [Current helper](export-helpers/export.cjs) | All three final exports | `b538eb1777398a1736f49c34e4a3c66a6ef93de0c7b319c8a42b88bf04039a09` |

[Helper provenance](export-helpers/provenance.json) and
[helper checksums](export-helpers/SHA256SUMS) identify this producer. The current
helper checks active bindings while preserving retired records in the archive.
Stale/proposed bindings remain ineligible for export; duplicate historical binding
IDs are rejected. Nonempty verification notes require an explicit review bound
to the exact handoff, certificate, source fingerprint, and cited evidence. Blocking
findings and unproved mathematical rows still prevent export. External dependency
binaries are not independently hashed.

For a maintainer preparing exports, use the producer matching the target:

```sh
node docs/verification/native/export-helpers/export.cjs target \
  --repo "$PWD" --label thm:attainable-count --out /tmp/new-counting-export
```

For a handoff with reviewed verification limitations, also pass
`--handoff-limitations /absolute/path/to/review.json`; the helper checks the exact
notes and evidence hashes. This requires a current matching graph and refuses to
overwrite an export. To
package all three reviewed exports outside the repository:

```sh
python3 docs/verification/native/package.py pack \
  --root /tmp/antichain-final-native-evidence-after-helper-relocation-20261027 \
  --out /tmp/antichain-native-archives-final
```

Check the exported heads and source hashes against the final tree first. The
output directory must be new. Packaging preserves native file bytes and normalizes
only tar/gzip container metadata.
