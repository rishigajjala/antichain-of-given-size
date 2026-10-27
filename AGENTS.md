# Formalization work

The manuscript snapshot is `paper/Generating_Antichains_Simplified.tex`.
Preserve it and its checksum. `docs/current-paper.md` maps its mathematical
statements to the existing Lean development and records differences in proof
arguments.

For the Tex2Lean workflow, reuse the existing checked development where
appropriate. Preserve the definitions of generated ideals and `alpha`, and
the constants, domains, quantifiers, and conclusions of the manuscript.
Do not weaken statements or add unproved assumptions to make a target close.
Keep any changes to proof representations explicit in the correspondence
documentation.
The bounds on generator counts are mathematical size bounds. Do not introduce
running-time or memory claims that the manuscript does not make.

Let Tex2Lean produce its own plans, proof status, and handoff evidence. Do not
manually mark a target proved or fabricate workflow output. Distinguish new
proofs from interfaces that reuse earlier proofs.
Retain proved modules belonging to other results: a single target's dependency
graph need not reach every result in this multi-theorem project.

Register every checked claim in `scripts/capstones.txt`, including semantic
representation equivalences. Keep the individual `#modelClosureOfType` checks.
The whole-library `#surplusIn` check belongs in generated `Meta/Audit.lean`,
after all registered claims have been imported. The default library root
imports that audit. Do not add a per-file check over all of `Model/` using only
one claim: later claims would then produce false surplus warnings. Preserve
the generated checkers; their reviewed compatibility changes are reproduced
by `scripts/tex2lean-compat/build_compat.py`.

Keep all source files covered by the axiom audit. If library modules change,
update the explicit registry in `scripts/CheckAxioms.lean` and the appropriate
imports; do not remove the registry or its source-coverage checks. Preserve
the independently expanded contracts in `scripts/CheckPaperStatements.lean`.

Before reporting successful integration, run:

```sh
lake build --wfail
lake env lean -DwarningAsError=true scripts/CheckAxioms.lean
lake env lean -DwarningAsError=true scripts/CheckPaperStatements.lean
shasum -a 256 --check paper/SHA256SUMS
```

Keep the existing Lean and Mathlib pins unless a migration is explicitly
requested. Do not push, merge, or publish from a Tex2Lean worker; the parent
task handles repository integration after reviewing the generated changes.
