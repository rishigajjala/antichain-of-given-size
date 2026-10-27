# Handoff check — Counting attainable ideal sizes

> 2026-10-27T07:19:21.488Z · ChatGPT subscription · gpt-6-astra · Lean project `.`
> This check reads source text and may include Lean answers such as `#print axioms`. The correspondence verdicts are readings of statements. Anything not established is reported as unknown rather than as a pass.

## Paper claim progress

| Paper claim | Coverage | Proof state | Nearest blocker |
| --- | --- | --- | --- |
| One absolute threshold works for every B above it and every K in the exact stated real-log budget, and \|V(B,K)\| ≤ 2^(B−√B). | mapped | proved | — |
| V(B,K) consists exactly of numerical ideal sizes from nonempty families of at most K generators of individual size at most B, with no ambient cap. | mapped | proved | — |
| Repeating a final generator and relabelling the active ground set preserve the ideal size and give N ≤ KB. | mapped | proved | — |
| Φ equals the complete signed inclusion–exclusion sum over nonempty queries. | mapped | proved | — |
| Each eligible family admits a structural header; there are at most (J+1)K^K possible headers. | mapped | proved | — |
| The exceptional set has size at most 2Kρ/λ^6 and cluster members agree off it. | mapped | proved | — |
| The incidence record and central exponent transcript determine the exact signed central sum Z. | mapped | proved | — |
| There are at most (KB+1)2^(2K²ρ/λ⁶) incidence records and (B+1)^(2^J(1+K2^h)) central transcripts. | mapped | proved | — |
| Every noncentral exponent is at most B−ρ; the signed tail lies in an interval with at most 2^(B−ρ+K+2) integer values. | mapped | proved | — |
| For each header the attainable-value count is bounded by the product of the incidence, transcript and tail-interval counts. | mapped | proved | — |
| Uniformly in admissible K, Γ≥2^(7λ/10), eventually d≤1/4 and L_rec≤Γ/2, and eventually Γ/4≥√B; summing over headers yields the stronger intermediate bound 2^(B−Γ/4). | mapped | proved | — |
| The existing endpoint proves the exact target with a different, larger clustered record encoding; identify reuse honestly and preserve the correspondence note. | excluded | not-applicable | — |
| This target asserts no probabilistic or computational resource result; the following uniformly sampled dyadic corollary is separate. | excluded | not-applicable | — |

The original paper target is not yet completely certified.

The supplied audit found no mathematical mismatch or additional substantive assumption between the selected counting statement, `thm:attainable-count` at `paper/Generating_Antichains_Simplified.tex:987`, and `AntichainOfGivenSize.attainable_count` at `AntichainOfGivenSize/Model/Theorem.lean:44`. The recorded proof checks also support the Lean result. These are separate conclusions: correspondence rests on inspection of the statement and its definitions; proof status rests on the supplied elaborator output and inspected verification records. The readers did not rerun Lean during this review.

Lean preserves the paper’s quantifier order: one absolute threshold works for every sufficiently large B and every K in the stated range. The lower bound K ≥ 1, constant 100, squared logarithm, iterated logarithm, and exact real bound \(2^{B-\sqrt B}\) all agree. Lean explicitly uses base-two logarithms, as the paper specifies at line 215. Its natural-number parameters differ from the paper’s integer parameters only in representation within this eventual positive range; the internal threshold result already supplies a threshold of at least 1.

The identification of the counted objects is supported by `AntichainOfGivenSize.Model.attainableValues_membership` at `AntichainOfGivenSize/Model/Prelude.lean:56`. For K > 0, it characterizes membership by a nonempty family of at most K generators, each of size at most B, over an arbitrary finite ambient universe. `generatedIdeal` is the union of the generators’ powersets, and `attainableValues` counts distinct exact cardinalities. The representation proofs justify deduplication, padding, and removal of unused ground elements. Consequently, the profile representation adds no antichain requirement, balancedness condition, intermediate-intersection restriction, independent ambient-size cap, or restriction to values below \(2^B\).

Two interface details deserve clarification. The argument `(hprior : Prior)` is vacuous: `Prior` has no fields and is inhabited by `⟨⟩`, so it contributes no mathematical premise. The membership bridge also extends to B = 0, but requires K > 0. At K = 0 the implementation contains the value 0, whereas the paper’s nonempty-family definition admits no family. That difference lies outside the selected theorem’s K ≥ 1 range. The bounded-profile fields and finite-type instances are justified representation machinery, rather than additional hypotheses on the paper’s families.

For proof verification, the supplied fresh elaborator output and inspected saved outputs agree that the headline declaration and membership bridge depend only on `propext`, `Classical.choice`, and `Quot.sound`. The saved project-wide axiom audit reports the same profile across 3,086 declarations in 124 library modules. All 138 recorded source/input hashes matched the current files, and every local Lean file was recorded. The saved `lake build --wfail` run records exit code 0 and successful completion of 3,548 jobs without `sorry` warnings; saved closure checks also succeeded for the headline and membership bridge. Source inspection found no proof holes or custom axioms. The three partial definitions identified belong to audit tooling and are outside the mathematical proof dependency chain.

This evidence is specific to the selected counting theorem and its supporting representation. Although the audit records correspondences for other paper statements, the focused review did not establish exhaustive coverage of the paper. The selected theorem is deterministic; the separate probability corollary is a consequence, not a premise.

No mathematical repair is identified. For a fresh reproduction of the recorded evidence, the audit supplies these commands to run from the project root:

- `lake env lean -DwarningAsError=true AntichainOfGivenSize/Model/Theorem.lean` — headline axiom profile and closure checks.
- `lake env lean -DwarningAsError=true scripts/CheckAxioms.lean` — project-wide axiom audit.

---

The machine-readable audit is in [`handoff.json`](handoff.json).
