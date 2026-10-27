# Handoff check — Main theorem

> 2026-10-27T06:27:01.255Z · ChatGPT subscription · gpt-6-astra · Lean project `.`
> This check reads source text and may include Lean answers such as `#print axioms`. The correspondence verdicts are readings of statements. Anything not established is reported as unknown rather than as a pass.

## Paper claim progress

| Paper claim | Coverage | Proof state | Nearest blocker |
| --- | --- | --- | --- |
| There exist absolute C > 0 and an integer n_0 such that alpha(n) <= C f(n) for every integer n >= n_0. | mapped | proved | — |
| For an absolute c > 0, the integers n >= 5 with c f(n) <= alpha(n) have natural density 1; c is chosen independently of all n and cutoffs. | mapped | proved | — |
| For fixed positive absolute c and C, the simultaneous inequalities c f(n) <= alpha(n) <= C f(n) hold on a set of positive integers of natural density 1. | mapped | proved | — |
| There exist a,A > 0 and X_0 > 4 such that a f(X) <= max_{1<=n<X} alpha(n) <= A f(X) for every real X >= X_0. | mapped | proved | — |
| For X >= 0, realGoodInputs c C X consists exactly of the integers n with 5 <= n <= X satisfying both non-strict bounds. | mapped | proved | — |
| A density-zero count of orderExceptions is equivalent to the density-one goodInputs proportion, and the natural-cutoff good proportion gives the same real-cutoff proportion. | mapped | proved | — |
| For X > 1, maximumBelow X is the maximum of alpha(n) over exactly the positive integers n < X. | mapped | proved | — |

Every reportable paper claim is certified as proved.

The supplied audit finds matching mathematical content between the paper’s main theorem and `AntichainOfGivenSize.alpha_asymptotic_order`, with no substantive extra hypothesis identified. Recorded verification supports the Lean proof’s kernel status, subject to the evidence limits below. The substantive presentation issue concerns a conditional helper exposed on the audit surface; its premises are discharged in the headline proof, so it does not leave a missing headline assumption or conclusion.

The correspondence is between `thm:main` at `paper/Generating_Antichains_Simplified.tex:156` and `AntichainOfGivenSize.alpha_asymptotic_order` at `AntichainOfGivenSize/Model/Theorem.lean:126`. The Lean statement retains all four conclusions: an eventual upper bound, a density-one lower bound, simultaneous two-sided bounds for almost all inputs, and two-sided bounds for the maximum below every sufficiently large real cutoff. Shared positive constants `c,C` serve the density assertions; separate positive extremal constants `a,A` correctly express the paper’s Θ notation. Enlarging existential thresholds to `n₀ ≥ 5` and `X₀ > 4` does not restrict the claimed inputs.

The underlying definitions also agree. `generatedIdeal` represents the union of generator powersets, and `alpha` minimizes generator cardinality over arbitrary finite ambient universes. Existence and attainment are proved in `BasicLemmas.lean:88–102`, and `AntichainReduction.lean:101` supplies an optimal antichain witness. The extension to `alpha 0` leaves the paper’s positive domain unchanged. `quadraticLogLogScale` uses the paper’s base-two logarithms. The density count uses exactly `5 ≤ n ≤ N`, while `Paper.maximumBelow` uses `Ico 1 (ceil X)`, preserving the strict endpoint `1 ≤ n < X` for integral and nonintegral cutoffs.

The correspondence inventory records no missing numbered result. Several supporting statements are generalized to zero inputs or broader construction histories; the reviewed generalizations retain the paper’s cases. The counting representation covers unrestricted finite ambient size, and its normalization and generator-load conditions do not add balancedness or intersection restrictions. The headline’s sole explicit binder, `(hprior : Prior)`, is an empty proposition-valued structure, constructible as `⟨⟩`, rather than an assumed mathematical result.

Kernel verification and correspondence are separate evidence claims. All 138 source hashes in `.blueprint/verification/checks.json` matched the inspected files. The saved `lake build --wfail`, strict axiom audit, and `Model/Theorem.lean` elaboration each recorded exit code 0. The build log reports successful completion with 3548 jobs and no warning or sorry lines; the elaboration log records successful closure checks, including the headline. The saved axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound` across 3086 declarations in 124 library modules. The separately supplied fresh headline `#print axioms` output agrees. Source inspection found no operative mathematical `sorry`, `admit`, or custom axioms; the partial definitions identified are audit tooling outside the mathematical proof dependencies.

These results were inspected, not rerun during the review. No fresh build or kernel replay was performed, and dependency checkouts under `.lake` were outside the inspection scope. Eight Lean files under `.blueprint/scratch` are outside the recorded hash manifest and build coverage and are not imported by the reviewed library. Their textual scan found no proof placeholders or custom axioms, but their independent compilation remains unverified. That limitation does not affect the supplied headline axiom profile.

The audit-surface finding concerns `AntichainOfGivenSize.alpha_simultaneous_density_one` at `AntichainOfGivenSize/Model/Theorem.lean:97`. It is a universally quantified conditional transfer lemma, whereas the paper’s almost-all conclusion asserts unconditional existence of positive constants. The paper does not separately state this helper. The headline uses it with both premises supplied by proved components in `Analysis/TheoremProof.lean`; the finding therefore concerns its placement and description on the audit surface, not the headline’s mathematical content.

The headline is deterministic: its finite-cardinality ratios express natural density, not random executions. The separate probability corollary was inspected and uses the actual uniform PMF on the literal dyadic block, with the paper’s strict event and probability bound.

The findings justify the following follow-up:

- Place `AntichainOfGivenSize.alpha_simultaneous_density_one` in proof content rather than presenting it as the paper’s unconditional corollary.
- If the eight `.blueprint/scratch` files belong to the deliverable, record separate compilation checks for them.
- To reproduce the headline axiom and closure output, run `lake env lean -DwarningAsError=true AntichainOfGivenSize/Model/Theorem.lean` from the project root.

---

The machine-readable audit is in [`handoff.json`](handoff.json).
