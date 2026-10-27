# Handoff check — Main theorem

> 2026-10-27T06:57:31.876Z · ChatGPT subscription · gpt-6-astra · Lean project `.`
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

The supplied reviews found no substantive extra hypothesis or missing conclusion in the correspondence between the paper’s main theorem and `AntichainOfGivenSize.alpha_asymptotic_order`. The recorded verification evidence supports successful Lean checking of the reviewed sources. These are separate findings: the mathematical comparison establishes what the statement says, while the build, closure, and axiom evidence concerns its proof. No fresh Lean execution was performed during this review.

The target is `thm:main` at `paper/Generating_Antichains_Simplified.tex:156–170`; its Lean counterpart is at `AntichainOfGivenSize/Model/Theorem.lean:106`. Lean explicitly includes the eventual universal upper bound, the density-one lower bound, the simultaneous two-sided almost-all assertion, and the two-sided bound for the maximum below every sufficiently large real cutoff. The positive constants `c,C` are shared across the upper and density conclusions. Separate positive constants for the maximum correctly express its own Θ assertion.

The definitions and endpoints support that correspondence. `generatedIdeal` is the union of the generators’ powersets, and `alpha` minimizes generator count over unrestricted finite ambient universes. Existence and attainment are established in `BasicLemmas.lean`, with an antichain witness supplied by `AntichainReduction.lean`. `quadraticLogLogScale` uses the paper’s base-two logarithms. Natural density counts precisely `5 ≤ n ≤ N`; the real-cutoff version uses `floor X` and denominator `X`. `Paper.maximumBelow` selects exactly the positive integers strictly below `X`, and its specification establishes attainment. Enlarging the existential thresholds to `n₀ ≥ 5` and `X₀ > 4` does not change the eventual assertions.

The explicit binder `(hprior : Prior)` adds no mathematical hypothesis: `Prior`, defined at `AntichainOfGivenSize/Model/Prior.lean:22`, is a fieldless proposition inhabited by `⟨⟩`. Likewise, decidable equality for the finite ambient representation imposes no extra input restriction. For the counting argument, `AntichainOfGivenSize.Model.attainableValues_membership` establishes equivalence with the paper’s attainable ideal sizes over arbitrary finite ambient universes. The internal profile fields encode deletion of unused ground elements and the stated generator-size bound; they do not impose balancedness, intersection restrictions, or an external ambient-size cap. `AntichainOfGivenSize.attainable_count` retains the threshold independent of `K`, budget constant `100`, and real square-root saving.

The supporting-statement inventory records exact matches and generalizations. The generalizations include defining `alpha` at zero, allowing zero inputs in `liftingLemma`, and proving construction identities for arbitrary admissible active sets and histories rather than only chronological stages. `AntichainOfGivenSize.Paper.blockMatching` supplies the explicit witnesses `5,3` also obtained in the paper’s proof. There are proof-route differences: `Paper.universalUpper_from_five` reuses the project’s earlier upper-bound route and absorbs the finite prefix, and Lean can derive density directly from counting. Neither difference weakens the corresponding statement.

The main theorem is deterministic; natural density here is a limit of proportions, not a sampling claim. Separately, `AntichainOfGivenSize.Paper.typicalLowerBound_probability` uses a concrete uniform PMF on the paper’s dyadic interval, the strict event `K < alpha n`, and the exact error bound `1 − 2^(1 − sqrt B)`.

For proof verification, all 138 SHA-256 entries in `.blueprint/verification/checks.json` matched the current files, and every local Lean source was recorded. The saved `lake build --wfail` exited with code 0 and reported successful completion without `sorry` warnings. The saved `Model/Theorem.lean` check also exited with code 0 and recorded successful closure checks. The supplied current headline axiom output and saved project-wide audit agree on only `propext`, `Classical.choice`, and `Quot.sound`; the latter covers 3,086 declarations across 124 library modules. The source sweep found no proof holes or custom axioms. The three partial definitions identified belong to audit tooling outside the mathematical proof dependencies.

The evidence has two explicit limits. Dependency checkout contents under `.lake` were not independently audited or hashed. Also, `paper-statements.txt` is empty and supplies no elaborator output itself: its companion record supplies the statement-check command and exit code 0, while the correspondence findings rest on reading declarations and definitions. The review does not establish a complete, independently certified inventory of every paper statement.

No mathematical repair is indicated by these findings. To reproduce the recorded axiom evidence from the project root, run `lake env lean -DwarningAsError=true scripts/CheckAxioms.lean`.

---

The machine-readable audit is in [`handoff.json`](handoff.json).
