# Handoff check — Splitting Lemma

> 2026-10-27T07:31:33.355Z · ChatGPT subscription · gpt-6-astra · Lean project `.`
> This check reads source text and may include Lean answers such as `#print axioms`. The correspondence verdicts are readings of statements. Anything not established is reported as unknown rather than as a pass.

## Paper claim progress

| Paper claim | Coverage | Proof state | Nearest blocker |
| --- | --- | --- | --- |
| For every positive integer m and every positive integer n, alpha(m+n) ≤ alpha(m)+alpha(n+1). | mapped | proved | — |

Every reportable paper claim is certified as proved.

The supplied audit identifies no mathematical discrepancy between the paper’s Splitting Lemma and `AntichainOfGivenSize.alpha_splitting`, and no additional mathematical assumption in its proof chain. The recorded verification evidence supports the Lean proof; the principal limitation is that the reviewers inspected saved results and matching source files without running a new build or elaboration.

## Correspondence with the paper

The lemma at `paper/Generating_Antichains_Simplified.tex:240–245` asserts

\[
\alpha(m+n)\le\alpha(m)+\alpha(n+1).
\]

At `AntichainOfGivenSize/Model/Theorem.lean:129`, `AntichainOfGivenSize.alpha_splitting` states the same inequality for natural numbers `m` and `n`, with hypotheses `hm : 0 < m` and `hn : 0 < n`. These hypotheses exactly encode the paper’s explicit convention at line 192 that natural numbers are positive. The arguments of `alpha`, additions, constant `1`, and inequality direction all agree.

The additional parameter `hprior : Prior` carries no mathematical premise: `Prior` has no fields, is inhabited by `⟨⟩`, and is unused by the splitting proof. Likewise, `[DecidableEq V]` in `generatedIdeal` supplies finite-set infrastructure without imposing an additional mathematical hypothesis on callers.

The definition correspondence supports this statement-level match. `AntichainOfGivenSize.generatedIdeal` represents the union of the generators’ powersets. `AntichainOfGivenSize.alpha` minimizes generator cardinality over unrestricted finite ambient universes, and `BasicLemmas.lean` establishes both existence of witnesses and attainment of the minimum. Thus the infimum does not conceal an empty feasible set. Finite relabelling preserves the paper’s objects, with no ambient-size restriction or antichain prerequisite introduced.

There are two extensions beyond the paper’s positive-input formulation: `alpha` also has a value at zero, and `AntichainOfGivenSize.splittingLemma` at `BasicLemmas.lean:169` permits `n = 0`. Neither changes the requested inequality on the paper’s domain. The proof follows the paper’s construction: it takes optimal families, embeds them into disjoint ground sets, establishes that their generated ideals intersect exactly in the empty subset, and bounds the combined generator count.

## Proof verification and its limits

Kernel proof evidence and faithfulness to the paper are separate matters. The correspondence findings above address the mathematical meaning of the definitions and statement. The supplied elaborator output reports that `AntichainOfGivenSize.alpha_splitting` depends only on `propext`, `Classical.choice`, and `Quot.sound`.

The saved verification records provide further support:

- `lake build --wfail` recorded exit code `0` and successful completion, with no `sorry` warnings.
- The strict axiom audit recorded exit code `0`, checked 3,086 declarations across 124 library modules, and reported only those three ambient axioms.
- The saved statement-closure check succeeded. All 138 recorded source hashes matched the inspected files, covering all 129 local Lean files with no unrecorded project Lean files.

Source inspection found no proof holes or custom trust mechanisms. The three partial definitions belong to audit traversal tooling in `Meta/`, outside the target’s mathematical dependency chain.

These are inspected records tied to matching sources, not fresh execution results from this review. The wider correspondence inventory includes other paper results, but their complete correspondence was not assessed within this requested lemma review. Probability-denotation review is inapplicable because the Splitting Lemma is deterministic. No unresolved correspondence questions were recorded for the target.

## Follow-up

No mathematical repair is indicated by these findings. To reproduce the target’s axiom and statement-closure checks from the project root, run:

```sh
lake env lean -DwarningAsError=true AntichainOfGivenSize/Model/Theorem.lean
```

---

The machine-readable audit is in [`handoff.json`](handoff.json).
