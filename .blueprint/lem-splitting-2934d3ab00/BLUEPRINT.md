# Formalization blueprint — Splitting Lemma

> Generated 2026-10-27T01:39:45.140Z by ChatGPT subscription · gpt-6-astra from `paper/Generating_Antichains_Simplified.tex:240` (`\begin{lemma}`).
> This is a **plan**, not a proof. Every Lean statement below is a proposal to be checked against the paper line by line before anyone starts proving it.

## What is being claimed

The 7 statements this development exists to prove, as `./AntichainOfGivenSize/Model/Theorem.lean` states them. Read these against the paper before anything else here: every section below inherits whatever is wrong in them, and a plan for the wrong statement looks exactly like a plan for the right one.

### `AntichainOfGivenSize.attainable_count`

Theorem 7.1: one absolute threshold gives the stated bound on the number of distinct attainable ideal sizes for every admissible pair `B, K`. The real arithmetic and the constant `100` are expanded for comparison with the manuscript and `scripts/CheckPaperStatements.lean`.

```lean
theorem attainable_count (hprior : Prior) :
    ∃ B₀ : ℕ, ∀ B K : ℕ, B₀ ≤ B →
      (1 ≤ K ∧ (K : ℝ) ≤ (Real.logb 2 (B : ℝ)) ^ 2 /
        (100 * Real.logb 2 (Real.logb 2 (B : ℝ)))) →
      ((Paper.attainableValues B K).card : ℝ) ≤
        (2 : ℝ) ^ ((B : ℝ) - Real.sqrt (B : ℝ))
```

### `AntichainOfGivenSize.alpha_eventual_upper`

Theorem 1.1(i): an absolute eventual upper bound, with its threshold chosen inside the manuscript's domain.

```lean
theorem alpha_eventual_upper (hprior : Prior) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 5 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n →
        (alpha n : ℝ) ≤ C * quadraticLogLogScale (n : ℝ)
```

### `AntichainOfGivenSize.alpha_lower_density_one`

Theorem 1.1(ii): the lower-good inputs, including exactly `5 ≤ n ≤ N`, have natural density one.

```lean
theorem alpha_lower_density_one (hprior : Prior) :
    ∃ c : ℝ, 0 < c ∧ Filter.Tendsto
      (fun N : ℕ ↦
        (((Finset.Icc 5 N).filter fun n : ℕ ↦
          c * quadraticLogLogScale (n : ℝ) ≤ (alpha n : ℝ)).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1)
```

### `AntichainOfGivenSize.alpha_simultaneous_density_one`

The simultaneous consequence of Theorem 1.1, also Corollary 10.2: an eventual upper bound and a density-one lower bound give both literal proportions with the same constants. The real denominator is `X`.

```lean
theorem alpha_simultaneous_density_one (hprior : Prior)
    (c C : ℝ) (n₀ : ℕ)
    (hupper : ∀ n : ℕ, n₀ ≤ n →
      (alpha n : ℝ) ≤ C * quadraticLogLogScale (n : ℝ))
    (hlower : Filter.Tendsto
      (fun N : ℕ ↦
        (((Finset.Icc 5 N).filter fun n : ℕ ↦
          c * quadraticLogLogScale (n : ℝ) ≤ (alpha n : ℝ)).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1)) :
    Filter.Tendsto
      (fun N : ℕ ↦ ((Paper.goodInputs c C N).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) ∧
    Filter.Tendsto
      (fun X : ℝ ↦ ((Paper.realGoodInputs c C X).card : ℝ) / X)
      Filter.atTop (nhds 1)
```

### `AntichainOfGivenSize.alpha_maximum_order`

The extremal consequence of Theorem 1.1, expanded into positive constant bounds for every sufficiently large real cutoff.

```lean
theorem alpha_maximum_order (hprior : Prior) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∃ X₀ : ℝ, 4 < X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        a * quadraticLogLogScale X ≤ (Paper.maximumBelow X : ℝ) ∧
        (Paper.maximumBelow X : ℝ) ≤ A * quadraticLogLogScale X
```

### `AntichainOfGivenSize.alpha_asymptotic_order`

Theorem 1.1: shared absolute constants for the universal upper bound, the density-one lower bound, and the simultaneous natural- and real-cutoff proportions, together with the real-cutoff extremal order.

```lean
theorem alpha_asymptotic_order (hprior : Prior) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, 5 ≤ n₀ ∧
      (∀ n : ℕ, n₀ ≤ n →
        (alpha n : ℝ) ≤ C * quadraticLogLogScale (n : ℝ)) ∧
      Filter.Tendsto
        (fun N : ℕ ↦
          (((Finset.Icc 5 N).filter fun n : ℕ ↦
            c * quadraticLogLogScale (n : ℝ) ≤ (alpha n : ℝ)).card : ℝ) / (N : ℝ))
        Filter.atTop (nhds 1) ∧
      Filter.Tendsto
        (fun N : ℕ ↦ ((Paper.goodInputs c C N).card : ℝ) / (N : ℝ))
        Filter.atTop (nhds 1) ∧
      Filter.Tendsto
        (fun X : ℝ ↦ ((Paper.realGoodInputs c C X).card : ℝ) / X)
        Filter.atTop (nhds 1)) ∧
    (∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∃ X₀ : ℝ, 4 < X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        a * quadraticLogLogScale X ≤ (Paper.maximumBelow X : ℝ) ∧
        (Paper.maximumBelow X : ℝ) ≤ A * quadraticLogLogScale X)
```

### `AntichainOfGivenSize.alpha_splitting`

Lemma 3.1: splitting on the manuscript's positive natural-number domain. The existing `splittingLemma` also permits `n = 0`.

```lean
theorem alpha_splitting (hprior : Prior) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    alpha (m + n) ≤ alpha m + alpha (n + 1)
```


## What this run produced

| Where | What it holds |
| --- | --- |
| `.blueprint/lem-splitting-2934d3ab00/BLUEPRINT.md` | This file: the whole plan, in reading order. |
| `.blueprint/lem-splitting-2934d3ab00/blueprint.json` | The same plan as data — every pass's output verbatim, including the source excerpt it was built from. |
| — | There are no briefs. This plan is executed **top-down**: agents go at the capstone and state the lemmas they turn out to need, so the work list is whatever still carries `sorry` in `./` at the start of each round. |
| `./AntichainOfGivenSize/Model/` | The **audit surface**: 2 files holding everything the headline theorem asserts, and nothing else. |
| `./README.md` | How to build the project, and the three checks that decide whether it is actually proved. |

### Read it in this order

1. **[What is being claimed](#what-is-being-claimed)** — the theorem as `./AntichainOfGivenSize/Model/Theorem.lean` states it, with the definitions it is stated in. This is the whole of what the run is trying to prove, quoted rather than described, so it is the first thing to check against the paper.

2. **[The result, restated](#the-result-restated)** — the same statement in words, with a verdict on each hypothesis and what the paper leaves unsaid. Every later section inherits whatever is wrong here, and a plan for the wrong statement looks exactly like a plan for the right one.

3. **The rest of the audit surface** — `./AntichainOfGivenSize/Model/Prelude.lean`. Everything else in the project is machinery serving these. This is the part a reader has to trust, so it is the part to read.

4. **[The crux](#the-crux)** — the step the proof actually turns on. If the architecture is wrong, it is wrong here, and it is cheaper to find that out before anything else is built.

5. **[Landing order](#landing-order)** — the sequence to prove things in, with what depends on what. Rebuild green after each one.

Sections between the restatement and the crux — the architecture and the reuse map — say what is being taken from Mathlib and arlib rather than proved here, and why the proof is split the way it is. Read them when a decision looks wrong, not before.

## The result, restated

For every pair of positive integers m and n, alpha(m+n) ≤ alpha(m) + alpha(n+1). Here alpha(k) is the minimum cardinality of a finite family S of finite sets, over an arbitrary ground set, whose generated ideal ID(S) = ⋃_{A∈S} P(A) contains exactly k subsets. No bound on the ambient ground-set size or the sizes of individual generators is imposed.

Reading provenance: `reader-agent`

### Canonical target

Exactly Lemma 3.1, lem:splitting: for all m,n ∈ {1,2,...}, alpha(m+n) ≤ alpha(m)+alpha(n+1). In the existing natural-number vocabulary the exact paper domain is ∀ m n : ℕ, 0 < m → 0 < n → alpha (m+n) ≤ alpha m + alpha (n+1). Reuse AntichainOfGivenSize.splittingLemma (m n : ℕ) (hm : 0 < m), whose stronger domain also permits n=0, by restriction to the paper domain. (paper/Generating_Antichains_Simplified.tex:192, 240–252; AntichainOfGivenSize/BasicLemmas.lean:169–200.)

Non-goals:

- The Lifting Lemma, counting theorem, main asymptotic theorem, and all other numbered results.
- A new definition of alpha, a new finite-family representation, or an additional antichain hypothesis.
- An executable procedure for finding optimal generating families, and time, space, query, or probability bounds.
- The unrestricted zero-first-input assertion, or treating the existing n=0 extension as part of the literal manuscript statement.

### Paper evidence

Target: paper/Generating_Antichains_Simplified.tex:240–245, Lemma 3.1 (lem:splitting).

Conventions read:

- paper/Generating_Antichains_Simplified.tex:119–124: finite generating sets, union of powersets, and exact ideal cardinality.
- paper/Generating_Antichains_Simplified.tex:190–236: N = {1,2,...} at line 192; definitions of generated ideal and alpha at 197–205; existence for each positive size at 208; indexed-family notation at 221–234.
- AntichainOfGivenSize/Model/Prelude.lean and Model/Theorem.lean: inspected the existing surface; its counting and asymptotic headlines are separate targets.
- AntichainOfGivenSize/Model/MainVocabulary.lean:17–33 and Model/CountingVocabulary.lean:20–26: inspected the actual definitions of HasGeneratorCount, alpha, and generatedIdeal.
- docs/current-paper.md: numbered-result correspondence and positive-natural/finite-representation discussion; .blueprint/notes/independent-reuse-review.md: existing splitting endpoint.
- lakefile.toml, lake-manifest.json, and lean-toolchain: inspected required libraries and pins. Searched local arlib Lean sources for splittingLemma, Splitting Lemma, HasGeneratorCount, def alpha, and def generatedIdeal; no matches. Read local Mathlib/Data/Finset/Card.lean:548–576 and Mathlib/Order/Lattice/Nat.lean:79–94 for the finite-union and minimum APIs already used by the project.

Proof sections read:

- paper/Generating_Antichains_Simplified.tex:247–252: complete splitting proof; no unresolved ref, cref, or eqref occurs in this statement or proof.
- paper/Generating_Antichains_Simplified.tex:254–267: neighboring lifting lemma and proof, confirming it is a separate result.
- AntichainOfGivenSize/BasicLemmas.lean: full file, especially alpha attainment at 88–105, union and intersection facts at 119–165, and splittingLemma at 167–200.
- AntichainOfGivenSize/Paper/BasicResults.lean:13–51: downward closure and small positive-input boundary values.
- paper/Generating_Antichains_Simplified.tex:1582–1586: bibliography entry for the attribution in the lemma title.

Omitted or missing sources:

- The cited Chandran–Gajjala–Meel article is not included under paper/; only its bibliography entry is present there. The frozen manuscript supplies the entire splitting proof locally, so no external article is needed for this statement.
- The separate /tmp/antichain-remaining-target-guidance-v2.json was not inspected because this pass limits source reads to the project and listed library directories. The exact existing endpoint was independently read in BasicLemmas.lean.

### Claims in the headline

| Claim | Can it fail? | Note |
| --- | --- | --- |
| alpha(m+n) ≤ alpha(m)+alpha(n+1), for every m>0 and n>0. | no — holds on every reachable outcome | This is an extremal mathematical size bound. It bounds no run's time, memory, queries, or other computational cost. |

Proposed shape, as the restatement pass wrote it:

```lean
A universally quantified deterministic inequality for the minimum generator count, for two positive integer arguments.
```

Claim ledger:

- For every positive integer m and every positive integer n, alpha(m+n) ≤ alpha(m)+alpha(n+1). (other, Model/Theorem; paper/Generating_Antichains_Simplified.tex:192, 240–245.)

### Modelling choices

- **acceptable** Existing vocabulary: Introduce no vocabulary: use the existing generatedIdeal, HasGeneratorCount, and alpha.. Risk: A second alpha or a bounded ambient universe would change the quantity.
- **modeling-note** Positive paper naturals versus Lean Nat: Express the literal paper domain with m>0 and n>0; retain the existing stronger splittingLemma unchanged for reuse.. Risk: Dropping m>0 is invalid; silently dropping n>0 mislabels a stronger library statement as the literal paper domain.
- **acceptable** Finite ambient representation: Use the existing existential Fin d representation with no upper bound on d; ground-set relabelling stays inside the proof.. Risk: Fixing or bounding d externally would restrict the minimum.
- **modeling-note** Family union and empty generators: Use an upper bound on the union's generator count, not an asserted equality. Its generated ideals intersect in the singleton {∅}.. Risk: Confusing {∅} with ∅ loses the subtraction of one; assuming additive generator cardinality can fail.
- **handoff-risk** Reuse status: Use splittingLemma as the existing proof endpoint; the present artifact records a source-level statement comparison.. Risk: A source inspection alone is not fresh proof certification.

### Downstream contract

- Program: No program or operational contract is needed for this lemma.
- Pseudocode: Any explanation of disjoint relabelling and union is proof-only. The existing sum-type encoding faithfully realizes the manuscript's relabelling.
- Theorem: State the single splitting inequality using existing alpha and the manuscript's positive domains for both m and n.
- Theorem: Apply the existing AntichainOfGivenSize.splittingLemma m n hm. Its n=0 extension is a property of the reuse endpoint, not an additional manuscript claim.
- Theorem: Do not replace alpha(n+1) by alpha(n), replace the inequality by equality, bound the ambient universe, or add disjointness, optimality, or antichain assumptions to the public statement.
- Handoff: Compare the exact domain with manuscript line 192 as well as the displayed inequality at 243.
- Handoff: Compare alpha with Model/MainVocabulary.lean and generatedIdeal with Model/CountingVocabulary.lean; verify that the count concerns subsets in the ideal, not elements in the union of generators.
- Handoff: Identify this as reuse of the existing splitting proof, not a newly derived result.
- Handoff: Check the size-one case and the distinction between an empty family and a family containing the empty set. Source inspection here supplies no fresh build or axiom-audit evidence.

### Hypotheses

| Hypothesis | Verdict | Why |
| --- | --- | --- |
| m and n are positive integers. | `required` | Both belong to the paper's explicitly positive N. The existing stronger endpoint needs m>0 and allows n=0, so its proof covers the exact domain directly. |
| Optimal finite generating families exist at the two input sizes. | `discharge-internally` | Already supplied by alpha_hasGeneratorCount; not an extra assumption about the input. |
| The two ground sets are disjoint. | `discharge-internally` | Disjoint relabelling is a proof construction, not a premise of the inequality. |
| Nonempty individual generators, a prescribed ambient universe, or a prescribed antichain structure. | `unnecessary` | None is imposed by the definition of alpha or by this lemma; each would unnecessarily restrict the statement. |

### Caller Conditions

- **Splitting Lemma target in Model/Theorem.lean** (model-internal) — There is no helper algorithm, loop, or reachable state. The proof is a pure inequality and reuses AntichainOfGivenSize.splittingLemma. Source: paper/Generating_Antichains_Simplified.tex:240–252; existing endpoint AntichainOfGivenSize/BasicLemmas.lean:169–200.
- **Positive domains for m and n** (add-hypothesis) — The paper defines natural numbers as positive (line 192), so retain 0 < m and 0 < n in the literal theorem statement. The existing endpoint requires 0 < m and allows n = 0; that stronger extension does not remove the paper's caller guard 0 < n. Source: paper/Generating_Antichains_Simplified.tex:192, 240–245; existing splittingLemma binder hm : 0 < m.
- **Optimal generating families and disjoint relabelling** (model-internal) — These are proof constructions, not caller assumptions: alpha_hasGeneratorCount supplies optimal-family witnesses, and the proof places their ground sets in disjoint summands. Source: paper/Generating_Antichains_Simplified.tex:247–252; existing BasicLemmas.lean splitting proof.
- **Ideal intersection and generator-family union** (proof-obligation) — After disjoint relabelling, the ideals intersect in the singleton containing the empty set, so their cardinalities combine with a subtraction of one; generator-family cardinality is only subadditive. Do not interpret the prose as disjoint ideals or assert additive generator counts. Source: paper/Generating_Antichains_Simplified.tex:248–251; existing splitting proof and mapped_inl_inter_mapped_inr.

### What the paper leaves unstated

Lean will force each of these. Where one turns out to be false rather than
merely unstated, that is a finding about the paper, not a modelling problem.

- No unresolved mathematical ambiguity remains after reading the source: line 192 explicitly settles positivity, and lines 197–208 settle the generated-ideal and minimum conventions.
- The existing splittingLemma permits n=0, while the paper quantifies only positive n. This is a documented stronger library endpoint; the literal target retains both positive domains.
- The phrase 'intersect only in the empty set' means the ideals' intersection is {∅}, of cardinality one. It does not mean the ideals are disjoint.
- The settled counting-target quantity and canonical theorem in the supplied context do not apply to this target: lem:splitting concerns the already defined AntichainOfGivenSize.alpha, not Paper.attainableValues. No declaration needs to change.

## Architecture

This target is planned as a standalone theorem: the proof route, reusable
source theorems and statement checks are the architecture. No interface or
concrete instance is being invented for it.

### Route — `library-corollary`

The existing project theorem AntichainOfGivenSize.splittingLemma proves the identical inequality under the weaker hypothesis 0 < m. Its source proof was inspected. Restrict its domain to the fixed capstone's positive m and n; retain the empty Prior parameter unchanged.

### Source theorems

| Declaration | Module | Why it applies |
| --- | --- | --- |
| `AntichainOfGivenSize.splittingLemma` | `AntichainOfGivenSize.BasicLemmas` | BasicLemmas.lean:169–200 already supplies the complete proof: attain optimal families, embed into opposite sides of a sum type, compute the singleton intersection of their ideals, and bound the union's generator count. No part needs re-proving. |

### Proof steps

- **Create one proof-side owner in AntichainOfGivenSize/Analysis/AlphaSplittingProof.lean.** — `Import AntichainOfGivenSize.BasicLemmas and AntichainOfGivenSize.Model.Prior. Declare AntichainOfGivenSize.Analysis.AlphaSplittingProof.splitting with exactly the fixed capstone's binders and conclusion.`. Both import paths were inspected. These imports expose the existing alpha and field-free Prior without importing the capstone or creating an import cycle.
- **Discharge the owner by direct application.** — `by exact AntichainOfGivenSize.splittingLemma m n hm`. The conclusion matches syntactically. No rewriting, arithmetic weakening, witness construction, or use of hprior or hn is needed.
- **Wire the fixed capstone to the proof owner.** — `After importing the new Analysis module into the existing surface, replace only the placeholder proof with: by exact AntichainOfGivenSize.Analysis.AlphaSplittingProof.splitting hprior m n hm hn`. Preserves the exact public declaration and every other completed proof.
- **Reconcile registration and verify the integration.** — `Register the new Analysis module and declaration in the existing source/axiom audit; retain the existing capstone registration, #modelClosureOfType, and #print axioms commands. Run lake build --wfail, lake env lean -DwarningAsError=true scripts/CheckAxioms.lean, lake env lean -DwarningAsError=true scripts/CheckPaperStatements.lean, and shasum -a 256 --check paper/SHA256SUMS.`. The capstone is already registered. Fresh compilation must establish that both owner and capstone have no sorryAx dependency; existing registry-based audits must retain coverage.

### Statement checks

- **Dropping positivity because Lean ℕ includes zero.** — Keep both hm : 0 < m and hn : 0 < n exactly. The manuscript explicitly defines ℕ as positive at line 192; the source theorem's additional n = 0 case does not change the fixed surface.
- **Treating the existing Prior binder as permission to assume the splitting result.** — Model/Prior.lean was inspected: Prior is a field-free Prop structure. Keep it unchanged and extract no mathematical assumption from it.
- **Substituting the counting theorem's bounded-family quantity for alpha.** — Use the existing AntichainOfGivenSize.alpha from Model/MainVocabulary.lean: the minimum over arbitrary finite ambient sizes, with exact generated-ideal cardinality. Introduce no new quantity or ambient bound.
- **Misdescribing the reused construction as disjoint ideals or additive generator cardinalities.** — The ideals intersect in {∅}, of cardinality one. Generator-family cardinality is bounded by the sum, not necessarily equal to it. The inspected source uses exact ideal inclusion–exclusion and Finset.card_union_le.
- **Changing the successor argument or inequality direction.** — Compare the capstone literally with alpha (m + n) ≤ alpha m + alpha (n + 1); preserve all binders and natural-number arithmetic.
- **Mistaking source inspection or historical verification for fresh proof certification.** — This pass inspected the sources and successfully checked the frozen-paper checksum. It did not compile the proposed owner or run the Lean build, closure, or axiom audits.


### Capstone — `AntichainOfGivenSize.alpha_splitting`

```lean
theorem AntichainOfGivenSize.alpha_splitting (hprior : AntichainOfGivenSize.Prior) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : AntichainOfGivenSize.alpha (m + n) ≤ AntichainOfGivenSize.alpha m + AntichainOfGivenSize.alpha (n + 1)
```

## The crux

Prove this first, in isolation. Once it is green the surrounding theorem
usually collapses into bookkeeping — and if it does not, the crux was
mis-identified and the architecture above needs another look.

### `AntichainOfGivenSize.splittingLemma`

```lean
∀ m n : ℕ, 0 < m → AntichainOfGivenSize.alpha (m + n) ≤ AntichainOfGivenSize.alpha m + AntichainOfGivenSize.alpha (n + 1)
```

**Why this is the heart:** This existing theorem already contains all mathematical work. The remaining obligation is an exact statement-preserving application.

**How to attack it:** Reuse directly. The sum-type relabelling and singleton-intersection argument remain inside the existing proof; introduce no helper obligations.

## Invariants to bake into the model

Cheaper as structure fields than as case splits later: Lean's `x / 0 = 0`
convention means a cancellation that ignores the zero case gets stuck on a
false-looking identity.

- `unchanged_alpha_semantics`: alpha n = sInf {k : ℕ \| HasGeneratorCount n k}, where HasGeneratorCount quantifies an arbitrary finite ambient size and exact ideal and generator cardinalities. — Ensures the wrapper concerns the manuscript's minimum generator count.
- `fixed_positive_domain`: The owner and capstone retain hprior, m, n, hm : 0 < m, and hn : 0 < n in the supplied order. — The stronger reuse endpoint must not induce a public statement change.
- `empty_prior`: AntichainOfGivenSize.Prior remains field-free. — The result is already proved mathematics, with no borrowed assumption.

## Modelling decisions

### Use one small Analysis wrapper and the existing vocabulary.

- **Rejected:** Rebuild the disjoint-union construction or introduce an abstract interface.
- **Because:** The named existing theorem exactly closes the obligation; additional architecture would duplicate finished work.
- **Scope caveat:** This is a deterministic extremal inequality, with no algorithm, probability, runtime, or coupling contract.

### Preserve the existing multi-result audit surface and registry.

- **Rejected:** Restructure the surface into new files for this target.
- **Because:** The fixed declaration already exists, and its quantity definitions already belong to Model. Only one new proof-side file is needed.
- **Scope caveat:** Preserve unrelated completed declarations and global audits; this target does not certify other results.

## Paper guide

- **Exact domain and quantity:** paper/Generating_Antichains_Simplified.tex:192, paper/Generating_Antichains_Simplified.tex:197–208, AntichainOfGivenSize/Model/MainVocabulary.lean:17–33, AntichainOfGivenSize/Model/CountingVocabulary.lean:20–26 — Checking positivity, the meaning of alpha, or whether the ambient universe is unrestricted.
- **Splitting statement and construction:** paper/Generating_Antichains_Simplified.tex:240–252, AntichainOfGivenSize/BasicLemmas.lean:119–200 — Checking exact conclusion alignment or explaining the shared empty subset and subadditive generator count.
- **Reuse correspondence and audit obligations:** docs/current-paper.md: numbered-results table and positive-naturals discussion, .blueprint/notes/independent-reuse-review.md: Exact existing endpoints, /tmp/antichain-remaining-target-guidance-v2.json: targets entry lem:splitting, AGENTS.md: registry and verification requirements — Integrating the owner, preserving audit coverage, and distinguishing source correspondence from fresh certification.

## Known blockers

- **Resolve the dependency-configuration discrepancy before execution.:** The located repository's lakefile.toml lists both arlib and Mathlib v4.32.0, while the supplied project context excludes arlib. The selected source theorem and proposed wrapper require no arlib declaration. Next: Confirm the execution checkout and preserve its approved pins. Do not add arlib imports or change dependencies to implement this wrapper.
- **Fresh compilation and audit evidence remain pending.:** This is a read-only blueprint pass. Source inspection found the exact endpoint and the sole open surface declaration, but supplies no fresh Lean certification. Next: Implement the single owner, assemble the capstone, and run the prescribed strict checks. Report any remaining whole-project failures separately without weakening this statement.

## Initial proof owners

| # | New declaration | Discharges | File | Difficulty | Depends on |
| --- | --- | --- | --- | --- | --- |
| 1 | `AntichainOfGivenSize.Analysis.AlphaSplittingProof.splitting` | `AntichainOfGivenSize.alpha_splitting` | `AntichainOfGivenSize/Analysis/AlphaSplittingProof.lean` | routine | `AntichainOfGivenSize.splittingLemma` |

Rebuild green after each one. Do not batch.

## Files

| Path | Role | Purpose |
| --- | --- | --- |
| `AntichainOfGivenSize/Model/Prelude.lean` | audit-surface | The vocabulary, and the quantity the theorem is about |
| `AntichainOfGivenSize/Model/Theorem.lean` | audit-surface | The author's result, and one theorem per claim under it |

## Definition of done

- [ ] The mechanical checks pass. They are run by the extension over the whole project between rounds — the build, the `sorry` warnings, the axiom profile of every headline, a sweep for escape hatches, the closure checks, and the two layout rules — and what they find comes back to you as the next round's brief. Build the modules you created and read their errors; do not try to run the gate.
- [ ] `#print axioms` on the capstone reports exactly the three ambient axioms — propext, Classical.choice, Quot.sound — and nothing else.
- [ ] No `declaration uses sorry` warning anywhere in the build output.
- [ ] A grep sweep for `sorry`, `admit`, `native_decide` and `axiom` over the project comes back clean, and agrees with the other two checks.
- [ ] The closure checks have been observed to *fail* on a deliberately broken control, so that their passing means something.
- [ ] The audit surface still states the paper's theorem: every claim the paper makes is in it, and nothing was weakened to make a proof go through. No script decides this one — the extension's handoff check reads the paper and the surface side by side, and it runs as the last step of a run.

## Risks

- **A round closes the capstone by leaning on lemmas that are themselves still `sorry`, which looks like progress and is not.** — The open-goal list is read out of the Lean sources every round, so a lemma left `sorry` stays on it however the declaration above it was closed.
- **An agent weakens an intermediate lemma until it is provable but useless.** — Whatever depends on it stops building, and the next round re-reads the sources rather than the plan.

## Briefs


---

### Source material this was built from

- Target: `paper/Generating_Antichains_Simplified.tex:240`
- Proof: `paper/Generating_Antichains_Simplified.tex:247`
- Files read: `paper/Generating_Antichains_Simplified.tex`
