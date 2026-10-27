# Formalization blueprint — Main theorem

> Generated 2026-10-26T20:10:05.058Z by ChatGPT subscription · gpt-6-astra from `paper/Generating_Antichains_Simplified.tex:156` (`\begin{theorem}`).
> This is a **plan**, not a proof. Every Lean statement below is a proposal to be checked against the paper line by line before anyone starts proving it.

## What is being claimed

The 6 statements this development exists to prove, as `./AntichainOfGivenSize/Model/Theorem.lean` states them. Read these against the paper before anything else here: every section below inherits whatever is wrong in them, and a plan for the wrong statement looks exactly like a plan for the right one.

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


## What this run produced

| Where | What it holds |
| --- | --- |
| `.blueprint/thm-main-5e5f26eaeb/BLUEPRINT.md` | This file: the whole plan, in reading order. |
| `.blueprint/thm-main-5e5f26eaeb/blueprint.json` | The same plan as data — every pass's output verbatim, including the source excerpt it was built from. |
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

Let ID(G) be the union of the powersets of the finitely many finite sets in G. For every positive integer n, let alpha(n) be the minimum number of generators among all such families, over arbitrary ground sets, whose generated ideal has exactly n members. For real x > 4 put f(x) = (log_2(log_2 x))^2 / log_2(log_2(log_2 x)). There exist absolute real constants c > 0 and C > 0 and an integer threshold n_0, which may be chosen at least 5, such that (i) for every integer n >= n_0, alpha(n) <= C f(n), and (ii) the set L_c = {n an integer : n >= 5 and c f(n) <= alpha(n)} has natural density 1: lim_{N -> infinity, N a positive integer} |{n : 5 <= n <= N and c f(n) <= alpha(n)}|/N = 1. Consequently, with constants independent of n, the set {n an integer : n >= 5 and c f(n) <= alpha(n) <= C f(n)} has natural density 1; equivalently its count through a real cutoff X divided by X tends to 1 as X tends to positive infinity. Finally, there exist absolute real constants a > 0 and A > 0 and a real X_0 > 4 such that, for every real X >= X_0, a f(X) <= max{alpha(n) : n a positive integer, n < X} <= A f(X). The constants hidden in this last Theta assertion need not be the displayed c and C. All minima and maxima refer to mathematical cardinalities, and none of these assertions is about an algorithm's execution.

Reading provenance: `reader-agent`

### Canonical target

Exactly Theorem 1.1, thm:main: the eventual universal upper bound for alpha, the density-one lower bound for n >= 5, the simultaneous almost-all Theta consequence, and the two-sided extremal order for all sufficiently large real cutoffs. Preserve the existing Theorem 7.1 target as a separate result. The packet's assertion that the canonical target is already fixed to thm:attainable-count conflicts with the selected thm:main source; this blueprint records the selected main theorem without retargeting or replacing that existing counting declaration. (paper/Generating_Antichains_Simplified.tex:150–170; the conclusions are justified at 909–974 and 1365–1529.)

Non-goals:

- No replacement or weakening of AntichainOfGivenSize.attainable_count or its exact bounded-family semantics.
- No independently rederived counting theorem, no newly claimed proof of a numbered construction claim, and no requirement to reproduce every manuscript intermediate estimate.
- No eventual pointwise lower bound for all positive integers; powers of two explicitly rule that out.
- No algorithm, sampler, running-time bound, memory bound, query bound, or executable optimal-generator construction.
- No extra antichain, ambient-size, generator-size, dyadic-input, or unproved counting hypothesis.
- No certification of the bibliography, application claims, or account of formalization assistance.

### Paper evidence

Target: paper/Generating_Antichains_Simplified.tex:156–170, Theorem 1.1 (Main theorem), label thm:main; comparison function at 150–153.

Conventions read:

- Read the abstract and introduction, including generated ideals and alpha at 119–124, the almost-all interpretation at 98–110, and powers-of-two exceptions at 172.
- Read the preliminaries at 190–236: positive-natural convention at 192, ideal and alpha definitions at 196–208, base-two logarithms at 215, and indexed-family/inclusion–exclusion conventions at 219–235.
- Read Model/Prelude.lean and Model/Theorem.lean in full, Model/CountingVocabulary.lean:1–80, Model/Prior.lean in full, and MainStatement.lean:1–180. The current Model headline is explicitly the counting theorem, while alpha and the growth scale are existing declarations outside Model/.
- Read docs/current-paper.md in full, Paper/Statements.lean, Paper/Results.lean, Paper/AlmostAll.lean, Paper/RealDensity.lean, Paper/Extremal.lean, Paper/Scale.lean:1–100, and scripts/CheckPaperStatements.lean.
- Read lakefile.toml and lean-toolchain: the project requires arlib at 6262f60ad7556be62e94e87f6b5811cf299e7d94 and Mathlib/Lean v4.32.0. Searched 360 arlib source files for the main theorem's named vocabulary and natural-density terminology without finding a matching endpoint. Inspected the installed Mathlib Asymptotics/Defs.lean definitions of IsTheta and positive-constant Big-O characterizations; also searched Asymptotics/Theta.lean. The project already supplies the needed mathematical results.

Proof sections read:

- Read Section 3's splitting and lifting proofs at 238–267 and Sections 4–5 at 269–551 to account for the upper construction's referenced background.
- Read Section 6 at 553–974: the block construction and its floor/ceiling parameters, Claims 6.2–6.5, direct reduction, and the universal upper bound with finite-prefix absorption.
- Read Sections 7–9 and the counting proof at 976–1361, including V(B,K), the header and incidence representation, fixed-header estimate, and uniform threshold.
- Read the dyadic-block and almost-all arguments at 1365–1477. This includes the distinction between alpha <= K as the exceptional event, the fixed constant 1/800 available in the proof, and the finite-prefix density calculation.
- Read the extremal consequence at 1479–1529 and the following remark at 1531–1536. These clarify the strict cutoff n < X and eventual monotonicity of the comparison function.

Omitted or missing sources:

- The supplied excerpt omitted the full density and extremal arguments, the literal real-cutoff proportion, the precise definitions of alpha and the maximum, and the existing main-theorem implementation; these were read locally.
- The manuscript has no appendix or external input/include source directives; its mathematical proof material is in the supplied TeX file.
- The cited earlier papers were not needed to identify this theorem's statement and were not consulted. The scratch Claim 6.4/6.5 probes were not inspected, since this pass does not reconstruct those separate proofs.
- No shell commands, Lean probes, builds, axiom checks, or checksum checks were run. Prior verification reports in correspondence notes are historical evidence, not new validation from this pass.

### Claims in the headline

| Claim | Can it fail? | Note |
| --- | --- | --- |
| Universal eventual upper bound alpha(n) <= C f(n). | no — holds on every reachable outcome | The bound is on a minimum mathematical generator count, not the work used to find generators. |
| The integers n >= 5 satisfying alpha(n) >= c f(n) have natural density 1. | no — holds on every reachable outcome | Individual integers can violate the inequality; the asserted deterministic density limit has no probabilistic failure parameter. |
| Simultaneous two-sided bounds hold on a density-one set of positive integers. | no — holds on every reachable outcome | Almost all means natural density, not probability-one success of a sampled computation. |
| The maximum of alpha(n) over 1 <= n < X has order f(X) for every sufficiently large real X. | no — holds on every reachable outcome | The maximum is a mathematical read-off, not an algorithm to enumerate integers or families. |

Proposed shape, as the restatement pass wrote it:

```lean
One deterministic mathematical theorem with a shared existential c,C,n_0, a universal eventual upper bound, a density-one lower bound, a simultaneous density-one consequence, and a real-variable extremal Theta consequence. There is no run or failure event.
```

Claim ledger:

- There exist absolute C > 0 and an integer n_0 such that alpha(n) <= C f(n) for every integer n >= n_0. (other, Model/Theorem; Theorem 1.1(i), paper:157–159.)
- For an absolute c > 0, the integers n >= 5 with c f(n) <= alpha(n) have natural density 1; c is chosen independently of all n and cutoffs. (other, Model/Theorem; Theorem 1.1(ii), paper:157–160.)
- For fixed positive absolute c and C, the simultaneous inequalities c f(n) <= alpha(n) <= C f(n) hold on a set of positive integers of natural density 1. (other, Model/Theorem; Theorem 1.1 consequence, paper:162–166; explicit density formulation at 1392–1401.)
- There exist a,A > 0 and X_0 > 4 such that a f(X) <= max_{1<=n<X} alpha(n) <= A f(X) for every real X >= X_0. (other, Model/Theorem; Theorem 1.1 consequence, paper:166–169; extremal argument at 1479–1529.)
- For X >= 0, realGoodInputs c C X consists exactly of the integers n with 5 <= n <= X satisfying both non-strict bounds. (correctness, Interface; Paper/RealDensity.lean:21–27; paper:1395–1400.)
- A density-zero count of orderExceptions is equivalent to the density-one goodInputs proportion, and the natural-cutoff good proportion gives the same real-cutoff proportion. (correctness, Interface; Paper/AlmostAll.lean:25–51 and Paper/RealDensity.lean:36–51; paper:1451–1476.)
- For X > 1, maximumBelow X is the maximum of alpha(n) over exactly the positive integers n < X. (correctness, Interface; Paper/Statements.lean:80–82; Paper/Extremal.lean:100–104,153–155; paper:1481–1484.)

### Modelling choices

- **handoff-risk** Selected result versus existing canonical counting target: Describe thm:main as a separate target and explicitly flag the contradictory thm:attainable-count packet metadata. Leave the existing counting theorem and definitions intact.. Risk: A later pass could silently formalize the wrong theorem or overwrite a finished counting target.
- **modeling-note** Vocabulary reuse and model ownership: The listed vocabulary already exists outside Model/; reuse names and definitions rather than introduce synonyms or a new alpha. Only declarations reached by the chosen main-theorem statement need model ownership. No proof modules or unused construction parameters are part of its vocabulary.. Risk: A superficial import or a duplicated definition could obscure the exact quantity or violate the existing closure boundary.
- **acceptable** Positive integers versus Lean naturals: Use naturals for integer indices and explicit positive-range guards; choose n_0 >= 5. Keep the existing total alpha unchanged, including its extension at zero.. Risk: An unguarded statement at zero or at n <= 4 would assign significance to values outside the paper's domain.
- **modeling-note** Total growth function: Use quadraticLogLogScale without alteration, but interpret it as the manuscript's f only when x > 4. Reuse Paper.growth_pos_of_four_lt for positivity.. Risk: The totalized value at a singular logarithmic input cannot justify adding small inputs to the claim.
- **proof-obligation** Joint constants in the main conclusion: Assemble c,C,n_0 together. Existing Paper.mainTheorem supplies an upper constant and separate almost-all constants; if exposing one shared pair, keep a valid lower constant and enlarge the upper constant to the maximum of the two positive upper witnesses.. Risk: A mere alias to a conjunction of independently existential interfaces does not visibly establish a single shared pair until this elementary witness reconciliation is supplied.
- **acceptable** Density through complements and finite prefixes: Retain the existing exception sets and their strict lower-failure inequality, and use the existing complement-count and real-cutoff bridges to expose the good proportion. The omission of integers 1 through 4 is finite.. Risk: An infinitely-often lower bound or only upper density 1 would be strictly weaker than the asserted natural density 1.
- **proof-obligation** Real-cutoff maximum and Theta: Use maximumBelow with ceil(X) and a strict interval. Read IsTheta at the real atTop filter as eventual two-sided positive-constant bounds, using eventual positivity to remove norms.. Risk: Using floor(X) in a half-open interval would miss admissible integers at nonintegral cutoffs; using n <= X would alter the literal maximum at integral X.
- **modeling-note** Reuse versus a new paper proof: Reuse Paper.mainTheorem and the individual public endpoints; retain the documented differences for the upper, counting, density, and extremal proofs in the correspondence. Do not promote their proof-route estimates to claims of this target.. Risk: Calling the new interface a newly derived or line-by-line manuscript proof would misrepresent the work.

### Downstream contract

- Program: There is no program to implement and no random output contract.
- Program: If a program surface is required by the scaffold, it can only reference this mathematical model.
- Pseudocode: No algorithm listing is required for Theorem 1.1.
- Pseudocode: Any description of block matching, counting records, density conversion, or extremal witnesses is a proof outline; it must not assert running-time or memory guarantees.
- Theorem: Preserve Theorem 1.1's two numbered assertions and both displayed consequences. Keep Theorem 7.1 as its existing separate target.
- Theorem: Use the unchanged alpha and quadraticLogLogScale; c,C are positive absolute reals and n_0 is one absolute integer threshold. A witness n_0 = 5 is available from the stronger existing upper theorem.
- Theorem: Expose natural density 1 for the lower-good set and simultaneous bounds with fixed constants. The literal real-cutoff proportion has denominator X and counts 5 <= n <= X.
- Theorem: For the extremal conclusion, quantify all sufficiently large real X and use the exact maximum over positive integers strictly below X, with separate positive Theta constants permitted.
- Theorem: Reuse Paper.mainTheorem, Paper.universalUpper_from_five, Paper.almostAllLowerBound, Paper.almostAllOrder, Paper.realAlmostAllGoodProportion, and Paper.extremalOrder. Do not substitute the older LowerBoundStatement, which only says infinitely often.
- Theorem: Reconcile shared existential constants and the semantic equivalences explicitly; supporting construction and counting theorems are discharged dependencies, not new hypotheses.
- Handoff: Resolve the packet's conflicting target identity before changing a theorem surface: the JSON describes thm:main, while the current AntichainOfGivenSize.attainable_count remains thm:attainable-count.
- Handoff: Compare expanded inequalities, density limits, and real strict-cutoff maximum against the frozen TeX and scripts/CheckPaperStatements.lean:53–55,82–101, not merely against statement aliases.
- Handoff: Treat this work as an interface to existing results plus any necessary semantic or existential-witness bridges. No new proof status or integration success is asserted by this reader file.
- Handoff: Use the repository's existing capstone, closure, source-coverage, axiom, independent-statement, and snapshot validation process for later integration. Preserve the existing pins and model definitions; this pass did not execute those checks.

### Hypotheses

| Hypothesis | Verdict | Why |
| --- | --- | --- |
| n is an integer with n >= n_0 for (i), and n >= 5 in the density sets. | `required` | These are the exact positive domains of the theorem; the density cutoff is not a freely changeable input restriction. |
| c,C > 0 are absolute reals independent of n and of the cutoff. | `required` | Their existential quantifiers precede the universal upper bound and limit. |
| f(x) is the exact base-two iterated-log expression, interpreted for x > 4. | `required` | The expression and its domain are explicit in the setup and conventions. |
| For the maximum, X is an arbitrary sufficiently large real number and n is a positive integer strictly less than X. | `required` | The real cutoff and strict endpoint are part of the conclusion's semantics. |
| Thresholds lie inside the positive-log domain and the maximum is over a nonempty set. | `discharge-internally` | Choose existential thresholds large enough; this is not an additional input hypothesis. |
| An optimal finite generating family exists and may be represented over Fin m. | `discharge-internally` | The paper establishes finiteness and the project already supplies attainment and relabelling results. |
| The counting theorem, matching theorem, or a numerical asymptotic estimate is assumed. | `unnecessary` | The public main-theorem endpoints have these dependencies discharged. |
| The integer input is random, lies in a selected dyadic block, or satisfies a structural restriction on generators. | `unnecessary` | Such proof devices do not restrict the main theorem's input domain. |

### Caller Conditions

- **Theorem 1.1 / selected target `thm:main`** (handoff-risk) — The selected result has no helper algorithm, loop state, or invocation guard. It is a theorem about `alpha`, density, and a real-cutoff maximum. The prompt also records a handoff conflict: the existing `Model/Theorem.lean` is the separate counting target `thm:attainable-count`. Source: Selected theorem statement and `canonicalTarget` / `ambiguityLedger` in the paper-reading contract..
- **Claim 6.4 block update** (proof-obligation) — The author gives a proof route for a separate numbered claim: combine `block_increment` with `idealCard_update`, then cancel the additional `2^ell` term modulo `2^((i+1)*ell)`. This is not a caller guard or invariant for Theorem 1.1; it belongs to that claim's proof obligations. Source: Author instruction 2; scratch `Claim64Probe.lean` is described as a checked derivation, not integrated library work..
- **Claim 6.5 parameter rounding** (proof-obligation) — For the paper's floor/ceiling parameter choices, the listed inequalities and bridge from general `r,ell` estimates must be proved and connected to the constructed ideal. They are not additional assumptions of Theorem 1.1 or caller conditions. Source: Author instructions 2–4; scratch `Claim65.lean` is described as unintegrated..
- **Claim 6.3 position-only statement** (proof-obligation) — Use `position_intersection` for the literal position-only claim. Do not introduce a helper-state invariant or strengthen its claim ledger based on a proof-route description. Source: Author instruction 2..

### What the paper leaves unstated

Lean will force each of these. Where one turns out to be false rather than
merely unstated, that is a finding about the paper, not a modelling problem.

- Target metadata conflict: the selected theorem and its verbatim statement are thm:main, but the supplied prior canonical-target text and current Model/Theorem.lean identify thm:attainable-count. These are different results and quantities. This file describes the selected main theorem; it does not authorize rewriting the existing counting target.
- Theorem 1.1 does not separately type n_0 or X. The positive-integer convention and eventual upper-bound proof justify an integer n_0 >= 5. The real definition of f, the real-cutoff limit, and the floor(log X) extremal proof support arbitrary real X; the existing maximumBelow and ExtremalOrderStatement already fix that reading.
- The phrase alpha(n) = Theta(f(n)) for almost all n is shorthand, not ordinary pointwise IsTheta on all natural numbers atTop. The abstract and Corollary 10.2 resolve it as one fixed positive pair of constants holding on a density-one set. Powers of two prevent a universal eventual lower bound.
- The constants implicit in the extremal Theta are not specified or identified with c,C. They must be absolute and uniform in X, but may be different constants. The existence theorem does not require any numerical value for c,C,n_0 or the extremal constants; 1/800 is an available proof witness, not an extra statement requirement.
- Paper.mainTheorem packages a universal upper constant separately from the almost-all pair. A later interface that exposes the paper's shared c,C must reconcile these witnesses explicitly rather than assume they are definitionally identical.
- The paper defines f only for x > 4 and does not define a maximum over an empty index set. The existing total Lean definitions are harmless on the theorem's eventual range, but do not extend the paper's claim to small or nonpositive inputs.
- No unresolved mathematical defect in the selected main statement was identified in this reading. Its terse density and cutoff conventions are resolved by the surrounding source; the conflicting target identity is a handoff issue.

## Architecture

This target is planned as a standalone theorem: the proof route, reusable
source theorems and statement checks are the architecture. No interface or
concrete instance is being invented for it.

### Route — `library-corollary`

Reuse the project's existing upper-bound, density, and extremal theorems. The remaining work is witness-preserving finite-prefix bookkeeping and conversion of norm bounds. Assign each of the four open surface declarations its own Analysis file, preserving the proof-side owner names and the existing capstone assembly. No algorithm, abstract interface, or borrowed assumption is needed.

### Source theorems

| Declaration | Module | Why it applies |
| --- | --- | --- |
| `AntichainOfGivenSize.Paper.universalUpper_from_five` | `AntichainOfGivenSize.Paper.Extremal` | Supplies the eventual upper bound with n₀ = 5. Listed in the supplied declaration inventory; no upper-bound estimates need to be reproved. |
| `AntichainOfGivenSize.Paper.almostAllGoodProportion` | `AntichainOfGivenSize.Paper.Results` | Retain its lower constant c and squeeze the lower-good proportion between the simultaneous-good proportion and 1. The supplied previous-pass evidence reports this declaration and expansion; they could not be independently rechecked in the current workspace. |
| `AntichainOfGivenSize.Paper.extremalOrder` | `AntichainOfGivenSize.Paper.Results` | Provides both extremal bounds on real cutoffs. The supplied prior evidence reports this endpoint; reuse it rather than repeat the density-to-interval argument. |
| `AntichainOfGivenSize.Paper.growth_pos_of_four_lt` | `AntichainOfGivenSize.Paper.Scale` | Removes the absolute value of the growth function on the eventual range. Name and type are supported by the supplied prior evidence. |
| `Asymptotics.isBigO_iff'` | `Mathlib.Analysis.Asymptotics.Defs` | Extracts the positive upper constant from extremalOrder.isBigO. This is the instantiated mathematical signature reported in the supplied previous-pass inspection. |
| `Asymptotics.isBigO_iff''` | `Mathlib.Analysis.Asymptotics.Defs` | Applied to extremalOrder.isBigO_symm, supplies the lower constant directly in the required direction. Exact implicit arguments remain an elaboration check. |
| `Finset.card_le_card` | `Mathlib.Data.Finset.Card` | Turns good-set inclusions and finite-prefix containment into cardinality bounds. |
| `Finset.card_sdiff_add_card_eq_card` | `Mathlib.Data.Finset.Card` | With s the simultaneous-good set and t the lower-good set, counts exactly the inputs lost by imposing the upper inequality. |
| `Nat.card_Icc` | `Mathlib.Order.Interval.Finset.Nat` | Bounds the lower-good count by N and gives its normalized upper bound 1 on N ≥ 5. |
| `tendsto_of_tendsto_of_tendsto_of_le_of_le'` | `Mathlib.Topology.Order.Basic` | Eventual squeeze closes both density arguments. This schematic signature and module are inherited from the supplied previous-pass evidence. |
| `tendsto_const_div_atTop_nhds_zero_nat` | `Mathlib.Analysis.SpecificLimits.Basic` | The loss of at most n₀ inputs disappears after normalization. |
| `tendsto_nat_floor_atTop` | `Mathlib.Analysis.SpecificLimits.Basic` | Composes the natural density limit with the real cutoff's natural floor. |
| `tendsto_nat_floor_div_atTop` | `Mathlib.Analysis.SpecificLimits.Basic` | Changes the denominator from floor(X) to X while preserving the supplied constants. The exact polymorphic argument names should be checked in the execution checkout. |

### Proof steps

- **Give each open declaration a separate proof-side file without changing its owner name.** — `Create Analysis/AlphaSimultaneousDensityOneProof.lean, Analysis/AlphaEventualUpperProof.lean, Analysis/AlphaLowerDensityOneProof.lean, and Analysis/AlphaMaximumOrderProof.lean under AntichainOfGivenSize/. Each uses namespace AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof and defines only its assigned owner. Import Model.Prior and the necessary existing Paper modules; the density and maximum wrappers may import Paper.Results. Do not import Model.Theorem or the library root.`. This repairs the rejected file ownership while preserving the mathematical route and globally qualified owner names. Each file can compile independently before the surface imports it.
- **Prove the fixed-witness simultaneous natural proportion first.** — `Inside simultaneousDensityOne, let L N be the surface's lower-good filter and G N := Paper.goodInputs c C N. Prove G N ⊆ L N by unfolding goodInputs and unpacking Finset.mem_filter. Prove L N \ G N ⊆ Finset.range n₀: a member n with n₀ ≤ n satisfies hupper n, hence belongs to G N, a contradiction. Combine Finset.card_le_card and Finset.card_sdiff_add_card_eq_card to obtain (L N).card ≤ (G N).card + n₀ and (G N).card ≤ (L N).card. Cast and divide on the eventual range N ≥ 1, obtaining Lcard/N - (n₀ : ℝ)/N ≤ Gcard/N ≤ Lcard/N. Squeeze using hlower.sub (tendsto_const_div_atTop_nhds_zero_nat (n₀ : ℝ)) and hlower; simplify 1 - 0.`. The exported existential density endpoints do not supply this stronger interface for arbitrary fixed c,C,n₀. Only a finite prefix can fail the supplied upper bound, independently of the cutoff.
- **Transfer the simultaneous limit to real cutoffs with exactly the same constants.** — `For the preceding hNat, multiply hNat.comp tendsto_nat_floor_atTop by tendsto_nat_floor_div_atTop. Simplify the limit 1 * 1. Use eventual equality on X ≥ 1 to identify (goodCard(floor X)/floor X) * (floor X/X) with goodCard(floor X)/X. Establish floor(X) ≥ 1, obtain its nonzero real cast, unfold Paper.realGoodInputs, and cancel by field_simp. Return ⟨hNat, hReal⟩.`. The existing existential real-cutoff bridge may select different witnesses. Its floor-factor calculation gives the needed fixed-witness conclusion without changing the supplied c or C.
- **Discharge the eventual upper declaration using threshold 5.** — `In eventualUpper: obtain ⟨C, hC, hupper⟩ := Paper.universalUpper_from_five; exact ⟨C, hC, 5, le_rfl, hupper⟩.`. The stronger source already includes finite-prefix absorption. The required empty Prior argument contributes no mathematical assumption.
- **Extract a lower-density witness from the proved simultaneous density endpoint.** — `In lowerDensityOne, obtain ⟨c, D, hc, hD, hgood⟩ from Paper.almostAllGoodProportion. Define L N locally as the lower-good filter. Prove Paper.goodInputs c D N ⊆ L N. For N ≥ 5, use L N ⊆ Finset.Icc 5 N and Nat.card_Icc to show (L N).card ≤ N. Cast and divide by the positive real N. Squeeze the lower-good proportion between the hgood sequence and the constant sequence 1. Return ⟨c, hc, hLower⟩.`. The lower-good set contains the simultaneous-good set, so the completed density theorem supplies the result directly. Discarding D leaves the capstone free to use its independent upper witness C.
- **Expand the extremal IsTheta into the literal inequalities.** — `In maximumOrder, let hθ := Paper.extremalOrder. Obtain ⟨A, hA, hUpper⟩ from Asymptotics.isBigO_iff'.mp hθ.isBigO and ⟨a, ha, hLower⟩ from Asymptotics.isBigO_iff''.mp hθ.isBigO_symm. Extract a common real threshold R from hLower.and hUpper using Filter.eventually_atTop.mp. Choose X₀ := max 5 R. For X ≥ X₀, prove 4 < X, apply Paper.growth_pos_of_four_lt, and simplify Real.norm_eq_abs and abs_of_nonneg, using Nat.cast_nonneg for maximumBelow. Return a,A,X₀ and the resulting bounds.`. The lower constant multiplies the growth function, both constants are positive, and the threshold covers every sufficiently large real X. No extremal estimates are reproved.
- **Dispatch the four surface proofs and retain the capstone assembly.** — `Use exact Analysis.AlphaAsymptoticOrderProof.eventualUpper hprior; exact Analysis.AlphaAsymptoticOrderProof.lowerDensityOne hprior; exact Analysis.AlphaAsymptoticOrderProof.simultaneousDensityOne hprior c C n₀ hupper hlower; and exact Analysis.AlphaAsymptoticOrderProof.maximumOrder hprior in their respective surface bodies. Preserve the capstone's existing obtain statements and final ⟨⟨c, C, hc, hC, n₀, hn₀, hupper, hlower, alpha_simultaneous_density_one hprior c C n₀ hupper hlower⟩, alpha_maximum_order hprior⟩.`. The fixed assembly already reconciles the witnesses through the arbitrary-constant simultaneous lemma. It requires neither enlarging C nor another proof-side capstone owner.
- **Verify implementation, ownership, and statement fidelity in the execution checkout.** — `Read its AGENTS.md registries and docs/current-paper.md, confirm all four owner names and file paths are unused, and register each assigned file through the prescribed mechanism. Compile each proof file before dependent surface checks. Run the repository's strict build, independent paper-statement checks, source-coverage and closure audits, negative controls, and frozen-paper checksum. Inspect #print axioms for all four owners and alpha_asymptotic_order; retain the existing counting checks.`. The present workspace contains only standalone_decomposition.schema.json, so no Lean source, paper, registry, build, checksum, or axiom check could be executed here. Supplied historical inspection reports are evidence for this plan, not current validation.

### Statement checks

- **Using Paper.realAlmostAllGoodProportion_of_nat as though it preserved arbitrary c,C.** — The supplied evidence gives its type as AlmostAllGoodProportionStatement → RealAlmostAllGoodProportionStatement, with existential witnesses on both sides. Use the floor-factor calculation at the supplied constants instead.
- **Using Paper.orderExceptions_eq_exceptionalInputs with only an eventual upper bound.** — The supplied evidence says this theorem requires the bound for every n ≥ 5. The fixed simultaneous declaration supplies it only from n₀. Bound the lost inputs by Finset.range n₀.
- **Treating Paper.mainTheorem as definitionally equal to the fixed capstone.** — Preserve the shared c,C witnesses, both literal density limits, and the expanded extremal inequalities. Independently existential source interfaces and a norm-based IsTheta do not directly match this contract.
- **Replacing natural density one with infinitely often or an eventual pointwise lower bound.** — Retain Tendsto of the complete normalized count to 1. The older matchingLowerBoundInfinitelyOften is insufficient; powers of two preclude a universal eventual lower bound.
- **Changing the lower event at equality.** — The good event is c * quadraticLogLogScale n ≤ alpha n. Its failure is the strict inequality alpha n < c * quadraticLogLogScale n.
- **Mixing the inclusive density cutoff and strict maximum cutoff.** — Keep Icc 5 N and realGoodInputs c C X = goodInputs c C floor(X) for density, with denominator X. Keep maximumBelow X = (Ico 1 ceil(X)).sup alpha for the strict maximum, including at integral X.
- **Reversing the lower Big-O conversion or removing norms without signs.** — Apply isBigO_iff'' to extremalOrder.isBigO_symm to obtain a * ‖growth X‖ ≤ ‖maximumBelow X‖. Remove norms only after establishing X > 4 and nonnegativity.
- **Adding positivity or threshold assumptions to alpha_simultaneous_density_one.** — Preserve its exact binders: arbitrary c,C : ℝ and n₀ : ℕ, with only hupper and hlower. The finite-prefix proof does not need 0 < c, 0 < C, or 5 ≤ n₀.
- **Changing Prior, model vocabulary, or the separate counting target.** — Keep Prior empty and preserve the existing names and bodies of alpha, quadraticLogLogScale, and the density and maximum read-offs. Add no counting hypothesis and do not replace attainable_count.
- **Mistaking source evidence from earlier passes for verification in this environment.** — The local file inventory found no Lean checkout. Recheck declaration signatures, module paths, owner freshness, and audit commands in the execution checkout before implementation; do not report historical checks as newly run.


### Capstone — `AntichainOfGivenSize.alpha_asymptotic_order`

```lean
theorem AntichainOfGivenSize.alpha_asymptotic_order (hprior : AntichainOfGivenSize.Prior) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, 5 ≤ n₀ ∧
      (∀ n : ℕ, n₀ ≤ n →
        (AntichainOfGivenSize.alpha n : ℝ) ≤ C * AntichainOfGivenSize.quadraticLogLogScale (n : ℝ)) ∧
      Filter.Tendsto
        (fun N : ℕ ↦
          (((Finset.Icc 5 N).filter fun n : ℕ ↦
            c * AntichainOfGivenSize.quadraticLogLogScale (n : ℝ) ≤ (AntichainOfGivenSize.alpha n : ℝ)).card : ℝ) / (N : ℝ))
        Filter.atTop (nhds 1) ∧
      Filter.Tendsto
        (fun N : ℕ ↦ ((AntichainOfGivenSize.Paper.goodInputs c C N).card : ℝ) / (N : ℝ))
        Filter.atTop (nhds 1) ∧
      Filter.Tendsto
        (fun X : ℝ ↦ ((AntichainOfGivenSize.Paper.realGoodInputs c C X).card : ℝ) / X)
        Filter.atTop (nhds 1)) ∧
    (∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∃ X₀ : ℝ, 4 < X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        a * AntichainOfGivenSize.quadraticLogLogScale X ≤ (AntichainOfGivenSize.Paper.maximumBelow X : ℝ) ∧
        (AntichainOfGivenSize.Paper.maximumBelow X : ℝ) ≤ A * AntichainOfGivenSize.quadraticLogLogScale X)
```

## The crux

Prove this first, in isolation. Once it is green the surrounding theorem
usually collapses into bookkeeping — and if it does not, the crux was
mis-identified and the architecture above needs another look.

### `AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.simultaneousDensityOne`

```lean
For the supplied c,C,n₀, an upper bound valid from n₀ and a lower-good natural proportion tending to 1 imply both simultaneous-good proportions tending to 1 with those exact constants. Locally, for L N the lower-good set and G N = Paper.goodInputs c C N, G N ⊆ L N and L N \ G N ⊆ Finset.range n₀.
```

**Why this is the heart:** The available existential endpoints do not establish this stronger fixed-witness interface. It is what makes the already-written capstone's shared-constant assembly valid.

**How to attack it:** Prove both containments locally; derive Lcard ≤ Gcard + n₀ and Gcard ≤ Lcard; normalize on N ≥ 1 and squeeze. Compose that limit with natural floor and multiply by floor(X)/X. Keep these intermediate facts local to the assigned owner.

## Invariants to bake into the model

Cheaper as structure fields than as case splits later: Lean's `x / 0 = 0`
convention means a cancellation that ignores the zero case gets stuck on a
false-looking identity.

- `Fixed witnesses`: The c,C supplied to simultaneousDensityOne are unchanged in both its natural and real limits. — Selecting replacement existential witnesses would not discharge the fixed surface declaration.
- `Uniform finite-prefix loss`: For every N, L N \ Paper.goodInputs c C N ⊆ Finset.range n₀, so the lost count is at most n₀ independently of N. — Its normalized contribution tends to zero, including when n₀ < 5.
- `Positive-tail cancellation`: Natural normalization uses N ≥ 1; real-floor cancellation uses X ≥ 1 and floor(X) ≥ 1. — Total division at zero does not justify cancellation identities.
- `Extremal signs`: On X ≥ X₀ > 4, quadraticLogLogScale X > 0 and (Paper.maximumBelow X : ℝ) ≥ 0. — These facts turn the library's norm inequalities into the required literal bounds.
- `Audit ownership`: All four new proof owners are in separate Analysis files; no new definition enters the statement closure. — Proof completion preserves the fixed audit vocabulary and the independent counting target.

## Modelling decisions

### Implement this standalone mathematical target through a library-wrapper route.

- **Rejected:** Introduce an algorithm, probability space, or abstract analysis interface.
- **Because:** The statement concerns deterministic cardinalities and limits, and existing project results provide its substantive estimates.
- **Scope caveat:** No operational or resource guarantee is asserted.

### Assign exactly one Analysis file to each of the four open declarations, retaining the existing proposed owner namespace.

- **Rejected:** Place all four owners in Analysis/AlphaAsymptoticOrderProof.lean.
- **Because:** The corrected ownership contract requires a distinct file per lemmaOrder entry. This organizational change does not alter the proof route or require parallel workers.
- **Scope caveat:** The proposed paths must be checked for existing contents before creation; finished Analysis files are not overwritten.

### Use Paper.almostAllGoodProportion to extract the lower-density witness.

- **Rejected:** Repeat the conversion from the density-zero exceptional count.
- **Because:** That conversion is already represented by the proved good-proportion endpoint. Inclusion and squeeze give the lower-only statement.
- **Scope caveat:** Discard its auxiliary upper constant; the simultaneous owner still accepts the independently supplied C.

### Keep the fixed-witness floor calculation local to simultaneousDensityOne.

- **Rejected:** Assume the exported existential real-cutoff theorem preserves the given constants.
- **Because:** Its existential type does not provide that guarantee. The existing floor limits directly establish the required stronger interface.
- **Scope caveat:** No floor-limit theorem or underlying density theorem is reproved.

### Keep Prior empty and use project results plus Mathlib only.

- **Rejected:** Add assumptions for counting, upper bounds, or asymptotics.
- **Because:** The supplied project inventory already provides the mathematical endpoints.
- **Scope caveat:** The plan adds no arlib dependency. Historical manifest claims in the supplied material could not be checked in this workspace and are not treated as current availability.

## Paper guide

- **Exact target, quantifiers, and powers-of-two exceptions:** paper/Generating_Antichains_Simplified.tex:150–172, paper/Generating_Antichains_Simplified.tex:192–215 — Checking the fixed capstone, the domain x > 4, base-two logarithms, and the distinction between density one and an eventual pointwise lower bound. Locations are inherited from the supplied reading evidence.
- **Upper-bound witness and threshold 5:** paper/Generating_Antichains_Simplified.tex:909–974, AntichainOfGivenSize/Paper/Extremal.lean:19–49, docs/current-paper.md: Differences in proof implementation, sharp universal upper bound — Confirming universalUpper_from_five and documenting its existing proof route without claiming a new construction proof.
- **Natural density and finite prefixes:** paper/Generating_Antichains_Simplified.tex:1392–1476, AntichainOfGivenSize/Paper/AlmostAll.lean:25–55, AntichainOfGivenSize/Paper/Results.lean:48–67 — Checking non-strict good inequalities, lower-good containment, and the finite-prefix loss for arbitrary supplied constants.
- **Real-cutoff denominator and witness preservation:** paper/Generating_Antichains_Simplified.tex:1392–1401, AntichainOfGivenSize/Paper/RealDensity.lean:21–47 — Reusing the floor-factor calculation and checking why its existential exported interface does not directly discharge the fixed-witness target.
- **Strict real maximum and positive Theta constants:** paper/Generating_Antichains_Simplified.tex:1479–1529, AntichainOfGivenSize/Paper/Extremal.lean:81–168, Mathlib/Analysis/Asymptotics/Defs.lean:118–145 — Checking the strict cutoff, both Big-O directions, and removal of norms on the positive tail.

## Known blockers

- **Check the actual execution checkout and compile the four owners.:** The current directory contains only standalone_decomposition.schema.json. The source files, AGENTS.md, documentation, frozen paper, and Lean checkout described in the packet are absent. This pass could inspect their supplied excerpts and historical evidence only; no build, axiom audit, or paper checksum was run. Next: In the execution checkout, read the required source and registry files, verify the supplied reusable signatures and the freshness of all four owner names and paths, implement one owner per file, and run all prescribed checks. Do not replace missing evidence with additional theorem assumptions.
- **Check the single-seed surplus audit against the separately retained counting surface.:** The supplied surface invokes #surplusIn over Model using only alpha_asymptotic_order as seed. Prior evidence reports that unrelated counting vocabulary can then appear as surplus. This is an integration risk, not a failure observed in this pass. Next: Run the existing registered-claim audit and negative controls in the real checkout. Preserve individual closure checks and the counting declarations; resolve any registry issue through the existing audit mechanism rather than deleting vocabulary or changing statements.
- **Confirm exact elaboration of the inherited Mathlib applications.:** The mathematical signatures are supported by the supplied previous-pass evidence, but polymorphic argument names and tactic invocations were not tested here. Next: Check the pinned declarations before coding, especially floor-limit type arguments, Finset.card_sdiff_add_card_eq_card orientation, and the IsTheta projections. Adjust applications only; preserve every owner signature.

## Initial proof owners

| # | New declaration | Discharges | File | Difficulty | Depends on |
| --- | --- | --- | --- | --- | --- |
| 1 | `AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.simultaneousDensityOne` | `AntichainOfGivenSize.alpha_simultaneous_density_one` | `AntichainOfGivenSize/Analysis/AlphaSimultaneousDensityOneProof.lean` | moderate | `Finset.card_le_card`, `Finset.card_sdiff_add_card_eq_card`, `tendsto_of_tendsto_of_tendsto_of_le_of_le'`, `tendsto_const_div_atTop_nhds_zero_nat`, `tendsto_nat_floor_atTop`, `tendsto_nat_floor_div_atTop` |
| 2 | `AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.eventualUpper` | `AntichainOfGivenSize.alpha_eventual_upper` | `AntichainOfGivenSize/Analysis/AlphaEventualUpperProof.lean` | routine | `AntichainOfGivenSize.Paper.universalUpper_from_five` |
| 3 | `AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.lowerDensityOne` | `AntichainOfGivenSize.alpha_lower_density_one` | `AntichainOfGivenSize/Analysis/AlphaLowerDensityOneProof.lean` | routine | `AntichainOfGivenSize.Paper.almostAllGoodProportion`, `Finset.card_le_card`, `Nat.card_Icc`, `tendsto_of_tendsto_of_tendsto_of_le_of_le'` |
| 4 | `AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.maximumOrder` | `AntichainOfGivenSize.alpha_maximum_order` | `AntichainOfGivenSize/Analysis/AlphaMaximumOrderProof.lean` | routine | `AntichainOfGivenSize.Paper.extremalOrder`, `AntichainOfGivenSize.Paper.growth_pos_of_four_lt`, `Asymptotics.isBigO_iff'`, `Asymptotics.isBigO_iff''` |

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

- Target: `paper/Generating_Antichains_Simplified.tex:156`
- Files read: `paper/Generating_Antichains_Simplified.tex`
