# Formalization blueprint — Counting attainable ideal sizes

> Generated 2026-10-26T16:17:19.745Z by ChatGPT subscription · gpt-6-astra from `paper/Generating_Antichains_Simplified.tex:987` (`\begin{theorem}`).
> This is a **plan**, not a proof. Every Lean statement below is a proposal to be checked against the paper line by line before anyone starts proving it.

## What is being claimed

The statement this development exists to prove, as `./AntichainOfGivenSize/Model/Theorem.lean` states it. Read it against the paper before anything else here: every section below inherits whatever is wrong in it, and a plan for the wrong statement looks exactly like a plan for the right one.

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


## What this run produced

| Where | What it holds |
| --- | --- |
| `.blueprint/thm-attainable-count-04ffa9e627/BLUEPRINT.md` | This file: the whole plan, in reading order. |
| `.blueprint/thm-attainable-count-04ffa9e627/blueprint.json` | The same plan as data — every pass's output verbatim, including the source excerpt it was built from. |
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

All logarithms in this statement are to base 2. For positive integers B and K, let V(B,K) be the set of distinct integers n for which there exist a positive integer s with 1 ≤ s ≤ K and finite sets A_1,...,A_s on an arbitrary common ground set such that |A_i| ≤ B for every i and n = |⋃_{i=1}^s P(A_i)|. The sets A_i may be empty, equal, or contain one another; the ambient ground set has no prescribed size bound. There exists an absolute integer B_cnt, independent of K and of all generating families, such that for every integer B ≥ B_cnt and every integer K satisfying 1 ≤ K ≤ (log₂ B)^2 / (100 log₂(log₂ B)), the finite set V(B,K) satisfies |V(B,K)| ≤ 2^(B − √B). The existential threshold may be chosen sufficiently large and positive so that both logarithms and the positive denominator have their ordinary real meanings. Cardinality is coerced to the reals in this inequality; √B is the nonnegative real square root and the right-hand side is real exponentiation with real subtraction. The counted sizes need not lie below 2^B, and each attainable size is counted once regardless of how many families realize it.

Reading provenance: `reader-agent`

### Canonical target

Exactly Theorem 7.1 (thm:attainable-count): there exists one absolute integer threshold B_cnt such that for every integer B ≥ B_cnt and every integer K with 1 ≤ K ≤ (log₂ B)^2/(100 log₂(log₂ B)), the number of all distinct attainable ideal sizes from nonempty families of at most K finite sets, each of size at most B, is at most 2^(B−√B). Reuse AntichainOfGivenSize.Paper.countingBound : CountingBoundStatement with the proved representation equivalence; this is an interface to an existing proof, not a newly derived counting theorem. (paper/Generating_Antichains_Simplified.tex:981–997; proof 999–1361. Exact existing endpoint: AntichainOfGivenSize/Paper/CountingParameters.lean:119–136.)

Non-goals:

- No proof or restatement of universal upper bounds, the bit/block matching constructions, the main theorem, density-one statements, extremal order, or the subsequent dyadic probability corollary.
- No algorithm, sampler, probability monad, operational semantics, runtime, space bound, or enumeration procedure.
- No requirement to reproduce every intermediate manuscript equation or the streamlined header product when reusing the already proved endpoint.
- No optimization or requirement to expose a least threshold; the existing proof's witness 2^(2^20) is sufficient but is not prescribed by the manuscript.
- No restriction of B to powers of two or a sparse sequence; no replacement by an infinitely-often lower bound, asymptotic-O estimate, residue count, or weaker budget constant.
- No changes to generatedIdeal, alpha, completed library files, manuscript, checksum, dependency pins, audit registry, or independently expanded contracts in this pass.

### Paper evidence

Target: paper/Generating_Antichains_Simplified.tex:987–997, Theorem 7.1, label thm:attainable-count; defining paragraph at 976–986.

Conventions read:

- paper/Generating_Antichains_Simplified.tex:60–64: macros ID, V, indicator, bit alphabet, growth.
- Lines 119–124 and 192–208: finite generating sets, generated ideals, positive-natural convention, empty generator example.
- Lines 215–235: all logarithms base 2, integer interval notation, indexed families, Φ, nonempty queries and exact inclusion–exclusion.
- Lines 1011–1025: repetition padding, deleting unused ground elements, relabelling, derived N ≤ KB, signed sum.
- Lines 1151–1171 and 1224–1244: canonical header ordering, empty-intersection convention, incidence lists with repetitions.
- Lines 1531–1536: explicit absence of balancedness, intersection-order restrictions, or independent ambient-size hypothesis.

Proof sections read:

- Lines 999–1044 and figure at 1046–1081: auxiliary parameters, intended stronger estimate and counting scheme.
- Section Structural headers, lines 1083–1171: all scale selection, packing and header-count arguments.
- Section Values within one structural header, lines 1173–1294: exceptional set, central terms, records, tail interval, fixed-header product.
- Subsection Proof of the counting theorem, lines 1296–1361: uniform estimates and final choice B_cnt=2^λ₀.
- All references occurring in those proof sections were resolved: eq:main-parameters, eq:ground-bound, eq:IE, sec:headers, sec:fixed-header, fig:counting-scheme, eq:selected-scales, eq:header-count, eq:u-bound, eq:cluster-agreement, eq:center-query-count, eq:exceptional-record-count, eq:tail-final-bound, eq:fixed-header-count, sec:lower-consequences and eq:Gamma-lower.
- Theorem 1.1 at lines 156–170 and universal-upper statement at 909–915 were read to classify the introductory references as motivation, not counting dependencies. Corollary block-probability and its proof at 1369–1390 were read to delimit the excluded randomized claim.
- Existing-source reuse checked in MainStatement.lean, Paper/Statements.lean, Paper/Representation.lean, Paper/GeneralCounting.lean, Paper/CountingEstimates.lean, Paper/CountingParameters.lean, LowerBound/BoundedProfiles.lean, LowerBound/ProfilePadding.lean, LowerBound/ClusterImageBound.lean, docs/current-paper.md and scripts/CheckPaperStatements.lean; the independent reader also inspected the CheckAxioms registry.
- Required-library check: lakefile.toml and lean-toolchain pin Lean and Mathlib v4.32.0; lake-manifest.json resolves Mathlib to 81a5d257c8e410db227a6665ed08f64fea08e997. The reuse reader inspected Mathlib Real.logb, Real.rpow, Finset.powerset and Finset.card sources. No guessed declaration names are needed for the endpoint.

Omitted or missing sources:

- The supplied excerpt omitted the base-two convention, full definitions of ID and Φ, all counting proof sections, and the concluding no-extra-restrictions remark; these were read from the local manuscript.
- The manuscript has no appendix or input/include dependency for this proof; the complete counting argument is in the main text. No missing external mathematical source was required.
- The numerical manuscript threshold λ₀ is intentionally nonexplicit. The opening B ≥ 2^20 is only a starting proof range, not a claimed sufficient final threshold.
- This pass inspected source and performed no Lean compilation, build, or axiom-check execution. Prior verification reported in docs/current-paper.md is historical evidence, not a fresh result of this pass.
- The manuscript bytes read have SHA-256 137f3d51bc6dee4e62a4897bf4da0584cd7ff247aa6003811ff239794c295b1f, matching paper/SHA256SUMS. No manuscript or library source is modified.

### Claims in the headline

| Claim | Can it fail? | Note |
| --- | --- | --- |
| A single absolute threshold makes the exact attainable-size cardinality bound hold uniformly for every sufficiently large B and every admissible K. | no — holds on every reachable outcome | This is a deterministic combinatorial inequality, not a probability-one assertion. It bounds how many mathematical values are attainable, not time, memory, queries, passes or any cost of computing them. |

Proposed shape, as the restatement pass wrote it:

```lean
One deterministic eventual cardinality theorem: ∃ an absolute integer threshold B_cnt, ∀ integers B≥B_cnt, ∀ integers K in the exact base-two logarithmic budget, |V(B,K)|≤2^(B−√B). There is no algorithm run.
```

Claim ledger:

- One absolute threshold works for every B above it and every K in the exact stated real-log budget, and \|V(B,K)\| ≤ 2^(B−√B). (correctness, Model/Theorem; Paper:987–997 and 1300–1361.)
- V(B,K) consists exactly of numerical ideal sizes from nonempty families of at most K generators of individual size at most B, with no ambient cap. (correctness, Interface; Paper:981–986,1011–1017,1531–1536; Representation.lean:24–27,89–92.)
- Repeating a final generator and relabelling the active ground set preserve the ideal size and give N ≤ KB. (correctness, Analysis; Paper:1011–1017.)
- Φ equals the complete signed inclusion–exclusion sum over nonempty queries. (correctness, Analysis; Paper:221–235,1019–1025.)
- Each eligible family admits a structural header; there are at most (J+1)K^K possible headers. (other, Analysis; Paper:1097–1122,1151–1171.)
- The exceptional set has size at most 2Kρ/λ^6 and cluster members agree off it. (correctness, Analysis; Paper:1175–1199.)
- The incidence record and central exponent transcript determine the exact signed central sum Z. (correctness, Analysis; Paper:1204–1257.)
- There are at most (KB+1)2^(2K²ρ/λ⁶) incidence records and (B+1)^(2^J(1+K2^h)) central transcripts. (other, Analysis; Paper:1225–1233,1259–1265.)
- Every noncentral exponent is at most B−ρ; the signed tail lies in an interval with at most 2^(B−ρ+K+2) integer values. (other, Analysis; Paper:1270–1286.)
- For each header the attainable-value count is bounded by the product of the incidence, transcript and tail-interval counts. (other, Analysis; Paper:1287–1294.)
- Uniformly in admissible K, Γ≥2^(7λ/10), eventually d≤1/4 and L_rec≤Γ/2, and eventually Γ/4≥√B; summing over headers yields the stronger intermediate bound 2^(B−Γ/4). (other, Analysis; Paper:1300–1361.)
- The existing endpoint proves the exact target with a different, larger clustered record encoding; identify reuse honestly and preserve the correspondence note. (correctness, Handoff; CountingParameters.lean:119–136; docs/current-paper.md:166–175.)
- This target asserts no probabilistic or computational resource result; the following uniformly sampled dyadic corollary is separate. (other, Handoff; Paper:987–997 versus 1365–1390.)

### Modelling choices

- **acceptable** Integers versus Lean natural-number parameters.: Reuse the existing ℕ statement with K≥1 and an existential sufficiently large positive B threshold. Explain the equivalence with the paper's integer quantifiers.. Risk: Do not silently restrict to a special sequence or let a threshold depend on K.
- **modeling-note** One-based [s] and [N], including the all-empty family.: Use Fin s and Fin N as reindexings; allow N=0 and interpret [0] as empty.. Risk: Adding N≥1 or requiring a nonempty generator would alter membership and could lose the attainable value 1.
- **acceptable** Tuples versus Finset families and exact-K profiles.: Reuse the proved representation equivalence, deduplication of tuples, and padding by repetition.. Risk: Do not count tuple lengths or multiplicities as ideal sizes; do not apply the equivalence at K=0.
- **acceptable** Unspecified ground universe.: Quantify an arbitrary finite ambient size in the direct predicate; treat finite active support and relabelling as justified reductions.. Risk: Do not replace the individual bound B by a fixed universe Fin B or an independent input cap.
- **acceptable** Set cardinality and exact values.: Reuse the finite image attainableValues and its membership equivalence, preserving exact natural values before taking Finset.card.. Risk: Residue images may collapse distinct values; Set.ncard without finiteness or a family count would not be an adequate semantic substitute.
- **handoff-risk** Real logs, real square root, real subtraction and real power.: Keep Real.logb 2, Real.sqrt, and real exponentiation in the expanded theorem. Auxiliary integral bounds are confined to the existing proof.. Risk: Compare the expanded statement against scripts/CheckPaperStatements.lean:65–70, not merely an alias with a matching name.
- **modeling-note** Threshold and the preliminary B ≥ 2^20 range.: State only existence of a sufficiently large absolute integer threshold. Record that the existing certificate uses 2^(2^20); do not attribute that specific witness to the manuscript.. Risk: Claiming B_cnt=2^20 from the opening proof paragraph would overstate the manuscript.
- **acceptable** Reuse rather than rederive the counting proof.: Use Paper.countingBound and Paper.mem_attainableValues_iff as the endpoint and its semantic interface.. Risk: Do not overwrite completed files, invent replacement lemma names, or call a wrapper a new proof of the counting theorem.
- **handoff-risk** Different proof representation in existing Lean.: Preserve the documented fact that the checked proof uses a larger clustered encoding and different auxiliary integral parameters, rather than the manuscript's exact fixed-header product.. Risk: An interface reusing the endpoint must not claim that every displayed intermediate manuscript estimate was newly formalized.
- **modeling-note** Proof encodings versus executable algorithms.: No Program or Pseudocode algorithm contract is needed. Graphs, packings, records and transcripts are proof-only vocabulary.. Risk: Do not add probability-one claims or resource annotations to deterministic cardinality inequalities.
- **modeling-note** J=0, no clusters, and empty central index choices.: Retain K<h and J=0. Allow an empty cluster collection and empty U; exclude only the pair (S,Q)=(∅,∅) from recorded central queries.. Risk: Extra positivity on J or including the empty query would change the proof and possibly its exponent bounds.
- **handoff-risk** Proof and workflow status.: Report only source inspection in this reader pass. Let later Tex2Lean passes generate their own plans, status and handoff evidence.. Risk: Do not fabricate workflow output, mark newly generated targets proved by hand, or claim current successful integration.

### Downstream contract

- Program: No algorithm is present. Do not implement a sampler, maximum-packing search, enumeration program, cost semantics, or probability monad for this target.
- Program: If a scaffold requires Model/Program.lean, keep it limited to references to the mathematical model; do not invent an operational contract.
- Program: Reuse existing generatedIdeal, HasBoundedGeneratingFamily, attainableValues and AdmissibleBudget definitions and their proved links; preserve alpha unchanged.
- Pseudocode: No algorithm listing is available or required. The paper's record/transcript construction is an explanatory proof encoding, not a mandated executable program.
- Pseudocode: If presenting proof steps, label them as proof-only and distinguish the manuscript encoding from the existing larger clustered encoding documented in docs/current-paper.md.
- Pseudocode: Existential choices of header and maximum packing are not random sampling.
- Theorem: Reuse AntichainOfGivenSize.Paper.countingBound : CountingBoundStatement. Its expanded shape is ∃ B₀ : ℕ, ∀ B K : ℕ, B₀ ≤ B → (1 ≤ K ∧ (K : ℝ) ≤ (Real.logb 2 (B : ℝ))^2 / (100 * Real.logb 2 (Real.logb 2 (B : ℝ)))) → ((attainableValues B K).card : ℝ) ≤ (2 : ℝ)^((B : ℝ) - Real.sqrt (B : ℝ)).
- Theorem: Use Paper.mem_attainableValues_iff with 0<K to bind the finite implementation to the exact paper definition over all nonempty families and arbitrary finite ambient sizes. Explain the positive-integer/natural-number equivalence.
- Theorem: Keep denominator 100, the real square-root saving, the quantifier order ∃ threshold ∀ B ∀ K, and all admissible B and K. Add no antichain, balancedness, intersection-pattern, ambient-size, dyadic, or unproved counting hypothesis.
- Theorem: Do not expose manuscript proof-only parameters as extra inputs. Do not add the later probability or density conclusions.
- Handoff: Compare both the semantics of V(B,K) and the expanded numerical theorem against scripts/CheckPaperStatements.lean:57–70 and the manuscript; alias equality alone is insufficient.
- Handoff: Classify the result as an interface reusing an existing proof. Preserve docs/current-paper.md's explanation of the different counting representation; any later changed correspondence must be explicit.
- Handoff: Check degenerate membership: nonempty tuples of empty generators yield ideal size 1; size 0 is excluded for K>0; duplicates and redundant generators remain permitted. Membership equivalence is only invoked with positive K.
- Handoff: Keep the Lean/Mathlib pins and manuscript/checksum unchanged. Preserve all audit registry entries and source-coverage checks, and register/import any later new library modules without removing existing coverage.
- Handoff: Before later reporting successful repository integration, run the repository-required lake build --wfail, lake env lean -DwarningAsError=true scripts/CheckAxioms.lean, lake env lean -DwarningAsError=true scripts/CheckPaperStatements.lean, and shasum -a 256 --check paper/SHA256SUMS. This reader pass must not run shell commands or Lean probes and does not claim those checks were rerun.
- Handoff: Let Tex2Lean produce its own proof status and handoff evidence; do not manually mark a target proved. No commit, push, merge or publication is part of this pass.

### Hypotheses

| Hypothesis | Verdict | Why |
| --- | --- | --- |
| B,K are integers in the positive range, B≥B_cnt, with one absolute existential threshold chosen independently of K. | `required` | These are the input domain and quantifier order; natural-number representation is equivalent on this range. |
| 1≤K≤(log₂ B)^2/(100 log₂(log₂ B)). | `required` | The exact real budget, inclusive endpoints and denominator 100 belong to the statement. |
| Every witness for an attainable size is a nonempty tuple of s finite sets with 1≤s≤K and \|A_i\|≤B for every i. | `required` | This is part of the definition of the counted set, not an additional hypothesis about a selected input family. |
| Positivity and well-defined ordinary real interpretation of log₂ B and log₂(log₂ B), plus h>0 for the manuscript proof. | `discharge-internally` | Follow from choosing a sufficiently large absolute threshold; do not expose them as extra independent assumptions. |
| Exactly K generators on an active ground set [N] satisfying N≤KB. | `discharge-internally` | Padding by repetition and relabelling the union give these internally; no algorithmic preprocessing is required because there is no algorithm. |
| Generators are nonempty, distinct, inclusion-incomparable, minimal, balanced, or all of size B. | `unnecessary` | The paper permits arbitrary finite sets with upper cardinality bounds. Nonempty refers to the family, not every generator. |
| Restrictions on intermediate-order intersections or an independently bounded ambient universe. | `unnecessary` | Explicitly excluded by the concluding remark at lines 1531–1536. |
| B is dyadic, K≥h, J≥1, or attainable values lie below 2^B. | `unnecessary` | None is part of the theorem; all sufficiently large integer B, all admissible K, and all attained sizes are counted. |
| Existence of a suitable header and the auxiliary numerical inequalities used in counting. | `discharge-internally` | They belong to the proof, already discharged by the existing endpoint, and must not become assumptions of a new interface. |

### Caller Conditions

- **The theorem's uniform parameter range** — Choose one absolute threshold B₀ and require B₀ ≤ B together with 1 ≤ K and K ≤ (Real.logb 2 B)^2 / (100 * Real.logb 2 (Real.logb 2 B)). (Theorem 7.1, paper lines 987–997; existing endpoint AntichainOfGivenSize.Paper.countingBound : CountingBoundStatement.; applies to AntichainOfGivenSize.Paper.countingBound, Model/Theorem headline); Lean binder `After unpacking CountingBoundStatement: hB : B₀ ≤ B and hBudget : Paper.AdmissibleBudget B K.`.
- **Positive K for the attainable-value membership bridge** — Require 0 < K when invoking Paper.mem_attainableValues_iff. (Paper/Representation.lean:89–92; the contract explicitly says to use this equivalence with 0 < K.; applies to Paper.mem_attainableValues_iff, Paper.attainableValues membership semantics); Lean binder `Helper invocation: hK : 0 < K, derived from hBudget.1.`.
- **Nonempty family in attainable-value membership** — A witness family has 1 ≤ s ≤ K; each generator is finite and has cardinality at most B. The family may include empty, repeated, or redundant generators. (Setup paragraph before Theorem 7.1, paper lines 981–986; Paper.HasBoundedGeneratingFamily in Paper/Representation.lean:24–27.; applies to Paper.HasBoundedGeneratingFamily, Paper.attainableValues, Paper.mem_attainableValues_iff).
- **Algorithm and loop state** (handoff-risk) — The target is a deterministic cardinality theorem, with no helper algorithm, execution state, or loop. Do not add operational caller guards or reachable-state invariants for the proof's headers, packings, or records. Source: canonicalTarget and algorithm.present = false; the counting proof is supplied by Paper.countingBound..
- **Active ground set size N** (model-internal) — Do not require N > 0. If all generators are empty, the active ground set can be Fin 0 and the generated ideal still has cardinality 1. The proof's N ≤ KB bound and relabeling are internal reductions, not assumptions on V-membership. Source: Ambiguity ledger on [0]; paper lines 1011–1017 and 1531–1536; existing profile and representation lemmas..
- **Logarithm domain and threshold** (proof-obligation) — Do not add separate assumptions such as B > 2 or positive log denominators to the headline. The existential sufficiently large threshold supplies the range needed by the proof; the paper's initial B ≥ 2^20 condition is not the final threshold claim. Source: Paper lines 999–1004 and 1337–1361; CountingParameters.lean:119–136..
- **Natural-number representation and real arithmetic** (handoff-risk) — The existing endpoint uses ℕ parameters; match the paper's positive-integer range through the positive threshold and K ≥ 1. Preserve base-two Real.logb, Real.sqrt, real subtraction and real exponentiation exactly. Source: Paper line 215 for the base-two convention and lines 987–997 for the theorem; scripts/CheckPaperStatements.lean:57–70..
- **Proof encodings** (model-internal) — Exact-K padding, finite active support, header existence, maximum packings, and transcript bounds are proof-side constructions already discharged by the endpoint. Do not expose them as caller hypotheses or imply the existing proof transcribes the manuscript's streamlined fixed-header product. Source: Paper lines 1011–1025 and 1097–1294; docs/current-paper.md:166–175; existing CountingParameters.lean endpoint..

### What the paper leaves unstated

Lean will force each of these. Where one turns out to be false rather than
merely unstated, that is a finding about the paper, not a modelling problem.

- A genuine minor notation gap occurs at N=0: the proof relabels the active union as [N], but the interval convention explicitly discusses only ordered endpoints. All generators may be empty, so interpret [0] as empty (Fin 0), preserving Φ=1. Do not exclude this case.
- The paper says integers while the existing theorem uses ℕ. Explain that an absolute positive threshold and K≥1 identify the domains; there is no claim about negative or arbitrary real parameters.
- The precise numerical B_cnt is intentionally unspecified. B≥2^20 at the start of the proof is not the final threshold; the final λ₀ is increased to satisfy all estimates uniformly in K.
- The ambient ground universe and tuple ordering are not fixed. Finite active support, bijective relabelling, deduplication and padding are acceptable representations, justified by the existing semantic equivalence, not extra restrictions.
- There is no unresolved log-base ambiguity: line 215 explicitly fixes base 2. Likewise the final exponent is real; rounding, integer square roots, or truncated subtraction are not alternatives authorized by the paper.
- The proof's maximum-packing choices need not be unique and no selection algorithm is specified. This is sufficient for a deterministic covering/counting argument and creates no missing program or randomness contract.
- No apparent mathematical defect or missing premise was found in the read counting argument. Uniform asymptotic estimates and degenerate cases remain proof matters, but the exact theorem already has a reusable proved endpoint.

## Architecture

This target is planned as a standalone theorem: the proof route, reusable
source theorems and statement checks are the architecture. No interface or
concrete instance is being invented for it.

### Route — `library-corollary`

The supplied project evidence identifies an exact existing endpoint, AntichainOfGivenSize.Paper.countingBound, and the required membership equivalence, Paper.mem_attainableValues_iff. Both open surface declarations follow by definitional unfolding. This is a standalone deterministic theorem reusing existing results; no interface structure, algorithm, or borrowed mathematical assumption is needed.

### Source theorems

| Declaration | Module | Why it applies |
| --- | --- | --- |
| `AntichainOfGivenSize.Paper.mem_attainableValues_iff` | `AntichainOfGivenSize.Paper.Representation` | Unfolding HasBoundedGeneratingFamily gives exactly the existential family predicate in the open membership cross-check. The name and contract come from the supplied source inspection; binder elaboration has not been independently checked in this correction pass. |
| `AntichainOfGivenSize.Paper.countingBound` | `AntichainOfGivenSize.Paper.CountingParameters` | CountingBoundStatement unfolds, through AdmissibleBudget, to the entire fixed capstone conclusion with the same quantifiers, constant 100, real logarithms, square root, and real exponent. Its supplied signature has no counting hypothesis or Prior argument. |

### Proof steps

- **Establish separate, acyclic proof-side owners for the two open surface declarations.** — `Analysis/AttainableValuesMembershipProof.lean imports AntichainOfGivenSize.Model.CountingVocabulary and AntichainOfGivenSize.Paper.Representation. Analysis/AttainableCountProof.lean imports AntichainOfGivenSize.Model.CountingVocabulary, AntichainOfGivenSize.Model.Prior, and AntichainOfGivenSize.Paper.CountingParameters. Check the transitive imports before connecting the surface proofs.`. Each lemmaOrder entry must own a distinct file. The membership owner must not import Model.Prelude or Model.Theorem, since Prelude delegates to it. The counting owner must not import Model.Theorem. A Prior-to-Prelude dependency is permissible with this separation, provided the membership owner does not import Prior.
- **Discharge the membership cross-check.** — `In namespace AntichainOfGivenSize, try: exact Paper.mem_attainableValues_iff hK Explicit-unfolding variant: simpa only [Paper.HasBoundedGeneratingFamily] using (Paper.mem_attainableValues_iff (B := B) (K := K) (n := n) hK)`. The source theorem already proves both directions, including finite-universe representation, deduplication, and padding. Only the definition of HasBoundedGeneratingFamily separates its conclusion from the fixed expanded predicate.
- **Discharge the expanded counting conclusion while retaining the fixed Prior binder.** — `In namespace AntichainOfGivenSize, try: exact (fun (_ : Prior) => Paper.countingBound) hprior Explicit-unfolding variant: simpa only [Paper.CountingBoundStatement, Paper.AdmissibleBudget] using ((fun (_ : Prior) => Paper.countingBound) hprior)`. The existing theorem supplies the conclusion independently of hprior. The constant-function application references the fixed binder without inspecting Prior or borrowing any fact from it. No threshold reconstruction, arithmetic weakening, event splitting, or monotonicity argument is required.
- **Connect each fixed surface declaration to its corresponding proof-side owner.** — `Membership body: exact AntichainOfGivenSize.Analysis.AttainableCountProof.attainableValuesMembership hK Capstone body: exact AntichainOfGivenSize.Analysis.AttainableCountProof.attainableCount hprior`. Keep both existing signatures unchanged. The two owners are independent; the membership theorem validates the meaning of the counted set but is not a logical premise of the counting proof.
- **Verify the completed wrappers and retain the semantic audit.** — `Run the existing closure and surplus commands; inspect #print axioms for both owners and both surface theorems. During implementation run lake build --wfail, lake env lean -DwarningAsError=true scripts/CheckAxioms.lean, lake env lean -DwarningAsError=true scripts/CheckPaperStatements.lean, and shasum -a 256 --check paper/SHA256SUMS.`. Definitional compatibility, transitive axiom cleanliness, source coverage, and manuscript correspondence require actual execution. No such verification was performed for this correction pass.

### Statement checks

- **The fixed capstone includes hprior : Prior, whereas the supplied paper statement and existing countingBound endpoint are unconditional.** — Inspect Model.Prior and record its exact meaning. Preserve the fixed binder, but prove the conclusion without extracting any fact from it. An axiom check does not detect extra hypotheses in a theorem's type. If Prior is substantive, report the conditional surface explicitly; do not classify this route as borrowed-prior.
- **An apparently matching alias could conceal different quantifiers or arithmetic.** — Unfold CountingBoundStatement and AdmissibleBudget and compare against the fixed signature and scripts/CheckPaperStatements.lean:57–70. Require ∃ B₀, ∀ B K, the inclusive budget with denominator 100, and ((attainableValues B K).card : ℝ) ≤ (2 : ℝ) ^ ((B : ℝ) - Real.sqrt (B : ℝ)).
- **Replacing exact attainable values by residues, values below 2^B, profiles, or generating families would change the counted quantity.** — Keep Paper.attainableValues unchanged and complete the expanded membership cross-check. No bound on the numerical attained value or ambient size may be added.
- **The membership equivalence requires positive K, and nonempty family does not mean nonempty generators.** — Retain hK : 0 < K in the cross-check. In the capstone range it follows from 1 ≤ K. Preserve Fin 0, the attainable value 1 from empty generators, and allowance for repeated or redundant generators.
- **A conditional downstream consequence could be mistaken for a proof of the counting theorem.** — Do not use Paper.almostAllLowerBound_of_countingBound, Paper.almostAllOrder_of_countingBound, or Paper.extremal_lower_of_countingBound as counting sources: they require CountingBoundStatement and establish different conclusions.
- **Natural subtraction, integer square roots, a different logarithm base, or a threshold depending on K would weaken or alter the target.** — Preserve the expanded real expressions literally and the quantifier order ∃ B₀ : ℕ, ∀ B K : ℕ. Do not identify the final threshold with the manuscript's preliminary condition B ≥ 2^20.
- **Successful wrapper elaboration would not establish that every intermediate manuscript estimate follows the existing Lean proof.** — Retain the correspondence note in docs/current-paper.md:166–175. Attribute the endpoint to the existing larger clustered encoding, without claiming a line-by-line formalization of the streamlined manuscript argument.


### Capstone — `AntichainOfGivenSize.attainable_count`

```lean
In namespace AntichainOfGivenSize:
theorem attainable_count (hprior : Prior) :
    ∃ B₀ : ℕ, ∀ B K : ℕ, B₀ ≤ B →
      (1 ≤ K ∧ (K : ℝ) ≤ (Real.logb 2 (B : ℝ)) ^ 2 /
        (100 * Real.logb 2 (Real.logb 2 (B : ℝ)))) →
      ((Paper.attainableValues B K).card : ℝ) ≤
        (2 : ℝ) ^ ((B : ℝ) - Real.sqrt (B : ℝ))
```

## The crux

Prove this first, in isolation. Once it is green the surrounding theorem
usually collapses into bookkeeping — and if it does not, the crux was
mis-identified and the architecture above needs another look.

### `Definitional compatibility of the existing endpoints`

```lean
Paper.CountingBoundStatement is definitionally the fixed counting conclusion, and Paper.HasBoundedGeneratingFamily B K n is definitionally the expanded family predicate in Model.attainableValues_membership.
```

**Why this is the heart:** These two checks determine whether both obligations are immediate wrappers. The difficult combinatorial counting argument is already discharged by the supplied existing endpoint.

**How to attack it:** Inspect the defining constants and try the two exact applications first. If conversion fails, inspect the actual mismatch before introducing any helper lemma. Do not rebuild the counting argument or change the fixed statements to accommodate a mismatch.

## Invariants to bake into the model

Cheaper as structure fields than as case splits later: Lean's `x / 0 = 0`
convention means a cancellation that ignores the zero case gets stuck on a
false-looking identity.

- `One existing mathematical representation`: Keep generatedIdeal, Paper.attainableValues, Paper.HasBoundedGeneratingFamily, and their existing defining vocabulary unchanged. — The counted object must remain the same object used by the proved source theorem and the semantic cross-check.
- `Proof owners stay outside the statement closure`: Both new owners are declared under AntichainOfGivenSize.Analysis and occur only in surface proof terms. No owner, encoding, or proof record is added to a surface theorem type. — The closure audit begins from the capstone's type; proof-side reuse should not enlarge its mathematical statement.
- `Validation theorem survives the surplus audit`: Retain Model.attainableValues_membership even though attainable_count need not reference it. — It is an intentional semantic validation theorem, not a dead proof helper.
- `Uniform deterministic conclusion`: One existential threshold works for every sufficiently large natural B and every K satisfying the exact budget; the conclusion bounds distinct attainable values. — There is no probability object, algorithm execution, resource cost, or additional family hypothesis to introduce.
- `No mathematical use of Prior`: The counting owner obtains its conclusion directly from Paper.countingBound for any supplied hprior. — Preserving the scaffold binder must not turn an existing unconditional proof into an assumed counting result.
- `Exact owner names and distinct owner files`: Each lemmaOrder signature declares its name literally as a fully qualified identifier, and each entry has a different Analysis/ file. — This satisfies the corrected ownership contract without changing either surface declaration or creating unnecessary mathematical subtasks.

## Modelling decisions

### Use Analysis/AttainableValuesMembershipProof.lean for the membership owner and Analysis/AttainableCountProof.lean for the counting owner. Implement them as one small serial task.

- **Rejected:** Place both owners in one file or manufacture separate interface and analysis layers.
- **Because:** The corrected ownership contract requires one file per lemmaOrder entry. Two tiny files suffice; the wrappers do not warrant parallel implementation.
- **Scope caveat:** Paths in lemmaOrder are relative to the AntichainOfGivenSize source directory. Keep the existing owner names even though the membership owner's file has a different basename.

### Preserve the fixed natural-number statement and its Prior binder.

- **Rejected:** Replace it with a literal integer theorem or remove the binder during this pass.
- **Because:** The surface declarations are fixed. Natural parameters match the paper on its sufficiently large positive range, and the source theorem supplies the conclusion without using Prior.
- **Scope caveat:** The meaning of Prior remains an inspection obligation; it must not be assumed to be True.

### Reuse the exact existing endpoint and representation theorem.

- **Rejected:** Reprove packing, exceptional-set, central-transcript, tail-interval, and asymptotic estimates.
- **Because:** The supplied reuse inventory already contains the required result with the exact constants. No additional Arlib or Mathlib theorem is needed for these wrappers.
- **Scope caveat:** This correction relies on the supplied library and source inspection evidence. It does not claim a fresh checkout inspection or Lean compilation.

### Use ordinary finite-set cardinality and real arithmetic exactly as written.

- **Rejected:** Introduce a probabilistic interpretation, executable enumerator, or rounded bound.
- **Because:** The target is a deterministic cardinality theorem with no algorithm.
- **Scope caveat:** The later dyadic probability corollary, density consequences, and runtime claims are outside this target.

## Paper guide

- **What the counted values mean:** paper/Generating_Antichains_Simplified.tex:197–208, paper/Generating_Antichains_Simplified.tex:215–235, paper/Generating_Antichains_Simplified.tex:981–986, AntichainOfGivenSize/Paper/Representation.lean:24–27,87–92, scripts/CheckPaperStatements.lean:57–70 — Checking the expanded membership theorem, family nonemptiness, the base-two convention, or exact values versus residues. Locations are taken from the supplied reading report.
- **Exact endpoint and uniform threshold:** paper/Generating_Antichains_Simplified.tex:987–997, paper/Generating_Antichains_Simplified.tex:1300–1361, AntichainOfGivenSize/Paper/CountingParameters.lean:119–136 — Comparing CountingBoundStatement with the fixed capstone, especially the quantifier order, constant 100, and unrounded square-root saving.
- **Representation reductions and degenerate families:** paper/Generating_Antichains_Simplified.tex:1011–1017, paper/Generating_Antichains_Simplified.tex:1531–1536, AntichainOfGivenSize/Paper/Representation.lean, AntichainOfGivenSize/LowerBound/ProfilePadding.lean — Investigating a semantic mismatch involving exact-K padding, arbitrary ambient universes, empty active support, or prohibited extra restrictions. Reuse the established representation results.
- **What the reused proof actually formalizes:** paper/Generating_Antichains_Simplified.tex:999–1361, docs/current-paper.md:166–175, AntichainOfGivenSize/Paper/GeneralCounting.lean, AntichainOfGivenSize/Paper/CountingEstimates.lean, AntichainOfGivenSize/Paper/CountingParameters.lean — Documenting proof provenance or investigating an unexpected mismatch in the existing endpoint. These are supporting evidence, not new implementation obligations.

## Known blockers

- **Independently verify source signatures, module paths, and freshness of both owner names.:** The earlier attempt reported that its accessible workspace lacked the advertised Lean checkout. This correction has not performed a fresh filesystem or elaboration check. The exact source names remain supported by the supplied project inspection. Next: In the actual project, inspect the two source declarations and the definitions of CountingBoundStatement, AdmissibleBudget, and HasBoundedGeneratingFamily. Confirm module paths and search for both fully qualified owner names before creating their distinct files. No new mathematical gap is identified.
- **Inspect Prior and confirm the two-file import graph is acyclic.:** Model.Prior is referenced but its contents were not supplied. Its semantic strength and transitive imports remain unknown. Next: Read Model.Prior and follow the proposed imports. The membership owner must remain independent of Model.Prelude, Model.Prior, and Model.Theorem; the counting owner may depend on Prelude through Prior but must remain independent of Model.Theorem. Preserve the existing Prior type and extract no facts from it.
- **Produce fresh build, closure, and axiom evidence after implementation.:** This is a blueprint correction. Historical checks and source-level wrapper reasoning are not current build results. Next: Run the repository checks listed in proofSteps, retain the membership validation theorem, and confirm both owners and both surface theorems have no sorryAx or custom axioms. Confirm that the closure checker rejects a deliberate out-of-surface control if no such test has yet been observed.

## Initial proof owners

| # | New declaration | Discharges | File | Difficulty | Depends on |
| --- | --- | --- | --- | --- | --- |
| 1 | `AntichainOfGivenSize.Analysis.AttainableCountProof.attainableValuesMembership` | `AntichainOfGivenSize.Model.attainableValues_membership` | `Analysis/AttainableValuesMembershipProof.lean` | routine | `AntichainOfGivenSize.Paper.mem_attainableValues_iff` |
| 2 | `AntichainOfGivenSize.Analysis.AttainableCountProof.attainableCount` | `AntichainOfGivenSize.attainable_count` | `Analysis/AttainableCountProof.lean` | routine | `AntichainOfGivenSize.Paper.countingBound` |

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

- Target: `paper/Generating_Antichains_Simplified.tex:987`
- Files read: `paper/Generating_Antichains_Simplified.tex`
