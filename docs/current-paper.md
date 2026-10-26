# Correspondence with the current manuscript

This inventory concerns the saved manuscript
[`paper/Generating_Antichains_Simplified.tex`](../paper/Generating_Antichains_Simplified.tex),
*Generating Antichains for Ideals of Prescribed Size: Universal Upper Bounds
and Almost-All Lower Bounds*.
Its SHA-256 digest is

```text
137f3d51bc6dee4e62a4897bf4da0584cd7ff247aa6003811ff239794c295b1f
```

The mathematical targets below preserve the numbered statements of this
snapshot. Some proofs use a different encoding, rounding convention, or
previously checked construction. Those differences are described below;
this is a correspondence between mathematical results, not a claim that
every displayed intermediate equation is reproduced verbatim in Lean.

The namespace prefix `Paper.` in this document abbreviates
`AntichainOfGivenSize.Paper.`. Unprefixed names from the earlier development
have namespace prefix `AntichainOfGivenSize.`.

**Integration status:** all mathematical integrations listed below are
complete. The block construction, its complete residue induction, and the
uniform parameter bounds are connected in the unconditional certificate
`Paper.blockMatching`. The counting and matching hypotheses in the
intermediate analytic files are discharged in `Paper.Results`.

**Repository-wide verification, 26 October 2026:** the independent upper,
lower, and statement-coverage reviews found no mathematical defect in the
proved endpoints. The follow-up verification added the real-cutoff density
bridge, explicit integer-residue and position-intersection interfaces,
and persistent checks against weaker statements or omitted audit inputs.

These commands completed successfully:

```sh
lake build --wfail
lake env lean -DwarningAsError=true scripts/CheckAxioms.lean
lake env lean -DwarningAsError=true scripts/CheckPaperStatements.lean
shasum -a 256 --check paper/SHA256SUMS
```

The build completed 8,743 jobs with warnings treated as errors. The expanded
axiom audit checked all 2,680 project declarations across 88 library modules
and their matching source files, including 2,133 theorem declarations.
Eighty theorem declarations require no axioms; the union of all observed
axioms was exactly `propext`, `Classical.choice`, and `Quot.sound`.
All fourteen public manuscript certificates printed by the audit use only
those standard axioms. The separate statement check passed all twelve
expanded contracts. CI runs these checks and the snapshot checksum
(`sha256sum --check paper/SHA256SUMS` on Linux).

## Numbered results

| Manuscript result | Lean declaration and implementation |
| --- | --- |
| Theorem 1.1: universal upper bound, almost-all order, and extremal order | `Paper.mainTheorem` in [`Results.lean`](../AntichainOfGivenSize/Paper/Results.lean), combining `Paper.universalUpper_from_five`, `Paper.almostAllOrder`, and `Paper.extremalOrder`. |
| Definition 2.1: generated ideal and downward closure | `generatedIdeal` in [`MainStatement.lean`](../AntichainOfGivenSize/MainStatement.lean): the union of the generators' powersets. `Paper.generatedIdeal_isLowerSet` in [`BasicResults.lean`](../AntichainOfGivenSize/Paper/BasicResults.lean) proves downward closure under inclusion. |
| Definition 2.2: minimum generator number | `alpha` and `HasGeneratorCount` in [`MainStatement.lean`](../AntichainOfGivenSize/MainStatement.lean); `alpha_hasGeneratorCount` in [`BasicLemmas.lean`](../AntichainOfGivenSize/BasicLemmas.lean) proves attainment. `mainAlphaHasAntichainWitness` certifies an antichain attaining the same minimum. |
| Lemma 3.1: splitting | `splittingLemma` in [`BasicLemmas.lean`](../AntichainOfGivenSize/BasicLemmas.lean). The first ideal size has the required positivity hypothesis. |
| Lemma 3.2: lifting | `liftingLemma` in [`BasicLemmas.lean`](../AntichainOfGivenSize/BasicLemmas.lean). |
| Theorem 4.1: bit matching | `Paper.bitMatchingInt` in [`Results.lean`](../AntichainOfGivenSize/Paper/Results.lean), using `Paper.BitMatching.exists_matching_int`, for every integer target including negative targets. `Paper.bitMatching` is the natural-target interface used in the reduction. |
| Claim 4.2: separation of fresh elements | `Paper.BitMatching.fresh_separation` in [`BitMatching.lean`](../AntichainOfGivenSize/Paper/BitMatching.lean). |
| Claim 4.3: primary intersection size | `Paper.BitMatching.primary_intersection_card` in [`BitMatching.lean`](../AntichainOfGivenSize/Paper/BitMatching.lean), with the stronger set identity `primary_intersection`. |
| Claim 4.4: proper contributing intersections are larger | `Paper.BitMatching.proper_intersection_card` in [`BitMatching.lean`](../AntichainOfGivenSize/Paper/BitMatching.lean). |
| Theorem 5.1: exact bound `4q²+3` | `Paper.firstUpper` in [`Results.lean`](../AntichainOfGivenSize/Paper/Results.lean), from `Paper.first_upper` and `Paper.first_upper_cumulative` in [`FirstUpper.lean`](../AntichainOfGivenSize/Paper/FirstUpper.lean). `Paper.quadraticUpper` supplies its unconditional asymptotic conclusion directly from bit matching. |
| Theorem 6.1: block matching, with `a=5`, `b=3` | `Paper.blockMatching` in [`Results.lean`](../AntichainOfGivenSize/Paper/Results.lean), combining `Paper.UpperConstruction.blockMatchingConstruction` in [`UpperConstructionBounds.lean`](../AntichainOfGivenSize/Paper/UpperConstructionBounds.lean) with `blockMatching_of_construction` in [`UpperParameters.lean`](../AntichainOfGivenSize/Paper/UpperParameters.lean). Its full statement includes arbitrary integer residues, positivity, the generator bound, and the logarithmic size bound. |
| Claim 6.2: the pattern gadget has size `2^ell+d` | `Paper.PatternGadget.ideal_card_bits` in [`PatternGadget.lean`](../AntichainOfGivenSize/Paper/PatternGadget.lean), using the exact decomposition `ideal_decomposition`. |
| Claim 6.3: position addressing | `Paper.UpperConstruction.position_intersection` in [`UpperConstructionGeometry.lean`](../AntichainOfGivenSize/Paper/UpperConstructionGeometry.lean) states the position-only set identity directly; `full_position_intersection` also covers mixed queries. |
| Claim 6.4: the complete stage increment congruence | `Paper.UpperConstruction.block_increment` and `idealCard_update` in [`UpperConstructionSteps.lean`](../AntichainOfGivenSize/Paper/UpperConstructionSteps.lean), from the complete sum `selected_card_zmod` in [`UpperConstructionCore.lean`](../AntichainOfGivenSize/Paper/UpperConstructionCore.lean) and the concrete geometry `stage_card_zmod`. Every nonempty contributing query is included. |
| Claim 6.5: uniform generator and ideal-size bounds | `Paper.UpperConstruction.card_generator_le`, `alpha_idealCard_le`, and `idealCard_bound` in [`UpperConstructionBounds.lean`](../AntichainOfGivenSize/Paper/UpperConstructionBounds.lean), followed by `Paper.block_small_cost` and `Paper.block_uniform_size` in [`UpperParameters.lean`](../AntichainOfGivenSize/Paper/UpperParameters.lean). |
| Lemma 6.6: direct reduction | `Paper.directReduction` in [`DirectReduction.lean`](../AntichainOfGivenSize/Paper/DirectReduction.lean), with the complete positivity, strict-decrease, and logarithmic-quotient requirements. Its explicit constants are `a=8`, `C₁=4096`. |
| Theorem 6.7: upper bound for every integer `n≥5` | `Paper.universalUpper_from_five` in [`Extremal.lean`](../AntichainOfGivenSize/Paper/Extremal.lean). This is stronger than merely restating an unspecified eventual bound. |
| Theorem 7.1: counting attainable values | `Paper.countingBound` in [`CountingParameters.lean`](../AntichainOfGivenSize/Paper/CountingParameters.lean), proving `Paper.CountingBoundStatement` from [`Statements.lean`](../AntichainOfGivenSize/Paper/Statements.lean). It retains the budget denominator `100`, all sufficiently large integers `B`, every admissible `K`, and the real exponent `B−sqrt(B)`. |
| Corollary 10.1: probability in a dyadic block | `Paper.typicalLowerBound` in [`Results.lean`](../AntichainOfGivenSize/Paper/Results.lean), implemented by `typicalLowerBound_of_countingBound` in [`Typical.lean`](../AntichainOfGivenSize/Paper/Typical.lean). The finite probability of `alpha≤K` is at most `2^(1−sqrt(B))`; equivalently the complementary event has the paper's lower bound. |
| Corollary 10.2: simultaneous almost-all bounds | `Paper.almostAllOrder`, `Paper.almostAllGoodProportion`, and `Paper.realAlmostAllGoodProportion` in [`Results.lean`](../AntichainOfGivenSize/Paper/Results.lean). The first is the density-zero exceptional-set statement, the second is the integer-cutoff proportion, and the third is the displayed limit over arbitrary real cutoffs, implemented in [`RealDensity.lean`](../AntichainOfGivenSize/Paper/RealDensity.lean). |

Sections 8 and 9 contain the counting proof's intermediate constructions
and estimates, but no further numbered theorem, lemma, claim, or corollary.
Remark 10.3 states the absence of additional restrictions on the counting
theorem; this is reflected in the representation equivalence below.

## Definitions, endpoints, and quantifiers

### Positive naturals and exact finite representations

The paper uses positive natural numbers. Lean's `Nat` also contains zero,
so positivity assumptions are explicit where needed. The extension
`alpha 0 = 0` does not change any positive-input conclusion. In particular,
the splitting lemma does not silently assert its false zero-first-input
version.

[`Representation.lean`](../AntichainOfGivenSize/Paper/Representation.lean)
defines `Paper.HasBoundedGeneratingFamily B K n` using a nonempty finite
family of at most `K` sets, each of size at most `B`, and an existentially
quantified ambient size without a cap. For `K>0`,
`Paper.mem_attainableValues_iff` proves that this is exactly membership in
the finite implementation `Paper.attainableValues B K`. The implementation
uses exact-`K` indexed profiles; smaller nonempty families are padded by
repeated generators. Thus the counting theorem is not restricted to
families with a special ambient universe, balanced generators, or special
intersection patterns.

`Paper.mem_attainableValues_of_alpha_le` in
[`Typical.lean`](../AntichainOfGivenSize/Paper/Typical.lean) proves the
bridge needed in the probability argument: whenever `0<n<2^B` and
`alpha n≤K`, the exact integer `n` belongs to `attainableValues B K`.
This counts integer values, not just residues with possible collisions.

The finite examples are proved in
[`BasicResults.lean`](../AntichainOfGivenSize/Paper/BasicResults.lean):
`alpha_one`, `alpha_two_pow`, `alpha_thirteen`,
`thirteenFamily_ideal_card`, `alpha_le_three_of_le_sixteen`, and
`alpha_le_max_one_pred`. The proof that two generators cannot give size
13 works over every ambient type. Small closed finite checks use Lean's
kernel evaluator (`decide`), not `native_decide`.

### Actual density one

The new lower theorem is not the repository's older infinitely-often
lower bound. [`Density.lean`](../AntichainOfGivenSize/Paper/Density.lean)
proves

```text
card {n ∈ [5,X] : alpha(n) < (1/800) g(n)} / X → 0
```

as the integer cutoff `X` tends to infinity. The upper inequality is valid
for every integer at least five. Consequently
[`AlmostAll.lean`](../AntichainOfGivenSize/Paper/AlmostAll.lean) proves that
the proportion satisfying both bounds tends to one, with the omitted
finite initial segment accounted for explicitly.

[`RealDensity.lean`](../AntichainOfGivenSize/Paper/RealDensity.lean) extends
this to real cutoffs. `mem_realGoodInputs_iff` identifies the counted set
exactly with the good integers satisfying `5≤n≤X`; the factor
`floor(X)/X→1` gives the same proportion limit over all real `X`.

### Real extremal cutoffs

`Paper.maximumBelow X` is the maximum of `alpha n` over the finite set
`1≤n<ceil(X)`, which for an integer `n` is exactly `1≤n<X`, including when
`X` itself is an integer. `Paper.ExtremalOrderStatement` is a real-variable
`IsTheta` statement as `X→+∞`. It is not a statement only along integer
cutoffs or a sparse sequence.

## Differences in proof implementation

These differences preserve the target conclusions and their quantifiers.

* **The first upper bound.** The induction in
  [`FirstUpper.lean`](../AntichainOfGivenSize/Paper/FirstUpper.lean) proves
  the cumulative statement for all smaller inputs at once. It keeps the
  exact bound `4q²+3` and the paper's range endpoints, and derives the
  quadratic asymptotic upper bound independently of the sharp upper bound.
* **Block parameters.** The integral parameter implementation in
  [`UpperParameters.lean`](../AntichainOfGivenSize/Paper/UpperParameters.lean)
  uses conservative natural-number divisions in place of the paper's
  real-logarithm floor and ceiling choices. Its target still has the
  stated final constants `5` and `3` for every sufficiently large `B`.
  The numerical conversion explicitly assumes
  `BlockMatchingConstructionStatement`; `Paper.blockMatching` supplies
  its proof `UpperConstruction.blockMatchingConstruction`, including the
  complete finite-stage residue induction and negative integer targets.
* **The counting proof.**
  [`GeneralCounting.lean`](../AntichainOfGivenSize/Paper/GeneralCounting.lean)
  generalizes the previously checked clustered encoding to arbitrary
  natural `B,K`. This encoding retains more information than the paper's
  streamlined fixed-header product. The resulting larger record count is
  still small enough: [`CountingEstimates.lean`](../AntichainOfGivenSize/Paper/CountingEstimates.lean)
  and [`CountingParameters.lean`](../AntichainOfGivenSize/Paper/CountingParameters.lean)
  prove the exact final `2^(B−sqrt(B))` bound under the unchanged budget
  `K≤(log₂B)²/(100 log₂log₂B)`. No restriction to the older dyadic parameter
  subsequence remains.
* **Counting audit vocabulary.**
  [`Model/CountingVocabulary.lean`](../AntichainOfGivenSize/Model/CountingVocabulary.lean)
  owns the existing generated-ideal and bounded-profile vocabulary, including
  `Paper.attainableValues`. These declarations retain their qualified names and
  mathematical definitions; their original modules import them. This relocation
  makes the quantity's defining dependency chain visible under `Model/` without
  widening the closure check's permitted modules. The structural finite-type
  instances use term-form library constructors. The representation equivalence
  and counting proofs remain in their original proof modules. The Model
  membership equivalence and headline reuse the checked theorems
  `Paper.mem_attainableValues_iff` and `Paper.countingBound`. The headline's
  `Prior` parameter is an empty structure and adds no assumption. These are
  interfaces to the existing proofs; they do not replace the counting argument.
* **Direct reduction.**
  [`DirectReduction.lean`](../AntichainOfGivenSize/Paper/DirectReduction.lean)
  uses the previously checked unconditional range-matching construction,
  choosing its real range parameter as `q=τ−log₂τ+12`, where
  `τ=log₂log₂n`. This gives constants `a=8`, `C₁=4096`. Lemma 6.6 asserts
  existence of positive absolute constants, so these choices preserve
  its statement. The reduced integer remains positive and strictly less
  than the original input.
* **The sharp universal upper bound.** The formal proof reuses the
  existing unconditional `mainUpperBound` and proves the missing finite
  prefix absorption explicitly, using positivity of `g(n)` for `n≥5`.
  It does not claim to reproduce the manuscript's derivative/potential
  calculation line by line.
* **Density.** Eventual monotonicity of `g` allows a single all-values
  counting estimate at `B=floor(log₂X)+1`, instead of summing all earlier
  dyadic blocks. A fixed finite initial segment is retained in the
  estimate, and its contribution divided by `X` tends to zero. The lower
  constant is the paper's `1/800`.
* **The extremal conclusion.** Density zero of the exceptions ensures
  a good integer in every sufficiently large interval `[Y,2Y)`. Taking
  `Y=floor(X/2)` and using `g(X)≤4g(X/4)` gives the lower bound for real
  cutoffs. Eventual monotonicity and a finite-prefix estimate give the
  upper bound.

## How this inventory is checked

The canonical public certificates are assembled in
[`Results.lean`](../AntichainOfGivenSize/Paper/Results.lean). Intermediate
theorems whose names end in `_of_countingBound` or `_of_matching` retain
their hypotheses openly; the public certificates supply the proved
counting and matching theorems.

The dependency checker compares the actual library sources, the explicit
module registry, and the imported modules. It checks every project
declaration, including proof-bearing definitions and instances. Negative
checks verified that it rejects both an untracked source file and an
unused definition containing an omitted proof.

At the Tex2Lean opening proof frontier, ordinary elaboration of
`scripts/CheckAxioms.lean` reports each transitive `sorryAx` dependency as an
`OPEN` warning and does not report `PASS`. This permits structural inspection
of the existing proof placeholders without certifying them. The prescribed
`-DwarningAsError=true` integration check still rejects every such dependency;
custom axioms, other unexpected axioms, and source/import coverage violations
remain errors in both modes. The generated `Meta/Audit.lean` imports library
modules, while the standalone audit scripts consume it: importing those
scripts back into `Meta/Audit.lean` creates an import cycle.

[`scripts/CheckPaperStatements.lean`](../scripts/CheckPaperStatements.lean)
separately spells out twelve mathematical contracts from the manuscript.
It checks the integer-residue domain, exact constants and endpoints,
the intended meaning of `V(B,K)`, density one, and real cutoffs against
the unconditional certificates. Thus changing a library statement alias
together with its proof cannot silently weaken those checked contracts.
A negative check confirmed rejection when the counting-budget constant
in the independently stated contract was changed from `100` to `99`.
The snapshot digest is also checked in CI against
[`paper/SHA256SUMS`](../paper/SHA256SUMS). These checks complement the
statement-to-paper comparison; they do not replace it. The background
literature discussion, bibliography, and authors' account of AI assistance
are not mathematical propositions certified by Lean.
