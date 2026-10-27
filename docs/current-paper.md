# Correspondence with the current manuscript

This inventory concerns the saved manuscript
[`paper/Generating_Antichains_Simplified.tex`](../paper/Generating_Antichains_Simplified.tex),
*Generating Antichains for Ideals of Prescribed Size: Universal Upper Bounds
and Almost-All Lower Bounds*.
Its SHA-256 digest is

```text
137f3d51bc6dee4e62a4897bf4da0584cd7ff247aa6003811ff239794c295b1f
```

The polished editor copy has SHA-256
`c0efe8be586ab40746ca51fa97c4f56cf36aec35f6564500dcbbbcace90b3424`.
The [source comparison recorded on 26 October 2026 at 23:27:50 UTC](verification/polished-manuscript-equivalence-review.json)
found all 18 numbered statement bodies identical after ignoring whitespace and
all 34 labeled mathematical displays equal modulo the recorded notation changes.
Its full-diff review found no substantive mathematical change. This preserves an
existing source comparison, not a fresh proof audit; native records remain pinned
to the frozen manuscript above, and do not certify processing of the editor copy.

The mathematical targets below preserve the numbered statements of this
snapshot. Some proofs use a different encoding, rounding convention, or
previously checked construction. Those differences are described below;
this is a correspondence between mathematical results, not a claim that
every displayed intermediate equation is reproduced verbatim in Lean.

The namespace prefix `Paper.` in this document abbreviates
`AntichainOfGivenSize.Paper.`. Unprefixed names from the earlier development
have namespace prefix `AntichainOfGivenSize.`.

**Mathematical coverage.** All 18 numbered proof targets have checked Lean
endpoints, listed below. The current development includes the manuscript's
literal block parameters and finite-stage construction, its shorter counting
argument with the intermediate estimates, density and real-cutoff equivalences,
and the actual uniform probability distribution for Corollary 10.1. This does
not mean every proof calculation follows the manuscript verbatim; the
implementation differences are recorded below.

The strict verification commands are listed below. Their execution times,
exit codes, logs, and exact input hashes are recorded in
[`.blueprint/verification/checks.json`](../.blueprint/verification/checks.json).
That report, rather than a fixed timestamp in this document, identifies the
checked source snapshot.

```sh
lake build --wfail
lake env lean -DwarningAsError=true scripts/CheckAxioms.lean
lake env lean -DwarningAsError=true scripts/CheckPaperStatements.lean
lake env lean -DwarningAsError=true AntichainOfGivenSize/Model/Theorem.lean
shasum -a 256 --check paper/SHA256SUMS
```

The axiom audit covers 3,086 project declarations across 124 library modules,
including 2,433 theorem declarations and 82 that require no axioms. Its observed
axiom union is `propext`, `Classical.choice`, and `Quot.sound`. The statement
check independently expands 19 contracts.
Closure checks cover 27 declarations in Model and the conditional helper in
Analysis; the latter remains an internal step of the unconditional main theorem.
The capstone registry and source-coverage checks identify the audited library.
Compatibility JavaScript has separate tests and is outside the Lean audit.

The earlier 26 October snapshot passed a warning-free 8,743-job build and an
audit of 2,680 declarations in 88 modules, including 2,133 theorem declarations
and 80 with no axioms, plus 12 expanded statement contracts. Those historical
totals are not the current verification counts. CI runs the strict build,
axiom and statement checks, and the manuscript checksum (`sha256sum --check
paper/SHA256SUMS` on Linux).

## Tex2Lean records and review

Native Tex2Lean records track restatement, planning, proof reuse, correspondence
review, certification, and handoff separately from Lean compilation. The tool's
[documented workflow](https://github.com/meelgroup/tex2lean-releases/blob/main/README.md)
operates on selected results. This run selects the principal main and counting
theorems, plus the splitting-lemma pilot, in the existing Lean project. It does
not require a separate native plan for every result already proved in the
library. All three selected workflows have native certificates and matching
handoffs on the same Lean source tree. Their exact records and archive hashes
are in [the native evidence package](verification/native/README.md).

| Paper target | Native evidence | Preservation and qualifications |
| --- | --- | --- |
| Theorem 1.1 (`thm:main`) | Generation 91; 06:57:31 UTC handoff reports formalized, assumptions pass, 7 proved, and both completion flags true | Exact export preserves two verification limitations and their explicit review |
| Theorem 7.1 (`thm:attainable-count`) | Generation 141; 07:19:21 UTC handoff reports formalized, assumptions pass, 11 proved, and no unknowns | Exact export preserves two metadata exclusions and both false aggregate-completion flags |
| Lemma 3.1 (`lem:splitting`) | Generation 9; 07:31:33 UTC handoff reports formalized, assumptions pass, 1 proved, no unknowns, and both completion flags true | Exact graph, certificate, and handoff export preserved |
| Other 15 numbered proof targets | Existing Lean endpoints are listed below and covered by the complete source audit | No separate native plans; outside the selected native scope |

The counting ledger also retains two excluded notes: one describes the older
encoding implementation, and one separates deterministic counting from the
probability corollary and computational-resource claims. They are not mathematical
claims counted as proved. Their original receipt membership and reasons are
preserved. Native aggregate fields `complete` and `whollyProved` remain false
for the counting ledger because of these exclusions, despite the eleven verified
mathematical bindings. Each final export is pinned to the common source
fingerprint recorded in the archive index. Superseded bindings and earlier
certificates remain in the immutable native mapping history. The
[earlier main handoff](verification/history/main-before-helper-relocation/HANDOFF.md)
that prompted the helper relocation is preserved separately; older working
exports are not part of this final three-archive package.

The main handoff retains two top-level verification notes. Its read-only review
used saved successful commands/logs and 138 source hashes matching at review rather
than rerunning Lean; external dependency checkout contents were not independently
hashed. It also records that the empty statement log supplies no output by itself,
while the command record shows exit code zero and the source hash matches. The
review established correspondence by reading the declarations and definitions.
These notes remain verbatim in the handoff and export; they are not replaced with
an empty `unknowns` list or described as a fresh execution by the reviewer.

The main archive preserves the exact verification logs cited at handoff time.
The repository's `checks.json` records the later final integration check after
documentation changes. The Lean source fingerprint is unchanged by those prose
edits; the archived 138-input manifest may contain earlier documentation bytes
and is not claimed identical to every file in the final checkout.

The plans, proof owners, receipts, and handoffs come from Tex2Lean 1.0.2's actual
bundled CLI, using a local compatibility build rather than an unmodified upstream
executable. The [compatibility scripts](../scripts/tex2lean-compat/README.md)
document and test the changes to import generation, provider/source access,
transaction recovery, and preservation of registered claims. ModelClosure's
checks for private definitions and structure fields were strengthened. The
[optional extension](../scripts/tex2lean-compat/extensions/README.md) also repairs
progress display only when the native certificate, target, source, ledger, and
graph agree; it does not create proof receipts or assign verified bindings.

The extension exposes exact elaborated types, reached definitions, and complete
relevant sources for correspondence review. Codex performs that review under the
user's formalization request and records proposed bindings, semantic decisions,
and justified target-inventory or metadata decisions through the native
immutable ledger. The recorded provenance is **assistant review; no human
semantic-review signature is asserted**. Ordinary native reconciliation must
then verify the interfaces and issue the proof receipts and certificate.

The ordinary CLI may report proved modules as unreachable from the selected
capstone. That warning concerns the selected theorem's dependency graph. Modules
supporting other proved results are retained and remain covered by the complete
whole-library axiom audit above.

The recorded native `/check` result is `FAIL` for two heuristic diagnostics.
The `surface-states` rule
counts indented lines in multiline theorem types as proof lines, although the
flagged Model wrappers each have a single `exact` proof. The
`hypothesis-is-in-the-bundle` rule treats `BoundedProfile.empty_zero` and
`load_le` as borrowed assumptions. These fields specify the domain of bounded
generating families: the proved membership equivalence relates them to the
paper's family definition in both directions. They are not unproved external
results and do not belong in `Prior`, which remains field-free. These diagnoses
do not constitute a clean overall native `/check` result; the strict Lean checks
and the native heuristic report must be reported separately.

The canonical Model files are now `ProblemSetting.lean`, `Prelude.lean`,
`Prior.lean`, and `Theorem.lean`. The reorganization preserves the public names
and source definition bodies. A separate kernel-checked comparison completed
at 03:07:16 UTC: all 78 declaration types and 74 of the 75 available bodies
are equal to their captured predecessors; erasing binder names also makes
those expressions structurally identical. Twenty-two raw records differ:
21 only in hygienic binder names, and one in the decision procedure selected
for `Paper.BitMatching.intersection`. That body's old and new expressions
are not definitionally equal. A separate Lean theorem proves their resulting
intersection functions equal for every argument, using only `propext`,
`Classical.choice`, and `Quot.sound`. This comparison establishes preservation
of meaning; it does not claim byte-identical elaboration or supply a native
Tex2Lean receipt.

The three selected runs have checked exact exports. The other 15 numbered
results have no separate native plan. Existing proof reuse, new interfaces, and alternative
proof arguments are distinguished below. Neither kernel checking nor statement
review authenticates the bibliography or prose attribution.

## Numbered results

| Manuscript result | Lean declaration and implementation |
| --- | --- |
| Theorem 1.1: universal upper bound, almost-all order, and extremal order | `Paper.mainTheorem` in [`Results.lean`](../AntichainOfGivenSize/Paper/Results.lean), combining `Paper.universalUpper_from_five`, `Paper.almostAllOrder`, and `Paper.extremalOrder`. |
| Definition 2.1: generated ideal and downward closure | `generatedIdeal` in [`Model/ProblemSetting.lean`](../AntichainOfGivenSize/Model/ProblemSetting.lean): the union of the generators' powersets. `Paper.generatedIdeal_isLowerSet` in [`BasicResults.lean`](../AntichainOfGivenSize/Paper/BasicResults.lean) proves downward closure under inclusion. |
| Definition 2.2: minimum generator number | `alpha` and `HasGeneratorCount` in [`Model/ProblemSetting.lean`](../AntichainOfGivenSize/Model/ProblemSetting.lean); `alpha_hasGeneratorCount` in [`BasicLemmas.lean`](../AntichainOfGivenSize/BasicLemmas.lean) proves attainment. `mainAlphaHasAntichainWitness` certifies an antichain attaining the same minimum. |
| Lemma 3.1: splitting | `splittingLemma` in [`BasicLemmas.lean`](../AntichainOfGivenSize/BasicLemmas.lean). The first ideal size has the required positivity hypothesis. |
| Lemma 3.2: lifting | `liftingLemma` in [`BasicLemmas.lean`](../AntichainOfGivenSize/BasicLemmas.lean). |
| Theorem 4.1: bit matching | `Paper.bitMatchingInt` in [`Results.lean`](../AntichainOfGivenSize/Paper/Results.lean), using `Paper.BitMatching.exists_matching_int`, for every integer target including negative targets. `Paper.bitMatching` is the natural-target interface used in the reduction. |
| Claim 4.2: separation of fresh elements | `Paper.BitMatching.fresh_separation` in [`BitMatching.lean`](../AntichainOfGivenSize/Paper/BitMatching.lean). |
| Claim 4.3: primary intersection size | `Paper.BitMatching.primary_intersection_card` in [`BitMatching.lean`](../AntichainOfGivenSize/Paper/BitMatching.lean), with the stronger set identity `primary_intersection`. |
| Claim 4.4: proper contributing intersections are larger | `Paper.BitMatching.proper_intersection_card` in [`BitMatching.lean`](../AntichainOfGivenSize/Paper/BitMatching.lean). |
| Theorem 5.1: exact bound `4q²+3` | `Paper.firstUpper` in [`Results.lean`](../AntichainOfGivenSize/Paper/Results.lean), from `Paper.first_upper` and `Paper.first_upper_cumulative` in [`FirstUpper.lean`](../AntichainOfGivenSize/Paper/FirstUpper.lean). `Paper.quadraticUpper` supplies its unconditional asymptotic conclusion directly from bit matching. |
| Theorem 6.1: block matching, with `a=5`, `b=3` | `Paper.blockMatching` in [`Results.lean`](../AntichainOfGivenSize/Paper/Results.lean), using `Paper.LiteralUpperParameters.blockMatching` in [`LiteralBlockMatching.lean`](../AntichainOfGivenSize/Paper/LiteralBlockMatching.lean) with the literal floor/ceiling parameter choices. Its full statement includes arbitrary integer residues, positivity, the generator bound, and the logarithmic size bound. |
| Claim 6.2: the pattern gadget has size `2^ell+d` | `Paper.PatternGadget.ideal_card_bits` in [`PatternGadget.lean`](../AntichainOfGivenSize/Paper/PatternGadget.lean), using the exact decomposition `ideal_decomposition`. |
| Claim 6.3: position addressing | `Paper.UpperConstruction.position_intersection` in [`UpperConstructionGeometry.lean`](../AntichainOfGivenSize/Paper/UpperConstructionGeometry.lean) states the position-only set identity directly; `full_position_intersection` also covers mixed queries. |
| Claim 6.4: the complete stage increment congruence | `Paper.UpperConstruction.paper_block_increment` in [`UpperConstructionIncrement.lean`](../AntichainOfGivenSize/Paper/UpperConstructionIncrement.lean), using `block_increment` and `idealCard_update` in [`UpperConstructionSteps.lean`](../AntichainOfGivenSize/Paper/UpperConstructionSteps.lean), from the complete sum `selected_card_zmod` in [`UpperConstructionCore.lean`](../AntichainOfGivenSize/Paper/UpperConstructionCore.lean) and the concrete geometry `stage_card_zmod`. Every nonempty contributing query is included. |
| Claim 6.5: uniform generator and ideal-size bounds | `Paper.UpperConstruction.card_generator_le`, `alpha_idealCard_le`, and `idealCard_bound` in [`UpperConstructionBounds.lean`](../AntichainOfGivenSize/Paper/UpperConstructionBounds.lean), combined with `Paper.LiteralUpperParameters.exists_literal_constructed_size_threshold` in [`LiteralUpperParameters.lean`](../AntichainOfGivenSize/Paper/LiteralUpperParameters.lean). |
| Lemma 6.6: direct reduction | `Paper.directReduction` in [`DirectReduction.lean`](../AntichainOfGivenSize/Paper/DirectReduction.lean), with the complete positivity, strict-decrease, and logarithmic-quotient requirements. Its explicit constants are `a=8`, `C₁=4096`. |
| Theorem 6.7: upper bound for every integer `n≥5` | `Paper.universalUpper_from_five` in [`Extremal.lean`](../AntichainOfGivenSize/Paper/Extremal.lean). This is stronger than merely restating an unspecified eventual bound. |
| Theorem 7.1: counting attainable values | `Paper.faithfulCountingBound` in [`Results.lean`](../AntichainOfGivenSize/Paper/Results.lean), using [`FaithfulCounting/CompleteCounting.lean`](../AntichainOfGivenSize/Paper/FaithfulCounting/CompleteCounting.lean). The Model interface `attainable_count` uses the same proof. It retains the budget denominator `100`, a threshold uniform in `K`, arbitrary sufficiently large integers `B`, and the real exponent `B−sqrt(B)`. |
| Corollary 10.1: probability in a dyadic block | `Paper.typicalLowerBound_probability` in [`TypicalProbability.lean`](../AntichainOfGivenSize/Paper/TypicalProbability.lean) bounds the actual uniform probability of `alpha>K`. `Paper.dyadicUniformPMF_good_probability` identifies that probability with the exact cardinality ratio proved by `Paper.typicalLowerBound_good` in [`TypicalGoodEvent.lean`](../AntichainOfGivenSize/Paper/TypicalGoodEvent.lean). |
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
`alpha_le_max_one_pred`. The stronger base-case sentence `alpha(n)≤2` for
`4≤n<16`, `n≠13`, is proved by `Paper.alpha_le_two_of_base_range` in
[`FiniteTwoGeneratorBound.lean`](../AntichainOfGivenSize/Paper/FiniteTwoGeneratorBound.lean).
The proof that two generators cannot give size
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
[`MainSemantics.lean`](../AntichainOfGivenSize/Paper/MainSemantics.lean)
proves both directions of the complement-density and natural/real density
representations with the same fixed constants.

### Real extremal cutoffs

`Paper.maximumBelow X` is the maximum of `alpha n` over the finite set
`1≤n<ceil(X)`, which for an integer `n` is exactly `1≤n<X`, including when
`X` itself is an integer. `Paper.ExtremalOrderStatement` is a real-variable
`IsTheta` statement as `X→+∞`. It is not a statement only along integer
cutoffs or a sparse sequence. `Paper.maximumBelow_spec` also proves attainment
at an allowed integer and the upper-bound property for every allowed integer
when `X>1`; `mem_maximumBelow_domain` exposes the exact strict-cutoff equivalence.

## Differences in proof implementation

These differences preserve the target conclusions and their quantifiers.

* **The first upper bound.** The induction in
  [`FirstUpper.lean`](../AntichainOfGivenSize/Paper/FirstUpper.lean) proves
  the cumulative statement for all smaller inputs at once. It keeps the
  exact bound `4q²+3` and the paper's range endpoints, and derives the
  quadratic asymptotic upper bound independently of the sharp upper bound.
* **Block parameters.** The public `Paper.blockMatching` now uses
  [`LiteralBlockMatching.lean`](../AntichainOfGivenSize/Paper/LiteralBlockMatching.lean)
  and [`LiteralUpperParameters.lean`](../AntichainOfGivenSize/Paper/LiteralUpperParameters.lean).
  They choose exactly `r=floor(log₂(B/log₂B))`, `H=2^r`, and `ell=ceil(B/H)`;
  the actual update history matches every integer residue, including negative
  targets. The uniform bounds retain constants `5` and `3`. The final numerical
  absorption uses the sufficient eventual estimate `9(log₂B)^3≤B`.
  The earlier integral-parameter implementation in
  [`UpperParameters.lean`](../AntichainOfGivenSize/Paper/UpperParameters.lean)
  remains available as a separate proved route.
* **The counting proof.** The fourteen modules in
  [`Paper/FaithfulCounting/`](../AntichainOfGivenSize/Paper/FaithfulCounting/CompleteCounting.lean)
  formalize Sections 8--10.1: the maximum-packing plateau, connected clusters
  of exactly `h` vertices, the partition count `(J+1)K^K`, the intrinsic
  exceptional set with bound `2Kρ'`, the incidence and exponent records,
  original signed inclusion--exclusion terms, and the integer tail interval.
  `NumericalParameters` uses the exact real logarithm, floor, scale sequence,
  and denominator `100`. `CompleteCounting` exports both the `Γ/4` and
  square-root savings above one absolute threshold.
  Least-element block labels encode the paper's canonical ordering. Pattern
  multiplicities encode its sorted incidence words. Taking `ceil(ρ)` gives
  exactly the real-threshold proximity graph; this equivalence is proved.
  The numerical absorption uses an explicit polynomial times `2^(3λ/10)`
  bound for the recording cost. These representations preserve the paper's
  counting argument. `ClaimBundles` exposes the combined intermediate
  estimates explicitly. Its normalization theorem relabels the actual union
  of the original generators onto `Fin N`, with `N≤KB`, full union, bounded
  generators, and unchanged ideal cardinality. Padding repeats index zero;
  [`ExactClaimBundles.lean`](../AntichainOfGivenSize/Paper/FaithfulCounting/ExactClaimBundles.lean)
  additionally proves the literal final-index padding identity for the entire
  generated ideal, paired with all normalization conclusions. Its
  `paper_numerics_full` retains the preliminary Gamma estimate for every
  `λ≥20` as well as the common threshold for all later numerical/counting bounds.
  The earlier larger encoding remains as `Paper.countingBound` in
  [`CountingParameters.lean`](../AntichainOfGivenSize/Paper/CountingParameters.lean).
  The public dyadic, density, and extremal certificates in `Paper.Results`
  now use `Paper.faithfulCountingBound`. The new Model lower-density and
  extremal interfaces use the same route through `attainableCount`.
* **Counting audit vocabulary.**
  [`Model/ProblemSetting.lean`](../AntichainOfGivenSize/Model/ProblemSetting.lean)
  owns the existing generated-ideal and bounded-profile vocabulary, including
  `Paper.attainableValues`. These declarations retain their qualified names and
  mathematical definitions; their original modules import them. This relocation
  makes the quantity's defining dependency chain visible under `Model/` without
  widening the closure check's permitted modules. The structural finite-type
  instances use term-form library constructors. The representation equivalence
  and counting proofs remain in their original proof modules. The Model
  membership equivalence reuses `Paper.mem_attainableValues_iff`. The headline
  uses the new proof in `FaithfulCounting/CompleteCounting`. Its `Prior`
  parameter is an empty structure and adds no assumption. The quantity's
  definition and the public counting statement are unchanged.
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
separately spells out mathematical contracts from the manuscript,
checking the counting contract against both complete proofs.
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

### Uniform probability in Corollary 10.1

`Paper.dyadicUniformPMF` in `Model/ProblemSetting.lean` is Mathlib's
`PMF.uniformOfFinset` on the half-open block `[2^(B-1), 2^B)`. Its positive
block index ensures the sample space is nonempty. `Paper/TypicalProbability.lean`
proves its exact support, reciprocal point masses, and probability-measure
property, and identifies the probability of every event with its finite count
ratio. The strict event `K < alpha n` therefore has exactly the ratio used by
`Paper.typicalLowerBound_good`. The resulting probability bound retains the
constant `100`, error `2^(1-sqrt B)`, and a single threshold independent of `K`.
Two expanded contracts construct the raw Mathlib PMF to check this denotation
and the corollary independently of the project's distribution alias.

## Main-theorem surface ownership

`Model/ProblemSetting.lean` now owns `HasGeneratorCount`, `alpha`,
`quadraticLogLogScale`, `Paper.goodInputs`, `Paper.realGoodInputs`, and
`Paper.maximumBelow`, with their original qualified names and definition
bodies unchanged. Their former modules import this vocabulary transitively.
Exception sets remain in `Paper/Statements.lean`: the literal density-one
surface does not reach them. No proof module is moved into Model.

`alpha_asymptotic_order` assembles four separate main-theorem interfaces.
The assembly argument lives in `Analysis/TheoremProof.lean` as
`Analysis.TheoremProof.alphaAsymptoticOrder`; the unchanged Model statement
applies that result. The assembly receives the proved
`alpha_simultaneous_density_one hprior` implication as an argument and uses it
on the chosen constants and upper/lower witnesses. The other components remain
the existing Analysis results. This preserves the original helper dependency
without an import back into `Model/Theorem.lean`.
Tex2Lean's proof workers completed all four owners: the eventual upper bound,
the lower-good density limit, the simultaneous natural/real limits at fixed
constants, and the real-cutoff extremal inequalities. The first and last reuse
existing upper/extremal estimates; the density transfer retains an explicit
finite-prefix error. Their statements and the empty `Prior` are unchanged.
The semantic interfaces in `Paper.MainSemantics` are also registered and have
individual closure checks.

The earlier main handoff flagged `alpha_simultaneous_density_one` as an internal
conditional lemma presented among Model's paper statements. Its complete theorem
text and individual closure check moved unchanged into the existing
[`Analysis/AlphaSimultaneousDensityOneProof.lean`](../AntichainOfGivenSize/Analysis/AlphaSimultaneousDensityOneProof.lean).
The qualified name, statement, proof body, and main-theorem application are
preserved, as recorded in the [relocation review](verification/helper-relocation-independent-review.json).
The unconditional main result remains in Model and still uses this helper;
the [earlier handoff finding](verification/history/main-before-helper-relocation/HANDOFF.md)
remains available with its original report. There are now
27 closure checks in Model and one for the helper in Analysis. The strict-check
report identifies the final checked inputs. The three selected native certificates and handoffs match the exported Lean
source fingerprint. The other numbered
results are covered by their checked Lean endpoints without separate native runs.
