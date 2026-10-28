import AntichainOfGivenSize.Analysis.TheoremProof
import AntichainOfGivenSize.Model.Prelude
import AntichainOfGivenSize.Analysis.Paper.RealDensity
import AntichainOfGivenSize.Model.Prior
import AntichainOfGivenSize.Meta.ModelClosure
import AntichainOfGivenSize.Analysis.AttainableCountProof
import AntichainOfGivenSize.Analysis.AlphaSimultaneousDensityOneProof
import AntichainOfGivenSize.Analysis.AlphaEventualUpperProof
import AntichainOfGivenSize.Analysis.AlphaLowerDensityOneProof
import AntichainOfGivenSize.Analysis.AlphaMaximumOrderProof
import AntichainOfGivenSize.Analysis.Paper.MainSemantics
import AntichainOfGivenSize.Analysis.Paper.TypicalGoodEvent
import AntichainOfGivenSize.Analysis.Paper.FiniteTwoGeneratorBound
import AntichainOfGivenSize.Analysis.Paper.TypicalProbability
import AntichainOfGivenSize.Analysis.AlphaSplittingProof

/-!
# Counting attainable ideal sizes

Theorem 7.1 (`thm:attainable-count`) has one deterministic cardinality claim.
Its proof interface now uses the formalization in `Paper/FaithfulCounting/`:
the partition header, intrinsic exceptional set, original-query reconstruction,
integer tail interval, literal scale sequence, and uniform numerical estimates.
The earlier larger encoding remains available as `Paper.countingBound`.

Natural parameters represent the paper's integers on the positive range:
the absolute existential threshold may be enlarged to make `B` positive,
and the budget requires `1 ≤ K`. That threshold is independent of `K` and
is not identified with the proof's preliminary bound `2 ^ 20`.
The budget also supplies `0 < K` for the membership cross-check in Prelude.

The defining vocabulary of `Paper.attainableValues` is in
`Model/ProblemSetting.lean`, retaining the existing names and definitions.
The statement's complete quantity dependency chain therefore lies within the
audit surface, while the counting and representation proofs stay outside it.
-/

namespace AntichainOfGivenSize

/-- Theorem 7.1: one absolute threshold gives the stated bound on the number
of distinct attainable ideal sizes for every admissible pair `B, K`.
The real arithmetic and the constant `100` are expanded for comparison with
the manuscript and `scripts/CheckPaperStatements.lean`. -/
theorem attainable_count (hprior : Prior) :
    ∃ B₀ : ℕ, ∀ B K : ℕ, B₀ ≤ B →
      (1 ≤ K ∧ (K : ℝ) ≤ (Real.logb 2 (B : ℝ)) ^ 2 /
        (100 * Real.logb 2 (Real.logb 2 (B : ℝ)))) →
      ((Paper.attainableValues B K).card : ℝ) ≤
        (2 : ℝ) ^ ((B : ℝ) - Real.sqrt (B : ℝ)) := by
    exact AntichainOfGivenSize.Analysis.AttainableCountProof.attainableCount hprior


/-! ## Minimum generator counts: Theorem 1.1

This is a separate target from `attainable_count`. It uses the unchanged
`HasGeneratorCount`, `alpha`, and `quadraticLogLogScale` definitions, and
`Paper.goodInputs`, `Paper.realGoodInputs`, and `Paper.maximumBelow`.
The latter uses `Ico 1 ⌈X⌉₊`, so its endpoint is strictly below the real `X`;
the density sets use inclusive upper endpoints instead.

The upper and lower assertions supply witnesses independently. The
transfer lemma in `Analysis` preserves any such witnesses, so the assembly
uses one shared pair `c, C` without identifying unrelated existential choices.
Its premises are supplied by the first two parts, not by callers of the
assembled theorem. The extremal constants may be different.

The intended reuse endpoints are `Paper.universalUpper_from_five`,
`Paper.almostAllLowerBound`, the complement-count and real-cutoff bridges,
and `Paper.extremalOrder`. These are interfaces to existing results.

The reused main-theorem vocabulary is owned by `Model/ProblemSetting.lean`,
retaining its original names and bodies. The closure check below checks this
ownership boundary; no duplicate definitions are used.
-/

/-- Theorem 1.1(i): an absolute eventual upper bound, with its threshold
chosen inside the manuscript's domain. -/
theorem alpha_eventual_upper (hprior : Prior) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 5 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n →
        (alpha n : ℝ) ≤ C * quadraticLogLogScale (n : ℝ) := by
    exact AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.eventualUpper hprior

/-- Theorem 1.1(ii): the lower-good inputs, including exactly `5 ≤ n ≤ N`,
have natural density one. -/
theorem alpha_lower_density_one (hprior : Prior) :
    ∃ c : ℝ, 0 < c ∧ Filter.Tendsto
      (fun N : ℕ ↦
        (((Finset.Icc 5 N).filter fun n : ℕ ↦
          c * quadraticLogLogScale (n : ℝ) ≤ (alpha n : ℝ)).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) := by
    exact AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.lowerDensityOne hprior

/-- The extremal consequence of Theorem 1.1, expanded into positive
constant bounds for every sufficiently large real cutoff. -/
theorem alpha_maximum_order (hprior : Prior) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∃ X₀ : ℝ, 4 < X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        a * quadraticLogLogScale X ≤ (Paper.maximumBelow X : ℝ) ∧
        (Paper.maximumBelow X : ℝ) ≤ A * quadraticLogLogScale X := by
    exact AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.maximumOrder hprior

/-- Theorem 1.1: shared absolute constants for the universal upper bound,
the density-one lower bound, and the simultaneous natural- and real-cutoff
proportions, together with the real-cutoff extremal order. -/
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
        (Paper.maximumBelow X : ℝ) ≤ A * quadraticLogLogScale X) := by
  exact Analysis.TheoremProof.alphaAsymptoticOrder hprior (alpha_simultaneous_density_one hprior)

/-- Lemma 3.1: splitting on the manuscript's positive natural-number domain.
The existing `splittingLemma` also permits `n = 0`. -/
theorem alpha_splitting (hprior : Prior) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    alpha (m + n) ≤ alpha m + alpha (n + 1) := by
    exact AntichainOfGivenSize.Analysis.AlphaSplittingProof.splitting hprior m n hm hn

end AntichainOfGivenSize

#modelClosureOfType AntichainOfGivenSize.attainable_count
#modelClosureOfType AntichainOfGivenSize.Model.attainableValues_membership
#print axioms AntichainOfGivenSize.attainable_count

-- Meta/Audit checks Model/ for surplus after loading every registered claim.

#modelClosureOfType AntichainOfGivenSize.alpha_eventual_upper
#modelClosureOfType AntichainOfGivenSize.alpha_lower_density_one
#modelClosureOfType AntichainOfGivenSize.alpha_maximum_order
#modelClosureOfType AntichainOfGivenSize.alpha_asymptotic_order
#print axioms AntichainOfGivenSize.alpha_asymptotic_order

#modelClosureOfType AntichainOfGivenSize.Paper.mem_realGoodInputs_iff
#modelClosureOfType AntichainOfGivenSize.Paper.density_representations
#modelClosureOfType AntichainOfGivenSize.Paper.mem_maximumBelow_domain
#modelClosureOfType AntichainOfGivenSize.Paper.maximumBelow_spec

#modelClosureOfType AntichainOfGivenSize.Paper.typicalLowerBound_good
#modelClosureOfType AntichainOfGivenSize.Paper.alpha_le_two_of_base_range
#modelClosureOfType AntichainOfGivenSize.FaithfulLower.paper_final_padding_and_normalization

#modelClosureOfType AntichainOfGivenSize.Paper.dyadicUniformPMF_apply
#modelClosureOfType AntichainOfGivenSize.Paper.dyadicUniformPMF_support
#modelClosureOfType AntichainOfGivenSize.Paper.dyadicUniformPMF_probabilityMeasure
#modelClosureOfType AntichainOfGivenSize.Paper.dyadicUniformPMF_event_measure
#modelClosureOfType AntichainOfGivenSize.Paper.dyadicUniformPMF_good_probability
#modelClosureOfType AntichainOfGivenSize.Paper.typicalLowerBound_probability

#modelClosureOfType AntichainOfGivenSize.alpha_splitting
#print axioms AntichainOfGivenSize.alpha_splitting

#modelClosureOfType AntichainOfGivenSize.Paper.BitMatching.fresh_separation
#modelClosureOfType AntichainOfGivenSize.Paper.BitMatching.primary_intersection_card
#modelClosureOfType AntichainOfGivenSize.Paper.BitMatching.proper_intersection_card
#modelClosureOfType AntichainOfGivenSize.Paper.PatternGadget.ideal_card_bits
#modelClosureOfType AntichainOfGivenSize.Paper.UpperConstruction.position_intersection
#modelClosureOfType AntichainOfGivenSize.Paper.UpperConstruction.paper_block_increment
#modelClosureOfType AntichainOfGivenSize.Paper.LiteralUpperParameters.exists_literal_constructed_size_threshold
