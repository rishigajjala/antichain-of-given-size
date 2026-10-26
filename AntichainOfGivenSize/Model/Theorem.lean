import AntichainOfGivenSize.Model.Prelude
import AntichainOfGivenSize.Paper.RealDensity
import AntichainOfGivenSize.Model.Prior
import AntichainOfGivenSize.Meta.ModelClosure
import AntichainOfGivenSize.Analysis.AttainableCountProof
import AntichainOfGivenSize.Analysis.AlphaSimultaneousDensityOneProof
import AntichainOfGivenSize.Analysis.AlphaEventualUpperProof
import AntichainOfGivenSize.Analysis.AlphaLowerDensityOneProof
import AntichainOfGivenSize.Analysis.AlphaMaximumOrderProof

/-!
# Counting attainable ideal sizes

Theorem 7.1 (`thm:attainable-count`) has one deterministic cardinality claim.
Its intended proof interface reuses `AntichainOfGivenSize.Paper.countingBound`;
it does not rederive the counting argument. The existing proof uses the larger
clustered encoding documented in `docs/current-paper.md`, rather than a
line-by-line transcription of the manuscript's fixed-header product.

Natural parameters represent the paper's integers on the positive range:
the absolute existential threshold may be enlarged to make `B` positive,
and the budget requires `1 ≤ K`. That threshold is independent of `K` and
is not identified with the proof's preliminary bound `2 ^ 20`.
The budget also supplies `0 < K` for the membership cross-check in Prelude.

The defining vocabulary of `Paper.attainableValues` is in
`Model/CountingVocabulary.lean`, retaining the existing names and definitions.
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
simultaneous-density part below preserves any such witnesses, so the assembly
uses one shared pair `c, C` without identifying unrelated existential choices.
Its premises are supplied by the first two parts, not by callers of the
assembled theorem. The extremal constants may be different.

The intended reuse endpoints are `Paper.universalUpper_from_five`,
`Paper.almostAllLowerBound`, the complement-count and real-cutoff bridges,
and `Paper.extremalOrder`. These are interfaces to existing results.

The reused main-theorem vocabulary is owned by `Model/MainVocabulary.lean`,
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

/-- The simultaneous consequence of Theorem 1.1, also Corollary 10.2:
an eventual upper bound and a density-one lower bound give both literal
proportions with the same constants. The real denominator is `X`. -/
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
      Filter.atTop (nhds 1) := by
    exact AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.simultaneousDensityOne hprior c C n₀ hupper hlower

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
  obtain ⟨C, hC, n₀, hn₀, hupper⟩ := alpha_eventual_upper hprior
  obtain ⟨c, hc, hlower⟩ := alpha_lower_density_one hprior
  exact ⟨⟨c, C, hc, hC, n₀, hn₀, hupper, hlower,
    alpha_simultaneous_density_one hprior c C n₀ hupper hlower⟩,
    alpha_maximum_order hprior⟩

end AntichainOfGivenSize

#modelClosureOfType AntichainOfGivenSize.attainable_count
#modelClosureOfType AntichainOfGivenSize.Model.attainableValues_membership
#print axioms AntichainOfGivenSize.attainable_count

-- Meta/Audit checks Model/ for surplus after loading every registered claim.

#modelClosureOfType AntichainOfGivenSize.alpha_eventual_upper
#modelClosureOfType AntichainOfGivenSize.alpha_lower_density_one
#modelClosureOfType AntichainOfGivenSize.alpha_simultaneous_density_one
#modelClosureOfType AntichainOfGivenSize.alpha_maximum_order
#modelClosureOfType AntichainOfGivenSize.alpha_asymptotic_order
#print axioms AntichainOfGivenSize.alpha_asymptotic_order
