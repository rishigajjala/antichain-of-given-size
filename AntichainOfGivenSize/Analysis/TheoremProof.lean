import AntichainOfGivenSize.Analysis.AlphaEventualUpperProof
import AntichainOfGivenSize.Analysis.AlphaLowerDensityOneProof
import AntichainOfGivenSize.Analysis.AlphaSimultaneousDensityOneProof
import AntichainOfGivenSize.Analysis.AlphaMaximumOrderProof

namespace AntichainOfGivenSize

/-- Assemble the four existing main-theorem components with shared constants. -/
theorem Analysis.TheoremProof.alphaAsymptoticOrder (hprior : Prior) :
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
  obtain ⟨C, hC, n₀, hn₀, hupper⟩ := Analysis.AlphaAsymptoticOrderProof.eventualUpper hprior
  obtain ⟨c, hc, hlower⟩ := Analysis.AlphaAsymptoticOrderProof.lowerDensityOne hprior
  exact ⟨⟨c, C, hc, hC, n₀, hn₀, hupper, hlower,
    Analysis.AlphaAsymptoticOrderProof.simultaneousDensityOne hprior c C n₀ hupper hlower⟩,
    Analysis.AlphaAsymptoticOrderProof.maximumOrder hprior⟩

end AntichainOfGivenSize
