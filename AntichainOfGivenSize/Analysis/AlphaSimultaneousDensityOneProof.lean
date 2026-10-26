import AntichainOfGivenSize.Model.Prelude
import AntichainOfGivenSize.Paper.RealDensity
import AntichainOfGivenSize.Model.Prior
import AntichainOfGivenSize.Meta.ModelClosure
import AntichainOfGivenSize.Analysis.AttainableCountProof

/-- Proof-side owner for `AntichainOfGivenSize.alpha_simultaneous_density_one`; its statement is fixed by the proof charter. -/
theorem AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.simultaneousDensityOne
    (hprior : AntichainOfGivenSize.Prior)
    (c C : ℝ) (n₀ : ℕ)
    (hupper : ∀ n : ℕ, n₀ ≤ n →
      (AntichainOfGivenSize.alpha n : ℝ) ≤ C * AntichainOfGivenSize.quadraticLogLogScale (n : ℝ))
    (hlower : Filter.Tendsto
      (fun N : ℕ ↦
        (((Finset.Icc 5 N).filter fun n : ℕ ↦
          c * AntichainOfGivenSize.quadraticLogLogScale (n : ℝ) ≤ (AntichainOfGivenSize.alpha n : ℝ)).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1)) :
    Filter.Tendsto
      (fun N : ℕ ↦ ((AntichainOfGivenSize.Paper.goodInputs c C N).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) ∧
    Filter.Tendsto
      (fun X : ℝ ↦ ((AntichainOfGivenSize.Paper.realGoodInputs c C X).card : ℝ) / X)
      Filter.atTop (nhds 1) := by
  sorry
