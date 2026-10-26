import AntichainOfGivenSize.Model.Prelude
import AntichainOfGivenSize.Paper.RealDensity
import AntichainOfGivenSize.Model.Prior
import AntichainOfGivenSize.Meta.ModelClosure
import AntichainOfGivenSize.Analysis.AttainableCountProof

/-- Proof-side owner for `AntichainOfGivenSize.alpha_lower_density_one`; its statement is fixed by the proof charter. -/
theorem AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.lowerDensityOne
    (hprior : AntichainOfGivenSize.Prior) :
    ∃ c : ℝ, 0 < c ∧ Filter.Tendsto
      (fun N : ℕ ↦
        (((Finset.Icc 5 N).filter fun n : ℕ ↦
          c * AntichainOfGivenSize.quadraticLogLogScale (n : ℝ) ≤ (AntichainOfGivenSize.alpha n : ℝ)).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) := by
  sorry
