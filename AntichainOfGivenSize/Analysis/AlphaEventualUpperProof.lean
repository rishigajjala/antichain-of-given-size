import AntichainOfGivenSize.Model.Prelude
import AntichainOfGivenSize.Paper.RealDensity
import AntichainOfGivenSize.Model.Prior
import AntichainOfGivenSize.Meta.ModelClosure
import AntichainOfGivenSize.Analysis.AttainableCountProof

/-- Proof-side owner for `AntichainOfGivenSize.alpha_eventual_upper`; its statement is fixed by the proof charter. -/
theorem AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.eventualUpper
    (hprior : AntichainOfGivenSize.Prior) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 5 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n →
        (AntichainOfGivenSize.alpha n : ℝ) ≤ C * AntichainOfGivenSize.quadraticLogLogScale (n : ℝ) := by
  sorry
