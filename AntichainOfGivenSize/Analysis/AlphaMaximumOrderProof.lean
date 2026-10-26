import AntichainOfGivenSize.Model.Prelude
import AntichainOfGivenSize.Paper.RealDensity
import AntichainOfGivenSize.Model.Prior
import AntichainOfGivenSize.Meta.ModelClosure
import AntichainOfGivenSize.Analysis.AttainableCountProof

/-- Proof-side owner for `AntichainOfGivenSize.alpha_maximum_order`; its statement is fixed by the proof charter. -/
theorem AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.maximumOrder
    (hprior : AntichainOfGivenSize.Prior) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∃ X₀ : ℝ, 4 < X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        a * AntichainOfGivenSize.quadraticLogLogScale X ≤ (AntichainOfGivenSize.Paper.maximumBelow X : ℝ) ∧
        (AntichainOfGivenSize.Paper.maximumBelow X : ℝ) ≤ A * AntichainOfGivenSize.quadraticLogLogScale X := by
  sorry
