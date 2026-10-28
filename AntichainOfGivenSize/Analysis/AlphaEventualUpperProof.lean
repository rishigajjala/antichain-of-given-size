import AntichainOfGivenSize.Model.Prelude
import AntichainOfGivenSize.Analysis.Paper.RealDensity
import AntichainOfGivenSize.Model.Prior
import AntichainOfGivenSize.Meta.ModelClosure
import AntichainOfGivenSize.Analysis.AttainableCountProof

/-- PAPER: paper/Generating_Antichains_Simplified.tex:909-915
Proof-side owner for `AntichainOfGivenSize.alpha_eventual_upper`.

This interface reuses `Paper.universalUpper_from_five`, choosing threshold five.
The existing proof uses `mainUpperBound` and finite-prefix absorption, as
documented in `docs/current-paper.md`, rather than reproducing the manuscript's
derivative/potential argument. No fact is extracted from the empty `Prior`. -/
theorem AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.eventualUpper
    (hprior : AntichainOfGivenSize.Prior) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 5 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n →
        (AntichainOfGivenSize.alpha n : ℝ) ≤ C * AntichainOfGivenSize.quadraticLogLogScale (n : ℝ) := by
  cases hprior
  obtain ⟨C, hC, hupper⟩ := AntichainOfGivenSize.Paper.universalUpper_from_five
  exact ⟨C, hC, 5, le_rfl, hupper⟩

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · reused `Paper.universalUpper_from_five` with threshold five; no new helpers or assumptions.
-/
