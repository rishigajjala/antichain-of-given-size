import AntichainOfGivenSize.Model.Prelude
import AntichainOfGivenSize.Model.Prior
import AntichainOfGivenSize.Meta.ModelClosure
import AntichainOfGivenSize.Paper.CountingParameters

/-- PAPER: paper/Generating_Antichains_Simplified.tex:987-997
Proof-side owner for `AntichainOfGivenSize.attainable_count`.

This interface reuses `Paper.countingBound`, preserving its threshold uniform in
`K`, constant 100, and unrounded real square-root saving. Its existing proof uses
the larger clustered encoding documented in `docs/current-paper.md:166-175`,
rather than newly formalizing the manuscript's streamlined fixed-header estimates.
The natural parameters agree with the paper's integer range after choosing a
positive absolute threshold; the budget already requires `K ≥ 1`.
No fact is extracted from the empty `Prior` structure. -/
theorem AntichainOfGivenSize.Analysis.AttainableCountProof.attainableCount (hprior : AntichainOfGivenSize.Prior) :
    ∃ B₀ : ℕ, ∀ B K : ℕ, B₀ ≤ B →
      (1 ≤ K ∧ (K : ℝ) ≤ (Real.logb 2 (B : ℝ)) ^ 2 /
        (100 * Real.logb 2 (Real.logb 2 (B : ℝ)))) →
      ((AntichainOfGivenSize.Paper.attainableValues B K).card : ℝ) ≤
        (2 : ℝ) ^ ((B : ℝ) - Real.sqrt (B : ℝ)) := by
  cases hprior
  exact AntichainOfGivenSize.Paper.countingBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · reused `Paper.countingBound` directly; no additional assumptions or helper lemmas.
-/
