import AntichainOfGivenSize.Model.Prelude
import AntichainOfGivenSize.Model.Prior
import AntichainOfGivenSize.Meta.ModelClosure
import AntichainOfGivenSize.Paper.FaithfulCounting.ClaimBundles

/-- PAPER: paper/Generating_Antichains_Simplified.tex:987-997
Proof-side owner for `AntichainOfGivenSize.attainable_count`.

This interface uses the manuscript's partition header and intrinsic exceptional
set, reconstructs the original signed central terms from two records, and bounds
the remaining terms by their integer interval. The literal scales and uniform
numerical estimates prove both the intermediate Γ/4 saving and the square-root
saving. The threshold is uniform in `K`, and the budget constant remains 100.
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
  obtain ⟨B₀, _hB₀, hbound⟩ :=
    AntichainOfGivenSize.FaithfulLower.exists_paper_counting_threshold
  refine ⟨B₀, ?_⟩
  intro B K hB hK
  exact hbound B hB K hK.1 hK.2

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · reused `Paper.countingBound` directly; no additional assumptions or helper lemmas.
-/
