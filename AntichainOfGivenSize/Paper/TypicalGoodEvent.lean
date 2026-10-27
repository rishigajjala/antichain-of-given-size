import AntichainOfGivenSize.Paper.Results

namespace AntichainOfGivenSize.Paper

/-- Corollary 10.1 with its literal good event. The ratio is the uniform
probability on the half-open dyadic block. The threshold is uniform in `K`. -/
theorem typicalLowerBound_good :
    ∃ B₀ : ℕ, ∀ B K : ℕ, B₀ ≤ B →
      (1 ≤ K ∧ (K : ℝ) ≤ (Real.logb 2 (B : ℝ)) ^ 2 /
        (100 * Real.logb 2 (Real.logb 2 (B : ℝ)))) →
      1 - (2 : ℝ) ^ (1 - Real.sqrt (B : ℝ)) ≤
        (((Finset.Ico (2 ^ (B - 1)) (2 ^ B)).filter
          fun n : ℕ ↦ K < alpha n).card : ℝ) /
          ((Finset.Ico (2 ^ (B - 1)) (2 ^ B)).card : ℝ) := by
  classical
  obtain ⟨B₀, hbound⟩ := typicalLowerBound
  refine ⟨max B₀ 1, ?_⟩
  intro B K hB hK
  have hB₀ : B₀ ≤ B := (le_max_left _ _).trans hB
  have hB1 : 1 ≤ B := (le_max_right _ _).trans hB
  have hbad := hbound B K hB₀ hK
  have hcounts : (badBlock B K).card +
      ((dyadicBlock B).filter fun n : ℕ ↦ K < alpha n).card =
        (dyadicBlock B).card := by
    simpa only [badBlock, not_le] using
      (Finset.card_filter_add_card_filter_not (s := dyadicBlock B)
        (fun n : ℕ ↦ alpha n ≤ K))
  have hcountsR : ((badBlock B K).card : ℝ) +
      (((dyadicBlock B).filter fun n : ℕ ↦ K < alpha n).card : ℝ) =
        ((dyadicBlock B).card : ℝ) := by exact_mod_cast hcounts
  have hden : (0 : ℝ) < ((dyadicBlock B).card : ℝ) := by
    rw [dyadicBlock_card hB1]
    positivity
  have hsum : ((badBlock B K).card : ℝ) / ((dyadicBlock B).card : ℝ) +
      (((dyadicBlock B).filter fun n : ℕ ↦ K < alpha n).card : ℝ) /
        ((dyadicBlock B).card : ℝ) = 1 := by
    rw [← add_div, hcountsR, div_self (ne_of_gt hden)]
  change 1 - (2 : ℝ) ^ (1 - Real.sqrt (B : ℝ)) ≤
    (((dyadicBlock B).filter fun n : ℕ ↦ K < alpha n).card : ℝ) /
      ((dyadicBlock B).card : ℝ)
  linarith

end AntichainOfGivenSize.Paper
