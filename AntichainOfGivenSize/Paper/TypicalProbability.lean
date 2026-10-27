import AntichainOfGivenSize.Model.ProbabilityVocabulary
import AntichainOfGivenSize.Paper.TypicalGoodEvent

open scoped ENNReal Classical

namespace AntichainOfGivenSize.Paper

/-- Each point in the block receives its reciprocal-cardinality mass; all
other natural numbers receive zero mass. -/
theorem dyadicUniformPMF_apply (B : ℕ) (hB : 1 ≤ B) (n : ℕ) :
    dyadicUniformPMF B hB n =
      if n ∈ Finset.Ico (2 ^ (B - 1)) (2 ^ B) then
        (((Finset.Ico (2 ^ (B - 1)) (2 ^ B)).card : ℝ≥0∞))⁻¹
      else 0 := by
  classical
  by_cases hn : n ∈ Finset.Ico (2 ^ (B - 1)) (2 ^ B) <;>
    simp [dyadicUniformPMF, hn]

/-- The sampling support is exactly the dyadic block. -/
theorem dyadicUniformPMF_support (B : ℕ) (hB : 1 ≤ B) :
    (dyadicUniformPMF B hB).support =
      (Finset.Ico (2 ^ (B - 1)) (2 ^ B) : Set ℕ) := by
  exact PMF.support_uniformOfFinset _

/-- The associated measure has total mass one. -/
theorem dyadicUniformPMF_probabilityMeasure (B : ℕ) (hB : 1 ≤ B) :
    MeasureTheory.IsProbabilityMeasure (dyadicUniformPMF B hB).toMeasure := by
  infer_instance

/-- Exact denotation of every event under uniform sampling of the dyadic block. -/
theorem dyadicUniformPMF_event_measure (B : ℕ) (hB : 1 ≤ B) (S : Set ℕ) :
    (dyadicUniformPMF B hB).toMeasure S =
      (((Finset.Ico (2 ^ (B - 1)) (2 ^ B)).filter fun n ↦ n ∈ S).card : ℝ≥0∞) /
        ((Finset.Ico (2 ^ (B - 1)) (2 ^ B)).card : ℝ≥0∞) := by
  classical
  exact PMF.toMeasure_uniformOfFinset_apply _ S (Set.to_countable S).measurableSet

/-- The actual probability of the strict good event equals the already proved
finite uniform cardinality ratio. -/
theorem dyadicUniformPMF_good_probability (B K : ℕ) (hB : 1 ≤ B) :
    ((dyadicUniformPMF B hB).toMeasure {n : ℕ | K < alpha n}).toReal =
      (((Finset.Ico (2 ^ (B - 1)) (2 ^ B)).filter fun n : ℕ ↦ K < alpha n).card : ℝ) /
        ((Finset.Ico (2 ^ (B - 1)) (2 ^ B)).card : ℝ) := by
  classical
  rw [dyadicUniformPMF_event_measure]
  simp only [Set.mem_setOf_eq, ENNReal.toReal_div, ENNReal.toReal_natCast]

/-- Corollary 10.1 as a probability bound for an actual uniform PMF, with one
threshold for every admissible K and the paper's exact square-root error. -/
theorem typicalLowerBound_probability :
    ∃ B₀ : ℕ, ∃ hB₀ : 1 ≤ B₀, ∀ B K : ℕ, ∀ hB : B₀ ≤ B,
      (1 ≤ K ∧ (K : ℝ) ≤ (Real.logb 2 (B : ℝ)) ^ 2 /
        (100 * Real.logb 2 (Real.logb 2 (B : ℝ)))) →
      1 - (2 : ℝ) ^ (1 - Real.sqrt (B : ℝ)) ≤
        ((dyadicUniformPMF B (hB₀.trans hB)).toMeasure
          {n : ℕ | K < alpha n}).toReal := by
  obtain ⟨B₁, hbound⟩ := typicalLowerBound_good
  refine ⟨max B₁ 1, le_max_right _ _, ?_⟩
  intro B K hB hK
  rw [dyadicUniformPMF_good_probability]
  exact hbound B K ((le_max_left _ _).trans hB) hK

end AntichainOfGivenSize.Paper
