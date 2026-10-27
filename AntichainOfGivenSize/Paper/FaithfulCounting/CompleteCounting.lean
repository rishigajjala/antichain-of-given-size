import AntichainOfGivenSize.Paper.FaithfulCounting.ActualCounting
import AntichainOfGivenSize.Paper.FaithfulCounting.LiteralScales
import AntichainOfGivenSize.Paper.FaithfulCounting.ScalarNormalization
open scoped BigOperators
open Finset
open AntichainOfGivenSize.ClusterLowerBound
open AntichainOfGivenSize.FaithfulLower.Numerical

namespace AntichainOfGivenSize.FaithfulLower

/-- Closed counting theorem at parameters satisfying the proved numerical
threshold, with both the stronger Γ/4 saving and the stated square-root saving. -/
theorem paper_counting_at_parameters {B K : ℕ} {L : ℝ}
    (hL : 20 ≤ L) (hK : Admissible L K) (hBL : (2 : ℝ)^L = B)
    (hrec : recordCost L K ≤ gamma L K / 2) :
    (#(AntichainOfGivenSize.Paper.attainableValues B K) : ℝ) ≤
        (2 : ℝ)^((B : ℝ) - gamma L K / 4) ∧
      (#(AntichainOfGivenSize.Paper.attainableValues B K) : ℝ) ≤
        (2 : ℝ)^((B : ℝ) - Real.sqrt B) := by
  obtain ⟨hpos, hcover, hanti, hρ, hρB, hloss⟩ := literal_scale_conditions hL hK hBL
  have hc := boundedValues_card_le_uniform_loss hpos hcover
    (fun i : Fin (packingBound L K + 2) ↦ (B : ℝ) / L ^ (6 * i.val))
    hanti hρ hρB hloss
  exact ⟨hc.trans (countProduct_le_gamma_quarter_bound hL hK hBL hrec),
    hc.trans (countProduct_le_sqrt_bound hL hK hBL hrec)⟩

/-- One absolute threshold gives both the intermediate Γ/4 bound and the
square-root bound, uniformly in the paper's generator-budget range. -/
theorem exists_paper_counting_threshold_strong : ∃ B₀ : ℕ, 1 ≤ B₀ ∧
    ∀ B : ℕ, B₀ ≤ B → ∀ K : ℕ,
      1 ≤ K → (K : ℝ) ≤ (Real.logb 2 B)^2 / (100 * Real.logb 2 (Real.logb 2 B)) →
      (#(AntichainOfGivenSize.Paper.attainableValues B K) : ℝ) ≤
        (2 : ℝ)^((B : ℝ) - gamma (Real.logb 2 B) K / 4) ∧
      (#(AntichainOfGivenSize.Paper.attainableValues B K) : ℝ) ≤
        (2 : ℝ)^((B : ℝ) - Real.sqrt B) := by
  obtain ⟨L₀, hL₀, hthreshold⟩ := exists_uniform_threshold
  refine ⟨2^L₀, one_le_pow₀ (by norm_num), ?_⟩
  intro B hB K hKpos hKbound
  have hBpos : (0 : ℝ) < B := by
    exact_mod_cast lt_of_lt_of_le (pow_pos (by norm_num : 0 < (2 : ℕ)) L₀) hB
  have hlog : (L₀ : ℝ) ≤ Real.logb 2 B := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (2 : ℝ)^L₀) (show (2 : ℝ)^L₀ ≤ B by exact_mod_cast hB)
    simpa [Real.logb_pow] using hh
  have hL₀real : (20 : ℝ) ≤ L₀ := by exact_mod_cast hL₀
  have h20 : 20 ≤ Real.logb 2 B := hL₀real.trans hlog
  have hK : Admissible (Real.logb 2 B) K := ⟨hKpos, hKbound⟩
  have hrec := (hthreshold (Real.logb 2 B) hlog K hK).2.1
  have hBL : (2 : ℝ)^(Real.logb 2 B) = B :=
    Real.rpow_logb (by norm_num) (by norm_num) hBpos
  exact paper_counting_at_parameters h20 hK hBL hrec

/-- Theorem 7.1, with no assumptions beyond the displayed parameter range. -/
theorem exists_paper_counting_threshold : ∃ B₀ : ℕ, 1 ≤ B₀ ∧
    ∀ B : ℕ, B₀ ≤ B → ∀ K : ℕ,
      1 ≤ K → (K : ℝ) ≤ (Real.logb 2 B)^2 / (100 * Real.logb 2 (Real.logb 2 B)) →
      (#(AntichainOfGivenSize.Paper.attainableValues B K) : ℝ) ≤
        (2 : ℝ)^((B : ℝ) - Real.sqrt B) := by
  obtain ⟨B₀, hB₀, hbound⟩ := exists_paper_counting_threshold_strong
  exact ⟨B₀, hB₀, fun B hB K hK hbudget ↦ (hbound B hB K hK hbudget).2⟩


end AntichainOfGivenSize.FaithfulLower
