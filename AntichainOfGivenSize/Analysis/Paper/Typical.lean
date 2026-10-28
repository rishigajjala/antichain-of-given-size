import AntichainOfGivenSize.Analysis.Paper.Statements
import AntichainOfGivenSize.Analysis.LowerBound.ProfilePadding
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The finite probability consequence of the manuscript's counting theorem

The counting estimate is an explicit hypothesis in this file.  In particular,
the finite probability conclusion is not substituted for a proof of counting.
-/

open Finset Filter

namespace AntichainOfGivenSize.Paper

/-- A nonempty ideal cannot have a zero-generator representation. -/
theorem alpha_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < alpha n := by
  by_contra h
  have hz : alpha n = 0 := by omega
  obtain ⟨m, G, hG, hc⟩ := alpha_hasGeneratorCount n
  have hzero : G = ∅ := Finset.card_eq_zero.mp (hc.trans hz)
  subst G
  simp [generatedIdeal] at hG
  omega

/-- The representation bridge uses exact values, and repeats generators when
padding to the counting theorem's exact coordinate count. -/
theorem mem_attainableValues_of_alpha_le {n B K : ℕ}
    (hnpos : 0 < n) (hn : n < 2 ^ B) (hK : alpha n ≤ K) :
    n ∈ attainableValues B K := by
  classical
  have hp := VennProfile.hasVennProfile_of_hasGeneratorCount
    (alpha_hasGeneratorCount n)
  obtain ⟨x, hx⟩ := ClusterLowerBound.exists_boundedProfile_of_hasVennProfile hp hn
  have heq : (x.pad hK (alpha_pos_of_pos hnpos)).value = n := by
    simpa using hx
  exact Finset.mem_image.mpr
    ⟨x.pad hK (alpha_pos_of_pos hnpos), Finset.mem_univ _, heq⟩

theorem badBlock_subset_attainableValues (B K : ℕ) :
    badBlock B K ⊆ attainableValues B K := by
  classical
  intro n hn
  obtain ⟨hn, hK⟩ := Finset.mem_filter.mp hn
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hn
  exact mem_attainableValues_of_alpha_le
    (lt_of_lt_of_le (by positivity : 0 < 2 ^ (B - 1)) hlo) hhi hK

theorem dyadicBlock_card {B : ℕ} (hB : 1 ≤ B) :
    (dyadicBlock B).card = 2 ^ (B - 1) := by
  rw [dyadicBlock, Nat.card_Ico]
  have heq : B = (B - 1) + 1 := by omega
  conv_lhs => rw [heq]
  simp only [Nat.add_sub_cancel, pow_succ]
  omega

/-- Corollary 10.1, with the exact cardinality of the uniform sample space. -/
theorem typicalLowerBound_of_countingBound
    (hcount : CountingBoundStatement) : TypicalLowerBoundStatement := by
  classical
  obtain ⟨B₀, hcount⟩ := hcount
  refine ⟨max B₀ 1, ?_⟩
  intro B K hB hK
  have hB₀ : B₀ ≤ B := (le_max_left _ _).trans hB
  have hB1 : 1 ≤ B := (le_max_right _ _).trans hB
  have hcard : ((badBlock B K).card : ℝ) ≤
      (2 : ℝ) ^ ((B : ℝ) - Real.sqrt B) :=
    (Nat.cast_le.mpr (Finset.card_le_card
      (badBlock_subset_attainableValues B K))).trans (hcount B K hB₀ hK)
  rw [dyadicBlock_card hB1]
  have hpow : (0 : ℝ) < ((2 ^ (B - 1) : ℕ) : ℝ) := by positivity
  apply (div_le_iff₀ hpow).2
  calc
    ((badBlock B K).card : ℝ) ≤
        (2 : ℝ) ^ ((B : ℝ) - Real.sqrt B) := hcard
    _ = (2 : ℝ) ^ (1 - Real.sqrt B) * ((2 ^ (B - 1) : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      rw [Nat.cast_sub hB1]
      norm_num

end AntichainOfGivenSize.Paper
