import AntichainOfGivenSize.Paper.FaithfulCounting.NumericalParameters
namespace AntichainOfGivenSize.FaithfulLower.Numerical

/-- The manuscript's real-valued scale, with no initial logarithmic factor. -/
noncomputable def literalScale (B L : ℝ) (j : ℕ) : ℝ := B / L ^ (6 * j)

theorem literalScale_pos {B L : ℝ} (hB : 0 < B) (hL : 0 < L) (j : ℕ) :
    0 < literalScale B L j := by
  unfold literalScale
  positivity

theorem literalScale_nonneg {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) (j : ℕ) :
    0 ≤ literalScale B L j := by
  unfold literalScale
  positivity

theorem literalScale_le {B L : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (j : ℕ) :
    literalScale B L j ≤ B :=
  div_le_self hB (one_le_pow₀ hL)

theorem literalScale_antitone {B L : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) :
    Antitone (literalScale B L) := by
  intro i j hij
  apply div_le_div_of_nonneg_left hB
    (pow_pos (lt_of_lt_of_le zero_lt_one hL) (6 * i))
  exact pow_le_pow_right₀ hL (Nat.mul_le_mul_left 6 hij)

theorem literalScale_succ (B L : ℝ) (j : ℕ) :
    literalScale B L (j + 1) = literalScale B L j / L ^ 6 := by
  simp only [literalScale, Nat.mul_add, Nat.mul_one, pow_add, div_div]

theorem literalScale_at_packingBound {B L : ℝ} {K : ℕ}
    (hBL : (2 : ℝ) ^ L = B) :
    literalScale B L (packingBound L K) = gamma L K := by
  unfold literalScale gamma
  rw [hBL]

theorem gamma_le_literalScale {B L : ℝ} {K j : ℕ}
    (hB : 0 ≤ B) (hL : 1 ≤ L) (hBL : (2 : ℝ) ^ L = B)
    (hj : j ≤ packingBound L K) :
    gamma L K ≤ literalScale B L j := by
  rw [← literalScale_at_packingBound hBL]
  exact literalScale_antitone hB hL hj

theorem clusterSize_pos {L : ℝ} (hL : 20 ≤ L) : 0 < clusterSize L := by
  have hh := (clusterSize_bounds hL).1
  have hp : (0 : ℝ) < clusterSize L := by linarith
  exact_mod_cast hp

theorem packingBound_cover {L : ℝ} (hL : 20 ≤ L) (K : ℕ) :
    K < (packingBound L K + 1) * clusterSize L := by
  have hp := clusterSize_pos hL
  have hm := Nat.mod_lt K hp
  have he := Nat.mod_add_div K (clusterSize L)
  unfold packingBound
  nlinarith

/-- Separation of adjacent scales pays for the intrinsic incidence record. -/
theorem literalScale_net_loss {B L : ℝ} {K j : ℕ}
    (hL : 20 ≤ L) (hK : Admissible L K) (hBL : (2 : ℝ) ^ L = B)
    (hj : j ≤ packingBound L K) :
    2 * (K : ℝ) ^ 2 * literalScale B L (j + 1) ≤
      literalScale B L j - (1 - fineCost L K) * gamma L K := by
  have hd := fineCost_le_quarter hL hK
  have hB : 0 ≤ B := by rw [← hBL]; positivity
  have hgamma := gamma_le_literalScale hB (by linarith) hBL hj
  have hmult := mul_le_mul_of_nonneg_left hgamma
    (show 0 ≤ 1 - fineCost L K by linarith)
  calc
    2 * (K : ℝ) ^ 2 * literalScale B L (j + 1) =
        fineCost L K * literalScale B L j := by
      rw [literalScale_succ]
      unfold fineCost
      ring
    _ ≤ literalScale B L j - (1 - fineCost L K) * gamma L K := by
      nlinarith

noncomputable def literalScales (B L : ℝ) (K : ℕ) :
    Fin (packingBound L K + 2) → ℝ := fun j ↦ literalScale B L j.1

/-- All graph/header hypotheses and the common net loss, in one interface
for the finite counting theorem. -/
theorem literal_scale_conditions {B K : ℕ} {L : ℝ}
    (hL : 20 ≤ L) (hK : Admissible L K) (hBL : (2 : ℝ) ^ L = B) :
    0 < clusterSize L ∧
    K < (packingBound L K + 1) * clusterSize L ∧
    Antitone (literalScales B L K) ∧
    (∀ i, 0 ≤ literalScales B L K i) ∧
    (∀ i, literalScales B L K i ≤ B) ∧
    ∀ j : Fin (packingBound L K + 1),
      2 * (K : ℝ) ^ 2 * literalScales B L K j.succ ≤
        literalScales B L K j.castSucc - (1 - fineCost L K) * gamma L K := by
  refine ⟨clusterSize_pos hL, packingBound_cover hL K, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact literalScale_antitone (by positivity) (by linarith) hij
  · intro i
    exact literalScale_nonneg (by positivity) (by linarith) i.1
  · intro i
    exact literalScale_le (by positivity) (by linarith) i.1
  · intro j
    exact literalScale_net_loss hL hK hBL (Nat.le_of_lt_succ j.2)

/-- The stronger exponent bound explicitly proved before the square-root
simplification in the manuscript. -/
theorem exponent_saving_gamma_quarter {L : ℝ} {K : ℕ} (hL : 20 ≤ L)
    (hK : Admissible L K) (hrec : recordCost L K ≤ gamma L K / 2) :
    (2 : ℝ) ^ L - (1 - fineCost L K) * gamma L K + recordCost L K ≤
      (2 : ℝ) ^ L - gamma L K / 4 := by
  have hd := fineCost_le_quarter hL hK
  have hg : 0 ≤ gamma L K := by unfold gamma; positivity
  have hm := mul_le_mul_of_nonneg_right hd hg
  nlinarith


end AntichainOfGivenSize.FaithfulLower.Numerical
