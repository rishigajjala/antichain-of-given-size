import AntichainOfGivenSize.Analysis.Paper.FaithfulCounting.NumericalParameters
namespace AntichainOfGivenSize.FaithfulLower.Numerical

/-- The complete header product, with its original natural prefactors, is
exactly the exponential whose overhead is the displayed `recordCost`. -/
theorem countProduct_eq {B K : ℕ} {L : ℝ} (hK : 0 < K)
    (hBL : (2 : ℝ)^L = B) (η : ℝ) :
    (((packingBound L K + 1) * K^K : ℕ) : ℝ) * ((K*B+1 : ℕ) : ℝ) *
      (B+1 : ℝ)^(2^(packingBound L K) * (1 + K*2^(clusterSize L))) *
      (2 : ℝ)^((B : ℝ)-η+K+2) =
      (2 : ℝ)^((B : ℝ)-η+recordCost L K) := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  symm
  apply (Real.logb_eq_iff_rpow_eq (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1) (by positivity)).mp
  push_cast
  rw [Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity),
    Real.logb_pow, Real.logb_pow,
    Real.logb_rpow (by norm_num) (by norm_num)]
  unfold recordCost
  rw [hBL]
  push_cast
  ring

/-- The stronger intermediate saving retained in the paper's last display. -/
theorem countProduct_le_gamma_quarter_bound {B K : ℕ} {L : ℝ} (hL : 20 ≤ L)
    (hK : Admissible L K) (hBL : (2 : ℝ)^L = B)
    (hrec : recordCost L K ≤ gamma L K/2) :
    (((packingBound L K + 1) * K^K : ℕ) : ℝ) * ((K*B+1 : ℕ) : ℝ) *
      (B+1 : ℝ)^(2^(packingBound L K) * (1 + K*2^(clusterSize L))) *
      (2 : ℝ)^((B : ℝ)-(1-fineCost L K)*gamma L K+K+2) ≤
      (2 : ℝ)^((B : ℝ)-gamma L K/4) := by
  rw [countProduct_eq (by have := hK.1; omega) hBL]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hd := fineCost_le_quarter hL hK
  have hg : 0 ≤ gamma L K := by unfold gamma; positivity
  have hh := mul_le_mul_of_nonneg_right hd hg
  nlinarith

/-- Combining the exact header product with the numerical estimates yields
precisely the paper's `2^(B-sqrt B)` upper bound. -/
theorem countProduct_le_sqrt_bound {B K : ℕ} {L : ℝ} (hL : 20 ≤ L)
    (hK : Admissible L K) (hBL : (2 : ℝ)^L = B)
    (hrec : recordCost L K ≤ gamma L K/2) :
    (((packingBound L K + 1) * K^K : ℕ) : ℝ) * ((K*B+1 : ℕ) : ℝ) *
      (B+1 : ℝ)^(2^(packingBound L K) * (1 + K*2^(clusterSize L))) *
      (2 : ℝ)^((B : ℝ)-(1-fineCost L K)*gamma L K+K+2) ≤
      (2 : ℝ)^((B : ℝ)-Real.sqrt B) := by
  rw [countProduct_eq (by have := hK.1; omega) hBL]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hh := exponent_saving hL hK hrec
  rw [hBL] at hh
  exact hh


end AntichainOfGivenSize.FaithfulLower.Numerical
