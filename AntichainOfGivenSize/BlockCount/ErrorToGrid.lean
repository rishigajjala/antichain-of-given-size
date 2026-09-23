import AntichainOfGivenSize.BlockCount.ErrorArithmetic
import AntichainOfGivenSize.BlockCount.FiniteScales

/-!
# From normalized geometric error to the leading-coefficient grid
-/

namespace AntichainOfGivenSize.BlockCount

/-- The positive remainder `2^-t` fits into one error unit when the shift
reaches the next scale cutoff. -/
theorem normalized_remainder_le_error_unit {t H : ℕ} (h : H ≤ t) :
    (2 : ℚ) ^ (-(t : ℤ)) ≤ 1 / (2 : ℚ) ^ H := by
  have hneg : -(t : ℤ) ≤ -(H : ℤ) :=
    neg_le_neg (by exact_mod_cast h)
  have hz := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mpr hneg
  simpa only [zpow_neg, zpow_natCast, one_div] using hz

/-- Add the single remainder `2^-t` to a bound for all geometric errors. -/
theorem leading_coefficient_close_of_normalized_error
    (p k t j : ℕ) (S : ℚ)
    (ht : finiteScale p k (j + 1) ≤ t)
    (hgeom : |(p : ℚ) + (2 : ℚ) ^ (-(t : ℤ)) - S| ≤
      (exponentBudget k : ℚ) /
        (2 : ℚ) ^ (finiteScale p k (j + 1))) :
    |(p : ℚ) - S| ≤
      ((exponentBudget k + 1 : ℕ) : ℚ) /
        (2 : ℚ) ^ (finiteScale p k (j + 1)) := by
  let eps : ℚ := (2 : ℚ) ^ (-(t : ℤ))
  let unit : ℚ := 1 / (2 : ℚ) ^ (finiteScale p k (j + 1))
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  have hunit : eps ≤ unit := normalized_remainder_le_error_unit ht
  have hgeom' : |(p : ℚ) + eps - S| ≤ (exponentBudget k : ℚ) * unit := by
    simpa only [eps, unit, one_div, div_eq_mul_inv, one_mul] using hgeom
  calc
    |(p : ℚ) - S| = |((p : ℚ) - ((p : ℚ) + eps)) + (((p : ℚ) + eps) - S)| := by
      congr 1
      ring
    _ ≤ |(p : ℚ) - ((p : ℚ) + eps)| + |((p : ℚ) + eps) - S| :=
      abs_add_le _ _
    _ = eps + |((p : ℚ) + eps) - S| := by simp [abs_of_nonneg heps]
    _ ≤ unit + (exponentBudget k : ℚ) * unit := add_le_add hunit hgeom'
    _ = ((exponentBudget k + 1 : ℕ) : ℚ) /
        (2 : ℚ) ^ (finiteScale p k (j + 1)) := by
      simp only [unit, div_eq_mul_inv, Nat.cast_add, Nat.cast_one]
      ring

end AntichainOfGivenSize.BlockCount
