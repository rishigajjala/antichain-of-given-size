import AntichainOfGivenSize.BlockCount.FiniteExponents

/-!
# Explicit scales for finite block-count witnesses

The scale sequence grows fast enough to make the error from small generators
and cross-cluster overlaps strictly less than the spacing of the dyadic grid.
-/

namespace AntichainOfGivenSize.BlockCount

@[simp] theorem finiteScale_zero (p k : ℕ) : finiteScale p k 0 = 1 := rfl

@[simp] theorem finiteScale_succ (p k j : ℕ) :
    finiteScale p k (j + 1) =
      finiteClusterRadius p k (finiteScale p k j) + scalePadding k := rfl

theorem finiteScale_le_succ (p k j : ℕ) :
    finiteScale p k j ≤ finiteScale p k (j + 1) := by
  simp only [finiteScale_succ, finiteClusterRadius]
  omega

theorem finiteScale_mono (p k : ℕ) : Monotone (finiteScale p k) :=
  monotone_nat_of_le_succ (finiteScale_le_succ p k)

theorem finiteScale_pos (p k j : ℕ) : 0 < finiteScale p k j := by
  have h := finiteScale_mono p k (Nat.zero_le j)
  simpa only [finiteScale_zero] using Nat.lt_of_lt_of_le Nat.zero_lt_one h

theorem finiteScale_pad (p k j : ℕ) :
    finiteClusterRadius p k (finiteScale p k j) + (exponentBudget k + 2) =
      finiteScale p k (j + 1) := by
  rfl

theorem finiteScale_succ_le_threshold (p k j : ℕ)
    (hj : j ≤ exponentBudget k) :
    finiteScale p k (j + 1) ≤ finiteThreshold p k :=
  finiteScale_mono p k (Nat.succ_le_succ hj)

theorem finiteThreshold_ge_two (p k : ℕ) : 2 ≤ finiteThreshold p k := by
  unfold finiteThreshold
  have hs : finiteScale p k 1 = finiteClusterRadius p k 1 + scalePadding k := rfl
  have h1 : 2 ≤ finiteScale p k 1 := by
    rw [hs]
    simp only [finiteClusterRadius, scalePadding]
    omega
  exact h1.trans (finiteScale_mono p k (by omega))

/-- The budget of at most `Q+1` error terms is smaller than one step of the
cluster grid after advancing one cutoff. -/
theorem finiteScale_error_lt_grid (p k j : ℕ) :
    ((exponentBudget k + 1 : ℕ) : ℚ) /
        (2 : ℚ) ^ (finiteScale p k (j + 1)) *
        (2 : ℚ) ^ (finiteClusterRadius p k (finiteScale p k j)) < 1 := by
  let R := finiteClusterRadius p k (finiteScale p k j)
  let C := scalePadding k
  have hRC : finiteScale p k (j + 1) = R + C := rfl
  have hq_nat : exponentBudget k + 1 < 2 ^ C := by
    have h : C < 2 ^ C := Nat.lt_two_pow_self
    dsimp [C, scalePadding] at h ⊢
    omega
  have hq : (((exponentBudget k + 1 : ℕ) : ℚ)) < (2 : ℚ) ^ C := by
    exact_mod_cast hq_nat
  have hR : (0 : ℚ) < (2 : ℚ) ^ R := by positivity
  have hC : (0 : ℚ) < (2 : ℚ) ^ C := by positivity
  rw [hRC, pow_add]
  change ((exponentBudget k + 1 : ℕ) : ℚ) /
      ((2 : ℚ) ^ R * (2 : ℚ) ^ C) * (2 : ℚ) ^ R < 1
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (mul_pos hR hC)).mpr
  nlinarith [mul_lt_mul_of_pos_right hq hR]

/-- The same spacing estimate applied to a supplied error bound. -/
theorem finiteScale_grid_close (p k j : ℕ) {x y : ℚ}
    (hclose : |x - y| ≤
      ((exponentBudget k + 1 : ℕ) : ℚ) /
        (2 : ℚ) ^ (finiteScale p k (j + 1))) :
    |x - y| * (2 : ℚ) ^ (finiteClusterRadius p k (finiteScale p k j)) < 1 := by
  have hR : (0 : ℚ) <
      (2 : ℚ) ^ (finiteClusterRadius p k (finiteScale p k j)) := by positivity
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hclose hR.le)
    (finiteScale_error_lt_grid p k j)

end AntichainOfGivenSize.BlockCount
