import AntichainOfGivenSize.Analysis.Paper.BasicResults
import AntichainOfGivenSize.Analysis.Paper.Scale
import AntichainOfGivenSize.Analysis.Supporting.RangeReduction

/-! The explicit quadratic upper bound in Section 5. The matching
construction is the sole hypothesis and is discharged in the assembly. -/

namespace AntichainOfGivenSize.Paper

def BitMatchingStatement : Prop :=
  ∀ q y : ℕ, 0 < q → ∃ m : ℕ,
    0 < m ∧ m < 2 ^ (2 ^ (q + 1)) ∧
      Nat.ModEq (2 ^ (2 ^ q)) m y ∧ alpha m ≤ 2 * q

def doubleTower (q : ℕ) : ℕ := 2 ^ (2 ^ q)

theorem doubleTower_succ (q : ℕ) :
    doubleTower (q + 1) = doubleTower q * doubleTower q := by
  unfold doubleTower
  rw [show 2 ^ (q + 1) = 2 ^ q * 2 by rw [pow_succ], pow_mul, pow_two]

theorem first_one_step (hmatch : BitMatchingStatement)
    {q n : ℕ} (hq : 0 < q) (hn : doubleTower (q + 1) ≤ n) :
    ∃ k : ℕ, 0 < k ∧ doubleTower q * k ≤ n ∧ alpha n ≤ 2 * q + alpha k := by
  obtain ⟨m, hm, hmhi, hmod, hma⟩ := hmatch q (n + 1) hq
  have hmn : m < n := hmhi.trans_le hn
  obtain ⟨k, hk, heq⟩ := exists_positive_quotient_of_modEq_succ hm hmn hmod
  refine ⟨k, hk, ?_, ?_⟩
  · change 2 ^ (2 ^ q) * k ≤ n
    omega
  · exact (alpha_le_of_block_decomposition hm hmn heq).trans (by omega)

/-- At most two applications move to the previous double-exponential range. -/
theorem first_range_reduction (hmatch : BitMatchingStatement)
    {q n : ℕ} (hq : 0 < q)
    (hnlo : doubleTower (q + 1) ≤ n) (hnhi : n < doubleTower (q + 2)) :
    ∃ k : ℕ, 0 < k ∧ k < doubleTower (q + 1) ∧ alpha n ≤ 4 * q + alpha k := by
  obtain ⟨k, hk, hkprod, hka⟩ := first_one_step hmatch hq hnlo
  by_cases hkhi : k < doubleTower (q + 1)
  · exact ⟨k, hk, hkhi, by omega⟩
  · obtain ⟨k', hk', hk'prod, hk'a⟩ := first_one_step hmatch hq (by omega : doubleTower (q + 1) ≤ k)
    have hprod : doubleTower (q + 1) * k' ≤ n := by
      rw [doubleTower_succ, mul_assoc]
      exact (Nat.mul_le_mul_left _ hk'prod).trans hkprod
    have hk'hi : k' < doubleTower (q + 1) := by
      by_contra h
      have hle := (Nat.mul_le_mul_left (doubleTower (q + 1)) (show doubleTower (q + 1) ≤ k' by omega)).trans hprod
      have ht : doubleTower (q + 2) = doubleTower (q + 1) * doubleTower (q + 1) :=
        doubleTower_succ (q + 1)
      omega
    exact ⟨k', hk', hk'hi, by omega⟩

/-- The slightly stronger cumulative induction statement includes every
smaller input, so it also covers transitions across several ranges. -/
theorem first_upper_cumulative (hmatch : BitMatchingStatement) (q : ℕ) :
    ∀ n : ℕ, n < doubleTower (q + 2) → alpha n ≤ 4 * q ^ 2 + 3 := by
  induction q with
  | zero =>
      intro n hn
      have hn16 : n ≤ 16 := by norm_num [doubleTower] at hn; omega
      simpa using alpha_le_three_of_le_sixteen hn16
  | succ q ih =>
      intro n hn
      have hpoly : 4 * (q + 1) ^ 2 + 3 = 4 * q ^ 2 + 3 + 8 * q + 4 := by ring
      by_cases hlo : n < doubleTower (q + 2)
      · have h := ih n hlo
        change alpha n ≤ 4 * (q + 1) ^ 2 + 3
        rw [hpoly]
        omega
      · obtain ⟨k, _, hkhi, hka⟩ := first_range_reduction hmatch
          (by omega : 0 < q + 1)
          (by simpa only [Nat.add_assoc, show 1 + 1 = 2 by decide] using Nat.le_of_not_gt hlo) hn
        have h := ih k (by simpa only [Nat.add_assoc, show 1 + 1 = 2 by decide] using hkhi)
        change alpha n ≤ 4 * (q + 1) ^ 2 + 3
        rw [hpoly]
        omega

/-- Theorem 5.1, including its exact constant and range endpoints. -/
theorem first_upper (hmatch : BitMatchingStatement) (q n : ℕ)
    (_hnlo : 2 ^ (2 ^ (q + 1)) ≤ n) (hnhi : n < 2 ^ (2 ^ (q + 2))) :
    alpha n ≤ 4 * q ^ 2 + 3 :=
  first_upper_cumulative hmatch q n hnhi

/-- The asymptotic conclusion of Theorem 5.1 follows already from the
bit-matching construction, independently of the sharp upper bound. -/
theorem quadratic_upper_of_matching (hmatch : BitMatchingStatement) :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ ↦ (alpha n : ℝ))
      (fun n : ℕ ↦ (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 2) := by
  apply Asymptotics.IsBigO.of_bound 7
  filter_upwards [Filter.eventually_ge_atTop 5,
    (tendsto_loglog.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 1)] with n hn hQ
  change 1 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) at hQ
  let Q := Real.logb 2 (Real.logb 2 (n : ℝ))
  let q : ℕ := ⌊Q⌋₊
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL0 : 0 < Real.logb 2 (n : ℝ) :=
    Real.logb_pos one_lt_two (by exact_mod_cast (show 1 < n by omega))
  have hqlo : (q : ℝ) ≤ Q := Nat.floor_le (by dsimp [Q]; linarith)
  have hqhi : Q < ((q + 2 : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one Q
    dsimp [q]
    push_cast
    linarith
  have hLhi : Real.logb 2 (n : ℝ) < (2 : ℝ) ^ (q + 2) := by
    have h := Real.rpow_lt_rpow_of_exponent_lt one_lt_two hqhi
    rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hL0,
      Real.rpow_natCast] at h
    exact h
  have hnhi : n < doubleTower (q + 2) := by
    have h := Real.rpow_lt_rpow_of_exponent_lt one_lt_two hLhi
    rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hn0] at h
    have hcast : (n : ℝ) < ((2 ^ (2 ^ (q + 2)) : ℕ) : ℝ) := by
      convert h using 1
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    exact_mod_cast hcast
  have ha : (alpha n : ℝ) ≤ 4 * (q : ℝ) ^ 2 + 3 := by
    exact_mod_cast first_upper_cumulative hmatch q n hnhi
  have hsq : (q : ℝ) ^ 2 ≤ Q ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg q) (by dsimp [Q]; linarith)).mpr hqlo
  have hbound : (alpha n : ℝ) ≤ 7 * Q ^ 2 := by
    have hQ' : 1 ≤ Q := hQ
    nlinarith
  change ‖(alpha n : ℝ)‖ ≤ 7 * ‖Q ^ 2‖
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (alpha n) : (0 : ℝ) ≤ alpha n),
    abs_of_nonneg (sq_nonneg Q)] using hbound

end AntichainOfGivenSize.Paper
