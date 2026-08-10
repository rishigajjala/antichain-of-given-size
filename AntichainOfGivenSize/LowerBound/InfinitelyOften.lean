import AntichainOfGivenSize.LowerBound.IdealBlockCount

namespace AntichainOfGivenSize

/-!
# An infinitely-often log-log lower bound

The paper announces the asymptotic consequence but does not supply the
infinite family.  We use the explicit integers with binary expansions
`1`, `101`, `10101`, and so on.
-/

/-- `alternatingOnes r` has binary expansion `101...01`, containing `r + 1`
isolated `1`-bits. -/
def alternatingOnes : ℕ → ℕ
  | 0 => 1
  | r + 1 => 4 * alternatingOnes r + 1

@[simp] theorem alternatingOnes_zero : alternatingOnes 0 = 1 := rfl

@[simp] theorem alternatingOnes_succ (r : ℕ) :
    alternatingOnes (r + 1) = 4 * alternatingOnes r + 1 := rfl

theorem alternatingOnes_pos (r : ℕ) : 0 < alternatingOnes r := by
  induction r with
  | zero => simp
  | succ r ih => simp [alternatingOnes]

theorem alternatingOnes_ne_zero (r : ℕ) : alternatingOnes r ≠ 0 :=
  (alternatingOnes_pos r).ne'

theorem alternatingOnes_bits_succ (r : ℕ) :
    (alternatingOnes (r + 1)).bits =
      true :: false :: (alternatingOnes r).bits := by
  rw [alternatingOnes_succ]
  have hnum : 4 * alternatingOnes r + 1 =
      2 * (2 * alternatingOnes r) + 1 := by omega
  rw [hnum, Nat.bit1_bits, Nat.bit0_bits _ (alternatingOnes_ne_zero r)]

@[simp] theorem alternatingOnes_bitLength (r : ℕ) :
    (alternatingOnes r).bits.length = 2 * r + 1 := by
  induction r with
  | zero => simp [Nat.one_bits]
  | succ r ih =>
      rw [alternatingOnes_bits_succ]
      simp [ih]
      omega

@[simp] theorem binaryBlockCount_alternatingOnes (r : ℕ) :
    binaryBlockCount (alternatingOnes r) = r + 1 := by
  induction r with
  | zero => norm_num [alternatingOnes, binaryBlockCount, Nat.binaryRec]
  | succ r ih =>
      rw [alternatingOnes_succ]
      have hnum : 4 * alternatingOnes r + 1 =
          Nat.bit true (Nat.bit false (alternatingOnes r)) := by
        norm_num [Nat.bit_val]
        omega
      rw [hnum, binaryBlockCount_bit_true, binaryBlockCount_bit_false, ih]
      simp

theorem alternatingOnes_lt_pow (r : ℕ) :
    alternatingOnes r < 2 ^ (2 * (r + 1)) := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      rw [alternatingOnes_succ]
      calc
        4 * alternatingOnes r + 1 < 4 * 2 ^ (2 * (r + 1)) := by omega
        _ = 2 ^ (2 * (r + 1 + 1)) := by ring

theorem index_le_alternatingOnes (r : ℕ) : r + 1 ≤ alternatingOnes r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [alternatingOnes_succ]
      omega

/-- On the explicit alternating-bit sequence, `alpha` is at least half the
iterated base-2 logarithm. -/
theorem alternatingOnes_logLog_lower (r : ℕ) (hr : 1 ≤ r) :
    (1 / 2 : ℝ) *
        Real.logb 2 (Real.logb 2 (alternatingOnes r : ℝ)) ≤
      (alpha (alternatingOnes r) : ℝ) := by
  have hnPos : (0 : ℝ) < alternatingOnes r := by
    exact_mod_cast alternatingOnes_pos r
  have hnOne : (1 : ℝ) < alternatingOnes r := by
    have : 1 < alternatingOnes r := by
      cases r with
      | zero => omega
      | succ r =>
          rw [alternatingOnes_succ]
          have := alternatingOnes_pos r
          omega
    exact_mod_cast this
  have hpowNat := alternatingOnes_lt_pow r
  have hpowReal :
      (alternatingOnes r : ℝ) ≤ (2 : ℝ) ^ (2 * (r + 1)) := by
    exact_mod_cast hpowNat.le
  have hlogInnerPos : 0 < Real.logb 2 (alternatingOnes r : ℝ) :=
    Real.logb_pos (by norm_num) hnOne
  have hlogFirst :
      Real.logb 2 (alternatingOnes r : ℝ) ≤ (2 * (r + 1) : ℕ) := by
    calc
      Real.logb 2 (alternatingOnes r : ℝ) ≤
          Real.logb 2 ((2 : ℝ) ^ (2 * (r + 1))) :=
        Real.logb_le_logb_of_le (by norm_num) hnPos hpowReal
      _ = (2 * (r + 1) : ℕ) := by
        rw [Real.logb_pow]
        norm_num [Real.logb_self_eq_one]
  have hlogSecond :
      Real.logb 2 (Real.logb 2 (alternatingOnes r : ℝ)) ≤
        Real.logb 2 ((2 * (r + 1) : ℕ) : ℝ) := by
    exact Real.logb_le_logb_of_le (by norm_num) hlogInnerPos
      (by exact_mod_cast hlogFirst)
  have hlogMul :
      Real.logb 2 ((2 * (r + 1) : ℕ) : ℝ) =
        1 + Real.logb 2 ((r + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
    rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  have hmono :
      Real.logb 2 ((r + 1 : ℕ) : ℝ) ≤
        Real.logb 2 ((r + 2 : ℕ) : ℝ) := by
    apply Real.logb_le_logb_of_le (by norm_num)
    · positivity
    · exact_mod_cast Nat.le_succ (r + 1)
  have hone : (1 : ℝ) ≤ Real.logb 2 ((r + 2 : ℕ) : ℝ) := by
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    apply Real.logb_le_logb_of_le (by norm_num)
    · norm_num
    · exact_mod_cast (show 2 ≤ r + 2 by omega)
  have hscale :
      Real.logb 2 (Real.logb 2 (alternatingOnes r : ℝ)) ≤
        2 * Real.logb 2 ((r + 2 : ℕ) : ℝ) := by
    rw [hlogMul] at hlogSecond
    linarith
  have hlower := logb_binaryBlockCount_le_alpha (alternatingOnes r)
  rw [binaryBlockCount_alternatingOnes] at hlower
  have hlower' :
      Real.logb 2 ((r + 2 : ℕ) : ℝ) ≤
        (alpha (alternatingOnes r) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc,
      one_add_one_eq_two] using hlower
  linarith

/-- There are arbitrarily large `n` for which `alpha n` is at least half of
`log₂(log₂ n)`.  This is an explicit infinitely-often
`Ω(log log n)` lower bound. -/
theorem logLog_lower_infinitely_often :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) ≤
        (alpha n : ℝ) := by
  intro N
  refine ⟨alternatingOnes (N + 1), ?_, ?_⟩
  · exact (Nat.le_add_right N 2).trans
      (index_le_alternatingOnes (N + 1))
  · exact alternatingOnes_logLog_lower (N + 1) (by omega)

/-- A named proposition for an infinitely-often `Ω(log log n)` lower
bound. -/
def HasLogLogLowerBoundInfinitelyOften : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    c * Real.logb 2 (Real.logb 2 (n : ℝ)) ≤ (alpha n : ℝ)

theorem hasLogLogLowerBoundInfinitelyOften :
    HasLogLogLowerBoundInfinitelyOften := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  exact logLog_lower_infinitely_often

end AntichainOfGivenSize
