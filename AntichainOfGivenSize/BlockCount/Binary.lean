import AntichainOfGivenSize.LowerBound.BinaryBlocks

namespace AntichainOfGivenSize

/-- Appending zero bits preserves the number of maximal `1`-blocks. -/
@[simp] theorem binaryBlockCount_two_pow_mul (t n : ℕ) :
    binaryBlockCount (2 ^ t * n) = binaryBlockCount n := by
  induction t with
  | zero => simp
  | succ t ih =>
      have heq : 2 ^ (t + 1) * n = Nat.bit false (2 ^ t * n) := by
        simp [Nat.bit_val, pow_succ]
        ring
      rw [heq, binaryBlockCount_bit_false, ih]

/-- At least two appended positions separate a new terminal `1`-block. -/
theorem binaryBlockCount_two_pow_mul_add_one (t n : ℕ) (ht : 2 ≤ t) :
    binaryBlockCount (2 ^ t * n + 1) = binaryBlockCount n + 1 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  have heq : 2 ^ (s + 2) * n + 1 =
      Nat.bit true (Nat.bit false (2 ^ s * n)) := by
    simp [Nat.bit_val, pow_succ]
    ring
  rw [heq, binaryBlockCount_bit_true, binaryBlockCount_bit_false,
    binaryBlockCount_two_pow_mul]
  simp only [Nat.bodd_bit, Bool.not_false, if_true]

end AntichainOfGivenSize
