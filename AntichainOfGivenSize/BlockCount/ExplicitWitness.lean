import AntichainOfGivenSize.BlockCount.Tight

/-!
# An explicit extremal integer for each positive block count

Starting with `n₁ = 3`, append one bit after a gap whose length is the explicit
finite threshold for the preceding integer. The resulting integer with `b`
binary blocks has minimum generator count exactly `b + 1`.
-/

namespace AntichainOfGivenSize.BlockCount

@[simp] theorem explicitBlockWitness_zero : explicitBlockWitness 0 = 0 := rfl

@[simp] theorem explicitBlockWitness_one : explicitBlockWitness 1 = 3 := rfl

/-- The positive-index recurrence is exactly a binary shift followed by one. -/
theorem explicitBlockWitness_succ (b : ℕ) (hb : 0 < b) :
    explicitBlockWitness (b + 1) =
      2 ^ explicitWitnessShift b * explicitBlockWitness b + 1 := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  rfl

/-- At each stage, the explicit integer has the required number of blocks
and cannot be represented at the smaller scaled-ideal cost. -/
theorem explicitBlockWitness_invariant (b : ℕ) :
    0 < explicitBlockWitness (b + 1) ∧
      binaryBlockCount (explicitBlockWitness (b + 1)) = b + 1 ∧
      ¬ HasDyadicIdealSum (explicitBlockWitness (b + 1) : ℚ) (b + 1) := by
  induction b with
  | zero =>
      refine ⟨by norm_num, ?_, ?_⟩
      · change binaryBlockCount (Nat.bit true (Nat.bit true 0)) = 1
        rw [binaryBlockCount_bit_true, binaryBlockCount_bit_true]
        norm_num
      · simpa only [Nat.zero_add, explicitBlockWitness_one, Nat.cast_ofNat] using
          not_hasDyadicIdealSum_three_one
  | succ b ih =>
      rcases ih with ⟨hn, hblocks, hcost⟩
      let n := explicitBlockWitness (b + 1)
      let t := explicitWitnessShift (b + 1)
      have ht : 2 ≤ t := le_max_left _ _
      have hthreshold : finiteThreshold n (b + 2) ≤ t := le_max_right _ _
      have hrec : explicitBlockWitness (b + 1 + 1) = 2 ^ t * n + 1 :=
        explicitBlockWitness_succ (b + 1) (by omega)
      change 0 < explicitBlockWitness (b + 1 + 1) ∧
        binaryBlockCount (explicitBlockWitness (b + 1 + 1)) = b + 1 + 1 ∧
        ¬ HasDyadicIdealSum (explicitBlockWitness (b + 1 + 1) : ℚ) (b + 1 + 1)
      rw [hrec]
      refine ⟨by omega, ?_, ?_⟩
      · rw [binaryBlockCount_two_pow_mul_add_one t n ht]
        exact congrArg (fun z => z + 1) hblocks
      · intro hnew
        have hold := finiteThreshold_costReduction_proved n (b + 2) t hthreshold hnew
        have hsub : b + 2 - 1 = b + 1 := by omega
        rw [hsub] at hold
        exact hcost hold

/-- Explicit attainment, including positivity of the produced integer. -/
theorem explicitBlockWitness_spec : ExplicitBlockWitnessStatement := by
  intro b hb
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  obtain ⟨hn, hblocks, hcost⟩ := explicitBlockWitness_invariant c
  refine ⟨hn, hblocks, ?_⟩
  change alpha (explicitBlockWitness (c + 1)) = c + 1 + 1
  have hupper := alpha_le_binaryBlockCount_add_one (explicitBlockWitness (c + 1))
  rw [hblocks] at hupper
  have hlower : c + 1 < alpha (explicitBlockWitness (c + 1)) := by
    by_contra h
    have hle : alpha (explicitBlockWitness (c + 1)) ≤ c + 1 := by omega
    exact hcost ((hasDyadicIdealSum_alpha _ hn).mono hle)
  omega

/-- The explicit witness has exactly its index in binary blocks. -/
theorem binaryBlockCount_explicitBlockWitness (b : ℕ) (hb : 0 < b) :
    binaryBlockCount (explicitBlockWitness b) = b :=
  (explicitBlockWitness_spec b hb).2.1

/-- Its minimum number of generators attains the universal upper bound. -/
theorem alpha_explicitBlockWitness (b : ℕ) (hb : 0 < b) :
    alpha (explicitBlockWitness b) = b + 1 :=
  (explicitBlockWitness_spec b hb).2.2

end AntichainOfGivenSize.BlockCount
