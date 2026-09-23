import AntichainOfGivenSize.BlockCount.Upper
import AntichainOfGivenSize.BlockCount.ScaledIdeals

namespace AntichainOfGivenSize.BlockCount

/-- The dyadic cost reduction needed to construct extremal block-count witnesses.
The appended gap may depend on the old integer and the proposed cost. -/
def DyadicCostReduction : Prop :=
  ∀ p k : ℕ, 0 < p → 0 < k →
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      HasDyadicIdealSum ((2 ^ t * p + 1 : ℕ) : ℚ) k →
        HasDyadicIdealSum (p : ℚ) (k - 1)

/-- Starting from three, append sufficiently long zero gaps and a final one.
The new number has one additional block and requires one additional unit of
scaled ideal cost. -/
theorem exists_block_witness_of_costReduction
    (hreduce : DyadicCostReduction) (b : ℕ) :
    ∃ n : ℕ, 0 < n ∧ binaryBlockCount n = b + 1 ∧
      ¬ HasDyadicIdealSum (n : ℚ) (b + 1) := by
  induction b with
  | zero =>
      refine ⟨3, by omega, ?_, ?_⟩
      · change binaryBlockCount (Nat.bit true (Nat.bit true 0)) = 1
        rw [binaryBlockCount_bit_true, binaryBlockCount_bit_true]
        norm_num
      · simpa using not_hasDyadicIdealSum_three_one
  | succ b ih =>
      rcases ih with ⟨n, hn, hblocks, hcost⟩
      obtain ⟨T, hT⟩ := hreduce n (b + 2) hn (by omega)
      let t : ℕ := max T 2
      refine ⟨2 ^ t * n + 1, by omega, ?_, ?_⟩
      · rw [binaryBlockCount_two_pow_mul_add_one t n (by simp [t]), hblocks]
      · intro hnew
        have hold := hT t (by simp [t]) hnew
        have hsub : b + 2 - 1 = b + 1 := by omega
        rw [hsub] at hold
        exact hcost hold

/-- The standard alpha witness transfers the strict scaled-cost lower bound
back to the ordinary minimum number of generators. -/
theorem exists_alpha_block_witness_of_costReduction
    (hreduce : DyadicCostReduction) (b : ℕ) :
    ∃ n : ℕ, 0 < n ∧ binaryBlockCount n = b + 1 ∧ alpha n = b + 2 := by
  obtain ⟨n, hn, hblocks, hcost⟩ :=
    exists_block_witness_of_costReduction hreduce b
  refine ⟨n, hn, hblocks, ?_⟩
  have hupper := alpha_le_binaryBlockCount_add_one n
  rw [hblocks] at hupper
  have hlower : b + 1 < alpha n := by
    by_contra h
    have hle : alpha n ≤ b + 1 := by omega
    exact hcost ((hasDyadicIdealSum_alpha n hn).mono hle)
  omega

/-- Conditional attainment of the sharp upper bound for every positive
number of binary blocks. The analytic cost-reduction theorem is the sole
hypothesis of this combinatorial recursion. -/
theorem exists_alpha_eq_blockCount_add_one_of_costReduction
    (hreduce : DyadicCostReduction) (b : ℕ) (hb : 0 < b) :
    ∃ n : ℕ, 0 < n ∧ binaryBlockCount n = b ∧ alpha n = b + 1 := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
    exists_alpha_block_witness_of_costReduction hreduce c

/-- The exact extremal statement, with the upper bound included in the contract. -/
theorem blockCount_bound_tight_of_costReduction
    (hreduce : DyadicCostReduction) (b : ℕ) (hb : 0 < b) :
    (∀ n : ℕ, binaryBlockCount n = b → alpha n ≤ b + 1) ∧
      ∃ n : ℕ, 0 < n ∧ binaryBlockCount n = b ∧ alpha n = b + 1 := by
  constructor
  · intro n hn
    simpa only [hn] using alpha_le_binaryBlockCount_add_one n
  · exact exists_alpha_eq_blockCount_add_one_of_costReduction hreduce b hb

end AntichainOfGivenSize.BlockCount
