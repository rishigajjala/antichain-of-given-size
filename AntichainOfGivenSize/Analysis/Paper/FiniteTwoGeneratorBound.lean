import AntichainOfGivenSize.Analysis.Paper.BasicResults

namespace AntichainOfGivenSize.Paper

/-- The finite assertion in the base case of Theorem 5.1: every integer
in `[4,16)` except `13` has a generating family of at most two sets. -/
theorem alpha_le_two_of_base_range {n : ℕ}
    (hnlo : 4 ≤ n) (hnhi : n < 16) (hne : n ≠ 13) : alpha n ≤ 2 := by
  have h2 : alpha 2 ≤ 1 := by simpa using alpha_two_pow_le_one 1
  have h3 : alpha 3 ≤ 2 := by simpa using alpha_two_pow_sub_one_le_two 2
  have h4 : alpha 4 ≤ 1 := by simpa using alpha_two_pow_le_one 2
  have h5 : alpha 5 ≤ 2 := by
    calc
      alpha 5 ≤ alpha 4 + alpha 2 := splittingLemma 4 1 (by decide)
      _ ≤ 2 := by omega
  have h6 : alpha 6 ≤ 2 := (liftingLemma 1 3).trans h3
  have h7 : alpha 7 ≤ 2 := by simpa using alpha_two_pow_sub_one_le_two 3
  have h8 : alpha 8 ≤ 1 := by simpa using alpha_two_pow_le_one 3
  have h9 : alpha 9 ≤ 2 := by
    calc
      alpha 9 ≤ alpha 8 + alpha 2 := splittingLemma 8 1 (by decide)
      _ ≤ 2 := by omega
  have h10 : alpha 10 ≤ 2 := (liftingLemma 1 5).trans h5
  have h11 : alpha 11 ≤ 2 := by
    calc
      alpha 11 ≤ alpha 8 + alpha 4 := splittingLemma 8 3 (by decide)
      _ ≤ 2 := by omega
  have h12 : alpha 12 ≤ 2 := (liftingLemma 2 3).trans h3
  have h14 : alpha 14 ≤ 2 := (liftingLemma 1 7).trans h7
  have h15 : alpha 15 ≤ 2 := by simpa using alpha_two_pow_sub_one_le_two 4
  interval_cases n <;> omega

end AntichainOfGivenSize.Paper
