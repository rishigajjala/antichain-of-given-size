import AntichainOfGivenSize.BasicLemmas
import AntichainOfGivenSize.BlockCount.Binary

namespace AntichainOfGivenSize

/-- A power of two has a one-generator representation. -/
theorem alpha_two_pow_le_one (t : ℕ) : alpha (2 ^ t) ≤ 1 := by
  simpa using (liftingLemma t 1).trans (alpha_le_self 1)

/-- A nonempty string of `1` bits needs at most two generators. -/
theorem alpha_two_pow_sub_one_le_two (t : ℕ) : alpha (2 ^ t - 1) ≤ 2 := by
  cases t with
  | zero =>
      change alpha 0 ≤ 2
      exact (alpha_le_self 0).trans (by omega)
  | succ t =>
      have hp : 0 < 2 ^ t := by positivity
      have heq : 2 ^ (t + 1) - 1 = 2 ^ t + (2 ^ t - 1) := by
        rw [pow_succ]
        omega
      rw [heq]
      have h := splittingLemma (2 ^ t) (2 ^ t - 1) hp
      have hsucc : 2 ^ t - 1 + 1 = 2 ^ t := by omega
      rw [hsucc] at h
      exact h.trans (by have h1 := alpha_two_pow_le_one t; omega)

private def appendOnes : ℕ → ℕ → ℕ
  | 0, n => n
  | t + 1, n => Nat.bit true (appendOnes t n)

private theorem appendOnes_bit_true (t n : ℕ) :
    appendOnes t (Nat.bit true n) = appendOnes (t + 1) n := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [appendOnes, ih]

private theorem appendOnes_eq (t n : ℕ) :
    appendOnes t n = 2 ^ t * n + (2 ^ t - 1) := by
  induction t with
  | zero => simp [appendOnes]
  | succ t ih =>
      have hp : 0 < 2 ^ t := by positivity
      simp only [appendOnes, Nat.bit_val, Bool.toNat_true, ih, pow_succ]
      have hsub : 2 ^ t - 1 + 1 = 2 ^ t := by omega
      have hsub2 : 2 ^ t * 2 - 1 + 1 = 2 ^ t * 2 := by omega
      have hmul : 2 ^ t * 2 * n = 2 * (2 ^ t * n) := by ring
      rw [hmul]
      omega

private theorem appendOnes_bodd (t n : ℕ) (ht : 0 < t) :
    (appendOnes t n).bodd = true := by
  cases t with
  | zero => omega
  | succ t => simp [appendOnes]

private theorem binaryBlockCount_appendOnes (t n : ℕ) (ht : 0 < t) :
    binaryBlockCount (appendOnes t n) =
      binaryBlockCount n + if !n.bodd then 1 else 0 := by
  cases t with
  | zero => omega
  | succ t =>
      induction t with
      | zero =>
          simpa only [appendOnes] using binaryBlockCount_bit_true n
      | succ t ih =>
          rw [appendOnes, binaryBlockCount_bit_true,
            appendOnes_bodd (t + 1) n (by omega)]
          simpa using ih (by omega)

private theorem alpha_appendOnes_le (t n : ℕ) (hn : 0 < n) :
    alpha (appendOnes t n) ≤ alpha n + 1 := by
  rw [appendOnes_eq]
  have hp : 0 < 2 ^ t := by positivity
  have h := splittingLemma (2 ^ t * n) (2 ^ t - 1) (by positivity)
  have hsucc : 2 ^ t - 1 + 1 = 2 ^ t := by omega
  rw [hsucc] at h
  have hl := liftingLemma t n
  have h1 := alpha_two_pow_le_one t
  omega

private theorem alpha_appendOnes_binaryBlockCount (n : ℕ) :
    ∀ t, alpha (appendOnes t n) ≤ binaryBlockCount (appendOnes t n) + 1 := by
  induction n using Nat.binaryRec' with
  | zero =>
      intro t
      cases t with
      | zero =>
          change alpha 0 ≤ 1
          exact (alpha_le_self 0).trans (by omega)
      | succ t =>
          have ha := alpha_two_pow_sub_one_le_two (t + 1)
          have hb := binaryBlockCount_appendOnes (t + 1) 0 (by omega)
          simp only [appendOnes_eq, Nat.mul_zero, Nat.zero_add] at ha ⊢
          rw [appendOnes_eq] at hb
          simp only [Nat.mul_zero, Nat.zero_add, binaryBlockCount_zero,
            Nat.bodd_zero, Bool.not_false, if_true] at hb
          omega
  | bit b n h ih =>
      intro t
      cases b with
      | true => simpa only [appendOnes_bit_true] using ih (t + 1)
      | false =>
          have hn : 0 < n := by
            by_contra hn
            have hz : n = 0 := by omega
            exact Bool.false_ne_true (h hz)
          cases t with
          | zero =>
              have hl : alpha (Nat.bit false n) ≤ alpha n := by
                simpa [Nat.bit_val] using liftingLemma 1 n
              have hi := ih 0
              simpa only [appendOnes, binaryBlockCount_bit_false] using hl.trans hi
          | succ t =>
              have ha := alpha_appendOnes_le (t + 1) (Nat.bit false n)
                (by simp [Nat.bit_val]; omega)
              have hl : alpha (Nat.bit false n) ≤ alpha n := by
                simpa [Nat.bit_val] using liftingLemma 1 n
              have hi := ih 0
              have hb := binaryBlockCount_appendOnes (t + 1) (Nat.bit false n)
                (by omega)
              simp only [appendOnes] at hi
              simp only [Nat.bodd_bit, Bool.not_false,
                if_true, binaryBlockCount_bit_false] at hb
              omega

/-- The elementary block-count upper bound, including the harmless zero case. -/
theorem alpha_le_binaryBlockCount_add_one (n : ℕ) :
    alpha n ≤ binaryBlockCount n + 1 := by
  simpa only [appendOnes] using alpha_appendOnes_binaryBlockCount n 0

end AntichainOfGivenSize
