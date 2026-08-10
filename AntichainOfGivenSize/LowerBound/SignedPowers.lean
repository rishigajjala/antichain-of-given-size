import AntichainOfGivenSize.LowerBound.BinaryBlocks
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace AntichainOfGivenSize

/-!
# Signed sums of powers of two

This is the arithmetic content of Observation 3.4 in the paper.  Positive and
negative summands are grouped separately, which keeps all intermediate
subtractions in `ℕ` and makes the no-underflow conditions explicit.
-/

/-- The natural-number sum of a list of powers of two. -/
def binaryPowerSum (exponents : List ℕ) : ℕ :=
  (exponents.map fun y ↦ 2 ^ y).sum

@[simp] theorem binaryPowerSum_nil : binaryPowerSum [] = 0 := rfl

@[simp] theorem binaryPowerSum_cons (y : ℕ) (ys : List ℕ) :
    binaryPowerSum (y :: ys) = 2 ^ y + binaryPowerSum ys := by
  simp [binaryPowerSum]

theorem binaryBlockCount_powerSum_le_length (exponents : List ℕ) :
    binaryBlockCount (binaryPowerSum exponents) ≤ exponents.length := by
  induction exponents with
  | nil => simp
  | cons y ys ih =>
      rw [binaryPowerSum_cons, Nat.add_comm]
      calc
        binaryBlockCount (binaryPowerSum ys + 2 ^ y) ≤
            binaryBlockCount (binaryPowerSum ys) + 1 :=
          binaryBlockCount_add_pow (binaryPowerSum ys) y
        _ ≤ ys.length + 1 := Nat.add_le_add_right ih 1
        _ = (y :: ys).length := by simp

theorem binaryBlockCount_sub_powerSum (n : ℕ) (exponents : List ℕ)
    (h : binaryPowerSum exponents ≤ n) :
    binaryBlockCount (n - binaryPowerSum exponents) ≤
      binaryBlockCount n + exponents.length := by
  induction exponents generalizing n with
  | nil => simp
  | cons y ys ih =>
      rw [binaryPowerSum_cons] at h ⊢
      have hy : 2 ^ y ≤ n := le_trans (Nat.le_add_right _ _) h
      have hys : binaryPowerSum ys ≤ n - 2 ^ y := by omega
      rw [Nat.sub_add_eq]
      exact (ih (n - 2 ^ y) hys).trans
        (by
          have hp := binaryBlockCount_sub_pow n y hy
          simp only [List.length_cons]
          omega)

/-- Observation 3.4 in grouped form: a positive signed sum of `t` powers of
two has at most `t` binary `1`-blocks.  The equation says that the positive
sum minus the negative sum is `k`. -/
theorem binaryBlockCount_signedPowerSums (k : ℕ)
    (positive negative : List ℕ)
    (h : binaryPowerSum positive = k + binaryPowerSum negative) :
    binaryBlockCount k ≤ positive.length + negative.length := by
  have hle : binaryPowerSum negative ≤ binaryPowerSum positive := by omega
  have hsub : binaryPowerSum positive - binaryPowerSum negative = k := by omega
  rw [← hsub]
  exact (binaryBlockCount_sub_powerSum
      (binaryPowerSum positive) negative hle).trans
    (Nat.add_le_add_right
      (binaryBlockCount_powerSum_le_length positive) negative.length)

lemma binaryPowerSum_toList_map {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (exponent : ι → ℕ) :
    binaryPowerSum (s.toList.map exponent) =
      ∑ i ∈ s, 2 ^ exponent i := by
  simp [binaryPowerSum]

/-- Finset-facing form of Observation 3.4, used for the terms in
inclusion-exclusion. -/
theorem binaryBlockCount_signedPowerFinsets
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (k : ℕ) (positive : Finset ι) (negative : Finset κ)
    (positiveExponent : ι → ℕ) (negativeExponent : κ → ℕ)
    (h : (∑ i ∈ positive, 2 ^ positiveExponent i) =
      k + ∑ i ∈ negative, 2 ^ negativeExponent i) :
    binaryBlockCount k ≤ positive.card + negative.card := by
  have hlist :
      binaryPowerSum (positive.toList.map positiveExponent) =
        k + binaryPowerSum (negative.toList.map negativeExponent) := by
    simpa only [binaryPowerSum_toList_map] using h
  simpa using binaryBlockCount_signedPowerSums k
    (positive.toList.map positiveExponent)
    (negative.toList.map negativeExponent) hlist

end AntichainOfGivenSize
