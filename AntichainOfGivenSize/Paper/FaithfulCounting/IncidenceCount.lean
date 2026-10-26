import AntichainOfGivenSize.LowerBound.SparseEncoding
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators
open AntichainOfGivenSize.ClusterLowerBound

namespace AntichainOfGivenSize.FaithfulLower

/-- Every multiset of exactly `u` symbols has a listing of length `u`. -/
theorem sym_ofVector_surjective (α : Type*) (u : ℕ) :
    Function.Surjective (Sym.ofVector : List.Vector α u → Sym α u) := by
  intro s
  refine ⟨⟨s.1.toList, ?_⟩, ?_⟩
  · simp
  · apply Subtype.ext
    simp [Sym.ofVector]

/-- Forgetting the order of a word can only decrease the number of records. -/
theorem card_sym_le_words (α : Type*) [Fintype α] [DecidableEq α] (u : ℕ) :
    Fintype.card (Sym α u) ≤ (Fintype.card α) ^ u := by
  calc
    Fintype.card (Sym α u) ≤ Fintype.card (List.Vector α u) :=
      Fintype.card_le_of_surjective _ (sym_ofVector_surjective α u)
    _ = Fintype.card (Fin u → α) :=
      Fintype.card_congr (Equiv.vectorEquivFin α u)
    _ = (Fintype.card α) ^ u := Fintype.card_pi_const α u

/-- Multisets of at most `u` symbols: choose the mass and then a word.
The `none` symbols encode unused positions, not elements of the alphabet. -/
theorem card_sym_option_le_mass_words (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] (u : ℕ) :
    Fintype.card (Sym (Option α) u) ≤ (u + 1) * (Fintype.card α) ^ u := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Fintype.card_congr (symOptionSuccEquiv (α := α) (n := u)),
      Fintype.card_sum]
    have hpow : (Fintype.card α) ^ u ≤ (Fintype.card α) ^ (u + 1) :=
      Nat.pow_le_pow_right Fintype.card_pos (Nat.le_succ u)
    calc
      Fintype.card (Sym (Option α) u) + Fintype.card (Sym α (u + 1)) ≤
          (u + 1) * (Fintype.card α) ^ u + (Fintype.card α) ^ (u + 1) :=
        Nat.add_le_add ih (card_sym_le_words α (u + 1))
      _ ≤ (u + 1) * (Fintype.card α) ^ (u + 1) +
          (Fintype.card α) ^ (u + 1) := by gcongr
      _ = (u + 1 + 1) * (Fintype.card α) ^ (u + 1) := by ring

/-- The sharper bound applies to the existing `SparseCode` type unchanged.
Counts retain the multiplicity of each incidence pattern. -/
theorem card_sparseCode_le_mass_words (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] (u : ℕ) :
    Fintype.card (SparseCode α u) ≤ (u + 1) * (Fintype.card α) ^ u := by
  exact (Fintype.card_le_of_injective _ (SparseCode.toSym_injective u)).trans
    (card_sym_option_le_mass_words α u)

/-- Incidence patterns are subsets of the `K` generator indices. -/
theorem card_incidence_records_le (K u : ℕ) :
    Fintype.card (SparseCode (Finset (Fin K)) u) ≤ (u + 1) * 2 ^ (K * u) := by
  simpa [Fintype.card_finset, ← pow_mul] using
    card_sparseCode_le_mass_words (Finset (Fin K)) u

/-- The factor used in Section 9: the exception budget is at most both `KB`
and `2Kρ'`. Here `ρ` stands for the fine scale `ρ'`. -/
theorem card_incidence_records_real_le {K B u : ℕ} {ρ : ℝ}
    (huB : u ≤ K * B) (huρ : (u : ℝ) ≤ 2 * (K : ℝ) * ρ) :
    (Fintype.card (SparseCode (Finset (Fin K)) u) : ℝ) ≤
      ((K * B + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (K : ℝ) ^ 2 * ρ) := by
  have hc : (Fintype.card (SparseCode (Finset (Fin K)) u) : ℝ) ≤
      ((u + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (K * u) := by
    exact_mod_cast card_incidence_records_le K u
  rw [← Real.rpow_natCast] at hc
  have hfactor : ((u + 1 : ℕ) : ℝ) ≤ ((K * B + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right huB 1
  have hexponent : ((K * u : ℕ) : ℝ) ≤ 2 * (K : ℝ) ^ 2 * ρ := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left huρ (Nat.cast_nonneg K)]
  exact hc.trans (mul_le_mul hfactor
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent)
    (by positivity) (by positivity))


end AntichainOfGivenSize.FaithfulLower
