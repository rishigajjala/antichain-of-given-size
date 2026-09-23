import AntichainOfGivenSize.BlockCount.FiniteScales
import AntichainOfGivenSize.BlockCount.SingletonBound

/-!
# One empty band for every component of a scaled representation

The finite exponent set includes every singleton and every ordered pair from
one component. Hence one missing band works for all of them simultaneously.
-/

namespace AntichainOfGivenSize.BlockCount

/-- The chosen empty band gives the singleton and within-component pair
dichotomies required by the cluster construction. -/
theorem exists_gap_for_terms (terms : List DyadicIdeal) (p t k : ℕ)
    (hcost : (terms.map DyadicIdeal.cost).sum ≤ k) :
    ∃ j : ℕ, j ≤ exponentBudget k ∧
      (∀ D ∈ terms, ∀ A ∈ D.generators,
        -(finiteScale p k j : ℤ) ≤
            (A.card : ℤ) + (D.exponent - (t : ℤ)) ∨
          (A.card : ℤ) + (D.exponent - (t : ℤ)) <
            -(finiteScale p k (j + 1) : ℤ)) ∧
      (∀ D ∈ terms, ∀ A ∈ D.generators, ∀ B ∈ D.generators,
        -(finiteScale p k j : ℤ) ≤
            ((A ∩ B).card : ℤ) + (D.exponent - (t : ℤ)) ∨
          ((A ∩ B).card : ℤ) + (D.exponent - (t : ℤ)) <
            -(finiteScale p k (j + 1) : ℤ)) := by
  obtain ⟨j, hj, hgap⟩ :=
    exists_empty_exponent_band_of_cost terms t k hcost
      (finiteScale p k) (finiteScale_mono p k)
  refine ⟨j, hj, ?_, ?_⟩
  · intro D hD A hA
    have h := hgap (singletonExponent D t A)
      (singletonExponent_mem terms t D hD A hA)
    simpa only [singletonExponent, add_sub_assoc] using h
  · intro D hD A hA B hB
    have h := hgap (pairExponent D t A B)
      (pairExponent_mem terms t D hD A B hA hB)
    simpa only [pairExponent, add_sub_assoc] using h

/-- Every singleton exponent in a representation of `2^t p+1` is below the
coarse budget `p+1`, expressed with the normalized component offset. -/
theorem singleton_upper_for_terms (terms : List DyadicIdeal) (p t : ℕ)
    (hvalue : (terms.map DyadicIdeal.value).sum = ((2 ^ t * p + 1 : ℕ) : ℚ)) :
    ∀ D ∈ terms, ∀ A ∈ D.generators,
      (A.card : ℤ) + (D.exponent - (t : ℤ)) ≤ (p + 1 : ℕ) := by
  intro D hD A hA
  have h := singletonExponent_le_of_sum terms p t hvalue D hD A hA
  simpa only [singletonExponent, Nat.cast_add, Nat.cast_one, add_sub_assoc] using h

end AntichainOfGivenSize.BlockCount
