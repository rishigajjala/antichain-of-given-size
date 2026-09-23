import AntichainOfGivenSize.BlockCount.FiniteExponents

namespace AntichainOfGivenSize.BlockCount

/-- A positive component is bounded above by the sum containing it. -/
theorem component_value_le_sum_value (terms : List DyadicIdeal)
    (D : DyadicIdeal) (hD : D ∈ terms) :
    D.value ≤ (terms.map DyadicIdeal.value).sum := by
  apply List.single_le_sum
  · intro x hx
    rcases List.mem_map.mp hx with ⟨E, _, rfl⟩
    exact E.value_nonneg
  · exact List.mem_map.mpr ⟨D, hD, rfl⟩

/-- A generator cube is contained in its component's ideal. -/
theorem scaled_generator_cube_le_value (D : DyadicIdeal)
    (A : Finset ℕ) (hA : A ∈ D.generators) :
    (2 : ℚ) ^ D.exponent * (2 : ℚ) ^ A.card ≤ D.value := by
  have hsub : A.powerset ⊆ generatedIdeal D.generators := by
    intro X hX
    simp only [generatedIdeal, Finset.mem_biUnion]
    exact ⟨A, hA, hX⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_powerset] at hcard
  have hcast : (2 : ℚ) ^ A.card ≤ (generatedIdeal D.generators).card := by
    exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_left hcast (by positivity)

/-- Convert the normalized singleton exponent to the scaled cube size. -/
theorem singletonExponent_zpow_eq (D : DyadicIdeal) (t : ℕ) (A : Finset ℕ) :
    (2 : ℚ) ^ singletonExponent D t A =
      ((2 : ℚ) ^ D.exponent * (2 : ℚ) ^ A.card) / (2 : ℚ) ^ t := by
  simp only [singletonExponent, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
    zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
  ring

/-- Every normalized cube in a representation of `2^t*p+1` has size at most
`p+1`. This uses positivity and does not require a cost bound. -/
theorem singletonExponent_zpow_le_of_sum (terms : List DyadicIdeal)
    (p t : ℕ)
    (hvalue : (terms.map DyadicIdeal.value).sum = ((2 ^ t * p + 1 : ℕ) : ℚ))
    (D : DyadicIdeal) (hD : D ∈ terms)
    (A : Finset ℕ) (hA : A ∈ D.generators) :
    (2 : ℚ) ^ singletonExponent D t A ≤ (p : ℚ) + 1 := by
  have hc := (scaled_generator_cube_le_value D A hA).trans
    (component_value_le_sum_value terms D hD)
  rw [hvalue] at hc
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_one] at hc
  rw [singletonExponent_zpow_eq]
  have hp : 0 < (2 : ℚ) ^ t := by positivity
  apply (div_le_iff₀ hp).mpr
  have hone : (1 : ℚ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
  nlinarith

/-- A deliberately coarse integral upper bound for all singleton exponents.
It avoids introducing a logarithm into the finite gap argument. -/
theorem singletonExponent_le_of_sum (terms : List DyadicIdeal)
    (p t : ℕ)
    (hvalue : (terms.map DyadicIdeal.value).sum = ((2 ^ t * p + 1 : ℕ) : ℚ))
    (D : DyadicIdeal) (hD : D ∈ terms)
    (A : Finset ℕ) (hA : A ∈ D.generators) :
    singletonExponent D t A ≤ (p : ℤ) + 1 := by
  have hsmall := singletonExponent_zpow_le_of_sum terms p t hvalue D hD A hA
  have hnat : p + 1 ≤ 2 ^ (p + 1) := Nat.le_of_lt Nat.lt_two_pow_self
  have hpow : (p : ℚ) + 1 ≤ (2 : ℚ) ^ ((p : ℤ) + 1) := by
    have hc : ((p + 1 : ℕ) : ℚ) ≤ (2 : ℚ) ^ (p + 1 : ℕ) := by
      exact_mod_cast hnat
    simpa only [Nat.cast_add, Nat.cast_one, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0),
      zpow_natCast, zpow_one, pow_succ] using hc
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mp
    (hsmall.trans hpow)

/-- Expose a witness list together with the uniform singleton bound. -/
theorem HasDyadicIdealSum.exists_terms_with_singleton_bound
    {p t k : ℕ}
    (h : HasDyadicIdealSum ((2 ^ t * p + 1 : ℕ) : ℚ) k) :
    ∃ terms : List DyadicIdeal,
      (terms.map DyadicIdeal.value).sum = ((2 ^ t * p + 1 : ℕ) : ℚ) ∧
      (terms.map DyadicIdeal.cost).sum ≤ k ∧
      ∀ D ∈ terms, ∀ A ∈ D.generators,
        singletonExponent D t A ≤ (p : ℤ) + 1 := by
  rcases h with ⟨terms, hv, hk⟩
  exact ⟨terms, hv, hk, fun D hD A hA =>
    singletonExponent_le_of_sum terms p t hv D hD A hA⟩

end AntichainOfGivenSize.BlockCount
