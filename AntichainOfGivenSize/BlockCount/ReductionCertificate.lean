import AntichainOfGivenSize.BlockCount.FiniteScales

/-!
# From a finite cluster certificate to a cost reduction

This lemma isolates the final arithmetic of the finite argument. A geometric
cluster construction supplies the listed hypotheses; the grid spacing then
forces the cluster sum to be exactly the leading integer coefficient.
-/

namespace AntichainOfGivenSize.BlockCount

/-- A finite cluster certificate, at one empty exponent band, reduces the
number of dyadically scaled generators required to represent `p`. -/
theorem hasDyadicIdealSum_of_cluster_certificate
    (p k t j : ℕ) (terms clusters : List DyadicIdeal)
    (hcost : (terms.map DyadicIdeal.cost).sum ≤ k)
    (hnormal : (2 : ℚ) ^ (-(t : ℤ)) *
        (terms.map DyadicIdeal.value).sum =
        (p : ℚ) + (2 : ℚ) ^ (-(t : ℤ)))
    (hclusterCost : (clusters.map DyadicIdeal.cost).sum ≤
        (terms.map DyadicIdeal.cost).sum)
    (hgrid : ∃ z : ℤ,
        (clusters.map DyadicIdeal.value).sum *
          (2 : ℚ) ^ (finiteClusterRadius p k (finiteScale p k j)) = z)
    (hclose : |(p : ℚ) - (clusters.map DyadicIdeal.value).sum| ≤
        ((exponentBudget k + 1 : ℕ) : ℚ) /
          (2 : ℚ) ^ (finiteScale p k (j + 1)))
    (hdrop : (clusters.map DyadicIdeal.cost).sum <
        (terms.map DyadicIdeal.cost).sum ∨
      (2 : ℚ) ^ (-(t : ℤ)) *
        (terms.map DyadicIdeal.value).sum ≤
          (clusters.map DyadicIdeal.value).sum) :
    HasDyadicIdealSum (p : ℚ) (k - 1) := by
  let R := finiteClusterRadius p k (finiteScale p k j)
  let D : ℕ := 2 ^ R
  have hD : 0 < D := by unfold D; positivity
  have hgridp : ∃ z : ℤ, (p : ℚ) * (D : ℚ) = z := by
    refine ⟨((p * D : ℕ) : ℤ), ?_⟩
    norm_cast
  have hgridS : ∃ z : ℤ,
      (clusters.map DyadicIdeal.value).sum * (D : ℚ) = z := by
    simpa only [D, Nat.cast_pow, Nat.cast_ofNat] using hgrid
  have hclose' : |(p : ℚ) - (clusters.map DyadicIdeal.value).sum| *
      (D : ℚ) < 1 := by
    simpa only [D, Nat.cast_pow, Nat.cast_ofNat, R] using
      finiteScale_grid_close p k j hclose
  have heq : (p : ℚ) = (clusters.map DyadicIdeal.value).sum :=
    eq_of_integer_grid_distance_lt_one _ _ D hD hgridp hgridS hclose'
  have hstrict : (clusters.map DyadicIdeal.cost).sum <
      (terms.map DyadicIdeal.cost).sum := by
    rcases hdrop with h | h
    · exact h
    · rw [hnormal, ← heq] at h
      have hp : (0 : ℚ) < (2 : ℚ) ^ (-(t : ℤ)) := by positivity
      linarith
  have hbudget := hclusterCost.trans hcost
  refine ⟨clusters, heq.symm, ?_⟩
  omega

end AntichainOfGivenSize.BlockCount
