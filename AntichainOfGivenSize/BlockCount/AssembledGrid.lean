import AntichainOfGivenSize.BlockCount.ClusterGrid
import AntichainOfGivenSize.BlockCount.AssembleClusters
import AntichainOfGivenSize.BlockCount.TermGap

/-!
# The common grid of all assembled clusters
-/

namespace AntichainOfGivenSize.BlockCount

/-- A global cost bound and singleton upper bound put every normalized cluster
on one common grid. -/
theorem assembledClusters_integer_grid (terms : List DyadicIdeal) (p t k j : ℕ)
    (hcost : (terms.map DyadicIdeal.cost).sum ≤ k)
    (hupper : ∀ D ∈ terms, ∀ A ∈ D.generators,
      (A.card : ℤ) + (D.exponent - (t : ℤ)) ≤ (p + 1 : ℕ)) :
    ∃ z : ℤ,
      ((assembledClusters terms t (finiteScale p k j)).map
          DyadicIdeal.value).sum *
        (2 : ℚ) ^ (finiteClusterRadius p k (finiteScale p k j)) = z := by
  apply list_value_integer_grid
  intro E hE
  obtain ⟨D, hD, hC, hExp⟩ := assembledClusters_source hE
  have hDcost : D.cost ≤ k := by
    have hmem : D.cost ∈ terms.map DyadicIdeal.cost :=
      List.mem_map.mpr ⟨D, hD, rfl⟩
    exact (List.le_sum_of_mem hmem).trans hcost
  have hgrid := normalized_cluster_integer_grid D t p k (finiteScale p k j)
    hDcost (hupper D hD) hC
  simpa only [DyadicIdeal.value, scaledIdealValue, hExp] using hgrid

/-- Supply the singleton upper bound directly from a representation of
`2^t*p+1`. -/
theorem assembledClusters_integer_grid_of_value (terms : List DyadicIdeal)
    (p t k j : ℕ)
    (hcost : (terms.map DyadicIdeal.cost).sum ≤ k)
    (hvalue : (terms.map DyadicIdeal.value).sum =
      ((2 ^ t * p + 1 : ℕ) : ℚ)) :
    ∃ z : ℤ,
      ((finiteClusters terms t p k j).map DyadicIdeal.value).sum *
        (2 : ℚ) ^ (finiteClusterRadius p k (finiteScale p k j)) = z := by
  exact assembledClusters_integer_grid terms p t k j hcost
    (singleton_upper_for_terms terms p t hvalue)

end AntichainOfGivenSize.BlockCount
