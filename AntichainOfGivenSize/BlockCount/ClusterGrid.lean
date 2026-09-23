import AntichainOfGivenSize.BlockCount.FiniteScales
import AntichainOfGivenSize.BlockCount.ClusterPartition
import AntichainOfGivenSize.BlockCount.ValuationBounds

/-!
# The dyadic grid of a list of clusters

Every nonempty intersection inside one cluster has a bounded-below exponent.
Inclusion-exclusion therefore places each cluster value, and their sum, on
one common dyadic grid.
-/

namespace AntichainOfGivenSize.BlockCount

open Finset

@[simp] theorem finiteClusterRadius_eq_clusterRadius (p k H : ℕ) :
    finiteClusterRadius p k H = clusterRadius k (p + 1) H := rfl

/-- Grid membership is preserved when adding finitely many scaled ideals. -/
theorem list_value_integer_grid (clusters : List DyadicIdeal) (R : ℕ)
    (h : ∀ D ∈ clusters, ∃ z : ℤ, D.value * (2 : ℚ) ^ R = z) :
    ∃ z : ℤ, (clusters.map DyadicIdeal.value).sum * (2 : ℚ) ^ R = z := by
  induction clusters with
  | nil => exact ⟨0, by simp⟩
  | cons D clusters ih =>
      obtain ⟨z, hz⟩ := h D (by simp)
      obtain ⟨w, hw⟩ := ih (by
        intro E hE
        exact h E (by simp [hE]))
      refine ⟨z + w, ?_⟩
      simp only [List.map_cons, List.sum_cons]
      rw [add_mul, hz, hw]
      push_cast
      rfl

/-- A cluster of one component lies on the grid determined by its connected
intersection bound. -/
theorem normalized_cluster_integer_grid
    (D : DyadicIdeal) (t p k H : ℕ)
    (hcard : D.cost ≤ k)
    (hupper : ∀ A ∈ D.generators,
      (A.card : ℤ) + (D.exponent - (t : ℤ)) ≤ (p + 1 : ℕ))
    {C : Finset (Finset ℕ)}
    (hC : C ∈ normalizedClusterPartition D.generators
      (D.exponent - (t : ℤ)) H) :
    ∃ z : ℤ,
      scaledIdealValue C (D.exponent - (t : ℤ)) *
        (2 : ℚ) ^ (finiteClusterRadius p k H) = z := by
  have hgrid := scaledIdealValue_integer_grid C
    (D.exponent - (t : ℤ)) (finiteClusterRadius p k H)
    (by
      intro S hSC hS
      have h := normalizedClusterPartition_intersection_lower
        D.generators (D.exponent - (t : ℤ)) (p + 1) H hupper hC hSC hS
      have hr : clusterRadius D.generators.card (p + 1) H ≤
          finiteClusterRadius p k H := by
        simp only [DyadicIdeal.cost] at hcard
        rw [finiteClusterRadius_eq_clusterRadius]
        unfold clusterRadius
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_right _ (Nat.mul_self_le_mul_self hcard)) _
      omega)
  exact hgrid

end AntichainOfGivenSize.BlockCount
