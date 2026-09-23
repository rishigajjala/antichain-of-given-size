import AntichainOfGivenSize.BlockCount.AssembledGrid
import AntichainOfGivenSize.BlockCount.ErrorToGrid
import AntichainOfGivenSize.BlockCount.ReductionCertificate
import AntichainOfGivenSize.BlockCount.ExtremalRecursion

/-!
# Reducing dyadic cost after a sufficiently long binary gap

The main finite increment proof is reduced to one geometric estimate for the
assembled clusters. That estimate is stated separately so its set-theoretic
proof can be checked independently of the arithmetic and extremal recursion.
-/

namespace AntichainOfGivenSize.BlockCount

/-- The uniform geometric error estimate for every finite scaled-ideal
representation at an empty exponent band. -/
def FiniteGeometricBound : Prop :=
  ∀ (terms : List DyadicIdeal) (p t k j : ℕ),
    (terms.map DyadicIdeal.cost).sum ≤ k →
    (∀ e ∈ exponentSet terms t,
      -(finiteScale p k j : ℤ) ≤ e ∨
        e < -(finiteScale p k (j + 1) : ℤ)) →
    |(2 : ℚ) ^ (-(t : ℤ)) * (terms.map DyadicIdeal.value).sum -
      ((finiteClusters terms t p k j).map DyadicIdeal.value).sum| ≤
        (exponentBudget k : ℚ) /
          (2 : ℚ) ^ (finiteScale p k (j + 1))

/-- The explicit finite threshold reduces cost for a concrete shift. -/
theorem finiteThreshold_costReduction
    (hgeom : FiniteGeometricBound) (p k t : ℕ)
    (ht : finiteThreshold p k ≤ t)
    (hrepr : HasDyadicIdealSum ((2 ^ t * p + 1 : ℕ) : ℚ) k) :
    HasDyadicIdealSum (p : ℚ) (k - 1) := by
  obtain ⟨terms, hvalue, hcost⟩ := hrepr
  obtain ⟨j, hj, hgap⟩ :=
    exists_empty_exponent_band_of_cost terms t k hcost
      (finiteScale p k) (finiteScale_mono p k)
  let clusters := finiteClusters terms t p k j
  have hnext : finiteScale p k (j + 1) ≤ t :=
    (finiteScale_succ_le_threshold p k j hj).trans ht
  have hnormal := normalize_sum_value_of_eq terms p t hvalue
  have hgrid : ∃ z : ℤ,
      (clusters.map DyadicIdeal.value).sum *
        (2 : ℚ) ^ (finiteClusterRadius p k (finiteScale p k j)) = z := by
    exact assembledClusters_integer_grid_of_value terms p t k j hcost hvalue
  have hclusterCost : (clusters.map DyadicIdeal.cost).sum ≤
      (terms.map DyadicIdeal.cost).sum :=
    assembledClusters_sum_cost_le terms t (finiteScale p k j)
  have hgeom' := hgeom terms p t k j hcost hgap
  rw [hnormal] at hgeom'
  have hclose : |(p : ℚ) - (clusters.map DyadicIdeal.value).sum| ≤
      ((exponentBudget k + 1 : ℕ) : ℚ) /
        (2 : ℚ) ^ (finiteScale p k (j + 1)) :=
    leading_coefficient_close_of_normalized_error p k t j
      (clusters.map DyadicIdeal.value).sum hnext hgeom'
  have hdrop : (clusters.map DyadicIdeal.cost).sum <
        (terms.map DyadicIdeal.cost).sum ∨
      (2 : ℚ) ^ (-(t : ℤ)) *
        (terms.map DyadicIdeal.value).sum ≤
          (clusters.map DyadicIdeal.value).sum := by
    rcases assembledClusters_cost_drop_or_all_large terms t
      (finiteScale p k j) with h | h
    · exact Or.inl h
    · exact Or.inr (assembledClusters_value_ge_of_all_large terms t
        (finiteScale p k j) h)
  exact hasDyadicIdealSum_of_cluster_certificate p k t j terms clusters
    hcost hnormal hclusterCost hgrid hclose hdrop

/-- The geometric estimate, the empty-band lemma, and grid spacing imply the
finite dyadic cost-reduction property used by the extremal recursion. -/
theorem dyadicCostReduction_of_finiteGeometricBound
    (hgeom : FiniteGeometricBound) : DyadicCostReduction := by
  intro p k _hp _hk
  refine ⟨finiteThreshold p k, ?_⟩
  intro t ht hrepr
  exact finiteThreshold_costReduction hgeom p k t ht hrepr

end AntichainOfGivenSize.BlockCount
