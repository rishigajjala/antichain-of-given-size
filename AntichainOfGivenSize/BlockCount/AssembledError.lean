import AntichainOfGivenSize.BlockCount.AssembleClusters
import AntichainOfGivenSize.BlockCount.ErrorArithmetic

/-!
# The global error from omitted generators and separated clusters

The list estimates preserve repeated source components. The error budget counts
at most `k` components, each with at most `k` singleton cubes and `k²` ordered
pair cubes.
-/

namespace AntichainOfGivenSize.BlockCount

/-- The selected pair gap controls the entire error for one source ideal. -/
theorem componentClusters_error_le (D : DyadicIdeal) (t H H' : ℕ)
    (hgap : ∀ A ∈ D.generators, ∀ E ∈ D.generators,
      -(H : ℤ) ≤ ((A ∩ E).card : ℤ) + (D.exponent - t) ∨
        ((A ∩ E).card : ℤ) + (D.exponent - t) < -(H' : ℤ)) :
    |(2 : ℚ) ^ (-(t : ℤ)) * D.value -
      ((componentClusters D t H).map DyadicIdeal.value).sum| ≤
      ((D.cost + D.cost ^ 2 : ℕ) : ℚ) * (1 / (2 : ℚ) ^ H') := by
  classical
  rw [componentClusters_sum_value, ← scaledIdealValue_normalized]
  apply scaledIdealValue_sub_clusters_abs_le _ _ _ _ (by positivity)
  · rw [normalizedClusterPartition_biUnion]
    exact Finset.filter_subset _ _
  · exact normalizedClusterPartition_sum_card_le _ _ _
  · intro A hA
    obtain ⟨hAG, hnot⟩ := Finset.mem_sdiff.mp hA
    rw [normalizedClusterPartition_biUnion] at hnot
    apply zpow_two_le_inv_pow_of_lt_neg
    exact exponent_low_of_not_mem_largeGenerators _ _ _ _ hgap hAG hnot
  · intro C hC E hE hCE A hA B hB
    apply zpow_two_le_inv_pow_of_lt_neg
    exact normalizedClusterPartition_cross_low _ _ _ _ hgap hC hE hCE hA hB

/-- A list-level triangle inequality retaining repeated entries. -/
theorem list_sum_difference_abs_le_length_mul {ι : Type*} (l : List ι)
    (f g : ι → ℚ) (B : ℚ) (h : ∀ i ∈ l, |f i - g i| ≤ B) :
    |(l.map f).sum - (l.map g).sum| ≤ (l.length : ℚ) * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun i hi => h i (by simp [hi]))
    have ht := abs_add_le (f a - g a) ((l.map f).sum - (l.map g).sum)
    simp only [List.map_cons, List.sum_cons, List.length_cons,
      Nat.cast_add, Nat.cast_one]
    have heq : f a + (l.map f).sum - (g a + (l.map g).sum) =
        (f a - g a) + ((l.map f).sum - (l.map g).sum) := by ring
    rw [heq]
    nlinarith

/-- Absolute normalized error for the complete assembled cluster list. -/
theorem assembledClusters_error_le (terms : List DyadicIdeal) (t k H H' : ℕ)
    (hcost : (terms.map DyadicIdeal.cost).sum ≤ k)
    (hgap : ∀ D ∈ terms, ∀ A ∈ D.generators, ∀ E ∈ D.generators,
      -(H : ℤ) ≤ ((A ∩ E).card : ℤ) + (D.exponent - t) ∨
        ((A ∩ E).card : ℤ) + (D.exponent - t) < -(H' : ℤ)) :
    |(2 : ℚ) ^ (-(t : ℤ)) * (terms.map DyadicIdeal.value).sum -
      ((assembledClusters terms t H).map DyadicIdeal.value).sum| ≤
      (exponentBudget k : ℚ) / (2 : ℚ) ^ H' := by
  have hcomponent : ∀ D ∈ terms,
      |(2 : ℚ) ^ (-(t : ℤ)) * D.value -
        ((componentClusters D t H).map DyadicIdeal.value).sum| ≤
      ((k + k * k : ℕ) : ℚ) * (1 / (2 : ℚ) ^ H') := by
    intro D hD
    have he := componentClusters_error_le D t H H' (hgap D hD)
    have hc := source_cost_le hcost hD
    have hbudget : D.cost + D.cost ^ 2 ≤ k + k * k := by nlinarith
    have hbudgetq : ((D.cost + D.cost ^ 2 : ℕ) : ℚ) ≤ (k + k * k : ℕ) := by
      exact_mod_cast hbudget
    exact he.trans (mul_le_mul_of_nonneg_right hbudgetq (by positivity))
  have he := list_sum_difference_abs_le_length_mul terms
    (fun D => (2 : ℚ) ^ (-(t : ℤ)) * D.value)
    (fun D => ((componentClusters D t H).map DyadicIdeal.value).sum)
    (((k + k * k : ℕ) : ℚ) * (1 / (2 : ℚ) ^ H')) hcomponent
  have hnormalize : (terms.map (fun D => (2 : ℚ) ^ (-(t : ℤ)) * D.value)).sum =
      (2 : ℚ) ^ (-(t : ℤ)) * (terms.map DyadicIdeal.value).sum := by
    clear hcost hgap hcomponent he
    induction terms with
    | nil => simp
    | cons D terms ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]
  rw [hnormalize, ← sum_map_assembledClusters] at he
  have hlen : (terms.length : ℚ) ≤ (k : ℚ) := by
    exact_mod_cast (length_le_sum_cost terms).trans hcost
  have hmul := mul_le_mul_of_nonneg_right hlen
    (show 0 ≤ ((k + k * k : ℕ) : ℚ) * (1 / (2 : ℚ) ^ H') by positivity)
  apply he.trans
  apply hmul.trans_eq
  simp only [exponentBudget, Nat.cast_mul]
  ring

/-- An exponent-set gap is a convenient sufficient hypothesis for the global bound. -/
theorem assembledClusters_error_le_of_exponent_gap
    (terms : List DyadicIdeal) (t k H H' : ℕ)
    (hcost : (terms.map DyadicIdeal.cost).sum ≤ k)
    (hgap : ∀ e ∈ exponentSet terms t, -(H : ℤ) ≤ e ∨ e < -(H' : ℤ)) :
    |(2 : ℚ) ^ (-(t : ℤ)) * (terms.map DyadicIdeal.value).sum -
      ((assembledClusters terms t H).map DyadicIdeal.value).sum| ≤
      (exponentBudget k : ℚ) / (2 : ℚ) ^ H' :=
  assembledClusters_error_le terms t k H H' hcost
    (fun _ hD => source_pair_gap hgap hD)

end AntichainOfGivenSize.BlockCount
