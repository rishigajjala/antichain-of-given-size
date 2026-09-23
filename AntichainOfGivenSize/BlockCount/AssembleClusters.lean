import AntichainOfGivenSize.BlockCount.FiniteScales
import AntichainOfGivenSize.BlockCount.ClusterPartition
import AntichainOfGivenSize.BlockCount.ValuationBounds

/-!
# Assembling normalized clusters

Each original scaled ideal contributes its proximity clusters at the common
normalization shift `t`. The assembled list retains the original multiplicities.
Its cost is exactly the number of retained generators, so discarding one small
generator gives a strict saving.
-/

namespace AntichainOfGivenSize.BlockCount

open Finset

/-- Regard a nonempty normalized cluster as a scaled ideal. -/
noncomputable def clusterIdeal (D : DyadicIdeal) (t H : ℕ)
    (C : {C // C ∈ normalizedClusterPartition D.generators (D.exponent - t) H}) :
    DyadicIdeal where
  generators := C.1
  generators_nonempty := normalizedClusterPartition_nonempty _ _ _ C.2
  exponent := D.exponent - t

@[simp] theorem clusterIdeal_generators (D : DyadicIdeal) (t H : ℕ)
    (C : {C // C ∈ normalizedClusterPartition D.generators (D.exponent - t) H}) :
    (clusterIdeal D t H C).generators = C.1 := rfl

@[simp] theorem clusterIdeal_exponent (D : DyadicIdeal) (t H : ℕ)
    (C : {C // C ∈ normalizedClusterPartition D.generators (D.exponent - t) H}) :
    (clusterIdeal D t H C).exponent = D.exponent - t := rfl

@[simp] theorem clusterIdeal_cost (D : DyadicIdeal) (t H : ℕ)
    (C : {C // C ∈ normalizedClusterPartition D.generators (D.exponent - t) H}) :
    (clusterIdeal D t H C).cost = C.1.card := rfl

/-- The list of normalized clusters from one scaled ideal. -/
noncomputable def componentClusters (D : DyadicIdeal) (t H : ℕ) : List DyadicIdeal :=
  (normalizedClusterPartition D.generators (D.exponent - t) H).attach.toList.map
    (clusterIdeal D t H)

/-- Assemble normalized clusters from a list, preserving repetitions of source ideals. -/
noncomputable def assembledClusters (terms : List DyadicIdeal) (t H : ℕ) :
    List DyadicIdeal := terms.flatMap (fun D => componentClusters D t H)

/-- The assembled list at the explicit cutoff used by the finite reduction. -/
noncomputable def finiteClusters (terms : List DyadicIdeal) (t p k j : ℕ) :
    List DyadicIdeal := assembledClusters terms t (finiteScale p k j)

theorem mem_componentClusters {D E : DyadicIdeal} {t H : ℕ} :
    E ∈ componentClusters D t H ↔
      ∃ C : {C // C ∈ normalizedClusterPartition D.generators (D.exponent - t) H},
        clusterIdeal D t H C = E := by
  classical
  simp [componentClusters]

theorem mem_assembledClusters {terms : List DyadicIdeal} {E : DyadicIdeal} {t H : ℕ} :
    E ∈ assembledClusters terms t H ↔
      ∃ D ∈ terms,
        ∃ C : {C // C ∈ normalizedClusterPartition D.generators (D.exponent - t) H},
          clusterIdeal D t H C = E := by
  simp only [assembledClusters, List.mem_flatMap, mem_componentClusters]

/-- Membership exposes the source family, the cluster, and the common scaling exponent. -/
theorem assembledClusters_source {terms : List DyadicIdeal} {E : DyadicIdeal} {t H : ℕ}
    (hE : E ∈ assembledClusters terms t H) :
    ∃ D ∈ terms,
      E.generators ∈ normalizedClusterPartition D.generators (D.exponent - t) H ∧
        E.exponent = D.exponent - t := by
  obtain ⟨D, hD, C, rfl⟩ := mem_assembledClusters.mp hE
  exact ⟨D, hD, C.2, rfl⟩

/-- Sum any function over the assembled list by first summing over each source ideal. -/
theorem sum_map_assembledClusters {M : Type*} [AddMonoid M]
    (terms : List DyadicIdeal) (t H : ℕ) (f : DyadicIdeal → M) :
    ((assembledClusters terms t H).map f).sum =
      (terms.map fun D => ((componentClusters D t H).map f).sum).sum := by
  induction terms with
  | nil => simp [assembledClusters]
  | cons D terms ih =>
      simp only [assembledClusters, List.flatMap_cons, List.map_append,
        List.sum_append, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]

theorem componentClusters_sum_cost (D : DyadicIdeal) (t H : ℕ) :
    ((componentClusters D t H).map DyadicIdeal.cost).sum =
      (largeGenerators D.generators (D.exponent - t) H).card := by
  classical
  simp only [componentClusters, List.map_map, Function.comp_def, clusterIdeal_cost,
    Finset.sum_map_toList, Finset.sum_attach, normalizedClusterPartition_sum_card]

theorem componentClusters_sum_cost_le (D : DyadicIdeal) (t H : ℕ) :
    ((componentClusters D t H).map DyadicIdeal.cost).sum ≤ D.cost := by
  rw [componentClusters_sum_cost]
  exact Finset.card_filter_le _ _

theorem componentClusters_sum_cost_lt (D : DyadicIdeal) (t H : ℕ)
    (hsmall : ∃ A ∈ D.generators, A ∉ largeGenerators D.generators (D.exponent - t) H) :
    ((componentClusters D t H).map DyadicIdeal.cost).sum < D.cost := by
  rw [componentClusters_sum_cost, ← normalizedClusterPartition_sum_card]
  exact normalizedClusterPartition_sum_card_lt _ _ _ hsmall

/-- Exact total cost: one cost unit for each large generator in each source component. -/
theorem assembledClusters_sum_cost (terms : List DyadicIdeal) (t H : ℕ) :
    ((assembledClusters terms t H).map DyadicIdeal.cost).sum =
      (terms.map fun D => (largeGenerators D.generators (D.exponent - t) H).card).sum := by
  rw [sum_map_assembledClusters]
  simp only [componentClusters_sum_cost]

theorem assembledClusters_sum_cost_le (terms : List DyadicIdeal) (t H : ℕ) :
    ((assembledClusters terms t H).map DyadicIdeal.cost).sum ≤
      (terms.map DyadicIdeal.cost).sum := by
  rw [sum_map_assembledClusters]
  exact List.sum_le_sum (fun D _ => componentClusters_sum_cost_le D t H)

/-- One omitted generator strictly reduces the total cost. -/
theorem assembledClusters_sum_cost_lt (terms : List DyadicIdeal) (t H : ℕ)
    (hsmall : ∃ D ∈ terms,
      ∃ A ∈ D.generators, A ∉ largeGenerators D.generators (D.exponent - t) H) :
    ((assembledClusters terms t H).map DyadicIdeal.cost).sum <
      (terms.map DyadicIdeal.cost).sum := by
  rw [sum_map_assembledClusters]
  apply List.sum_lt_sum _ _ (fun D _ => componentClusters_sum_cost_le D t H)
  obtain ⟨D, hD, hsmall⟩ := hsmall
  exact ⟨D, hD, componentClusters_sum_cost_lt D t H hsmall⟩

/-- If no cost is saved, every original generator must be large. -/
theorem all_large_of_assembledClusters_cost_ge (terms : List DyadicIdeal) (t H : ℕ)
    (hcost : (terms.map DyadicIdeal.cost).sum ≤
      ((assembledClusters terms t H).map DyadicIdeal.cost).sum) :
    ∀ D ∈ terms, ∀ A ∈ D.generators,
      A ∈ largeGenerators D.generators (D.exponent - t) H := by
  intro D hD A hA
  by_contra hsmall
  have hlt := assembledClusters_sum_cost_lt terms t H ⟨D, hD, A, hA, hsmall⟩
  omega

/-- Either a generator is discarded, or all source families are covered by clusters. -/
theorem assembledClusters_cost_drop_or_all_large (terms : List DyadicIdeal) (t H : ℕ) :
    ((assembledClusters terms t H).map DyadicIdeal.cost).sum <
        (terms.map DyadicIdeal.cost).sum ∨
      ∀ D ∈ terms, ∀ A ∈ D.generators,
        A ∈ largeGenerators D.generators (D.exponent - t) H := by
  by_cases h : ((assembledClusters terms t H).map DyadicIdeal.cost).sum <
      (terms.map DyadicIdeal.cost).sum
  · exact Or.inl h
  · exact Or.inr (all_large_of_assembledClusters_cost_ge terms t H (by omega))

/-- Component values as the explicit finite sum over their cluster families. -/
theorem componentClusters_sum_value (D : DyadicIdeal) (t H : ℕ) :
    ((componentClusters D t H).map DyadicIdeal.value).sum =
      ∑ C ∈ normalizedClusterPartition D.generators (D.exponent - t) H,
        scaledIdealValue C (D.exponent - t) := by
  classical
  simp only [componentClusters, List.map_map, Function.comp_def, DyadicIdeal.value,
    clusterIdeal_generators, clusterIdeal_exponent, Finset.sum_map_toList,
    scaledIdealValue]
  exact Finset.sum_attach _ (fun C =>
    (2 : ℚ) ^ (D.exponent - t) * (generatedIdeal C).card)

/-- Values of the full list can be estimated separately for each original component. -/
theorem assembledClusters_sum_value (terms : List DyadicIdeal) (t H : ℕ) :
    ((assembledClusters terms t H).map DyadicIdeal.value).sum =
      (terms.map fun D =>
        ∑ C ∈ normalizedClusterPartition D.generators (D.exponent - t) H,
          scaledIdealValue C (D.exponent - t)).sum := by
  rw [sum_map_assembledClusters]
  simp only [componentClusters_sum_value]

/-- A bound on total cost also bounds the cost of each source component. -/
theorem source_cost_le {terms : List DyadicIdeal} {k : ℕ}
    (hcost : (terms.map DyadicIdeal.cost).sum ≤ k)
    {D : DyadicIdeal} (hD : D ∈ terms) : D.cost ≤ k :=
  (List.le_sum_of_mem (List.mem_map.mpr ⟨D, hD, rfl⟩)).trans hcost

/-- The global empty band supplies the pair dichotomy in each source family. -/
theorem source_pair_gap {terms : List DyadicIdeal} {t H H' : ℕ}
    (hgap : ∀ e ∈ exponentSet terms t, -(H : ℤ) ≤ e ∨ e < -(H' : ℤ))
    {D : DyadicIdeal} (hD : D ∈ terms) :
    ∀ A ∈ D.generators, ∀ E ∈ D.generators,
      -(H : ℤ) ≤ ((A ∩ E).card : ℤ) + (D.exponent - t) ∨
        ((A ∩ E).card : ℤ) + (D.exponent - t) < -(H' : ℤ) := by
  intro A hA E hE
  have h := hgap _ (pairExponent_mem terms t D hD A E hA hE)
  simpa only [pairExponent, add_sub_assoc] using h

/-- Every omitted generator is below the next cutoff of the empty band. -/
theorem omitted_generator_exponent_lt {terms : List DyadicIdeal} {t H H' : ℕ}
    (hgap : ∀ e ∈ exponentSet terms t, -(H : ℤ) ≤ e ∨ e < -(H' : ℤ))
    {D : DyadicIdeal} (hD : D ∈ terms) {A : Finset ℕ} (hA : A ∈ D.generators)
    (hsmall : A ∉ largeGenerators D.generators (D.exponent - t) H) :
    singletonExponent D t A < -(H' : ℤ) := by
  have h := exponent_low_of_not_mem_largeGenerators D.generators (D.exponent - t)
    H H' (source_pair_gap hgap hD) hA hsmall
  simpa only [singletonExponent, add_sub_assoc] using h

/-- If every generator is large, the partition covers the original family. -/
theorem cluster_cover_of_all_large (D : DyadicIdeal) (t H : ℕ)
    (hlarge : ∀ A ∈ D.generators,
      A ∈ largeGenerators D.generators (D.exponent - t) H) :
    (normalizedClusterPartition D.generators (D.exponent - t) H).biUnion id =
      D.generators := by
  rw [normalizedClusterPartition_biUnion]
  exact Finset.Subset.antisymm (Finset.filter_subset _ _) hlarge

/-- Writing normalization as a common dyadic scalar. -/
theorem scaledIdealValue_normalized (D : DyadicIdeal) (t : ℕ) :
    scaledIdealValue D.generators (D.exponent - t) =
      (2 : ℚ) ^ (-(t : ℤ)) * D.value := by
  unfold scaledIdealValue DyadicIdeal.value
  rw [← mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  congr 2
  omega

/-- With no omitted generators, splitting into clusters can only increase value. -/
theorem componentClusters_value_ge_of_all_large (D : DyadicIdeal) (t H : ℕ)
    (hlarge : ∀ A ∈ D.generators,
      A ∈ largeGenerators D.generators (D.exponent - t) H) :
    (2 : ℚ) ^ (-(t : ℤ)) * D.value ≤
      ((componentClusters D t H).map DyadicIdeal.value).sum := by
  have h := scaledIdealValue_biUnion_le
    (normalizedClusterPartition D.generators (D.exponent - t) H) (D.exponent - t)
  rw [cluster_cover_of_all_large D t H hlarge, scaledIdealValue_normalized] at h
  rwa [componentClusters_sum_value]

/-- With no omitted generators, the assembled value bounds the normalized original sum. -/
theorem assembledClusters_value_ge_of_all_large (terms : List DyadicIdeal) (t H : ℕ)
    (hlarge : ∀ D ∈ terms, ∀ A ∈ D.generators,
      A ∈ largeGenerators D.generators (D.exponent - t) H) :
    (2 : ℚ) ^ (-(t : ℤ)) * (terms.map DyadicIdeal.value).sum ≤
      ((assembledClusters terms t H).map DyadicIdeal.value).sum := by
  induction terms with
  | nil => simp [assembledClusters]
  | cons D terms ih =>
      have hD := componentClusters_value_ge_of_all_large D t H
        (hlarge D (by simp))
      have htail := ih (by
        intro E hE
        exact hlarge E (by simp [hE]))
      simp only [assembledClusters, List.flatMap_cons, List.map_append,
        List.sum_append, List.map_cons, List.sum_cons] at htail ⊢
      rw [mul_add]
      exact add_le_add hD htail

end AntichainOfGivenSize.BlockCount
