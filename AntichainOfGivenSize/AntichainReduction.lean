import AntichainOfGivenSize.BasicLemmas
import Mathlib.Order.Preorder.Finite

/-!
# Reduction to an inclusion antichain

This file certifies the semantic bridge between the implementation-facing
minimum over arbitrary generating families and the paper's minimum over
generating antichains. Keeping only inclusion-maximal generators preserves the
generated ideal and cannot increase the family size.
-/

open Finset

namespace AntichainOfGivenSize

/-- The inclusion-maximal members of a finite generating family. -/
noncomputable def inclusionMaximalMembers {V : Type*} [DecidableEq V]
    (generators : Finset (Finset V)) : Finset (Finset V) := by
  classical
  exact generators.filter fun A ↦ Maximal (· ∈ generators) A

@[simp] theorem mem_inclusionMaximalMembers {V : Type*} [DecidableEq V]
    {generators : Finset (Finset V)} {A : Finset V} :
    A ∈ inclusionMaximalMembers generators ↔
      A ∈ generators ∧ Maximal (· ∈ generators) A := by
  classical
  simp [inclusionMaximalMembers]

theorem inclusionMaximalMembers_subset {V : Type*} [DecidableEq V]
    (generators : Finset (Finset V)) :
    inclusionMaximalMembers generators ⊆ generators := by
  classical
  intro A hA
  exact (mem_inclusionMaximalMembers.1 hA).1

theorem inclusionMaximalMembers_isInclusionAntichain
    {V : Type*} [DecidableEq V] (generators : Finset (Finset V)) :
    IsInclusionAntichain (inclusionMaximalMembers generators) := by
  classical
  intro A hA B hB hAB
  have hmaxA := (mem_inclusionMaximalMembers.1 hA).2
  have hBG : B ∈ generators :=
    inclusionMaximalMembers_subset generators hB
  exact Finset.Subset.antisymm hAB (hmaxA.2 hBG hAB)

theorem exists_inclusionMaximalMember_superset
    {V : Type*} [DecidableEq V]
    {generators : Finset (Finset V)} {A : Finset V}
    (hA : A ∈ generators) :
    ∃ B ∈ inclusionMaximalMembers generators, A ⊆ B := by
  classical
  obtain ⟨B, hAB, hmaxB⟩ := generators.exists_le_maximal hA
  exact ⟨B, mem_inclusionMaximalMembers.2 ⟨hmaxB.1, hmaxB⟩, hAB⟩

/-- Pruning to maximal generators leaves the generated ideal unchanged. -/
theorem generatedIdeal_inclusionMaximalMembers
    {V : Type*} [DecidableEq V]
    (generators : Finset (Finset V)) :
    generatedIdeal (inclusionMaximalMembers generators) =
      generatedIdeal generators := by
  classical
  ext X
  simp only [generatedIdeal, mem_biUnion, mem_powerset]
  constructor
  · rintro ⟨A, hA, hXA⟩
    exact ⟨A, inclusionMaximalMembers_subset generators hA, hXA⟩
  · rintro ⟨A, hA, hXA⟩
    obtain ⟨B, hB, hAB⟩ := exists_inclusionMaximalMember_superset hA
    exact ⟨B, hB, hXA.trans hAB⟩

theorem card_inclusionMaximalMembers_le
    {V : Type*} [DecidableEq V]
    (generators : Finset (Finset V)) :
    #(inclusionMaximalMembers generators) ≤ #generators :=
  Finset.card_le_card (inclusionMaximalMembers_subset generators)

/-- Every generating family can be pruned to an antichain subfamily without
changing its generated ideal. -/
theorem exists_antichain_subfamily_same_generatedIdeal
    {V : Type*} [DecidableEq V]
    (generators : Finset (Finset V)) :
    ∃ antichain ⊆ generators,
      IsInclusionAntichain antichain ∧
      generatedIdeal antichain = generatedIdeal generators ∧
      #antichain ≤ #generators := by
  classical
  exact ⟨inclusionMaximalMembers generators,
    inclusionMaximalMembers_subset generators,
    inclusionMaximalMembers_isInclusionAntichain generators,
    generatedIdeal_inclusionMaximalMembers generators,
    card_inclusionMaximalMembers_le generators⟩

theorem alpha_le_of_hasAntichainGeneratorCount {n k : ℕ}
    (h : HasAntichainGeneratorCount n k) : alpha n ≤ k := by
  rcases h with ⟨m, generators, _hanti, hvalue, hcard⟩
  exact alpha_le_of_hasGeneratorCount ⟨m, generators, hvalue, hcard⟩

/-- The minimum defining `alpha` is attained by an actual inclusion
antichain, so it is exactly the generating-antichain minimum. -/
theorem alpha_hasAntichainGeneratorCount (n : ℕ) :
    HasAntichainGeneratorCount n (alpha n) := by
  classical
  obtain ⟨m, generators, hvalue, hcard⟩ := alpha_hasGeneratorCount n
  let antichain := inclusionMaximalMembers generators
  have hideal : generatedIdeal antichain = generatedIdeal generators :=
    generatedIdeal_inclusionMaximalMembers generators
  have hvalue' : (generatedIdeal antichain).card = n := by
    rw [hideal, hvalue]
  have hwitness : HasGeneratorCount n antichain.card :=
    ⟨m, antichain, hvalue', rfl⟩
  have hlower : alpha n ≤ antichain.card :=
    alpha_le_of_hasGeneratorCount hwitness
  have hupper : antichain.card ≤ alpha n := by
    simpa [antichain, hcard] using card_inclusionMaximalMembers_le generators
  exact ⟨m, antichain,
    inclusionMaximalMembers_isInclusionAntichain generators,
    hvalue', Nat.le_antisymm hupper hlower⟩

end AntichainOfGivenSize
