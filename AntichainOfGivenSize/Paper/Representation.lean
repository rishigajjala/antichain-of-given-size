import AntichainOfGivenSize.Paper.Statements
import AntichainOfGivenSize.LowerBound.ProfilePadding
import AntichainOfGivenSize.LowerBound.ClusterEncoding
import AntichainOfGivenSize.BasicLemmas
import AntichainOfGivenSize.Section6.IndexedBounds

/-!
# Exact interpretation of the paper's attainable-value set

The finite profile implementation is equivalent to a nonempty family of
at most `K` finite sets, each of size at most `B`, over an arbitrary finite
ambient universe. There is no restriction on the cardinality of that
universe in this representation predicate.
-/

open Finset

namespace AntichainOfGivenSize.Paper

open ClusterLowerBound

/-- A direct finite-family version of the paper's definition of `V(B,K)`.
The ambient size `m` is existentially quantified without an upper bound. -/
def HasBoundedGeneratingFamily (B K n : ℕ) : Prop :=
  ∃ m : ℕ, ∃ G : Finset (Finset (Fin m)),
    G.Nonempty ∧ G.card ≤ K ∧
      (∀ A ∈ G, A.card ≤ B) ∧ (generatedIdeal G).card = n

theorem hasBoundedGeneratingFamily_of_mem_attainableValues {B K n : ℕ}
    (hK : 0 < K) (hn : n ∈ attainableValues B K) :
    HasBoundedGeneratingFamily B K n := by
  classical
  rcases Finset.mem_image.1 hn with ⟨x, _hx, rfl⟩
  let G : Finset (Finset x.Point) := Finset.univ.image x.generators
  let e := Fintype.equivFin x.Point
  refine ⟨Fintype.card x.Point, relabelFamily e G, ?_, ?_, ?_, ?_⟩
  · have hG : G.Nonempty := by
      exact ⟨x.generators ⟨0, hK⟩,
        Finset.mem_image.2 ⟨⟨0, hK⟩, Finset.mem_univ _, rfl⟩⟩
    simpa [relabelFamily, mapFamily] using hG
  · calc
      (relabelFamily e G).card = G.card := Finset.card_map _
      _ ≤ K := by
        simpa [G] using (Finset.card_image_le :
          #(Finset.univ.image x.generators) ≤ #(Finset.univ : Finset (Fin K)))
  · intro A hA
    rcases Finset.mem_map.1 hA with ⟨A', hA', rfl⟩
    rcases Finset.mem_image.1 hA' with ⟨i, _hi, rfl⟩
    simpa [finsetMapEmbedding, BoundedProfile.generators] using
      x.card_profileGenerator_le i
  · rw [generatedIdeal_relabel, Finset.card_map]
    change (generatedIdeal (Finset.univ.image x.generators)).card = x.value
    rw [← generatedIdealIdx_eq_generatedIdeal_image]
    rfl

theorem mem_attainableValues_of_hasBoundedGeneratingFamily {B K n : ℕ}
    (hn : HasBoundedGeneratingFamily B K n) :
    n ∈ attainableValues B K := by
  classical
  obtain ⟨m, G, hGpos, hGK, hload, hvalue⟩ := hn
  let k := G.card
  let e : G ≃ Fin k := Fintype.equivFinOfCardEq (by simp [k])
  let A : Fin k → Finset (Fin m) := fun i ↦ (e.symm i).1
  have himage : Finset.univ.image A = G := by
    ext S
    constructor
    · intro hS
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.1 hS
      exact (e.symm i).2
    · intro hS
      apply Finset.mem_image.2
      refine ⟨e ⟨S, hS⟩, Finset.mem_univ _, ?_⟩
      simp [A]
  have hAload : ∀ i : Fin k, (A i).card ≤ B := by
    intro i
    exact hload _ (e.symm i).2
  let x := BoundedProfile.ofIndexedFamily A hAload
  have hx : x.value = n := by
    rw [BoundedProfile.value_ofIndexedFamily,
      generatedIdealIdx_eq_generatedIdeal_image, himage]
    exact hvalue
  have hkpos : 0 < k := Finset.card_pos.2 hGpos
  have hkK : k ≤ K := hGK
  exact Finset.mem_image.2 ⟨x.pad hkK hkpos, Finset.mem_univ _,
    (BoundedProfile.value_pad x hkK hkpos).trans hx⟩

/-- The implementation of `attainableValues` has exactly the paper's
semantics whenever the permitted number of generators is positive. -/
theorem mem_attainableValues_iff {B K n : ℕ} (hK : 0 < K) :
    n ∈ attainableValues B K ↔ HasBoundedGeneratingFamily B K n :=
  ⟨hasBoundedGeneratingFamily_of_mem_attainableValues hK,
    mem_attainableValues_of_hasBoundedGeneratingFamily⟩

end AntichainOfGivenSize.Paper
