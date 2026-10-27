import AntichainOfGivenSize.Model.ProblemSetting
import AntichainOfGivenSize.Paper.UpperConstructionGeometry
import AntichainOfGivenSize.Paper.PatternGadget
import AntichainOfGivenSize.Section6.Construction

open Finset
open scoped BigOperators

set_option maxHeartbeats 1200000

namespace AntichainOfGivenSize.Paper.UpperConstruction

open AntichainOfGivenSize.Section6

@[simp] theorem stageEmbedding_univ {r : ℕ} {K : Type*} [DecidableEq K]
    (i : BitMatching.Stage r) (D : Finset K) :
    Finset.univ.map (stageEmbedding i D) = selected i D := by
  classical
  ext p
  cases p with
  | inl p =>
    rcases p with ⟨j,b⟩
    simp [stageEmbedding,selected,BitMatching.address,BitMatching.chosenEmbedding,
      BitMatching.chosenIndex]
  | inr k => simp [stageEmbedding,selected]

theorem selected_ideal_eq {r ell : ℕ} {K V : Type*}
    [DecidableEq K] [Fintype V] [DecidableEq V]
    (active : Finset (BitMatching.Stage r)) (hist : BitMatching.Stage r → Finset K)
    (R : K → Finset V) (i : BitMatching.Stage r) (D : Finset K) :
    generatedIdealIdx (selected i D) (generator (ell := ell) active hist R) =
      generatedIdealIdx Finset.univ (stageGenerator active hist R i D) := by
  classical
  rw [← stageEmbedding_univ]
  ext A
  simp only [generatedIdealIdx,Finset.mem_biUnion,Finset.mem_map,
    Finset.mem_univ,true_and,stageGenerator]
  constructor
  · rintro ⟨p,⟨k,rfl⟩,hA⟩
    exact ⟨k,hA⟩
  · rintro ⟨k,hA⟩
    exact ⟨stageEmbedding i D k,⟨k,rfl⟩,hA⟩

theorem fresh_not_mem_generator {r ell : ℕ} {K V : Type*}
    [Fintype V] [DecidableEq V]
    (active : Finset (BitMatching.Stage r)) (hist : BitMatching.Stage r → Finset K)
    (R : K → Finset V) (i : BitMatching.Stage r) (hi : i ∉ active) (p : Index r K) :
    (Sum.inr (Sum.inr i) : Vertex r ell V) ∉ generator active hist R p := by
  simp [Present,hi]

theorem generator_update {r ell : ℕ} {K V : Type*}
    [DecidableEq K] [Fintype V] [DecidableEq V]
    (active : Finset (BitMatching.Stage r)) (hist : BitMatching.Stage r → Finset K)
    (R : K → Finset V) (i : BitMatching.Stage r) (hi : i ∉ active)
    (D : Finset K) (p : Index r K) :
    generator (ell := ell) (insert i active) (Function.update hist i D) R p =
      if p ∈ selected i D then insert (Sum.inr (Sum.inr i)) (generator active hist R p)
      else generator active hist R p := by
  classical
  ext v
  rcases v with u | (v | g)
  · by_cases hs : p ∈ selected i D <;> cases p <;> simp [hs,Present]
  · by_cases hs : p ∈ selected i D <;> cases p <;> simp [hs,Present]
  · by_cases hgi : g = i
    · subst g
      by_cases hs : p ∈ selected i D <;> simp [hs,Present,hi]
    · by_cases hs : p ∈ selected i D <;> simp [hs,Present,hgi]

theorem intersection_update {r ell : ℕ} {K V : Type*}
    [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]
    (active : Finset (BitMatching.Stage r)) (hist : BitMatching.Stage r → Finset K)
    (R : K → Finset V) (i : BitMatching.Stage r) (hi : i ∉ active) (D : Finset K)
    (t : (Finset.univ : Finset (Index r K)).powerset.filter (·.Nonempty)) :
    generatorIntersection
        (generator (ell := ell) (insert i active) (Function.update hist i D) R) t =
      if t.val ⊆ selected i D then
        insert (Sum.inr (Sum.inr i)) (generatorIntersection (generator active hist R) t)
      else generatorIntersection (generator active hist R) t := by
  classical
  ext v
  by_cases hv : v = Sum.inr (Sum.inr i)
  · subst v
    have hnot : (Sum.inr (Sum.inr i) : Vertex r ell V) ∉
        generatorIntersection (generator active hist R) t := by
      intro h
      obtain ⟨p,hp⟩ := (Finset.mem_filter.mp t.property).2
      rw [generatorIntersection,Finset.mem_inf'] at h
      exact fresh_not_mem_generator active hist R i hi p (h p hp)
    have hmem : (Sum.inr (Sum.inr i) : Vertex r ell V) ∈
        generatorIntersection
          (generator (insert i active) (Function.update hist i D) R) t ↔
        t.val ⊆ selected i D := by
      simp [generatorIntersection,Finset.mem_inf',Present,Finset.subset_iff]
    by_cases hs : t.val ⊆ selected i D <;> simp [hs,hmem,hnot]
  · have hmem (p : Index r K) :
        v ∈ generator (ell := ell) (insert i active) (Function.update hist i D) R p ↔
        v ∈ generator active hist R p := by
      rw [generator_update active hist R i hi D p]
      split <;> simp [hv]
    by_cases hs : t.val ⊆ selected i D <;>
      simp [hs,hv,generatorIntersection,Finset.mem_inf',hmem]

theorem idealCard_update {r ell : ℕ} {K V : Type*}
    [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]
    (active : Finset (BitMatching.Stage r)) (hist : BitMatching.Stage r → Finset K)
    (R : K → Finset V) (i : BitMatching.Stage r) (hi : i ∉ active) (D : Finset K) :
    idealCard (ell := ell) (insert i active) (Function.update hist i D) R =
      idealCard (ell := ell) active hist R +
      (generatedIdealIdx (selected i D) (generator (ell := ell) active hist R)).card := by
  classical
  apply generatedIdealIdx_card_stage_of_intersection_cards (Finset.subset_univ _)
  intro t
  rw [intersection_update active hist R i hi D t]
  have hnot : (Sum.inr (Sum.inr i) : Vertex r ell V) ∉
      generatorIntersection (generator active hist R) t := by
    intro h
    obtain ⟨p,hp⟩ := (Finset.mem_filter.mp t.property).2
    rw [generatorIntersection,Finset.mem_inf'] at h
    exact fresh_not_mem_generator active hist R i hi p (h p hp)
  by_cases hs : t.val ⊆ selected i D <;> simp [hs,hnot]

theorem pattern_subtype_ideal (ell : ℕ) (D : Finset (PatternGadget.Index ell)) :
    generatedIdealIdx Finset.univ (fun k : D => PatternGadget.generator k.val) =
      generatedIdealIdx D PatternGadget.generator := by
  ext A
  simp [generatedIdealIdx]

/-- Claim 6.4 for the baseline-plus-tags gadget of Claim 6.2. -/
theorem block_increment {r ell d : ℕ} (hr : 0 < r) (hd : d < 2 ^ ell)
    (active : Finset (BitMatching.Stage r))
    (hist : BitMatching.Stage r → Finset (PatternGadget.Index ell))
    (i : BitMatching.Stage r) (hi : i ∉ active) :
    ((generatedIdealIdx (selected i (digitSelection ell d))
      (generator (ell := ell) active hist PatternGadget.generator)).card :
        ZMod (2 ^ ((i.val + 1) * ell))) =
      (-1 : ZMod (2 ^ ((i.val + 1) * ell))) ^ r *
      ((2 ^ ell + d : ℕ) : ZMod (2 ^ ((i.val + 1) * ell))) *
      (2 : ZMod (2 ^ ((i.val + 1) * ell))) ^ (i.val * ell) := by
  classical
  rw [selected_ideal_eq,stage_card_zmod hr (by simp [PatternGadget.Vertex])
    active hist PatternGadget.generator i hi (digitSelection ell d)]
  rw [pattern_subtype_ideal,digitSelection,PatternGadget.ideal_card_bits hd]

end AntichainOfGivenSize.Paper.UpperConstruction
