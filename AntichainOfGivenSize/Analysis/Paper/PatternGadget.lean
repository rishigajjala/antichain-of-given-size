import AntichainOfGivenSize.Model.ProblemSetting
import AntichainOfGivenSize.Analysis.Section6.Core
import AntichainOfGivenSize.Analysis.Section6.Remainder

/-!
# The nested pattern gadget (Claim 6.2)

The left copy of `Fin ell` is the set `T`; the right copy supplies distinct
tags. The baseline generator is always present. A selected tag at position
`a` contributes exactly the subsets of the first `a` baseline elements
with that tag adjoined.
-/

open Finset

namespace AntichainOfGivenSize.Paper.PatternGadget

def tagged {ell : ℕ} (a : Fin ell) : Finset (Finset (Vertex ell)) :=
  (initialSegment a).powerset.image (insert (Sum.inr a))

@[simp] theorem mem_baseline {ell : ℕ} {v : Vertex ell} :
    v ∈ baseline ell ↔ ∃ a, v = Sum.inl a := by
  simp [baseline, eq_comm]

@[simp] theorem inr_not_mem_initialSegment {ell : ℕ} (a b : Fin ell) :
    Sum.inr b ∉ initialSegment a := by simp [initialSegment]

theorem initialSegment_subset_baseline {ell : ℕ} (a : Fin ell) :
    initialSegment a ⊆ baseline ell := by
  exact Finset.map_subset_map.mpr (Finset.subset_univ _)

@[simp] theorem card_baseline (ell : ℕ) : #(baseline ell) = ell := by
  simp [baseline]

@[simp] theorem card_initialSegment {ell : ℕ} (a : Fin ell) : #(initialSegment a) = a.val := by
  simp [initialSegment]

@[simp] theorem baseline_selected {ell : ℕ} (D : Finset (Fin ell)) :
    none ∈ selected D := by simp [selected]

@[simp] theorem some_selected_iff {ell : ℕ} (D : Finset (Fin ell)) (a : Fin ell) :
    some a ∈ selected D ↔ a ∈ D := by simp [selected]

@[simp] theorem card_selected {ell : ℕ} (D : Finset (Fin ell)) :
    #(selected D) = #D + 1 := by
  simp [selected, Finset.card_image_of_injective D (Option.some_injective (Fin ell))]

theorem card_selected_le {ell : ℕ} (D : Finset (Fin ell)) :
    #(selected D) ≤ ell + 1 := by
  rw [card_selected]
  simpa using Nat.add_le_add_right (Finset.card_le_univ D) 1

theorem mem_tagged_iff {ell : ℕ} {a : Fin ell} {S : Finset (Vertex ell)} :
    S ∈ tagged a ↔ Sum.inr a ∈ S ∧ S ⊆ generator (some a) := by
  constructor
  · intro h
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp h
    exact ⟨Finset.mem_insert_self _ _, Finset.insert_subset_insert _
      (Finset.mem_powerset.mp hR)⟩
  · rintro ⟨ha, hS⟩
    refine Finset.mem_image.mpr ⟨S.erase (Sum.inr a), Finset.mem_powerset.mpr ?_,
      Finset.insert_erase ha⟩
    intro v hv
    have hv' := Finset.mem_erase.mp hv
    rcases Finset.mem_insert.mp (hS hv'.2) with heq | hp
    · exact (hv'.1 heq).elim
    · exact hp

theorem card_tagged {ell : ℕ} (a : Fin ell) : #(tagged a) = 2 ^ a.val := by
  rw [tagged, Finset.card_image_iff.mpr]
  · simp
  · intro S hS R hR heq
    have hS' : Sum.inr a ∉ S := fun h ↦ inr_not_mem_initialSegment a a
      ((Finset.mem_powerset.mp hS) h)
    have hR' : Sum.inr a ∉ R := fun h ↦ inr_not_mem_initialSegment a a
      ((Finset.mem_powerset.mp hR) h)
    have := congrArg (Finset.erase · (Sum.inr a)) heq
    simpa [hS', hR'] using this

theorem disjoint_baseline_tagged {ell : ℕ} (a : Fin ell) :
    Disjoint (baseline ell).powerset (tagged a) := by
  rw [Finset.disjoint_left]
  intro S hS htag
  have hmem := (Finset.mem_powerset.mp hS) (mem_tagged_iff.mp htag).1
  simp at hmem

theorem disjoint_tagged {ell : ℕ} {a b : Fin ell} (hab : a ≠ b) :
    Disjoint (tagged a) (tagged b) := by
  rw [Finset.disjoint_left]
  intro S hSa hSb
  have hmem := (mem_tagged_iff.mp hSb).2 (mem_tagged_iff.mp hSa).1
  rcases Finset.mem_insert.mp hmem with heq | hpre
  · exact hab (Sum.inr.inj heq)
  · exact inr_not_mem_initialSegment b a hpre

theorem ideal_decomposition {ell : ℕ} (D : Finset (Fin ell)) :
    Section6.generatedIdealIdx (selected D) generator =
      (baseline ell).powerset ∪ D.biUnion tagged := by
  ext S
  simp only [Section6.generatedIdealIdx, Finset.mem_biUnion, Finset.mem_union,
    Finset.mem_powerset]
  constructor
  · rintro ⟨i, hi, hS⟩
    cases i with
    | none => exact Or.inl hS
    | some a =>
      by_cases ha : Sum.inr a ∈ S
      · exact Or.inr ⟨a, (some_selected_iff D a).mp hi,
          mem_tagged_iff.mpr ⟨ha, hS⟩⟩
      · left
        intro v hv
        rcases Finset.mem_insert.mp (hS hv) with heq | hp
        · exact (ha (heq ▸ hv)).elim
        · exact initialSegment_subset_baseline a hp
  · rintro (hS | ⟨a, ha, htag⟩)
    · exact ⟨none, baseline_selected D, hS⟩
    · exact ⟨some a, (some_selected_iff D a).mpr ha, (mem_tagged_iff.mp htag).2⟩

theorem ideal_card {ell : ℕ} (D : Finset (Fin ell)) :
    #(Section6.generatedIdealIdx (selected D) generator) =
      2 ^ ell + ∑ a ∈ D, 2 ^ a.val := by
  rw [ideal_decomposition, Finset.card_union_of_disjoint]
  · rw [Finset.card_biUnion]
    · simp [card_tagged]
    · intro a _ha b _hb hab
      exact disjoint_tagged hab
  · rw [Finset.disjoint_biUnion_right]
    intro a _ha
    exact disjoint_baseline_tagged a

/-- Claim 6.2 in the current manuscript, including the unchanged `+d`. -/
theorem ideal_card_bits {ell d : ℕ} (hd : d < 2 ^ ell) :
    #(Section6.generatedIdealIdx (selected (selectedBits ell d)) generator) =
      2 ^ ell + d := by
  rw [ideal_card]
  congr 1
  simpa [selectedBits, Section6.lowBitsValue, Finset.sum_filter] using
    Section6.lowBitsValue_eq hd

end AntichainOfGivenSize.Paper.PatternGadget
