import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.EquivFin

open Finset

namespace AntichainOfGivenSize.FaithfulLower

/-- A connected induced finite graph with at least two vertices can lose one
vertex while remaining connected. This is Mathlib's vertex-removal theorem
transported back from nested subtypes to a finset. -/
theorem exists_connected_erase {V : Type*} [DecidableEq V]
    (g : SimpleGraph V) {C : Finset V}
    (hC : (g.induce (C : Set V)).Connected) (hcard : 1 < C.card) :
    ∃ v ∈ C, (g.induce (C.erase v : Set V)).Connected := by
  classical
  letI : Nontrivial ↥(C : Set V) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by simpa using hcard)
  obtain ⟨v, hv⟩ := hC.exists_connected_induce_compl_singleton_of_finite_nontrivial
  let f : ((g.induce (C : Set V)).induce {v}ᶜ) →g
      g.induce (C.erase v.1 : Set V) :=
    { toFun := fun x ↦ ⟨x.1.1, mem_erase.mpr ⟨by
        intro heq
        apply x.2
        exact Subtype.ext heq, x.1.2⟩⟩
      map_rel' := fun h ↦ h }
  refine ⟨v.1, v.2, SimpleGraph.Connected.map f ?_ hv⟩
  intro y
  refine ⟨⟨⟨y.1, (mem_erase.mp y.2).2⟩, ?_⟩, ?_⟩
  · intro heq
    exact (mem_erase.mp y.2).1 (congrArg Subtype.val heq)
  · exact Subtype.ext rfl

/-- Every finite connected induced graph contains a connected induced set of
each positive size up to its cardinality. -/
theorem exists_connected_subset_card {V : Type*} [DecidableEq V]
    (g : SimpleGraph V) {C : Finset V}
    (hC : (g.induce (C : Set V)).Connected) {h : ℕ}
    (hpos : 0 < h) (hsize : h ≤ C.card) :
    ∃ D ⊆ C, D.card = h ∧ (g.induce (D : Set V)).Connected := by
  classical
  induction hn : C.card using Nat.strong_induction_on generalizing C with
  | h n ih =>
    by_cases heq : h = C.card
    · exact ⟨C, Subset.rfl, heq.symm, hC⟩
    · have hlt : h < C.card := lt_of_le_of_ne hsize heq
      obtain ⟨v, hv, hconn⟩ := exists_connected_erase g hC (by omega)
      have hsmall : (C.erase v).card < n := by
        rw [← hn]
        exact card_erase_lt_of_mem hv
      have hsize' : h ≤ (C.erase v).card := by
        rw [card_erase_of_mem hv]
        omega
      obtain ⟨D, hD, hcard, hconnected⟩ :=
        ih (C.erase v).card hsmall hconn hsize' rfl
      exact ⟨D, hD.trans (erase_subset v C), hcard, hconnected⟩

/-- Trim all members of an indexed disjoint connected packing to the same
positive size, without changing its index set. -/
theorem exists_disjoint_connected_subsets_card
    {ι V : Type*} [DecidableEq V] (g : SimpleGraph V)
    (C : ι → Finset V) {h : ℕ} (hpos : 0 < h)
    (hconnected : ∀ a, (g.induce (C a : Set V)).Connected)
    (hsize : ∀ a, h ≤ (C a).card)
    (hdisjoint : Pairwise (fun a b ↦ Disjoint (C a) (C b))) :
    ∃ D : ι → Finset V,
      (∀ a, D a ⊆ C a ∧ (D a).card = h ∧
        (g.induce (D a : Set V)).Connected) ∧
      Pairwise (fun a b ↦ Disjoint (D a) (D b)) := by
  classical
  choose D hD using fun a ↦
    exists_connected_subset_card g (hconnected a) hpos (hsize a)
  refine ⟨D, hD, ?_⟩
  intro a b hab
  exact (hdisjoint hab).mono (hD a).1 (hD b).1


end AntichainOfGivenSize.FaithfulLower
