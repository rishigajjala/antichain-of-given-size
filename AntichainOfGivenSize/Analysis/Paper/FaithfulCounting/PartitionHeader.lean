import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max

open Finset

namespace AntichainOfGivenSize.FaithfulLower

/-- The unlabeled partition in the manuscript's header. -/
abbrev Partition (K : ℕ) := Finpartition (univ : Finset (Fin K))

/-- Each vertex records the least element of its own part. -/
noncomputable def partitionCode {K : ℕ} (P : Partition K) (i : Fin K) : Fin K :=
  (P.part i).min' (P.part_nonempty.mpr (mem_univ i))

theorem partitionCode_mem {K : ℕ} (P : Partition K) (i : Fin K) :
    partitionCode P i ∈ P.part i :=
  Finset.min'_mem _ _

theorem partitionCode_eq_iff_part_eq {K : ℕ} (P : Partition K) (i j : Fin K) :
    partitionCode P i = partitionCode P j ↔ P.part i = P.part j := by
  constructor
  · intro h
    apply P.eq_of_mem_parts (P.part_mem.mpr (mem_univ i))
      (P.part_mem.mpr (mem_univ j)) (partitionCode_mem P i)
    rw [h]
    exact partitionCode_mem P j
  · intro h
    simp only [partitionCode, h]

theorem partitionCode_eq_iff_mem {K : ℕ} (P : Partition K) (i j : Fin K) :
    partitionCode P i = partitionCode P j ↔ i ∈ P.part j := by
  rw [partitionCode_eq_iff_part_eq]
  exact (P.mem_part_iff_part_eq_part (mem_univ i) (mem_univ j)).symm

/-- The partition is recovered as the fibers of the recorded function. -/
theorem part_eq_code_fiber {K : ℕ} (P : Partition K) (j : Fin K) :
    P.part j = univ.filter (fun i ↦ partitionCode P i = partitionCode P j) := by
  classical
  ext i
  simp only [mem_filter, mem_univ, true_and, partitionCode_eq_iff_mem]

theorem partitionCode_injective (K : ℕ) :
    Function.Injective (partitionCode : Partition K → Fin K → Fin K) := by
  intro P Q h
  have hpart : ∀ i, P.part i = Q.part i := by
    intro i
    rw [part_eq_code_fiber, part_eq_code_fiber, h]
  apply Finpartition.ext
  ext C
  constructor
  · intro hC
    obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts hC
    have heq := P.part_eq_of_mem hC hi
    rw [← heq, hpart]
    exact Q.part_mem.mpr (mem_univ i)
  · intro hC
    obtain ⟨i, hi⟩ := Q.nonempty_of_mem_parts hC
    have heq := Q.part_eq_of_mem hC hi
    rw [← heq, ← hpart]
    exact P.part_mem.mpr (mem_univ i)

/-- The exact paper bound, including the empty ground set. -/
theorem card_partitions_le (K : ℕ) :
    Fintype.card (Partition K) ≤ K ^ K := by
  simpa [Fintype.card_pi_const] using
    Fintype.card_le_of_injective partitionCode (partitionCode_injective K)

/-- Adding the selected threshold gives the manuscript's header bound. -/
theorem card_headers_le (J K : ℕ) :
    Fintype.card (Fin (J + 1) × Partition K) ≤ (J + 1) * K ^ K := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    Nat.mul_le_mul_left (J + 1) (card_partitions_le K)


end AntichainOfGivenSize.FaithfulLower
