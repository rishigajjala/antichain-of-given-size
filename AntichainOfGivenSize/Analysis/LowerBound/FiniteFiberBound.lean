import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

/-!
# Finite images from bounded-diameter fibers

This elementary lemma converts the cluster code into an image-cardinality
bound.  Every encoding fiber contributes at most `D+1` natural values.
-/

open Finset

namespace AntichainOfGivenSize.ClusterLowerBound

theorem card_nat_finset_le_of_diameter {s : Finset ℕ} {D : ℕ}
    (hdiam : ∀ a ∈ s, ∀ b ∈ s,
      Int.natAbs ((a : ℤ) - (b : ℤ)) ≤ D) :
    #s ≤ D + 1 := by
  classical
  by_cases hs : s.Nonempty
  · let m := s.min' hs
    have hm : m ∈ s := Finset.min'_mem s hs
    have hsub : s ⊆ Finset.Icc m (m + D) := by
      intro a ha
      have hma : m ≤ a := Finset.min'_le s a ha
      have hd := hdiam a ha m hm
      rw [Int.natAbs_natCast_sub_natCast_of_ge hma] at hd
      exact Finset.mem_Icc.2 ⟨hma, by omega⟩
    calc
      #s ≤ #(Finset.Icc m (m + D)) := Finset.card_le_card hsub
      _ = D + 1 := by simp; omega
  · simp only [Finset.not_nonempty_iff_eq_empty] at hs
    simp [hs]

/-- A map with diameter at most `D` on every fiber has image cardinality at
most `|S|(D+1)`. -/
theorem card_image_le_card_mul_of_fiber_diameter
    {X S : Type*} [Fintype X] [Fintype S]
    [DecidableEq X] [DecidableEq S]
    (encode : X → S) (value : X → ℕ) (D : ℕ)
    (hdiam : ∀ x y, encode x = encode y →
      Int.natAbs ((value x : ℤ) - (value y : ℤ)) ≤ D) :
    #((Finset.univ : Finset X).image value) ≤ Fintype.card S * (D + 1) := by
  classical
  let fiberValues : S → Finset ℕ := fun s ↦
    ((Finset.univ : Finset X).filter fun x ↦ encode x = s).image value
  have himage : (Finset.univ : Finset X).image value =
      (Finset.univ : Finset S).biUnion fiberValues := by
    ext n
    simp [fiberValues]
  rw [himage]
  calc
    #((Finset.univ : Finset S).biUnion fiberValues) ≤
        ∑ s : S, #(fiberValues s) := Finset.card_biUnion_le
    _ ≤ ∑ _s : S, (D + 1) := by
      apply Finset.sum_le_sum
      intro s _hs
      apply card_nat_finset_le_of_diameter
      intro a ha b hb
      rcases Finset.mem_image.1 ha with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.1 hb with ⟨y, hy, rfl⟩
      apply hdiam x y
      exact (Finset.mem_filter.1 hx).2.trans (Finset.mem_filter.1 hy).2.symm
    _ = Fintype.card S * (D + 1) := by simp

end AntichainOfGivenSize.ClusterLowerBound
