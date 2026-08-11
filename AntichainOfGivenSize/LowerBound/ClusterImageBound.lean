import AntichainOfGivenSize.LowerBound.BoundedProfiles
import AntichainOfGivenSize.LowerBound.FiniteFiberBound

/-!
# From clustered fibers to bounded-profile residues
-/

open Finset

namespace AntichainOfGivenSize.ClusterLowerBound

/-- Exact natural values represented by bounded `K`-profiles. -/
noncomputable def boundedValues (K B : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (BoundedProfile K B)).image BoundedProfile.value

theorem boundedResidues_card_le_boundedValues_card (K B : ℕ) :
    #(boundedResidues K B) ≤ #(boundedValues K B) := by
  classical
  have hfactor : boundedResidues K B =
      (boundedValues K B).image (fun n : ℕ ↦ (n : ZMod (2 ^ B))) := by
    ext z
    simp [boundedResidues, boundedValues]
  rw [hfactor]
  exact Finset.card_image_le

/-- A code with fiber diameter `D` bounds the residue image by
`|Code|(D+1)`. -/
theorem boundedResidues_card_le_of_encoding
    {K B D : ℕ} {Code : Type*} [Fintype Code] [DecidableEq Code]
    (encode : BoundedProfile K B → Code)
    (hdiam : ∀ x y, encode x = encode y →
      Int.natAbs ((x.value : ℤ) - (y.value : ℤ)) ≤ D) :
    #(boundedResidues K B) ≤ Fintype.card Code * (D + 1) := by
  exact (boundedResidues_card_le_boundedValues_card K B).trans
    (card_image_le_card_mul_of_fiber_diameter encode BoundedProfile.value D hdiam)

/-- Union bound for profiles with at most `K` coordinates. -/
theorem boundedResiduesUpTo_card_le_of_each {K B C : ℕ}
    (h : ∀ k ∈ Finset.range (K + 1), #(boundedResidues k B) ≤ C) :
    #(boundedResiduesUpTo K B) ≤ (K + 1) * C := by
  unfold boundedResiduesUpTo
  calc
    #((Finset.range (K + 1)).biUnion fun k ↦ boundedResidues k B) ≤
        ∑ k ∈ Finset.range (K + 1), #(boundedResidues k B) :=
      Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.range (K + 1), C := by
      apply Finset.sum_le_sum
      intro k hk
      exact h k hk
    _ = (K + 1) * C := by simp

end AntichainOfGivenSize.ClusterLowerBound
