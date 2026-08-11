import AntichainOfGivenSize.LowerBound.BoundedProfiles

/-!
# Padding bounded profiles

A positive number of generator coordinates can be padded to any larger
coordinate count by repeating one generator.  The zero-coordinate profile is
the sole edge case: its generated ideal is empty and hence has value zero.
-/

open Finset

namespace AntichainOfGivenSize.ClusterLowerBound

/-- Map a larger nonempty index type onto a smaller nonempty one, acting as
the identity on the canonical copy of `Fin k`. -/
def paddedIndex {k K : ℕ} (_hk : k ≤ K) (hkpos : 0 < k) (i : Fin K) : Fin k :=
  if hi : i.1 < k then ⟨i.1, hi⟩ else ⟨0, hkpos⟩

@[simp] theorem paddedIndex_castLE {k K : ℕ} (hk : k ≤ K) (hkpos : 0 < k)
    (i : Fin k) :
    paddedIndex hk hkpos (Fin.castLE hk i) = i := by
  simp [paddedIndex]

/-- Repeat generator zero outside the canonical copy of the original index
type. -/
noncomputable def BoundedProfile.paddedGenerators {k K B : ℕ}
    (x : BoundedProfile k B) (hk : k ≤ K) (hkpos : 0 < k) :
    Fin K → Finset (VennProfile.ProfilePoint x.toNatProfile) :=
  fun i ↦ VennProfile.profileGenerator x.toNatProfile
    (paddedIndex hk hkpos i)

theorem BoundedProfile.generatedIdealIdx_paddedGenerators {k K B : ℕ}
    (x : BoundedProfile k B) (hk : k ≤ K) (hkpos : 0 < k) :
    AntichainOfGivenSize.Section6.generatedIdealIdx Finset.univ
        (x.paddedGenerators hk hkpos) =
      AntichainOfGivenSize.Section6.generatedIdealIdx Finset.univ
        (VennProfile.profileGenerator x.toNatProfile) := by
  classical
  ext A
  simp only [AntichainOfGivenSize.Section6.generatedIdealIdx,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨paddedIndex hk hkpos i, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨Fin.castLE hk i, ?_⟩
    simpa [BoundedProfile.paddedGenerators] using hi

/-- A positive-coordinate bounded profile, padded by repeated generators. -/
noncomputable def BoundedProfile.pad {k K B : ℕ}
    (x : BoundedProfile k B) (hk : k ≤ K) (hkpos : 0 < k) :
    BoundedProfile K B :=
  BoundedProfile.ofIndexedFamily (x.paddedGenerators hk hkpos)
    (fun i ↦ x.card_profileGenerator_le (paddedIndex hk hkpos i))

@[simp] theorem BoundedProfile.value_pad {k K B : ℕ}
    (x : BoundedProfile k B) (hk : k ≤ K) (hkpos : 0 < k) :
    (x.pad hk hkpos).value = x.value := by
  rw [BoundedProfile.pad, BoundedProfile.value_ofIndexedFamily,
    x.generatedIdealIdx_paddedGenerators hk hkpos]
  rfl

@[simp] theorem BoundedProfile.value_eq_zero_of_no_coordinates {B : ℕ}
    (x : BoundedProfile 0 B) :
    x.value = 0 := by
  simp [BoundedProfile.value,
    AntichainOfGivenSize.Section6.generatedIdealIdx]

/-- Every residue using at most `K > 0` coordinates is either zero or is
represented after padding by a profile with exactly `K` coordinates. -/
theorem boundedResiduesUpTo_subset_insert_zero {K B : ℕ} (_hK : 0 < K) :
    boundedResiduesUpTo K B ⊆ insert 0 (boundedResidues K B) := by
  classical
  intro z hz
  rcases Finset.mem_biUnion.1 hz with ⟨k, hkRange, hz⟩
  have hkK : k ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hkRange)
  rcases mem_boundedResidues_iff.1 hz with ⟨x, rfl⟩
  by_cases hkzero : k = 0
  · subst k
    simp
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
    apply Finset.mem_insert_of_mem
    exact mem_boundedResidues_iff.2 ⟨x.pad hkK hkpos, by simp⟩

/-- Cardinal version of `boundedResiduesUpTo_subset_insert_zero`. -/
theorem boundedResiduesUpTo_card_le_exact_add_one {K B : ℕ} (hK : 0 < K) :
    #(boundedResiduesUpTo K B) ≤ #(boundedResidues K B) + 1 := by
  calc
    #(boundedResiduesUpTo K B) ≤
        #(insert 0 (boundedResidues K B)) :=
      Finset.card_le_card (boundedResiduesUpTo_subset_insert_zero hK)
    _ ≤ #(boundedResidues K B) + 1 := Finset.card_insert_le _ _

end AntichainOfGivenSize.ClusterLowerBound
