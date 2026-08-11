import AntichainOfGivenSize.LowerBound.VennProfiles

/-!
# Bounded Venn profiles

This file provides the finite parameter space used in the connected-cluster
lower-bound argument. A profile on `K` labelled generators is bounded at
load `B` when every Venn atom has multiplicity at most `B`, the empty atom is
discarded, and every generator contains at most `B` points.
-/

open scoped BigOperators
open Finset

namespace AntichainOfGivenSize.ClusterLowerBound

/-- The natural-valued multiplicity function underlying a finite profile. -/
def atomMultiplicity {K B : ℕ}
    (x : Finset (Fin K) → Fin (B + 1)) (A : Finset (Fin K)) : ℕ :=
  (x A).1

/-- Load of generator `i` in a finite Venn profile. -/
def profileLoad {K B : ℕ}
    (x : Finset (Fin K) → Fin (B + 1)) (i : Fin K) : ℕ :=
  ∑ A ∈ Finset.univ.powerset.filter (fun A : Finset (Fin K) ↦ i ∈ A),
    atomMultiplicity x A

/-- An atom belonging to generator `i` is counted in the singleton
intersection exponent at `i`. -/
theorem atom_le_singletonIntersection {K : ℕ}
    (x : Finset (Fin K) → ℕ) {A : Finset (Fin K)} {i : Fin K}
    (hi : i ∈ A) :
    x A ≤ VennProfile.profileIntersectionSize x {i} := by
  classical
  unfold VennProfile.profileIntersectionSize
  apply Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
  simp [hi]

/-- A finite Venn profile with `K` labelled generators and maximum load `B`.

The empty-pattern multiplicity is normalized to zero because points outside
all generators do not affect the generated ideal. -/
structure BoundedProfile (K B : ℕ) where
  atom : Finset (Fin K) → Fin (B + 1)
  empty_zero : atom ∅ = 0
  load_le : ∀ i : Fin K, profileLoad atom i ≤ B

noncomputable instance (K B : ℕ) : Fintype (BoundedProfile K B) :=
  Fintype.ofInjective BoundedProfile.atom (by
    intro x y h
    cases x
    cases y
    simp_all)

noncomputable instance (K B : ℕ) : DecidableEq (BoundedProfile K B) :=
  Classical.decEq _

/-- The natural-valued Venn multiplicities of a bounded profile. -/
def BoundedProfile.toNatProfile {K B : ℕ} (x : BoundedProfile K B) :
    Finset (Fin K) → ℕ :=
  atomMultiplicity x.atom

/-- Package a natural-valued profile whose empty atom is zero and whose
singleton intersection exponents are bounded by `B`. -/
noncomputable def BoundedProfile.ofNatProfile {K B : ℕ}
    (x : Finset (Fin K) → ℕ) (hempty : x ∅ = 0)
    (hload : ∀ i : Fin K,
      VennProfile.profileIntersectionSize x {i} ≤ B) :
    BoundedProfile K B where
  atom := fun A ↦ ⟨x A, by
    by_cases hA : A.Nonempty
    · rcases hA with ⟨i, hi⟩
      exact Nat.lt_succ_of_le ((atom_le_singletonIntersection x hi).trans (hload i))
    · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      simp [hAempty, hempty]⟩
  empty_zero := by simp [hempty]
  load_le := by
    intro i
    simpa [profileLoad, atomMultiplicity,
      VennProfile.profileIntersectionSize] using hload i

@[simp] theorem BoundedProfile.toNatProfile_ofNatProfile {K B : ℕ}
    (x : Finset (Fin K) → ℕ) (hempty)
    (hload : ∀ i : Fin K,
      VennProfile.profileIntersectionSize x {i} ≤ B) :
    (BoundedProfile.ofNatProfile x hempty hload).toNatProfile = x := by
  rfl

@[simp] theorem BoundedProfile.toNatProfile_empty {K B : ℕ}
    (x : BoundedProfile K B) : x.toNatProfile ∅ = 0 := by
  simp [BoundedProfile.toNatProfile, atomMultiplicity, x.empty_zero]

/-- Intersection exponent attached to a set of generator indices. -/
def BoundedProfile.intersectionSize {K B : ℕ} (x : BoundedProfile K B)
    (I : Finset (Fin K)) : ℕ :=
  VennProfile.profileIntersectionSize x.toNatProfile I

/-- Cardinality of the canonical ideal represented by a bounded profile. -/
noncomputable def BoundedProfile.value {K B : ℕ}
    (x : BoundedProfile K B) : ℕ :=
  (Section6.generatedIdealIdx Finset.univ
    (VennProfile.profileGenerator x.toNatProfile)).card

/-- The canonical profile value is exactly its inclusion--exclusion
expression. -/
theorem BoundedProfile.value_cast {K B : ℕ} (x : BoundedProfile K B) :
    (x.value : ℤ) = VennProfile.vennExpression x.toNatProfile := by
  exact VennProfile.generatedIdealIdx_profileGenerator_card x.toNatProfile

/-- The profile load is the singleton intersection exponent. -/
theorem profileLoad_eq_intersectionSize_singleton {K B : ℕ}
    (x : BoundedProfile K B) (i : Fin K) :
    profileLoad x.atom i = x.intersectionSize {i} := by
  classical
  simp only [profileLoad, BoundedProfile.intersectionSize,
    VennProfile.profileIntersectionSize, BoundedProfile.toNatProfile,
    atomMultiplicity]
  congr 1
  ext A
  simp

/-- Each canonical generator has exactly the corresponding profile load. -/
theorem card_profileGenerator_eq_profileLoad {K B : ℕ}
    (x : BoundedProfile K B) (i : Fin K) :
    (VennProfile.profileGenerator x.toNatProfile i).card =
      profileLoad x.atom i := by
  classical
  let I : Finset (Fin K) := {i}
  have hI : I.Nonempty := by simp [I]
  calc
    (VennProfile.profileGenerator x.toNatProfile i).card =
        (I.inf' hI (VennProfile.profileGenerator x.toNatProfile)).card := by
      apply congrArg Finset.card
      ext p
      simp [I]
    _ = VennProfile.profileIntersectionSize
        (VennProfile.atomCount
          (VennProfile.profileGenerator x.toNatProfile)) I :=
      VennProfile.inf_card_eq_profileIntersectionSize _ I hI
    _ = VennProfile.profileIntersectionSize x.toNatProfile I := by
      congr 1
      funext A
      exact VennProfile.atomCount_profileGenerator x.toNatProfile A
    _ = profileLoad x.atom i := by
      symm
      exact profileLoad_eq_intersectionSize_singleton x i

/-- Every generator in the canonical family has cardinality at most `B`. -/
theorem BoundedProfile.card_profileGenerator_le {K B : ℕ}
    (x : BoundedProfile K B) (i : Fin K) :
    (VennProfile.profileGenerator x.toNatProfile i).card ≤ B := by
  rw [card_profileGenerator_eq_profileLoad]
  exact x.load_le i

/-- Residues modulo `2^B` realized by bounded `K`-profiles. -/
noncomputable def boundedResidues (K B : ℕ) : Finset (ZMod (2 ^ B)) :=
  Finset.univ.image fun x : BoundedProfile K B ↦ (x.value : ZMod (2 ^ B))

/-- Residues represented using at most `K` generators. -/
noncomputable def boundedResiduesUpTo (K B : ℕ) : Finset (ZMod (2 ^ B)) :=
  (Finset.range (K + 1)).biUnion fun k ↦ boundedResidues k B

@[simp] theorem mem_boundedResidues_iff {K B : ℕ} {z : ZMod (2 ^ B)} :
    z ∈ boundedResidues K B ↔
      ∃ x : BoundedProfile K B, (x.value : ZMod (2 ^ B)) = z := by
  classical
  simp [boundedResidues]

theorem boundedResidues_subset_upTo {k K B : ℕ} (hk : k ≤ K) :
    boundedResidues k B ⊆ boundedResiduesUpTo K B := by
  intro z hz
  exact Finset.mem_biUnion.2 ⟨k, Finset.mem_range.2 (by omega), hz⟩

theorem mem_boundedResiduesUpTo_of_profile {k K B : ℕ}
    (hk : k ≤ K) (x : BoundedProfile k B) :
    (x.value : ZMod (2 ^ B)) ∈ boundedResiduesUpTo K B := by
  exact boundedResidues_subset_upTo hk (mem_boundedResidues_iff.2 ⟨x, rfl⟩)

/-! ## From indexed families to bounded profiles -/

/-- Discard the Venn atom outside every generator. -/
def normalizedAtomCount {K V : Type*} [Fintype K] [DecidableEq K]
    [Fintype V] [DecidableEq V] (G : K → Finset V) (A : Finset K) : ℕ :=
  if A = ∅ then 0 else VennProfile.atomCount G A

@[simp] theorem normalizedAtomCount_empty {K V : Type*}
    [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]
    (G : K → Finset V) : normalizedAtomCount G ∅ = 0 := by
  simp [normalizedAtomCount]

/-- Removing the empty Venn atom does not change a nonempty generator
intersection exponent. -/
theorem profileIntersectionSize_normalizedAtomCount {K V : Type*}
    [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]
    (G : K → Finset V) (I : Finset K) (hI : I.Nonempty) :
    VennProfile.profileIntersectionSize (normalizedAtomCount G) I =
      VennProfile.profileIntersectionSize (VennProfile.atomCount G) I := by
  classical
  unfold VennProfile.profileIntersectionSize
  apply Finset.sum_congr rfl
  intro A hA
  have hsub : I ⊆ A := (Finset.mem_filter.1 hA).2
  have hAne : A ≠ ∅ := by
    intro hzero
    subst A
    exact hI.ne_empty (Finset.subset_empty.mp hsub)
  simp [normalizedAtomCount, hAne]

/-- The singleton exponent of the normalized atom profile is the size of
the corresponding generator. -/
theorem profileIntersectionSize_normalized_singleton {K V : Type*}
    [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]
    (G : K → Finset V) (i : K) :
    VennProfile.profileIntersectionSize (normalizedAtomCount G) {i} =
      (G i).card := by
  rw [profileIntersectionSize_normalizedAtomCount G {i} (by simp)]
  symm
  simpa using
    VennProfile.inf_card_eq_profileIntersectionSize G {i} (by simp)

/-- Normalizing the empty atom leaves the full inclusion--exclusion
expression unchanged. -/
theorem vennExpression_normalizedAtomCount {K V : Type*}
    [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]
    (G : K → Finset V) :
    VennProfile.vennExpression (normalizedAtomCount G) =
      VennProfile.vennExpression (VennProfile.atomCount G) := by
  classical
  unfold VennProfile.vennExpression
  apply Finset.sum_congr rfl
  intro I hI
  congr 2
  exact profileIntersectionSize_normalizedAtomCount G I.1
    (Finset.mem_filter.1 I.2).2

/-- An indexed family whose generators have size at most `B` determines a
bounded profile with the same ideal cardinality. -/
noncomputable def BoundedProfile.ofIndexedFamily {K B : ℕ}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : Fin K → Finset V) (hload : ∀ i, (G i).card ≤ B) :
    BoundedProfile K B :=
  BoundedProfile.ofNatProfile (normalizedAtomCount G)
    (normalizedAtomCount_empty G) (by
      intro i
      rw [profileIntersectionSize_normalized_singleton]
      exact hload i)

/-- The bounded profile associated to an indexed family has exactly the
same generated-ideal cardinality. -/
theorem BoundedProfile.value_ofIndexedFamily {K B : ℕ}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : Fin K → Finset V) (hload : ∀ i, (G i).card ≤ B) :
    (BoundedProfile.ofIndexedFamily G hload).value =
      (Section6.generatedIdealIdx Finset.univ G).card := by
  have hv :=
    BoundedProfile.value_cast (BoundedProfile.ofIndexedFamily G hload)
  change ((BoundedProfile.ofIndexedFamily G hload).value : ℤ) =
    VennProfile.vennExpression (normalizedAtomCount G) at hv
  rw [vennExpression_normalizedAtomCount] at hv
  have hg := VennProfile.generatedIdealIdx_card_eq_vennExpression G
  exact Int.ofNat_injective (hv.trans hg.symm)

/-- A Venn profile representing an integer below `2^B` can be normalized to
a bounded profile with the same number of coordinates and the same value. -/
theorem exists_boundedProfile_of_hasVennProfile {n k B : ℕ}
    (hprofile : VennProfile.HasVennProfile n k) (hn : n < 2 ^ B) :
    ∃ x : BoundedProfile k B, x.value = n := by
  classical
  rcases hprofile with ⟨p, hp⟩
  let G : Fin k → Finset (VennProfile.ProfilePoint p) :=
    VennProfile.profileGenerator p
  have hvalueInt := VennProfile.generatedIdealIdx_profileGenerator_card p
  have hvalue : (Section6.generatedIdealIdx Finset.univ G).card = n := by
    exact_mod_cast hvalueInt.trans hp.symm
  have hload : ∀ i, (G i).card ≤ B := by
    intro i
    have hsubset : (G i).powerset ⊆ Section6.generatedIdealIdx Finset.univ G := by
      intro A hA
      simp only [Section6.generatedIdealIdx, Finset.mem_biUnion,
        Finset.mem_univ, true_and]
      exact ⟨i, hA⟩
    have hcard : 2 ^ (G i).card ≤ n := by
      rw [← Finset.card_powerset, ← hvalue]
      exact Finset.card_le_card hsubset
    have hpow : 2 ^ (G i).card < 2 ^ B := hcard.trans_lt hn
    exact ((Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).1 hpow).le
  let x : BoundedProfile k B := BoundedProfile.ofIndexedFamily G hload
  refine ⟨x, ?_⟩
  exact (BoundedProfile.value_ofIndexedFamily G hload).trans hvalue

/-- Any ideal of cardinality below `2^B` and generator number at most `K`
produces a residue in the bounded profile image. -/
theorem alpha_le_imp_mem_boundedResiduesUpTo {n K B : ℕ}
    (hK : AntichainOfGivenSize.alpha n ≤ K) (hn : n < 2 ^ B) :
    (n : ZMod (2 ^ B)) ∈ boundedResiduesUpTo K B := by
  let k := AntichainOfGivenSize.alpha n
  have hkK : k ≤ K := hK
  have hp : VennProfile.HasVennProfile n k :=
    VennProfile.hasVennProfile_of_hasGeneratorCount
      (AntichainOfGivenSize.alpha_hasGeneratorCount n)
  rcases exists_boundedProfile_of_hasVennProfile hp hn with ⟨x, hx⟩
  simpa [hx] using mem_boundedResiduesUpTo_of_profile hkK x

end AntichainOfGivenSize.ClusterLowerBound
