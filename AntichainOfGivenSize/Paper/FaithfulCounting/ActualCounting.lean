import AntichainOfGivenSize.Paper.FaithfulCounting.CanonicalHeader
import AntichainOfGivenSize.Paper.FaithfulCounting.RealTailFiberCore
import AntichainOfGivenSize.Paper.FaithfulCounting.NumericalParameters
open scoped BigOperators symmDiff
open Finset
open AntichainOfGivenSize.ClusterCore
open AntichainOfGivenSize.ClusterLowerBound
open AntichainOfGivenSize.Section6

namespace AntichainOfGivenSize.FaithfulLower

variable {K B h J : ℕ}

theorem realProximityGraph_mono {I V : Type*} [DecidableEq I] [DecidableEq V]
    (G : I → Finset V) (B : ℕ) {ρ σ : ℝ} (hρσ : ρ ≤ σ) :
    realProximityGraph G B ρ ≤ realProximityGraph G B σ := by
  intro i j hij
  exact ⟨hij.1, by linarith [hij.2]⟩

/-- A header is certified by exact-size connected fine clusters and the
actual coarse residual components; the certificate is not part of the record. -/
def ValidHeader (x : BoundedProfile K B) (h J : ℕ)
    (ρ : Fin (J + 2) → ℝ) (H : Fin (J + 1) × Partition K) : Prop :=
  ∃ r : ℕ, ∃ P : PackedClusters (realProximityGraph x.generators B (ρ H.1.succ)) h r,
    r ≤ J ∧ (∀ a, (P.cluster a).card = h) ∧
    (∀ i ∈ P.residual,
      (P.componentFiber (realProximityGraph x.generators B (ρ H.1.castSucc)) i).card < h) ∧
    H.2 = headerPartition P (realProximityGraph x.generators B (ρ H.1.castSucc))

theorem exists_validHeader (x : BoundedProfile K B) (h J : ℕ)
    (hpos : 0 < h) (hcover : K < (J + 1) * h)
    (ρ : Fin (J + 2) → ℝ) (hanti : Antitone ρ) :
    ∃ H : Fin (J + 1) × Partition K, ValidHeader x h J ρ H := by
  obtain ⟨j, r, P, hr, hexact, hsmall⟩ := exists_stable_exact_packing hpos hcover
    (fun i ↦ realProximityGraph x.generators B (ρ i)) (by
      intro i j hij
      exact realProximityGraph_mono x.generators B (hanti hij))
  refine ⟨⟨j, headerPartition P (realProximityGraph x.generators B (ρ j.castSucc))⟩,
    r, P, hr, hexact, ?_, rfl⟩
  exact P.componentFiber_card_lt _ hsmall

/-- Intrinsic disagreement uses points from the generators themselves. -/
theorem intrinsicExceptional_subset_generatorUnion {V : Type*} [DecidableEq V]
    (G : Fin K → Finset V) (P : Finset (Finset (Fin K))) :
    intrinsicExceptional G P ⊆ Finset.univ.biUnion G := by
  classical
  intro v hv
  rcases (mem_intrinsicExceptional G P v).1 hv with ⟨C, _hC, i, _hi, j, _hj, hvar⟩
  have hex : v ∈ G i ∨ v ∈ G j := by tauto
  rcases hex with h | h
  · exact mem_biUnion.mpr ⟨i, mem_univ i, h⟩
  · exact mem_biUnion.mpr ⟨j, mem_univ j, h⟩

theorem intrinsicExceptional_card_le_load {V : Type*} [DecidableEq V]
    (G : Fin K → Finset V) (P : Finset (Finset (Fin K)))
    (hsize : ∀ i, #(G i) ≤ B) :
    #(intrinsicExceptional G P) ≤ K * B := by
  classical
  calc
    #(intrinsicExceptional G P) ≤ #(Finset.univ.biUnion G) :=
      card_le_card (intrinsicExceptional_subset_generatorUnion G P)
    _ ≤ #(Finset.univ : Finset (Fin K)) * B :=
      card_biUnion_le_card_mul _ _ _ (fun i _ ↦ hsize i)
    _ = K * B := by simp

theorem packedIntrinsic_card_le {V : Type*} [DecidableEq V] {ρ : ℝ}
    (G : Fin K → Finset V) (hsize : ∀ i, #(G i) ≤ B) (hρ : 0 ≤ ρ)
    {r : ℕ} (P : PackedClusters (realProximityGraph G B ρ) h r) :
    (#(intrinsicExceptional G (packedClusterFamily P)) : ℝ) ≤ 2 * K * ρ := by
  classical
  apply intrinsicExceptional_card_le_two_mul hρ G hsize
  · intro C hC
    obtain ⟨a, _, rfl⟩ := mem_image.mp hC
    exact (P.large a).2.2
  · intro C hC D hD hne
    obtain ⟨a, _, rfl⟩ := mem_image.mp hC
    obtain ⟨b, _, rfl⟩ := mem_image.mp hD
    exact P.pairwise_disjoint (fun hab ↦ hne (congrArg P.cluster hab))

theorem validHeader_exceptional_bound {x : BoundedProfile K B}
    {ρ : Fin (J + 2) → ℝ} {H : Fin (J + 1) × Partition K}
    (hH : ValidHeader x h J ρ H) (hpos : 0 < h) (hρ : 0 ≤ ρ H.1.succ) :
    #(canonicalExceptional x.generators H.2 h) ≤ K * B ∧
      (#(canonicalExceptional x.generators H.2 h) : ℝ) ≤ 2 * K * ρ H.1.succ := by
  obtain ⟨r, P, _hr, hexact, hsmall, heq⟩ := hH
  rw [heq, canonicalExceptional_eq P _ hexact hsmall x.generators hpos]
  exact ⟨intrinsicExceptional_card_le_load _ _ x.card_profileGenerator_le,
    packedIntrinsic_card_le _ x.card_profileGenerator_le hρ P⟩

theorem validHeader_key_bound {x : BoundedProfile K B}
    {ρ : Fin (J + 2) → ℝ} {H : Fin (J + 1) × Partition K}
    (hH : ValidHeader x h J ρ H) (hpos : 0 < h) :
    (centralKeys (canonicalRole H.2 h) (canonicalCenters H.2 h)).card ≤
      2 ^ J * (1 + K * 2 ^ h) := by
  obtain ⟨r, P, hr, hexact, hsmall, heq⟩ := hH
  rw [heq]
  exact canonicalCentralKeys_card_le P _ hexact hsmall hpos hr

theorem validHeader_noncentral_bound {x : BoundedProfile K B}
    {ρ : Fin (J + 2) → ℝ} {H : Fin (J + 1) × Partition K}
    (hH : ValidHeader x h J ρ H) (hρ : 0 ≤ ρ H.1.castSucc)
    (hρB : ρ H.1.castSucc ≤ B)
    (t : IEQuery (univ : Finset (Fin K))) (ht : t ∉ canonicalCenters H.2 h) :
    #(generatorIntersection x.generators t) ≤ B - ⌈ρ H.1.castSucc⌉₊ := by
  obtain ⟨r, P, _hr, hexact, hsmall, heq⟩ := hH
  rw [heq, canonicalCenters_eq P _ hexact hsmall] at ht
  apply noncenter_intersection_card_le_ceil P x.generators hρ hρB t
  simpa [packedCenters] using ht

abbrev HeaderProfiles (K B h J : ℕ) (ρ : Fin (J + 2) → ℝ)
    (H : Fin (J + 1) × Partition K) :=
  {x : BoundedProfile K B // ValidHeader x h J ρ H}

noncomputable def valuesAtHeader (K B h J : ℕ) (ρ : Fin (J + 2) → ℝ)
    (H : Fin (J + 1) × Partition K) : Finset ℕ := by
  classical
  exact (univ : Finset (HeaderProfiles K B h J ρ H)).image (fun x ↦ x.1.value)

theorem valuesAtHeader_card_le (hpos : 0 < h)
    (ρ : Fin (J + 2) → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hρB : ∀ i, ρ i ≤ B)
    (H : Fin (J + 1) × Partition K) :
    (#(valuesAtHeader K B h J ρ H) : ℝ) ≤
      ((K * B + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (K : ℝ)^2 * ρ H.1.succ) *
      (B + 1 : ℝ) ^ (2 ^ J * (1 + K * 2 ^ h)) *
      (2 : ℝ) ^ ((B : ℝ) - ρ H.1.castSucc + K + 2) := by
  classical
  by_cases hX : Nonempty (HeaderProfiles K B h J ρ H)
  · let X := HeaderProfiles K B h J ρ H
    let G : ∀ x : X, Fin K → Finset x.1.Point := fun x ↦ x.1.generators
    let U : ∀ x : X, Finset x.1.Point := fun x ↦ canonicalExceptional (G x) H.2 h
    let u : ℕ := min (K * B) ⌊2 * (K : ℝ) * ρ H.1.succ⌋₊
    have hnonneg : 0 ≤ 2 * (K : ℝ) * ρ H.1.succ :=
      mul_nonneg (by positivity) (hρ H.1.succ)
    have hU : ∀ x : X, (U x).card ≤ u := by
      intro x
      have hu := validHeader_exceptional_bound x.2 hpos (hρ _)
      exact le_min hu.1 ((Nat.le_floor_iff hnonneg).2 hu.2)
    have huB : u ≤ K * B := min_le_left _ _
    have huρ : (u : ℝ) ≤ 2 * K * ρ H.1.succ := by
      have hfloor : (u : ℝ) ≤ (⌊2 * (K : ℝ) * ρ H.1.succ⌋₊ : ℝ) := by
        dsimp [u]
        exact_mod_cast min_le_right (K * B) ⌊2 * (K : ℝ) * ρ H.1.succ⌋₊
      exact hfloor.trans (Nat.floor_le hnonneg)
    have hm := validHeader_key_bound (Classical.choice hX).2 hpos
    have hb := fixedHeaderCount_real G U (canonicalRole H.2 h) (canonicalCenters H.2 h)
      (fun x ↦ x.1.card_profileGenerator_le) hU
      (fun x ↦ canonicalRole_agreement (G x) H.2 h)
      (fun x t ht ↦ validHeader_noncentral_bound x.2 (hρ _) (hρB _) t ht)
      huB huρ (hρB H.1.castSucc)
    have hb' : (#(valuesAtHeader K B h J ρ H) : ℝ) ≤
        ((K * B + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (K : ℝ)^2 * ρ H.1.succ) *
        (B + 1 : ℝ) ^ (centralKeys (canonicalRole H.2 h) (canonicalCenters H.2 h)).card *
        (2 : ℝ) ^ ((B : ℝ) - ρ H.1.castSucc + K + 2) := by
      exact hb
    apply hb'.trans
    gcongr
    linarith [show (0 : ℝ) ≤ B from Nat.cast_nonneg B]
  · letI : IsEmpty (HeaderProfiles K B h J ρ H) := ⟨fun x ↦ hX ⟨x⟩⟩
    simp only [valuesAtHeader, univ_eq_empty, image_empty, card_empty, Nat.cast_zero]
    positivity

theorem boundedValues_eq_header_union (hpos : 0 < h) (hcover : K < (J + 1) * h)
    (ρ : Fin (J + 2) → ℝ) (hanti : Antitone ρ) :
    boundedValues K B =
      (univ : Finset (Fin (J + 1) × Partition K)).biUnion (valuesAtHeader K B h J ρ) := by
  classical
  ext n
  simp only [boundedValues, valuesAtHeader, mem_image, mem_univ, true_and, mem_biUnion]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨H, hH⟩ := exists_validHeader x h J hpos hcover ρ hanti
    exact ⟨H, ⟨x, hH⟩, rfl⟩
  · rintro ⟨H, x, rfl⟩
    exact ⟨x.1, rfl⟩

/-- Actual attainable values satisfy the paper's finite counting product for
any scale sequence with a uniform net saving η. Header existence is proved. -/
theorem boundedValues_card_le_uniform_loss (hpos : 0 < h)
    (hcover : K < (J + 1) * h) (ρ : Fin (J + 2) → ℝ) (hanti : Antitone ρ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρB : ∀ i, ρ i ≤ B) {η : ℝ}
    (hloss : ∀ j : Fin (J + 1), 2 * (K : ℝ)^2 * ρ j.succ ≤ ρ j.castSucc - η) :
    (#(boundedValues K B) : ℝ) ≤
      (((J + 1) * K ^ K : ℕ) : ℝ) * ((K * B + 1 : ℕ) : ℝ) *
      (B + 1 : ℝ) ^ (2 ^ J * (1 + K * 2 ^ h)) *
      (2 : ℝ) ^ ((B : ℝ) - η + K + 2) := by
  classical
  let C : ℝ := ((K * B + 1 : ℕ) : ℝ) *
    (B + 1 : ℝ) ^ (2 ^ J * (1 + K * 2 ^ h)) *
    (2 : ℝ) ^ ((B : ℝ) - η + K + 2)
  have hC : 0 ≤ C := by positivity
  have hbound (H : Fin (J + 1) × Partition K) :
      (#(valuesAtHeader K B h J ρ H) : ℝ) ≤ C := by
    apply (valuesAtHeader_card_le hpos ρ hρ hρB H).trans
    calc
      _ = ((K * B + 1 : ℕ) : ℝ) *
          (B + 1 : ℝ) ^ (2 ^ J * (1 + K * 2 ^ h)) *
          (2 : ℝ) ^ (2 * (K : ℝ)^2 * ρ H.1.succ +
            ((B : ℝ) - ρ H.1.castSucc + K + 2)) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)
          (2 * (K : ℝ)^2 * ρ H.1.succ) ((B : ℝ) - ρ H.1.castSucc + K + 2)]
        ring
      _ ≤ C := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith [hloss H.1]
  rw [boundedValues_eq_header_union hpos hcover ρ hanti]
  calc
    (#((univ : Finset (Fin (J + 1) × Partition K)).biUnion
        (valuesAtHeader K B h J ρ)) : ℝ) ≤
        ∑ H : Fin (J + 1) × Partition K, (#(valuesAtHeader K B h J ρ H) : ℝ) := by
      exact_mod_cast (card_biUnion_le :
        #((univ : Finset (Fin (J + 1) × Partition K)).biUnion (valuesAtHeader K B h J ρ)) ≤
          ∑ H : Fin (J + 1) × Partition K, #(valuesAtHeader K B h J ρ H))
    _ ≤ ∑ _H : Fin (J + 1) × Partition K, C := sum_le_sum (fun H _ ↦ hbound H)
    _ = (Fintype.card (Fin (J + 1) × Partition K) : ℝ) * C := by simp
    _ ≤ (((J + 1) * K ^ K : ℕ) : ℝ) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast card_headers_le J K
    _ = _ := by dsimp [C]; ring


end AntichainOfGivenSize.FaithfulLower
