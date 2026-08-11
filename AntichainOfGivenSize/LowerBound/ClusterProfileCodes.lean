import AntichainOfGivenSize.LowerBound.ClusterEncoding
import AntichainOfGivenSize.LowerBound.ClusterState

/-!
# Sparse codes extracted from a clustered profile

The exceptional-set code records only Venn-pattern multiplicities of points
lying on a proximity edge.  Its total mass is the exceptional-set size.  The
second part of the file records center-query exponents after embedding the
actual cluster labels into a fixed ambient label set.
-/

open scoped BigOperators
open Finset

namespace AntichainOfGivenSize.ClusterLowerBound

open AntichainOfGivenSize.ClusterCore

/-- Multiplicity of Venn pattern `A` inside the global exceptional set. -/
noncomputable def exceptionalAtomCount {K B : ℕ} (x : BoundedProfile K B)
    (rho : ℕ) (A : Finset (Fin K)) : ℕ :=
  #(x.exceptionalSet rho |>.filter fun p ↦ p.1 = A)

theorem sum_exceptionalAtomCount {K B : ℕ} (x : BoundedProfile K B)
    (rho : ℕ) :
    ∑ A : Finset (Fin K), exceptionalAtomCount x rho A =
      #(x.exceptionalSet rho) := by
  classical
  unfold exceptionalAtomCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp

/-- The exceptional part of an intersection is recovered exactly from the
sparse pattern multiplicities. -/
theorem exceptionalIntersectionSize_eq_profile_sum {K B : ℕ}
    (x : BoundedProfile K B) (rho : ℕ)
    (t : IEQuery (Finset.univ : Finset (Fin K))) :
    exceptionalIntersectionSize x.generators (x.exceptionalSet rho) t =
      ∑ A ∈ Finset.univ.powerset.filter (t.1 ⊆ ·),
        exceptionalAtomCount x rho A := by
  classical
  unfold exceptionalIntersectionSize exceptionalAtomCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  apply congrArg Finset.card
  ext p
  simp only [mem_filter, mem_inter]
  constructor
  · rintro ⟨hpI, hpU⟩
    refine ⟨hpU, mem_powerset.2 (subset_univ _), ?_⟩
    have hpAll : ∀ i ∈ t.1, p ∈ x.generators i := by
      simpa [AntichainOfGivenSize.Section6.generatorIntersection] using hpI
    intro i hi
    simpa [BoundedProfile.generators, VennProfile.profileGenerator,
      AntichainOfGivenSize.Section6.generatorIntersection] using hpAll i hi
  · rintro ⟨hpU, hpPow, hpSub⟩
    refine ⟨?_, hpU⟩
    simp only [AntichainOfGivenSize.Section6.generatorIntersection,
      Finset.mem_inf' (Finset.mem_filter.1 t.2).2]
    intro i hi
    have hiA : i ∈ p.1 := hpSub hi
    simpa [BoundedProfile.generators, VennProfile.profileGenerator] using hiA

/-- Sparse exceptional-pattern code, padded to a uniform mass bound. -/
noncomputable def exceptionalSparseCode {K B U : ℕ}
    (x : BoundedProfile K B) (rho : ℕ)
    (hU : #(x.exceptionalSet rho) ≤ U) :
    SparseCode (Finset (Fin K)) U :=
  SparseCode.ofNat U (exceptionalAtomCount x rho) (by
    rw [sum_exceptionalAtomCount]
    exact hU)

@[simp] theorem exceptionalSparseCode_count {K B U : ℕ}
    (x : BoundedProfile K B) (rho : ℕ)
    (hU : #(x.exceptionalSet rho) ≤ U) (A : Finset (Fin K)) :
    ((exceptionalSparseCode x rho hU).count A : ℕ) =
      exceptionalAtomCount x rho A :=
  rfl

theorem exceptionalIntersectionSize_eq_of_codes_eq
    {K B U rhoX rhoY : ℕ} {x y : BoundedProfile K B}
    (hUX : #(x.exceptionalSet rhoX) ≤ U)
    (hUY : #(y.exceptionalSet rhoY) ≤ U)
    (hcode : exceptionalSparseCode x rhoX hUX =
      exceptionalSparseCode y rhoY hUY)
    (t : IEQuery (Finset.univ : Finset (Fin K))) :
    exceptionalIntersectionSize x.generators (x.exceptionalSet rhoX) t =
      exceptionalIntersectionSize y.generators (y.exceptionalSet rhoY) t := by
  rw [exceptionalIntersectionSize_eq_profile_sum,
    exceptionalIntersectionSize_eq_profile_sum]
  apply Finset.sum_congr rfl
  intro A _hA
  have hc := congrArg
    (fun c : SparseCode (Finset (Fin K)) U ↦ (c.count A : ℕ)) hcode
  exact hc

/-- Every nonempty canonical generator intersection has size at most the
load bound. -/
theorem generatorIntersection_card_le_load {K B : ℕ}
    (x : BoundedProfile K B)
    (t : IEQuery (Finset.univ : Finset (Fin K))) :
    #(AntichainOfGivenSize.Section6.generatorIntersection x.generators t) ≤ B := by
  classical
  obtain ⟨i, hi⟩ := (Finset.mem_filter.1 t.2).2
  apply (Finset.card_le_card ?_).trans (x.card_profileGenerator_le i)
  intro p hp
  have hpAll : ∀ j ∈ t.1, p ∈ x.generators j := by
    simpa [AntichainOfGivenSize.Section6.generatorIntersection] using hp
  exact hpAll i hi

theorem regularIntersectionSize_le_load {K B : ℕ}
    (x : BoundedProfile K B) (U : Finset x.Point)
    (t : IEQuery (Finset.univ : Finset (Fin K))) :
    regularIntersectionSize x.generators U t ≤ B := by
  unfold regularIntersectionSize
  exact (Finset.card_le_card (Finset.sdiff_subset)).trans
    (generatorIntersection_card_le_load x t)

/-! ## Center-query transcript codes -/

/-- Embed the actual `r` cluster labels into the fixed ambient `J` labels. -/
def embedClusterRole {K r J : ℕ} (hr : r ≤ J) :
    Fin r ⊕ Fin K → Fin J ⊕ Fin K
  | Sum.inl a => Sum.inl ⟨a.1, a.2.trans_le hr⟩
  | Sum.inr i => Sum.inr i

theorem embedClusterRole_injective {K r J : ℕ} (hr : r ≤ J) :
    Function.Injective (embedClusterRole (K := K) hr) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hj :
          (⟨a.1, a.2.trans_le hr⟩ : Fin J) =
            ⟨b.1, b.2.trans_le hr⟩ := Sum.inl.inj hab
      congr 1
      apply Fin.ext
      exact congrArg (fun z : Fin J ↦ z.val) hj
    | inr b => exact False.elim (Sum.inl_ne_inr hab)
  | inr a =>
    cases b with
    | inl b => exact False.elim (Sum.inr_ne_inl hab)
    | inr b => exact congrArg Sum.inr (Sum.inr.inj hab)

/-- Compressed key in a fixed cluster-label alphabet. -/
noncomputable def ProfileClusterState.fixedKey {K B rho h r J : ℕ}
    {x : BoundedProfile K B} (S : ProfileClusterState x rho h r)
    (hr : r ≤ J) (t : IEQuery (Finset.univ : Finset (Fin K))) :
    ClusterKey K J :=
  (S.key t).image (embedClusterRole (K := K) hr)

theorem ProfileClusterState.fixedKey_eq_iff_key_eq
    {K B rho h r J : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rho h r) (hr : r ≤ J)
    (t u : IEQuery (Finset.univ : Finset (Fin K))) :
    S.fixedKey hr t = S.fixedKey hr u ↔ S.key t = S.key u := by
  unfold ProfileClusterState.fixedKey
  exact Finset.image_inj (embedClusterRole_injective hr)

/-- Fixed-key/exponent pairs for all center queries. -/
noncomputable def ProfileClusterState.centerPairSet
    {K B rhoFine h r J : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r) (rho : ℕ) (hr : r ≤ J) :
    Finset (ClusterKey K J × Fin (B + 1)) := by
  classical
  exact ((Finset.univ :
      Finset (IEQuery (Finset.univ : Finset (Fin K)))).filter
        (IsCenterQuery (x.proximityGraph rho) S.packed)).image fun t ↦
      (S.fixedKey hr t,
        ⟨regularIntersectionSize x.generators (x.exceptionalSet rhoFine) t,
          Nat.lt_succ_of_le (regularIntersectionSize_le_load x _ t)⟩)

/-- Indicator of the finite center-pair transcript. -/
noncomputable def ProfileClusterState.centerPairCount
    {K B rhoFine h r J : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r) (rho : ℕ) (hr : r ≤ J)
    (p : ClusterKey K J × Fin (B + 1)) : ℕ :=
  if p ∈ S.centerPairSet rho hr then 1 else 0

theorem ProfileClusterState.sum_centerPairCount
    {K B rhoFine h r J : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r) (rho : ℕ) (hr : r ≤ J) :
    ∑ p, S.centerPairCount rho hr p = #(S.centerPairSet rho hr) := by
  classical
  simp [ProfileClusterState.centerPairCount]

/-- Sparse center transcript, given any uniform bound on its number of
distinct key/exponent pairs. -/
noncomputable def ProfileClusterState.centerSparseCode
    {K B rhoFine h r J M : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r) (rho : ℕ) (hr : r ≤ J)
    (hM : #(S.centerPairSet rho hr) ≤ M) :
    SparseCode (ClusterKey K J × Fin (B + 1)) M :=
  SparseCode.ofNat M (S.centerPairCount rho hr) (by
    rw [S.sum_centerPairCount]
    exact hM)

@[simp] theorem ProfileClusterState.centerSparseCode_count
    {K B rhoFine h r J M : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r) (rho : ℕ) (hr : r ≤ J)
    (hM : #(S.centerPairSet rho hr) ≤ M)
    (p : ClusterKey K J × Fin (B + 1)) :
    ((S.centerSparseCode rho hr hM).count p : ℕ) =
      S.centerPairCount rho hr p :=
  rfl

theorem ProfileClusterState.centerPair_mem
    {K B rhoFine h r J : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r) (rho : ℕ) (hr : r ≤ J)
    (t : IEQuery (Finset.univ : Finset (Fin K)))
    (ht : IsCenterQuery (x.proximityGraph rho) S.packed t) :
    (S.fixedKey hr t,
      ⟨regularIntersectionSize x.generators (x.exceptionalSet rhoFine) t,
        Nat.lt_succ_of_le (regularIntersectionSize_le_load x _ t)⟩) ∈
      S.centerPairSet rho hr := by
  classical
  unfold ProfileClusterState.centerPairSet
  apply Finset.mem_image.2
  exact ⟨t, Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩, rfl⟩

/-- Equality of sparse center codes identifies the regular exponent attached
to every common fixed key. -/
theorem regularIntersectionSize_eq_of_centerCodes_eq
    {K B J M : ℕ}
    {rhoFineX hX rX rhoFineY hY rY rho : ℕ}
    {x y : BoundedProfile K B}
    (SX : ProfileClusterState x rhoFineX hX rX)
    (SY : ProfileClusterState y rhoFineY hY rY)
    (hrX : rX ≤ J) (hrY : rY ≤ J)
    (hMX : #(SX.centerPairSet rho hrX) ≤ M)
    (hMY : #(SY.centerPairSet rho hrY) ≤ M)
    (hcode : SX.centerSparseCode rho hrX hMX =
      SY.centerSparseCode rho hrY hMY)
    (tX tY : IEQuery (Finset.univ : Finset (Fin K)))
    (hcenterX : IsCenterQuery (x.proximityGraph rho) SX.packed tX)
    (_hcenterY : IsCenterQuery (y.proximityGraph rho) SY.packed tY)
    (hkey : SX.fixedKey hrX tX = SY.fixedKey hrY tY) :
    regularIntersectionSize x.generators (x.exceptionalSet rhoFineX) tX =
      regularIntersectionSize y.generators (y.exceptionalSet rhoFineY) tY := by
  classical
  let eX : Fin (B + 1) :=
    ⟨regularIntersectionSize x.generators (x.exceptionalSet rhoFineX) tX,
      Nat.lt_succ_of_le (regularIntersectionSize_le_load x _ tX)⟩
  have hmemX : (SX.fixedKey hrX tX, eX) ∈ SX.centerPairSet rho hrX :=
    SX.centerPair_mem rho hrX tX hcenterX
  have hcountX :
      ((SX.centerSparseCode rho hrX hMX).count (SX.fixedKey hrX tX, eX) : ℕ) = 1 := by
    simp [ProfileClusterState.centerPairCount, hmemX]
  have hcountY :
      ((SY.centerSparseCode rho hrY hMY).count (SX.fixedKey hrX tX, eX) : ℕ) = 1 := by
    rw [← hcode]
    exact hcountX
  have hmemY : (SX.fixedKey hrX tX, eX) ∈ SY.centerPairSet rho hrY := by
    simpa [ProfileClusterState.centerPairCount] using hcountY
  unfold ProfileClusterState.centerPairSet at hmemY
  rcases Finset.mem_image.1 hmemY with ⟨u, hu, hp⟩
  have hukey : SY.fixedKey hrY u = SY.fixedKey hrY tY := by
    have hfirst := congrArg Prod.fst hp
    simpa [hkey] using hfirst
  have huKeyRaw : SY.key u = SY.key tY :=
    (SY.fixedKey_eq_iff_key_eq hrY u tY).1 hukey
  have hreg := SY.regularIntersectionSize_eq_of_key_eq u tY huKeyRaw
  have hsecond := congrArg (fun p ↦ (p.2 : ℕ)) hp
  have hsecond' :
      regularIntersectionSize y.generators (y.exceptionalSet rhoFineY) u =
        regularIntersectionSize x.generators (x.exceptionalSet rhoFineX) tX := by
    simpa [eX] using hsecond
  exact hsecond'.symm.trans hreg

end AntichainOfGivenSize.ClusterLowerBound
