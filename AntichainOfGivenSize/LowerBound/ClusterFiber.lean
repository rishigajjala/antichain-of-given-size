import AntichainOfGivenSize.LowerBound.ClusterProfileCodes

/-!
# Diameter of one cluster-encoding fiber

Profiles with the same sparse exceptional data and center transcript have the
same centered inclusion--exclusion sum.  Every remaining query contains a
coarse nonedge, so the whole tail is small.  This file proves that statement
as an exact integer estimate.
-/

open scoped BigOperators
open Finset

namespace AntichainOfGivenSize.ClusterLowerBound

open AntichainOfGivenSize.ClusterCore

/-- One signed inclusion--exclusion term of the canonical family. -/
noncomputable def profileIETerm {K B : ℕ} (x : BoundedProfile K B)
    (t : IEQuery (Finset.univ : Finset (Fin K))) : ℤ :=
  (-1 : ℤ) ^ (t.1.card + 1) *
    (2 : ℤ) ^ #(AntichainOfGivenSize.Section6.generatorIntersection
      x.generators t)

/-- Queries retained as centers for a packed state and coarse graph. -/
noncomputable def centerQueries {K B rhoFine h r : ℕ}
    {x : BoundedProfile K B} (S : ProfileClusterState x rhoFine h r)
    (rho : ℕ) : Finset (IEQuery (Finset.univ : Finset (Fin K))) := by
  classical
  exact Finset.univ.filter (IsCenterQuery (x.proximityGraph rho) S.packed)

/-- Exact centered contribution. -/
noncomputable def centerContribution {K B rhoFine h r : ℕ}
    {x : BoundedProfile K B} (S : ProfileClusterState x rhoFine h r)
    (rho : ℕ) : ℤ :=
  ∑ t ∈ centerQueries S rho, profileIETerm x t

/-- Exact contribution of the discarded noncenter queries. -/
noncomputable def tailContribution {K B rhoFine h r : ℕ}
    {x : BoundedProfile K B} (S : ProfileClusterState x rhoFine h r)
    (rho : ℕ) : ℤ := by
  classical
  exact ∑ t ∈ (Finset.univ :
    Finset (IEQuery (Finset.univ : Finset (Fin K)))).filter
      (fun t ↦ ¬ IsCenterQuery (x.proximityGraph rho) S.packed t),
      profileIETerm x t

theorem value_cast_eq_center_add_tail {K B rhoFine h r : ℕ}
    {x : BoundedProfile K B} (S : ProfileClusterState x rhoFine h r)
    (rho : ℕ) :
    (x.value : ℤ) = centerContribution S rho + tailContribution S rho := by
  classical
  rw [BoundedProfile.value,
    AntichainOfGivenSize.Section6.generatedIdealIdx_card_inclusionExclusion]
  change (∑ t : IEQuery (Finset.univ : Finset (Fin K)), profileIETerm x t) = _
  simpa [centerContribution, tailContribution, centerQueries] using
    (Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (IEQuery (Finset.univ : Finset (Fin K))))
      (IsCenterQuery (x.proximityGraph rho) S.packed) (profileIETerm x)).symm

theorem centerQueries_eq_of_iff
    {K B : ℕ} {rhoFineX hX rX rhoFineY hY rY rho : ℕ}
    {x y : BoundedProfile K B}
    (SX : ProfileClusterState x rhoFineX hX rX)
    (SY : ProfileClusterState y rhoFineY hY rY)
    (hcenter : ∀ t : IEQuery (Finset.univ : Finset (Fin K)),
      IsCenterQuery (x.proximityGraph rho) SX.packed t ↔
        IsCenterQuery (y.proximityGraph rho) SY.packed t) :
    centerQueries SX rho = centerQueries SY rho := by
  classical
  ext t
  simp [centerQueries, hcenter t]

/-- Equality of the two sparse codes and of the structural keys forces exact
equality of the centered sum. -/
theorem centerContribution_eq_of_codes_eq
    {K B J U M : ℕ}
    {rhoFineX hX rX rhoFineY hY rY rho : ℕ}
    {x y : BoundedProfile K B}
    (SX : ProfileClusterState x rhoFineX hX rX)
    (SY : ProfileClusterState y rhoFineY hY rY)
    (hrX : rX ≤ J) (hrY : rY ≤ J)
    (hUX : #(x.exceptionalSet rhoFineX) ≤ U)
    (hUY : #(y.exceptionalSet rhoFineY) ≤ U)
    (hMX : #(SX.centerPairSet rho hrX) ≤ M)
    (hMY : #(SY.centerPairSet rho hrY) ≤ M)
    (hexception : exceptionalSparseCode x rhoFineX hUX =
      exceptionalSparseCode y rhoFineY hUY)
    (hcenters : SX.centerSparseCode rho hrX hMX =
      SY.centerSparseCode rho hrY hMY)
    (hcenter : ∀ t : IEQuery (Finset.univ : Finset (Fin K)),
      IsCenterQuery (x.proximityGraph rho) SX.packed t ↔
        IsCenterQuery (y.proximityGraph rho) SY.packed t)
    (hkey : ∀ t : IEQuery (Finset.univ : Finset (Fin K)),
      SX.fixedKey hrX t = SY.fixedKey hrY t) :
    centerContribution SX rho = centerContribution SY rho := by
  classical
  have hset := centerQueries_eq_of_iff SX SY hcenter
  unfold centerContribution
  rw [hset]
  apply Finset.sum_congr rfl
  intro t ht
  have hcenterY : IsCenterQuery (y.proximityGraph rho) SY.packed t := by
    simpa [centerQueries] using ht
  have hcenterX : IsCenterQuery (x.proximityGraph rho) SX.packed t :=
    (hcenter t).2 hcenterY
  have hreg := regularIntersectionSize_eq_of_centerCodes_eq
    SX SY hrX hrY hMX hMY hcenters t t hcenterX hcenterY (hkey t)
  have hexc := exceptionalIntersectionSize_eq_of_codes_eq
    hUX hUY hexception t
  have hcardX := regular_add_exceptional_eq_intersection_card
    x.generators (x.exceptionalSet rhoFineX) t
  have hcardY := regular_add_exceptional_eq_intersection_card
    y.generators (y.exceptionalSet rhoFineY) t
  unfold profileIETerm
  congr 2
  omega

theorem card_ieQuery_le_two_pow (K : ℕ) :
    Fintype.card (IEQuery (Finset.univ : Finset (Fin K))) ≤ 2 ^ K := by
  change Fintype.card
    (↥((Finset.univ : Finset (Fin K)).powerset.filter
      (fun t : Finset (Fin K) ↦ t.Nonempty))) ≤ 2 ^ K
  rw [Fintype.card_coe]
  calc
    #((Finset.univ : Finset (Fin K)).powerset.filter
        (fun t : Finset (Fin K) ↦ t.Nonempty)) ≤
        #((Finset.univ : Finset (Fin K)).powerset) := Finset.card_filter_le _ _
    _ = 2 ^ K := by simp

/-- The whole noncenter tail has absolute value at most
`2^K * 2^(B-rho)`. -/
theorem tailContribution_natAbs_le
    {K B rhoFine h r : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r) (rho : ℕ) :
    (tailContribution S rho).natAbs ≤ 2 ^ K * 2 ^ (B - rho) := by
  classical
  let tails : Finset (IEQuery (Finset.univ : Finset (Fin K))) :=
    Finset.univ.filter
      (fun t ↦ ¬ IsCenterQuery (x.proximityGraph rho) S.packed t)
  change (∑ t ∈ tails, profileIETerm x t).natAbs ≤ _
  calc
    (∑ t ∈ tails, profileIETerm x t).natAbs ≤
        ∑ t ∈ tails, (profileIETerm x t).natAbs := by
      exact Int.natAbs_sum_le tails (profileIETerm x)
    _ ≤ ∑ _t ∈ tails, 2 ^ (B - rho) := by
      apply Finset.sum_le_sum
      intro t ht
      have hnoncenter :
          ¬ IsCenterQuery (x.proximityGraph rho) S.packed t :=
        (Finset.mem_filter.1 ht).2
      have hexp := noncenter_generatorIntersection_card_le x S rho t hnoncenter
      calc
        (profileIETerm x t).natAbs =
            2 ^ #(AntichainOfGivenSize.Section6.generatorIntersection
              x.generators t) := by
          simp [profileIETerm, Int.natAbs_mul, Int.natAbs_pow]
        _ ≤ 2 ^ (B - rho) :=
          Nat.pow_le_pow_right (by omega : 0 < 2) hexp
    _ = #tails * 2 ^ (B - rho) := by simp
    _ ≤ Fintype.card (IEQuery (Finset.univ : Finset (Fin K))) *
        2 ^ (B - rho) := by
      gcongr
      exact (Finset.card_le_univ tails)
    _ ≤ 2 ^ K * 2 ^ (B - rho) := by
      gcongr
      exact card_ieQuery_le_two_pow K

/-- Two profiles with one common encoding state have close exact values. -/
theorem value_natAbs_sub_le_of_codes_eq
    {K B J U M : ℕ}
    {rhoFineX hX rX rhoFineY hY rY rho : ℕ}
    {x y : BoundedProfile K B}
    (SX : ProfileClusterState x rhoFineX hX rX)
    (SY : ProfileClusterState y rhoFineY hY rY)
    (hrX : rX ≤ J) (hrY : rY ≤ J)
    (hUX : #(x.exceptionalSet rhoFineX) ≤ U)
    (hUY : #(y.exceptionalSet rhoFineY) ≤ U)
    (hMX : #(SX.centerPairSet rho hrX) ≤ M)
    (hMY : #(SY.centerPairSet rho hrY) ≤ M)
    (hexception : exceptionalSparseCode x rhoFineX hUX =
      exceptionalSparseCode y rhoFineY hUY)
    (hcenters : SX.centerSparseCode rho hrX hMX =
      SY.centerSparseCode rho hrY hMY)
    (hcenter : ∀ t : IEQuery (Finset.univ : Finset (Fin K)),
      IsCenterQuery (x.proximityGraph rho) SX.packed t ↔
        IsCenterQuery (y.proximityGraph rho) SY.packed t)
    (hkey : ∀ t : IEQuery (Finset.univ : Finset (Fin K)),
      SX.fixedKey hrX t = SY.fixedKey hrY t) :
    Int.natAbs ((x.value : ℤ) - (y.value : ℤ)) ≤
      2 * (2 ^ K * 2 ^ (B - rho)) := by
  have hcenterEq := centerContribution_eq_of_codes_eq SX SY hrX hrY
    hUX hUY hMX hMY hexception hcenters hcenter hkey
  rw [value_cast_eq_center_add_tail SX rho,
    value_cast_eq_center_add_tail SY rho, hcenterEq]
  have hx := tailContribution_natAbs_le SX rho
  have hy := tailContribution_natAbs_le SY rho
  calc
    Int.natAbs
        (centerContribution SY rho + tailContribution SX rho -
          (centerContribution SY rho + tailContribution SY rho)) =
        Int.natAbs (tailContribution SX rho - tailContribution SY rho) := by
      congr 1
      ring
    _ ≤ (tailContribution SX rho).natAbs +
        (tailContribution SY rho).natAbs := by
      simpa only [sub_eq_add_neg, Int.natAbs_neg] using
        Int.natAbs_add_le (tailContribution SX rho) (-tailContribution SY rho)
    _ ≤ 2 * (2 ^ K * 2 ^ (B - rho)) := by omega

end AntichainOfGivenSize.ClusterLowerBound
