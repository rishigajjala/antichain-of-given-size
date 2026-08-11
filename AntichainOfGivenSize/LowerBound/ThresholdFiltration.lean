import AntichainOfGivenSize.LowerBound.VennProfiles
import Mathlib.Data.Nat.Choose.Sum

/-!
# Threshold-complex filtration of a Venn profile

This file turns a Venn profile into a nested family of simplicial complexes
with the empty face omitted: at threshold `t`, a face is retained when its
encoded intersection has size at least `t`.  It proves an exact binary
layer-cake identity for the Venn expression and exact binomial-moment
identities for the face counts of the filtration.

These are structural tools used to study lower bounds.  This module is
independent of the unconditional quadratic-over-log lower bound assembled in
`LowerBound.Matching`.
-/

open scoped BigOperators
open Finset

namespace AntichainOfGivenSize.VennProfile

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Total number of ground-set points encoded by a Venn profile. -/
def profileMass (x : Finset I → ℕ) : ℕ :=
  ∑ A ∈ Finset.univ.powerset, x A

/-- The nonempty index sets whose encoded intersection has size at least `t`. -/
def thresholdComplex (x : Finset I → ℕ) (t : ℕ) : Finset (Finset I) :=
  Finset.univ.powerset.filter fun S ↦
    S.Nonempty ∧ t ≤ profileIntersectionSize x S

/-- Downward closure among nonempty faces. -/
def NonemptyDownwardClosed (K : Finset (Finset I)) : Prop :=
  ∀ ⦃S T : Finset I⦄, S ∈ K → T.Nonempty → T ⊆ S → T ∈ K

/-- Alternating face sum of a complex that omits the empty face. -/
def thresholdEuler (x : Finset I → ℕ) (t : ℕ) : ℤ :=
  ∑ S ∈ thresholdComplex x t, (-1 : ℤ) ^ (S.card + 1)

theorem profileIntersectionSize_antitone (x : Finset I → ℕ)
    {S T : Finset I} (hST : S ⊆ T) :
    profileIntersectionSize x T ≤ profileIntersectionSize x S := by
  unfold profileIntersectionSize
  apply Finset.sum_le_sum_of_subset
  intro A hA
  rw [Finset.mem_filter] at hA ⊢
  exact ⟨hA.1, hST.trans hA.2⟩

theorem profileIntersectionSize_le_profileMass (x : Finset I → ℕ)
    (S : Finset I) :
    profileIntersectionSize x S ≤ profileMass x := by
  unfold profileIntersectionSize profileMass
  apply Finset.sum_le_sum_of_subset
  exact Finset.filter_subset _ _

theorem thresholdComplex_downwardClosed (x : Finset I → ℕ) (t : ℕ) :
    NonemptyDownwardClosed (thresholdComplex x t) := by
  intro S T hS hT hTS
  rw [thresholdComplex, Finset.mem_filter] at hS ⊢
  refine ⟨?_, hT, ?_⟩
  · exact Finset.mem_powerset.2
      (hTS.trans (Finset.mem_powerset.1 hS.1))
  · exact hS.2.2.trans (profileIntersectionSize_antitone x hTS)

/-- Raising the intersection-size threshold can only remove faces. -/
theorem thresholdComplex_antitone (x : Finset I → ℕ) {s t : ℕ}
    (hst : s ≤ t) :
    thresholdComplex x t ⊆ thresholdComplex x s := by
  intro S hS
  rw [thresholdComplex, Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, hS.2.1, hst.trans hS.2.2⟩

theorem vennExpression_eq_finset_sum (x : Finset I → ℕ) :
    vennExpression x =
      ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset I ↦ S.Nonempty),
        (-1 : ℤ) ^ (S.card + 1) * (2 : ℤ) ^ profileIntersectionSize x S := by
  unfold vennExpression
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach
    (Finset.univ.powerset.filter (fun S : Finset I ↦ S.Nonempty))
    (fun S : Finset I ↦
      (-1 : ℤ) ^ (S.card + 1) *
        (2 : ℤ) ^ profileIntersectionSize x S)

lemma int_two_pow_eq_one_add_sum_range (r : ℕ) :
    (2 : ℤ) ^ r = 1 + ∑ t ∈ Finset.range r, (2 : ℤ) ^ t := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ]
      calc
        (2 : ℤ) ^ (r + 1) = (2 : ℤ) ^ r + 2 ^ r := by
          rw [pow_succ]
          ring
        _ = (1 + ∑ t ∈ Finset.range r, (2 : ℤ) ^ t) + 2 ^ r := by
          rw [ih]
        _ = 1 + ((∑ t ∈ Finset.range r, (2 : ℤ) ^ t) + 2 ^ r) := by
          ring

lemma sum_range_ite_lt_eq_sum_range {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) {r m : ℕ} (hrm : r ≤ m) :
    (∑ t ∈ Finset.range m, if t < r then f t else 0) =
      ∑ t ∈ Finset.range r, f t := by
  rw [← Finset.sum_filter]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma int_two_pow_eq_one_add_padded_sum {r m : ℕ} (hrm : r ≤ m) :
    (2 : ℤ) ^ r =
      1 + ∑ t ∈ Finset.range m,
        if t < r then (2 : ℤ) ^ t else 0 := by
  rw [sum_range_ite_lt_eq_sum_range (fun t ↦ (2 : ℤ) ^ t) hrm]
  exact int_two_pow_eq_one_add_sum_range r

lemma nonempty_powerset_euler [Nonempty I] :
    (∑ S ∈ Finset.univ.powerset.filter (fun S : Finset I ↦ S.Nonempty),
      (-1 : ℤ) ^ (S.card + 1)) = 1 := by
  let U : Finset I := Finset.univ
  have hU : U.Nonempty := Finset.univ_nonempty
  have htotal : (∑ S ∈ U.powerset, (-1 : ℤ) ^ S.card) = 0 :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty hU
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := U.powerset) (p := fun S : Finset I ↦ S.Nonempty)
    (f := fun S : Finset I ↦ (-1 : ℤ) ^ S.card)
  have hnot :
      U.powerset.filter (fun S : Finset I ↦ ¬ S.Nonempty) = {∅} := by
    ext S
    simp [U]
  have hbase :
      (∑ S ∈ U.powerset.filter (fun S : Finset I ↦ S.Nonempty),
        (-1 : ℤ) ^ S.card) = -1 := by
    rw [hnot] at hsplit
    simp only [Finset.sum_singleton, Finset.card_empty, pow_zero] at hsplit
    linarith
  change
    (∑ S ∈ U.powerset.filter (fun S : Finset I ↦ S.Nonempty),
      (-1 : ℤ) ^ (S.card + 1)) = 1
  calc
    (∑ S ∈ U.powerset.filter (fun S : Finset I ↦ S.Nonempty),
        (-1 : ℤ) ^ (S.card + 1)) =
        -(∑ S ∈ U.powerset.filter (fun S : Finset I ↦ S.Nonempty),
          (-1 : ℤ) ^ S.card) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro S _
      rw [pow_succ]
      ring
    _ = 1 := by rw [hbase]; norm_num

lemma weighted_threshold_sum (x : Finset I → ℕ) (t : ℕ) :
    (∑ S ∈ Finset.univ.powerset.filter (fun S : Finset I ↦ S.Nonempty),
      (-1 : ℤ) ^ (S.card + 1) *
        (if t < profileIntersectionSize x S then (2 : ℤ) ^ t else 0)) =
      (2 : ℤ) ^ t * thresholdEuler x (t + 1) := by
  calc
    (∑ S ∈ Finset.univ.powerset.filter (fun S : Finset I ↦ S.Nonempty),
        (-1 : ℤ) ^ (S.card + 1) *
          (if t < profileIntersectionSize x S then (2 : ℤ) ^ t else 0)) =
        ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset I ↦ S.Nonempty),
          if t + 1 ≤ profileIntersectionSize x S then
            (-1 : ℤ) ^ (S.card + 1) * 2 ^ t else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases h : t < profileIntersectionSize x S
      · have h' : t + 1 ≤ profileIntersectionSize x S := by omega
        simp [h, h']
      · have h' : ¬ t + 1 ≤ profileIntersectionSize x S := by omega
        simp [h, h']
    _ = ∑ S ∈
          (Finset.univ.powerset.filter (fun S : Finset I ↦ S.Nonempty)).filter
            (fun S ↦ t + 1 ≤ profileIntersectionSize x S),
          (-1 : ℤ) ^ (S.card + 1) * 2 ^ t := by
      symm
      exact Finset.sum_filter _ _
    _ = ∑ S ∈ thresholdComplex x (t + 1),
          (-1 : ℤ) ^ (S.card + 1) * 2 ^ t := by
      congr 1
      simp only [thresholdComplex, Finset.filter_filter]
    _ = thresholdEuler x (t + 1) * (2 : ℤ) ^ t := by
      rw [thresholdEuler, Finset.sum_mul]
    _ = (2 : ℤ) ^ t * thresholdEuler x (t + 1) := by
      rw [mul_comm]

/-- Binary layer-cake identity.  The zero-based index `t` represents the
one-based threshold `t + 1`. -/
theorem vennExpression_eq_threshold_filtration [Nonempty I]
    (x : Finset I → ℕ) :
    vennExpression x =
      1 + ∑ t ∈ Finset.range (profileMass x),
        (2 : ℤ) ^ t * thresholdEuler x (t + 1) := by
  let K := Finset.univ.powerset.filter (fun S : Finset I ↦ S.Nonempty)
  calc
    vennExpression x =
        ∑ S ∈ K, (-1 : ℤ) ^ (S.card + 1) *
          (2 : ℤ) ^ profileIntersectionSize x S := by
      exact vennExpression_eq_finset_sum x
    _ = ∑ S ∈ K, (-1 : ℤ) ^ (S.card + 1) *
          (1 + ∑ t ∈ Finset.range (profileMass x),
            if t < profileIntersectionSize x S then (2 : ℤ) ^ t else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [int_two_pow_eq_one_add_padded_sum
        (profileIntersectionSize_le_profileMass x S)]
    _ = (∑ S ∈ K, (-1 : ℤ) ^ (S.card + 1)) +
          ∑ S ∈ K, ∑ t ∈ Finset.range (profileMass x),
            (-1 : ℤ) ^ (S.card + 1) *
              (if t < profileIntersectionSize x S then (2 : ℤ) ^ t else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro S _
      rw [mul_add, mul_one, Finset.mul_sum]
    _ = 1 + ∑ t ∈ Finset.range (profileMass x),
          ∑ S ∈ K, (-1 : ℤ) ^ (S.card + 1) *
            (if t < profileIntersectionSize x S then (2 : ℤ) ^ t else 0) := by
      rw [show (∑ S ∈ K, (-1 : ℤ) ^ (S.card + 1)) = 1 by
        exact nonempty_powerset_euler]
      congr 1
      exact Finset.sum_comm
    _ = 1 + ∑ t ∈ Finset.range (profileMass x),
          (2 : ℤ) ^ t * thresholdEuler x (t + 1) := by
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      exact weighted_threshold_sum x t

/-- One-based form of `vennExpression_eq_threshold_filtration`, matching
`1 + Σ_{t=1}^{profileMass x} 2^(t-1) euler(K_t)`. -/
theorem vennExpression_eq_threshold_filtration_Icc [Nonempty I]
    (x : Finset I → ℕ) :
    vennExpression x =
      1 + ∑ t ∈ Finset.Icc 1 (profileMass x),
        (2 : ℤ) ^ (t - 1) * thresholdEuler x t := by
  rw [vennExpression_eq_threshold_filtration]
  congr 1
  have hshift := Finset.sum_Ico_add'
    (fun t : ℕ ↦ (2 : ℤ) ^ (t - 1) * thresholdEuler x t)
    0 (profileMass x) 1
  rw [Nat.Ico_zero_eq_range, zero_add,
    Finset.Ico_add_one_right_eq_Icc] at hshift
  simpa using hshift

/-! ## Binomial moments and the threshold f-vectors -/

/-- Summing encoded intersection sizes over all `j`-subsets gives the
`j`-th binomial moment of the atom multiplicities. -/
theorem sum_profileIntersectionSize_eq_binomialMoment
    (x : Finset I → ℕ) (j : ℕ) :
    (∑ S ∈ Finset.univ.powerset.filter (fun S : Finset I ↦ S.card = j),
      profileIntersectionSize x S) =
      ∑ A ∈ Finset.univ.powerset, x A * A.card.choose j := by
  unfold profileIntersectionSize
  calc
    (∑ S ∈ Finset.univ.powerset.filter (fun S : Finset I ↦ S.card = j),
        ∑ A ∈ Finset.univ.powerset.filter (S ⊆ ·), x A) =
        ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset I ↦ S.card = j),
          ∑ A ∈ Finset.univ.powerset, if S ⊆ A then x A else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      exact Finset.sum_filter _ _
    _ = ∑ A ∈ Finset.univ.powerset,
          ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset I ↦ S.card = j),
            if S ⊆ A then x A else 0 := by
      exact Finset.sum_comm
    _ = ∑ A ∈ Finset.univ.powerset, x A * A.card.choose j := by
      apply Finset.sum_congr rfl
      intro A _
      have hfaces :
          (Finset.univ.powerset.filter (fun S : Finset I ↦ S.card = j)).filter
              (fun S ↦ S ⊆ A) = A.powersetCard j := by
        ext S
        simp [Finset.mem_powersetCard, and_comm]
      rw [← Finset.sum_filter, hfaces, Finset.sum_const,
        Finset.card_powersetCard]
      simp [Nat.mul_comm]

/-- Number of `j`-element faces in the threshold complex `K_t`. -/
def thresholdFaceCount (x : Finset I → ℕ) (t j : ℕ) : ℕ :=
  ((thresholdComplex x t).filter fun S ↦ S.card = j).card

lemma thresholdFaceCount_succ_eq_indicator_sum
    (x : Finset I → ℕ) {j : ℕ} (hj : 0 < j) (t : ℕ) :
    thresholdFaceCount x (t + 1) j =
      ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset I ↦ S.card = j),
        if t < profileIntersectionSize x S then 1 else 0 := by
  unfold thresholdFaceCount thresholdComplex
  have hfilter :
      (Finset.univ.powerset.filter fun S : Finset I ↦
          S.Nonempty ∧ t + 1 ≤ profileIntersectionSize x S).filter
          (fun S ↦ S.card = j) =
        (Finset.univ.powerset.filter fun S : Finset I ↦ S.card = j).filter
          (fun S ↦ t < profileIntersectionSize x S) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hsub, _hne, hthreshold⟩, hcard⟩
      exact ⟨⟨hsub, hcard⟩, by omega⟩
    · rintro ⟨⟨hsub, hcard⟩, hthreshold⟩
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      exact ⟨⟨hsub, hne, by omega⟩, hcard⟩
  rw [hfilter, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The sum over all thresholds of the `j`-face count is the `j`-th
binomial moment of the Venn atoms. -/
theorem sum_thresholdFaceCount_eq_binomialMoment
    (x : Finset I → ℕ) {j : ℕ} (hj : 0 < j) :
    (∑ t ∈ Finset.range (profileMass x),
      thresholdFaceCount x (t + 1) j) =
      ∑ A ∈ Finset.univ.powerset, x A * A.card.choose j := by
  calc
    (∑ t ∈ Finset.range (profileMass x),
        thresholdFaceCount x (t + 1) j) =
        ∑ t ∈ Finset.range (profileMass x),
          ∑ S ∈ Finset.univ.powerset.filter
              (fun S : Finset I ↦ S.card = j),
            if t < profileIntersectionSize x S then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      exact thresholdFaceCount_succ_eq_indicator_sum x hj t
    _ = ∑ S ∈ Finset.univ.powerset.filter
            (fun S : Finset I ↦ S.card = j),
          ∑ t ∈ Finset.range (profileMass x),
            if t < profileIntersectionSize x S then 1 else 0 := by
      exact Finset.sum_comm
    _ = ∑ S ∈ Finset.univ.powerset.filter
            (fun S : Finset I ↦ S.card = j),
          profileIntersectionSize x S := by
      apply Finset.sum_congr rfl
      intro S _
      rw [sum_range_ite_lt_eq_sum_range (fun _ ↦ 1)
        (profileIntersectionSize_le_profileMass x S)]
      simp
    _ = ∑ A ∈ Finset.univ.powerset, x A * A.card.choose j :=
      sum_profileIntersectionSize_eq_binomialMoment x j

end AntichainOfGivenSize.VennProfile
