import AntichainOfGivenSize.Analysis.Paper.FaithfulCounting.OriginalQueryReconstruction
import AntichainOfGivenSize.Analysis.Paper.FaithfulCounting.IncidenceCount
import AntichainOfGivenSize.Analysis.LowerBound.FiniteFiberBound
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators
open Finset
open AntichainOfGivenSize.ClusterCore
open AntichainOfGivenSize.ClusterLowerBound
open AntichainOfGivenSize.Section6

namespace AntichainOfGivenSize.FaithfulLower

variable {V : Type*} [DecidableEq V]

/-- Rounding a real loss upward preserves exactly the integer adjacency test. -/
theorem ceil_proximity_iff {B : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρB : ρ ≤ B)
    (e : ℕ) : B - ⌈ρ⌉₊ < e ↔ (B : ℝ) - ρ < e := by
  have hq : ⌈ρ⌉₊ ≤ B := Nat.ceil_le.2 hρB
  have hqlo : ρ ≤ (⌈ρ⌉₊ : ℝ) := Nat.le_ceil ρ
  have hqhi : (⌈ρ⌉₊ : ℝ) < ρ + 1 := Nat.ceil_lt_add_one hρ
  constructor
  · intro he
    have he' : ((B - ⌈ρ⌉₊ : ℕ) : ℝ) + 1 ≤ e := by
      exact_mod_cast (Nat.succ_le_of_lt he)
    rw [Nat.cast_sub hq] at he'
    linarith
  · intro he
    have he' : ((B - ⌈ρ⌉₊ : ℕ) : ℝ) < e := by
      rw [Nat.cast_sub hq]
      linarith
    exact_mod_cast he'

theorem realProximityGraph_eq_ceil {I : Type*} [DecidableEq I]
    (G : I → Finset V) {B : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρB : ρ ≤ B) :
    realProximityGraph G B ρ = intersectionProximityGraph G B ⌈ρ⌉₊ := by
  ext i j
  exact and_congr_right (fun _ ↦ (ceil_proximity_iff hρ hρB _).symm)

/-- A noncentral original index set contains a coarse nonedge, bounding its
full intersection exponent without any exceptional-set correction. -/
theorem noncenter_intersection_card_le_real {K B h r : ℕ} {ρ : ℝ}
    {gFine : SimpleGraph (Fin K)} (P : PackedClusters gFine h r)
    (G : Fin K → Finset V) (t : IEQuery (Finset.univ : Finset (Fin K)))
    (ht : ¬ IsCenterQuery (realProximityGraph G B ρ) P t) :
    (#(generatorIntersection G t) : ℝ) ≤ B - ρ := by
  rcases exists_residual_nonedge_of_not_center P t ht with
    ⟨i, hi, j, hj, hij, hnonedge⟩
  have hinter : (#(G i ∩ G j) : ℝ) ≤ B - ρ := by
    by_contra hnot
    exact hnonedge ⟨hij, lt_of_not_ge hnot⟩
  have hsub : generatorIntersection G t ⊆ G i ∩ G j := by
    intro v hv
    have hall : ∀ a ∈ t.1, v ∈ G a := by simpa [generatorIntersection] using hv
    exact Finset.mem_inter.2
      ⟨hall i (Finset.mem_inter.1 hi).1, hall j (Finset.mem_inter.1 hj).1⟩
  have hcard : (#(generatorIntersection G t) : ℝ) ≤ (#(G i ∩ G j) : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans hinter

theorem noncenter_intersection_card_le_ceil {K B h r : ℕ} {ρ : ℝ}
    {gFine : SimpleGraph (Fin K)} (P : PackedClusters gFine h r)
    (G : Fin K → Finset V) (hρ : 0 ≤ ρ) (hρB : ρ ≤ B)
    (t : IEQuery (Finset.univ : Finset (Fin K)))
    (ht : ¬ IsCenterQuery (realProximityGraph G B ρ) P t) :
    #(generatorIntersection G t) ≤ B - ⌈ρ⌉₊ := by
  apply Nat.le_of_not_gt
  intro hgt
  exact (not_lt_of_ge (noncenter_intersection_card_le_real P G t ht))
    ((ceil_proximity_iff hρ hρB _).1 hgt)

noncomputable def originalIETerm {K : ℕ} (G : Fin K → Finset V)
    (t : IEQuery (Finset.univ : Finset (Fin K))) : ℤ :=
  (-1 : ℤ) ^ (t.1.card + 1) * (2 : ℤ) ^ #(generatorIntersection G t)

noncomputable def originalTailSum {K : ℕ} (G : Fin K → Finset V)
    (centers : Finset (IEQuery (Finset.univ : Finset (Fin K)))) : ℤ := by
  classical
  exact ∑ t ∈ Finset.univ \ centers, originalIETerm G t

theorem idealCard_eq_originalCentral_add_tail {K : ℕ} (G : Fin K → Finset V)
    (centers : Finset (IEQuery (Finset.univ : Finset (Fin K)))) :
    ((generatedIdealIdx Finset.univ G).card : ℤ) =
      originalCentralSum G centers + originalTailSum G centers := by
  classical
  rw [generatedIdealIdx_card_inclusionExclusion]
  exact (Finset.sum_add_sum_compl centers (originalIETerm G)).symm

/-- Pure original-query tail bound, parameterized only by the full exponents. -/
theorem originalTailSum_natAbs_le {K T : ℕ} (G : Fin K → Finset V)
    (centers : Finset (IEQuery (Finset.univ : Finset (Fin K))))
    (hexp : ∀ t, t ∉ centers → #(generatorIntersection G t) ≤ T) :
    (originalTailSum G centers).natAbs ≤ 2 ^ K * 2 ^ T := by
  classical
  let tails := (Finset.univ : Finset (IEQuery (Finset.univ : Finset (Fin K)))) \ centers
  change (∑ t ∈ tails, originalIETerm G t).natAbs ≤ _
  calc
    (∑ t ∈ tails, originalIETerm G t).natAbs ≤
        ∑ t ∈ tails, (originalIETerm G t).natAbs := Int.natAbs_sum_le tails _
    _ ≤ ∑ _t ∈ tails, 2 ^ T := by
      apply Finset.sum_le_sum
      intro t ht
      have hcard := hexp t (Finset.mem_sdiff.1 ht).2
      simpa [originalIETerm, Int.natAbs_mul, Int.natAbs_pow] using
        Nat.pow_le_pow_right (by omega : 0 < 2) hcard
    _ = #tails * 2 ^ T := by simp
    _ ≤ 2 ^ K * 2 ^ T := by
      exact Nat.mul_le_mul_right _
        ((Finset.card_le_univ tails).trans (card_ieQuery_le_two_pow K))

/-- The integer tail radius is bounded by the literal real power from the paper. -/
theorem tailRadius_real_le {K B : ℕ} {ρ : ℝ} (hρB : ρ ≤ B) :
    ((2 ^ K * 2 ^ (B - ⌈ρ⌉₊) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((B : ℝ) - ρ + K) := by
  have hq : ⌈ρ⌉₊ ≤ B := Nat.ceil_le.2 hρB
  have hqlo : ρ ≤ (⌈ρ⌉₊ : ℝ) := Nat.le_ceil ρ
  calc
    ((2 ^ K * 2 ^ (B - ⌈ρ⌉₊) : ℕ) : ℝ) =
        (2 : ℝ) ^ ((K + (B - ⌈ρ⌉₊) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, pow_add]
      push_cast
      rfl
    _ ≤ (2 : ℝ) ^ ((B : ℝ) - ρ + K) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [Nat.cast_add, Nat.cast_sub hq]
      linarith

theorem originalTailSum_abs_le_real {K B h r : ℕ} {ρ : ℝ}
    {gFine : SimpleGraph (Fin K)} (P : PackedClusters gFine h r)
    (G : Fin K → Finset V) (hρ : 0 ≤ ρ) (hρB : ρ ≤ B) :
    |(originalTailSum G (packedCenters P (realProximityGraph G B ρ)) : ℝ)| ≤
      (2 : ℝ) ^ ((B : ℝ) - ρ + K) := by
  have htail := originalTailSum_natAbs_le G
    (packedCenters P (realProximityGraph G B ρ)) (T := B - ⌈ρ⌉₊) (by
      intro t ht
      apply noncenter_intersection_card_le_ceil P G hρ hρB t
      simpa [packedCenters] using ht)
  have hcast : ((originalTailSum G
      (packedCenters P (realProximityGraph G B ρ))).natAbs : ℝ) ≤
      ((2 ^ K * 2 ^ (B - ⌈ρ⌉₊) : ℕ) : ℝ) := by exact_mod_cast htail
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast.trans (tailRadius_real_le hρB)

/-- The literal |Φ−Z| estimate after exact inclusion–exclusion splitting. -/
theorem idealCard_sub_center_abs_le_real {K B h r : ℕ} {ρ : ℝ}
    {gFine : SimpleGraph (Fin K)} (P : PackedClusters gFine h r)
    (G : Fin K → Finset V) (hρ : 0 ≤ ρ) (hρB : ρ ≤ B) :
    |((((generatedIdealIdx Finset.univ G).card : ℤ) -
      originalCentralSum G (packedCenters P (realProximityGraph G B ρ))) : ℝ)| ≤
      (2 : ℝ) ^ ((B : ℝ) - ρ + K) := by
  rw [idealCard_eq_originalCentral_add_tail G
    (packedCenters P (realProximityGraph G B ρ)), Int.cast_add, add_sub_cancel_left]
  exact originalTailSum_abs_le_real P G hρ hρB

/-- The size of an integer interval of radius the integer tail bound. -/
theorem integer_tail_interval_card {K B : ℕ} {ρ : ℝ} (Z : ℤ) (hρB : ρ ≤ B) :
    let R : ℕ := 2 ^ K * 2 ^ (B - ⌈ρ⌉₊)
    (#(Finset.Icc (Z - R) (Z + R)) : ℝ) ≤
      (2 : ℝ) ^ ((B : ℝ) - ρ + K + 2) := by
  dsimp only
  let R : ℕ := 2 ^ K * 2 ^ (B - ⌈ρ⌉₊)
  have hR : (R : ℝ) ≤ (2 : ℝ) ^ ((B : ℝ) - ρ + K) := tailRadius_real_le hρB
  have hpos : 1 ≤ (2 : ℝ) ^ ((B : ℝ) - ρ + K) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hc : (#(Finset.Icc (Z - R) (Z + R)) : ℝ) = 2 * (R : ℝ) + 1 := by
    have hcZ := Int.card_Icc_of_le (a := Z - R) (b := Z + R) (by omega)
    have hcZ' : (#(Finset.Icc (Z - R) (Z + R)) : ℤ) = 2 * (R : ℤ) + 1 := by
      rw [hcZ]
      ring
    exact_mod_cast hcZ'
  change (#(Finset.Icc (Z - R) (Z + R)) : ℝ) ≤ _
  rw [hc, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num
  linarith

/-- A fixed header gives this exact finite bound from the actual two records.
The hypotheses describe size bounds, within-cluster agreement, and the original
noncentral intersection bounds; no counting conclusion is assumed. -/
theorem fixedHeaderCount_nat {X κ : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq κ] {VX : X → Type*} [∀ x, DecidableEq (VX x)] {K B u T : ℕ}
    (G : ∀ x, Fin K → Finset (VX x)) (U : ∀ x, Finset (VX x))
    (role : Fin K → κ)
    (centers : Finset (IEQuery (Finset.univ : Finset (Fin K))))
    (hsize : ∀ x i, #(G x i) ≤ B) (hU : ∀ x, #(U x) ≤ u)
    (hagree : ∀ x, RoleAgreementOutside (G x) (U x) role)
    (htail : ∀ x t, t ∉ centers → #(generatorIntersection (G x) t) ≤ T) :
    #((Finset.univ : Finset X).image
        (fun x ↦ (generatedIdealIdx Finset.univ (G x)).card)) ≤
      Fintype.card (SparseCode (Finset (Fin K)) u) *
        (B + 1) ^ (centralKeys role centers).card *
        (2 * (2 ^ K * 2 ^ T) + 1) := by
  classical
  let Code := SparseCode (Finset (Fin K)) u ×
    (centralKeys role centers → Fin (B + 1))
  let encode : X → Code := fun x ↦
    (incidenceSparseCode (G x) (U x) u (hU x),
      centralExponentVector (G x) (U x) role centers B (hsize x))
  let value : X → ℕ := fun x ↦ (generatedIdealIdx Finset.univ (G x)).card
  have hdiam : ∀ x y, encode x = encode y →
      Int.natAbs ((value x : ℤ) - (value y : ℤ)) ≤ 2 * (2 ^ K * 2 ^ T) := by
    intro x y hcode
    have hcenter := originalCentralSum_eq_of_sparseCode_vector_eq
      (G x) (G y) (U x) (U y) role centers B u
      (hsize x) (hsize y) (hU x) (hU y) (hagree x) (hagree y)
      (congrArg Prod.fst hcode) (congrArg Prod.snd hcode)
    have hx := originalTailSum_natAbs_le (G x) centers (htail x)
    have hy := originalTailSum_natAbs_le (G y) centers (htail y)
    change Int.natAbs
      (((generatedIdealIdx Finset.univ (G x)).card : ℤ) -
        ((generatedIdealIdx Finset.univ (G y)).card : ℤ)) ≤ _
    rw [idealCard_eq_originalCentral_add_tail, idealCard_eq_originalCentral_add_tail, hcenter]
    have hdiff : originalCentralSum (G y) centers + originalTailSum (G x) centers -
        (originalCentralSum (G y) centers + originalTailSum (G y) centers) =
        originalTailSum (G x) centers - originalTailSum (G y) centers := by ring
    rw [hdiff]
    have htri := Int.natAbs_add_le (originalTailSum (G x) centers)
      (-originalTailSum (G y) centers)
    simp only [Int.natAbs_neg, ← sub_eq_add_neg] at htri
    omega
  have hb := card_image_le_card_mul_of_fiber_diameter encode value
    (2 * (2 ^ K * 2 ^ T)) hdiam
  simpa only [Code, Fintype.card_prod, card_centralExponentVectors] using hb

/-- Real interval factor needed after the finite-fiber lemma. -/
theorem tailFiberFactor_real_le {K B : ℕ} {ρ : ℝ} (hρB : ρ ≤ B) :
    ((2 * (2 ^ K * 2 ^ (B - ⌈ρ⌉₊)) + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((B : ℝ) - ρ + K + 2) := by
  have hR := tailRadius_real_le (K := K) hρB
  have hpos : 1 ≤ (2 : ℝ) ^ ((B : ℝ) - ρ + K) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num
  push_cast at hR ⊢
  linarith

/-- Literal fixed-header product bound: incidence record, central exponents,
and the integer interval containing every fiber. -/
theorem fixedHeaderCount_real {X κ : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq κ] {VX : X → Type*} [∀ x, DecidableEq (VX x)]
    {K B u : ℕ} {ρFine ρ : ℝ}
    (G : ∀ x, Fin K → Finset (VX x)) (U : ∀ x, Finset (VX x))
    (role : Fin K → κ)
    (centers : Finset (IEQuery (Finset.univ : Finset (Fin K))))
    (hsize : ∀ x i, #(G x i) ≤ B) (hU : ∀ x, #(U x) ≤ u)
    (hagree : ∀ x, RoleAgreementOutside (G x) (U x) role)
    (htail : ∀ x t, t ∉ centers →
      #(generatorIntersection (G x) t) ≤ B - ⌈ρ⌉₊)
    (huB : u ≤ K * B) (huρ : (u : ℝ) ≤ 2 * K * ρFine) (hρB : ρ ≤ B) :
    (#((Finset.univ : Finset X).image
        (fun x ↦ (generatedIdealIdx Finset.univ (G x)).card)) : ℝ) ≤
      ((K * B + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (K : ℝ) ^ 2 * ρFine) *
        (B + 1 : ℝ) ^ (centralKeys role centers).card *
        (2 : ℝ) ^ ((B : ℝ) - ρ + K + 2) := by
  have hnat := fixedHeaderCount_nat G U role centers hsize hU hagree htail
  have hcast :
      (#((Finset.univ : Finset X).image
        (fun x ↦ (generatedIdealIdx Finset.univ (G x)).card)) : ℝ) ≤
      (Fintype.card (SparseCode (Finset (Fin K)) u) : ℝ) *
        (B + 1 : ℝ) ^ (centralKeys role centers).card *
        ((2 * (2 ^ K * 2 ^ (B - ⌈ρ⌉₊)) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hrecord := card_incidence_records_real_le huB huρ
  have hfactor := tailFiberFactor_real_le (K := K) hρB
  exact hcast.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right hrecord (by positivity)) hfactor
    (by positivity) (by positivity))



end AntichainOfGivenSize.FaithfulLower
