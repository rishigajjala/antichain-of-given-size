import AntichainOfGivenSize.Definitions
import AntichainOfGivenSize.LowerBound.BoundedProfiles
import AntichainOfGivenSize.LowerBound.ClusterParameters
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.GCongr

/-!
# The quadratic-over-log lower-bound endpoint

This module formalizes the last, reusable part of the cluster obstruction.
It contains no assumption asserting the desired lower bound.
Instead, `hasMatchingLowerBoundInfinitelyOften_of_eventuallySparse` takes the
finite residue-cardinality estimate produced by the cluster argument and
derives the missing residue, the lower bound for `alpha`, and the
infinitely-often analytic conclusion.
-/

open Filter
open Finset

namespace AntichainOfGivenSize.ClusterLowerBound

open AntichainOfGivenSize.ClusterParameters

/-! ## The finite missing-residue argument -/

/-- Natural representatives in the upper half of `ZMod (2^B)`. -/
def upperDyadicHalf (B : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ (B - 1)) (2 ^ B)

@[simp] theorem upperDyadicHalf_card {B : ℕ} (hB : 1 ≤ B) :
    (upperDyadicHalf B).card = 2 ^ (B - 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hB
  simp [upperDyadicHalf, pow_add]
  have hp : 0 < 2 ^ d := pow_pos (by omega) _
  omega

/-- The upper dyadic half, embedded in its residue ring. -/
noncomputable def upperDyadicHalfResidues (B : ℕ) : Finset (ZMod (2 ^ B)) :=
  (upperDyadicHalf B).image fun n : ℕ ↦ (n : ZMod (2 ^ B))

theorem natCast_zmod_injOn_upperDyadicHalf (B : ℕ) :
    Set.InjOn (fun n : ℕ ↦ (n : ZMod (2 ^ B))) (upperDyadicHalf B) := by
  intro a ha b hb hab
  have haUpper : a < 2 ^ B := (Finset.mem_Ico.mp ha).2
  have hbUpper : b < 2 ^ B := (Finset.mem_Ico.mp hb).2
  have hval := congrArg ZMod.val hab
  simpa [ZMod.val_natCast_of_lt haUpper, ZMod.val_natCast_of_lt hbUpper] using hval

@[simp] theorem upperDyadicHalfResidues_card {B : ℕ} (hB : 1 ≤ B) :
    (upperDyadicHalfResidues B).card = 2 ^ (B - 1) := by
  rw [upperDyadicHalfResidues, Finset.card_image_iff.mpr
    (natCast_zmod_injOn_upperDyadicHalf B)]
  exact upperDyadicHalf_card hB

/-- A finite-set pigeonhole lemma in the orientation needed below. -/
theorem exists_mem_not_mem_of_card_lt {M : ℕ} {s t : Finset (ZMod M)}
    (h : s.card < t.card) : ∃ z, z ∈ t ∧ z ∉ s := by
  by_contra hnot
  push Not at hnot
  have hsub : t ⊆ s := fun z hz ↦ hnot z hz
  exact (not_le_of_gt h) (Finset.card_le_card hsub)

/-- Fewer than half of the bounded-profile residues leave a natural
representative missing in the upper dyadic half. -/
theorem exists_upperDyadicHalf_not_boundedResidue {K B : ℕ} (hB : 1 ≤ B)
    (hsparse : (boundedResiduesUpTo K B).card < 2 ^ (B - 1)) :
    ∃ n : ℕ,
      2 ^ (B - 1) ≤ n ∧ n < 2 ^ B ∧
        (n : ZMod (2 ^ B)) ∉ boundedResiduesUpTo K B := by
  have hcard : (boundedResiduesUpTo K B).card <
      (upperDyadicHalfResidues B).card := by
    simpa [upperDyadicHalfResidues_card hB] using hsparse
  obtain ⟨z, hz, hmissing⟩ := exists_mem_not_mem_of_card_lt hcard
  rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
  exact ⟨n, (Finset.mem_Ico.mp hn).1, (Finset.mem_Ico.mp hn).2, hmissing⟩

/-- A missing bounded-profile residue has more than `K` generators. -/
theorem exists_upperDyadicHalf_alpha_gt {K B : ℕ} (hB : 1 ≤ B)
    (hsparse : (boundedResiduesUpTo K B).card < 2 ^ (B - 1)) :
    ∃ n : ℕ,
      2 ^ (B - 1) ≤ n ∧ n < 2 ^ B ∧ K < AntichainOfGivenSize.alpha n := by
  obtain ⟨n, hnLower, hnUpper, hmissing⟩ :=
    exists_upperDyadicHalf_not_boundedResidue hB hsparse
  refine ⟨n, hnLower, hnUpper, ?_⟩
  by_contra hnot
  have halpha : AntichainOfGivenSize.alpha n ≤ K := Nat.le_of_not_gt hnot
  exact hmissing (alpha_le_imp_mem_boundedResiduesUpTo halpha hnUpper)

/-! ## The dyadic analytic window -/

/-- The scale `q² / log₂ q` in the dyadic index. -/
noncomputable def quadraticLogIndexScale (q : ℕ) : ℝ :=
  (q : ℝ) ^ 2 / Real.logb 2 (q : ℝ)

/-- Lower endpoint of the interval produced at index `q`. -/
def lowerTower (q : ℕ) : ℕ := 2 ^ (2 ^ q - 1)

/-- Upper endpoint of the interval produced at index `q`. -/
def upperTower (q : ℕ) : ℕ := 2 ^ (2 ^ q)

theorem logb_nat_two_pow (e : ℕ) :
    Real.logb 2 (((2 ^ e : ℕ) : ℝ)) = (e : ℝ) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow]
  norm_num [Real.logb_self_eq_one]

theorem two_pow_sub_one_lower (q : ℕ) (hq : 1 ≤ q) :
    2 ^ (q - 1) ≤ 2 ^ q - 1 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hq
  simp only [Nat.add_sub_cancel_left, pow_add, pow_one]
  have hp : 0 < 2 ^ d := pow_pos (by omega) _
  omega

/-- The tower interval pins `log₂(log₂ n)` between `q / 2` and `q`. -/
theorem logLog_mem_dyadicTower_window {q n : ℕ} (hq : 4 ≤ q)
    (hnLower : lowerTower q ≤ n) (hnUpper : n < upperTower q) :
    (q : ℝ) / 2 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) ∧
      Real.logb 2 (Real.logb 2 (n : ℝ)) ≤ (q : ℝ) := by
  have hq1 : 1 ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have hlowerPos : 0 < lowerTower q := pow_pos (by omega) _
  have hnPosNat : 0 < n := hlowerPos.trans_le hnLower
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hnPosNat
  have hpowqOneNat : 1 < 2 ^ q := Nat.one_lt_pow (by omega) (by omega)
  have hexpPos : 0 < 2 ^ q - 1 := Nat.sub_pos_of_lt hpowqOneNat
  have hlowerOneNat : 1 < lowerTower q :=
    Nat.one_lt_pow hexpPos.ne' (by omega)
  have hnOne : (1 : ℝ) < n := by
    exact_mod_cast hlowerOneNat.trans_le hnLower
  have hlognPos : 0 < Real.logb 2 (n : ℝ) :=
    Real.logb_pos (by norm_num) hnOne
  have hnLowerReal :
      (((2 ^ (2 ^ q - 1) : ℕ) : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast hnLower
  have hnUpperReal :
      (n : ℝ) ≤ (((2 ^ (2 ^ q) : ℕ) : ℝ)) := by
    exact_mod_cast hnUpper.le
  have hfirstLower :
      ((2 ^ q - 1 : ℕ) : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    calc
      ((2 ^ q - 1 : ℕ) : ℝ) =
          Real.logb 2 (((2 ^ (2 ^ q - 1) : ℕ) : ℝ)) := by
            symm
            exact logb_nat_two_pow _
      _ ≤ Real.logb 2 (n : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hnLowerReal
  have hfirstUpper :
      Real.logb 2 (n : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by
    calc
      Real.logb 2 (n : ℝ) ≤
          Real.logb 2 (((2 ^ (2 ^ q) : ℕ) : ℝ)) :=
        Real.logb_le_logb_of_le (by norm_num) hnPos hnUpperReal
      _ = ((2 ^ q : ℕ) : ℝ) := logb_nat_two_pow _
  have hhalfPowerNat : 2 ^ (q - 1) ≤ 2 ^ q - 1 :=
    two_pow_sub_one_lower q hq1
  have hhalfPower :
      (((2 ^ (q - 1) : ℕ) : ℝ)) ≤ Real.logb 2 (n : ℝ) := by
    exact (by exact_mod_cast hhalfPowerNat :
      (((2 ^ (q - 1) : ℕ) : ℝ)) ≤ ((2 ^ q - 1 : ℕ) : ℝ)).trans hfirstLower
  have hsecondLower :
      ((q - 1 : ℕ) : ℝ) ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) := by
    calc
      ((q - 1 : ℕ) : ℝ) =
          Real.logb 2 (((2 ^ (q - 1) : ℕ) : ℝ)) := by
            symm
            exact logb_nat_two_pow _
      _ ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hhalfPower
  have hsecondUpper :
      Real.logb 2 (Real.logb 2 (n : ℝ)) ≤ (q : ℝ) := by
    calc
      Real.logb 2 (Real.logb 2 (n : ℝ)) ≤
          Real.logb 2 (((2 ^ q : ℕ) : ℝ)) :=
        Real.logb_le_logb_of_le (by norm_num) hlognPos hfirstUpper
      _ = (q : ℝ) := logb_nat_two_pow _
  constructor
  · have hqsub : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub hq1]
      norm_num
    rw [hqsub] at hsecondLower
    have hq2Real : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    linarith
  · exact hsecondUpper

theorem index_le_lowerTower (q : ℕ) : q ≤ lowerTower q := by
  have hqpow : q < 2 ^ q := q.lt_two_pow_self
  have hexp : q ≤ 2 ^ q - 1 := by omega
  have hpowexp : 2 ^ q ≤ 2 ^ (2 ^ q - 1) :=
    Nat.pow_le_pow_right (by omega) hexp
  exact hqpow.le.trans hpowexp

/-- On the dyadic window, the target scale is at most twice the index scale. -/
theorem improvedScale_le_two_mul_quadraticLogIndexScale {q n : ℕ} (hq : 4 ≤ q)
    (hlower : (q : ℝ) / 2 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)))
    (hupper : Real.logb 2 (Real.logb 2 (n : ℝ)) ≤ (q : ℝ)) :
    AntichainOfGivenSize.improvedScale n ≤ 2 * quadraticLogIndexScale q := by
  let Q : ℝ := Real.logb 2 (Real.logb 2 (n : ℝ))
  have hq4 : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hqone : (1 : ℝ) < q := by linarith
  have hqhalfpos : (0 : ℝ) < (q : ℝ) / 2 := by positivity
  have hQtwo : (2 : ℝ) ≤ Q := by
    dsimp [Q]
    linarith
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQtwo
  have hQone : 1 < Q := lt_of_lt_of_le (by norm_num) hQtwo
  have hlogqpos : 0 < Real.logb 2 (q : ℝ) :=
    Real.logb_pos (by norm_num) hqone
  have hlogQpos : 0 < Real.logb 2 Q :=
    Real.logb_pos (by norm_num) hQone
  have hlogqTwo : (2 : ℝ) ≤ Real.logb 2 (q : ℝ) := by
    have hmono := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 4) hq4
    calc
      (2 : ℝ) = Real.logb 2 ((2 : ℝ) ^ (2 : ℕ)) := by
        rw [Real.logb_pow]
        norm_num [Real.logb_self_eq_one]
      _ = Real.logb 2 4 := by norm_num
      _ ≤ Real.logb 2 (q : ℝ) := hmono
  have hlogHalf :
      Real.logb 2 ((q : ℝ) / 2) = Real.logb 2 (q : ℝ) - 1 := by
    rw [Real.logb_div (ne_of_gt hqpos) (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num [Real.logb_self_eq_one]
  have hlogLower :
      Real.logb 2 ((q : ℝ) / 2) ≤ Real.logb 2 Q := by
    apply Real.logb_le_logb_of_le (by norm_num)
    · exact hqhalfpos
    · exact hlower
  have hdenom :
      (1 / 2 : ℝ) * Real.logb 2 (q : ℝ) ≤ Real.logb 2 Q := by
    rw [hlogHalf] at hlogLower
    linarith
  have hQnonneg : 0 ≤ Q := hQpos.le
  have hqnonneg : (0 : ℝ) ≤ q := hqpos.le
  have hQsq : Q ^ 2 ≤ (q : ℝ) ^ 2 :=
    (sq_le_sq₀ hQnonneg hqnonneg).2 hupper
  calc
    AntichainOfGivenSize.improvedScale n = Q ^ 2 / Real.logb 2 Q := by rfl
    _ ≤ (q : ℝ) ^ 2 / Real.logb 2 Q :=
      div_le_div_of_nonneg_right hQsq hlogQpos.le
    _ ≤ (q : ℝ) ^ 2 /
        ((1 / 2 : ℝ) * Real.logb 2 (q : ℝ)) := by
      exact div_le_div_of_nonneg_left (sq_nonneg (q : ℝ))
        (mul_pos (by norm_num) hlogqpos) hdenom
    _ = 2 * quadraticLogIndexScale q := by
      simp only [quadraticLogIndexScale]
      field_simp

/-! ## The floor in the facet budget -/

/-- If a positive denominator fits twice below a numerator, the natural
quotient is at least half of the corresponding real quotient. -/
theorem half_real_quotient_le_nat_quotient {x y : ℕ}
    (hy : 0 < y) (hxy : 2 * y ≤ x) :
    (x : ℝ) / (2 * y : ℕ) ≤ ((x / y : ℕ) : ℝ) := by
  have hmod : x % y < y := Nat.mod_lt x hy
  have hdecomp : y * (x / y) + x % y = x := Nat.div_add_mod x y
  have hltNat : x < (x / y + 1) * y := by
    calc
      x = x / y * y + x % y := by simpa [Nat.mul_comm] using hdecomp.symm
      _ < x / y * y + y := Nat.add_lt_add_left hmod _
      _ = (x / y + 1) * y := by ring
  have hyReal : (0 : ℝ) < y := by exact_mod_cast hy
  have hltReal : (x : ℝ) < ((x / y + 1) * y : ℕ) := by exact_mod_cast hltNat
  have hratioLt : (x : ℝ) / (y : ℝ) < ((x / y : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hyReal).2
    exact_mod_cast hltReal
  have hxyReal : (2 : ℝ) * (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxy
  have hratioTwo : (2 : ℝ) ≤ (x : ℝ) / (y : ℝ) := by
    apply (le_div_iff₀ hyReal).2
    exact hxyReal
  have hrewrite : (x : ℝ) / ((2 * y : ℕ) : ℝ) =
      ((x : ℝ) / (y : ℝ)) / 2 := by
    norm_num [Nat.cast_mul]
    field_simp
  rw [hrewrite]
  linarith

theorem two_mul_budgetDenominator_le {t : ℕ} (ht : 11 ≤ t) :
    2 * (1024 * t) ≤ dyadicQ t ^ 2 := by
  have htPower : t ≤ 2 ^ t := t.lt_two_pow_self.le
  have hexp : t + 11 ≤ 2 * t := by omega
  calc
    2 * (1024 * t) = 2 ^ 11 * t := by ring
    _ ≤ 2 ^ 11 * 2 ^ t := Nat.mul_le_mul_left _ htPower
    _ = 2 ^ (t + 11) := by rw [pow_add]; ring
    _ ≤ 2 ^ (2 * t) := Nat.pow_le_pow_right (by omega) hexp
    _ = 2 ^ (t + t) := by congr 1; omega
    _ = 2 ^ t * 2 ^ t := by rw [pow_add]
    _ = dyadicQ t ^ 2 := by simp [dyadicQ, pow_two]

/-- The concrete facet budget is a fixed positive fraction of
`q² / log₂ q` for `t ≥ 11`. -/
theorem facetBudget_real_lower {t : ℕ} (ht : 11 ≤ t) :
    (1 / 2048 : ℝ) * quadraticLogIndexScale (dyadicQ t) ≤
      (facetBudget t : ℝ) := by
  have htPos : 0 < t := by omega
  have hfloor := half_real_quotient_le_nat_quotient
    (x := dyadicQ t ^ 2) (y := 1024 * t) (by positivity)
    (two_mul_budgetDenominator_le ht)
  have hlog : Real.logb 2 (dyadicQ t : ℝ) = (t : ℝ) := by
    simpa [dyadicQ] using logb_nat_two_pow t
  rw [quadraticLogIndexScale, hlog, facetBudget]
  norm_num [Nat.cast_mul, Nat.cast_pow] at hfloor ⊢
  convert hfloor using 1
  field_simp
  ring

/-! ## Infinitely-often consequence -/

/-- A named proposition for an infinitely-often lower bound matching the
paper's upper-bound scale. -/
def HasMatchingLowerBoundInfinitelyOften : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    c * AntichainOfGivenSize.improvedScale n ≤
      (AntichainOfGivenSize.alpha n : ℝ)

/-- The exact finite cardinality estimate still to be supplied by the
cluster-counting argument. -/
def EventuallySparseDyadicProfiles : Prop :=
  ∀ᶠ t : ℕ in atTop,
    (boundedResiduesUpTo (facetBudget t) (dyadicB t)).card <
      2 ^ (dyadicB t - 1)

/-- The finite residue-sparsity estimate gives an explicit pointwise
constant on arbitrarily large witnesses. -/
theorem matchingLowerBoundInfinitelyOften_of_eventuallySparse
    (hsparse : EventuallySparseDyadicProfiles) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (1 / 4096 : ℝ) * AntichainOfGivenSize.improvedScale n ≤
        (AntichainOfGivenSize.alpha n : ℝ) := by
  rw [EventuallySparseDyadicProfiles, eventually_atTop] at hsparse
  obtain ⟨T, hT⟩ := hsparse
  intro N
  let t := max T (max N 11)
  let q := dyadicQ t
  have htT : T ≤ t := le_max_left _ _
  have htN : N ≤ t := (le_max_left N 11).trans (le_max_right T (max N 11))
  have ht11 : 11 ≤ t := (le_max_right N 11).trans (le_max_right T (max N 11))
  have hq4 : 4 ≤ q := by
    have : 4 ≤ 2 ^ t := by
      calc 4 = 2 ^ 2 := by norm_num
           _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) (by omega)
    simpa [q, dyadicQ] using this
  have hB : 1 ≤ dyadicB t := dyadicB_pos t
  obtain ⟨n, hnLower, hnUpper, halpha⟩ :=
    exists_upperDyadicHalf_alpha_gt hB (hT t htT)
  have hnTowerLower : lowerTower q ≤ n := by
    simpa [lowerTower, q, dyadicB] using hnLower
  have hnTowerUpper : n < upperTower q := by
    simpa [upperTower, q, dyadicB] using hnUpper
  obtain ⟨hwindowLower, hwindowUpper⟩ :=
    logLog_mem_dyadicTower_window hq4 hnTowerLower hnTowerUpper
  have hscale := improvedScale_le_two_mul_quadraticLogIndexScale
    hq4 hwindowLower hwindowUpper
  refine ⟨n, ?_, ?_⟩
  · exact htN.trans (t.lt_two_pow_self.le.trans (index_le_lowerTower q) |>.trans hnTowerLower)
  · have hbudget := facetBudget_real_lower ht11
    have halphaReal : (facetBudget t : ℝ) ≤
        (AntichainOfGivenSize.alpha n : ℝ) := by exact_mod_cast halpha.le
    calc
      (1 / 4096 : ℝ) * AntichainOfGivenSize.improvedScale n ≤
          (1 / 4096 : ℝ) * (2 * quadraticLogIndexScale q) := by
        gcongr
      _ = (1 / 2048 : ℝ) * quadraticLogIndexScale q := by ring
      _ ≤ (facetBudget t : ℝ) := by simpa [q] using hbudget
      _ ≤ (AntichainOfGivenSize.alpha n : ℝ) := halphaReal

/-- The finite residue-sparsity estimate implies the matching
`Ω((log log n)² / log log log n)` lower bound infinitely often. -/
theorem hasMatchingLowerBoundInfinitelyOften_of_eventuallySparse
    (hsparse : EventuallySparseDyadicProfiles) :
    HasMatchingLowerBoundInfinitelyOften := by
  exact ⟨1 / 4096, by norm_num,
    matchingLowerBoundInfinitelyOften_of_eventuallySparse hsparse⟩

end AntichainOfGivenSize.ClusterLowerBound
