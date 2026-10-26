import AntichainOfGivenSize.Paper.Typical
import AntichainOfGivenSize.Paper.Scale
import Mathlib.Analysis.Real.Sqrt

/-!
# Natural density of the exceptional ideal sizes

We count all exceptions up to a cutoff with one application of the counting
theorem. Eventual monotonicity of the comparison function permits this
equivalent alternative to summing dyadic blocks. The finite initial segment
is retained explicitly throughout the estimate.
-/

open Finset Filter Asymptotics
open scoped Topology

namespace AntichainOfGivenSize.Paper

/-- The manuscript's budget for its almost-all and extremal consequences. -/
noncomputable def paperBudget (B : ℕ) : ℕ :=
  ⌊indexScale (Real.logb 2 (B : ℝ)) / 200⌋₊

theorem eventually_paperBudget : ∀ᶠ B : ℕ in atTop,
    AdmissibleBudget B (paperBudget B) ∧
      indexScale (Real.logb 2 (B : ℝ)) / 400 ≤ (paperBudget B : ℝ) := by
  have ht : Tendsto (fun B : ℕ ↦ indexScale (Real.logb 2 (B : ℝ))) atTop atTop :=
    tendsto_indexScale.comp ((Real.tendsto_logb_atTop one_lt_two).comp
      tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually (eventually_ge_atTop 400)] with B hB
  have hnonneg : 0 ≤ indexScale (Real.logb 2 (B : ℝ)) / 200 := by positivity
  have hfloor := Nat.floor_le hnonneg
  have hfloor' := Nat.lt_floor_add_one (indexScale (Real.logb 2 (B : ℝ)) / 200)
  have hpos : 1 ≤ paperBudget B := by
    apply (Nat.one_le_floor_iff _).mpr
    linarith
  refine ⟨⟨hpos, ?_⟩, ?_⟩
  · have hle : (paperBudget B : ℝ) ≤ indexScale (Real.logb 2 (B : ℝ)) / 100 := by
      dsimp [paperBudget]
      linarith
    convert hle using 1
    simp only [indexScale]
    ring
  · dsimp [paperBudget]
    linarith

/-- The least integer exponent strictly above the logarithm of the cutoff. -/
noncomputable def cutoffBits (X : ℕ) : ℕ := ⌊Real.logb 2 (X : ℝ)⌋₊ + 1

theorem cutoffBits_pos (X : ℕ) : 0 < cutoffBits X := by
  unfold cutoffBits
  omega

theorem cutoffBits_bounds {X : ℕ} (hX : 0 < X) :
    X < 2 ^ cutoffBits X ∧
      ((2 ^ cutoffBits X : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hlog : 0 ≤ Real.logb 2 (X : ℝ) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast hX)
  have hfloor := Nat.floor_le hlog
  have hfloor' := Nat.lt_floor_add_one (Real.logb 2 (X : ℝ))
  have hpow : (X : ℝ) < (2 : ℝ) ^ (cutoffBits X : ℝ) := by
    rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hXr]
    apply Real.rpow_lt_rpow_of_exponent_lt one_lt_two
    simpa [cutoffBits, Nat.cast_add, Nat.cast_one] using hfloor'
  constructor
  · have hpow' : (X : ℝ) < (2 : ℝ) ^ cutoffBits X := by
      simpa only [Real.rpow_natCast] using hpow
    exact_mod_cast hpow'
  · rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    calc
      (2 : ℝ) ^ (cutoffBits X : ℝ) ≤
          (2 : ℝ) ^ (Real.logb 2 (X : ℝ) + 1) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        simpa [cutoffBits, Nat.cast_add, Nat.cast_one] using add_le_add_right hfloor 1
      _ = 2 * (X : ℝ) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
          Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hXr]
        ring

theorem tendsto_cutoffBits : Tendsto cutoffBits atTop atTop := by
  have h : Tendsto (fun X : ℕ ↦ ⌊Real.logb 2 (X : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((Real.tendsto_logb_atTop one_lt_two).comp
      tendsto_natCast_atTop_atTop)
  exact tendsto_atTop_mono (fun X ↦ by simp [cutoffBits]) h

theorem tendsto_block_error : Tendsto
    (fun B : ℕ ↦ (2 : ℝ) ^ (-Real.sqrt (B : ℝ))) atTop (nhds 0) := by
  exact (tendsto_rpow_atBot_of_base_gt_one 2 one_lt_two).comp
    (tendsto_neg_atTop_atBot.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))

/-- The all-values count implies the paper's density-zero exceptional set,
with its stated explicit lower constant `1/800`. -/
theorem density_of_countingBound (hcount : CountingBoundStatement) :
    Tendsto (fun X : ℕ ↦
      ((exceptionalInputs (1 / 800) X).card : ℝ) / (X : ℝ)) atTop (nhds 0) := by
  classical
  obtain ⟨B₀, hcount⟩ := hcount
  obtain ⟨R, _, hmono⟩ := eventually_growth_monotone
  let N : ℕ := ⌈max R 5⌉₊
  have hNR : R ≤ (N : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  have hbound : ∀ᶠ X : ℕ in atTop,
      ((exceptionalInputs (1 / 800) X).card : ℝ) / (X : ℝ) ≤
        (N : ℝ) / X + 2 * (2 : ℝ) ^ (-Real.sqrt (cutoffBits X : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1,
      tendsto_cutoffBits.eventually (eventually_ge_atTop B₀),
      tendsto_cutoffBits.eventually eventually_paperBudget] with X hX hB hbudget
    let B := cutoffBits X
    let K := paperBudget B
    have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
    have hb := cutoffBits_bounds (by omega : 0 < X)
    have hsub : exceptionalInputs (1 / 800) X ⊆
        Finset.range N ∪ attainableValues B K := by
      intro n hn
      obtain ⟨hnrange, hnsmall⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn5, hnX⟩ := Finset.mem_Icc.mp hnrange
      by_cases hnN : n < N
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr hnN)
      · apply Finset.mem_union_right
        have hnB : n < 2 ^ B := hnX.trans_lt hb.1
        have hgrowth : quadraticLogLogScale (n : ℝ) ≤
            indexScale (Real.logb 2 (B : ℝ)) := by
          rw [← growth_two_pow B]
          apply hmono n ((2 : ℝ) ^ B)
          · exact hNR.trans (by exact_mod_cast (show N ≤ n by omega))
          · exact_mod_cast hnB.le
        have hscale0 : 0 ≤ indexScale (Real.logb 2 (B : ℝ)) := by
          have hpos : 0 < indexScale (Real.logb 2 (B : ℝ)) := by
            have hraw := (Nat.one_le_floor_iff _).mp hbudget.1.1
            change 1 ≤ indexScale (Real.logb 2 (B : ℝ)) / 200 at hraw
            linarith
          exact hpos.le
        have halpha : (alpha n : ℝ) ≤ (K : ℝ) := by
          calc
            (alpha n : ℝ) ≤ (1 / 800 : ℝ) * quadraticLogLogScale (n : ℝ) := hnsmall.le
            _ ≤ (1 / 800 : ℝ) * indexScale (Real.logb 2 (B : ℝ)) := by gcongr
            _ ≤ indexScale (Real.logb 2 (B : ℝ)) / 400 := by nlinarith
            _ ≤ (K : ℝ) := hbudget.2
        exact mem_attainableValues_of_alpha_le (by omega) hnB (by exact_mod_cast halpha)
    have hcard : ((exceptionalInputs (1 / 800) X).card : ℝ) ≤
        N + (2 : ℝ) ^ ((B : ℝ) - Real.sqrt B) := by
      calc
        ((exceptionalInputs (1 / 800) X).card : ℝ) ≤
            ((Finset.range N ∪ attainableValues B K).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        _ ≤ (N : ℝ) + ((attainableValues B K).card : ℝ) := by
          exact_mod_cast (by simpa using
            (Finset.card_union_le (Finset.range N) (attainableValues B K)))
        _ ≤ N + (2 : ℝ) ^ ((B : ℝ) - Real.sqrt B) :=
          add_le_add_right (hcount B K hB hbudget.1) _
    calc
      ((exceptionalInputs (1 / 800) X).card : ℝ) / (X : ℝ) ≤
          (N + (2 : ℝ) ^ ((B : ℝ) - Real.sqrt B)) / X :=
        div_le_div_of_nonneg_right hcard hX0.le
      _ = (N : ℝ) / X + ((2 : ℝ) ^ B / X) * (2 : ℝ) ^ (-Real.sqrt B) := by
        rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
        ring
      _ ≤ (N : ℝ) / X + 2 * (2 : ℝ) ^ (-Real.sqrt B) := by
        have hp : (2 : ℝ) ^ B / X ≤ 2 := (div_le_iff₀ hX0).mpr (by exact_mod_cast hb.2)
        gcongr
  have hlim : Tendsto (fun X : ℕ ↦
      (N : ℝ) / X + 2 * (2 : ℝ) ^ (-Real.sqrt (cutoffBits X : ℝ))) atTop (nhds 0) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (N : ℝ)).add
      ((tendsto_block_error.comp tendsto_cutoffBits).const_mul 2) using 1 <;> norm_num
  exact squeeze_zero' (Filter.Eventually.of_forall fun X ↦ by positivity) hbound hlim

theorem almostAllLowerBound_of_countingBound
    (hcount : CountingBoundStatement) : AlmostAllLowerBoundStatement :=
  ⟨1 / 800, by norm_num, density_of_countingBound hcount⟩

end AntichainOfGivenSize.Paper
