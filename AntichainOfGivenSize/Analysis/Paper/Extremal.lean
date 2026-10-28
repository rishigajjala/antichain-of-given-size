import AntichainOfGivenSize.Analysis.Paper.Density
import AntichainOfGivenSize.Analysis.Supporting.MainTheorems

/-!
# The extremal conclusion for real cutoffs

The lower estimate follows from density zero of the exceptions: every
sufficiently large interval `[Y,2Y)` contains a nonexceptional integer.
The upper estimate retains and absorbs the finite initial segment.
-/

open Finset Filter Asymptotics
open scoped Topology

namespace AntichainOfGivenSize.Paper

/-- Theorem 6.7 and Theorem 1.1(i), with all inputs `n ≥ 5`, not merely an
unspecified eventual range. -/
theorem universalUpper_from_five : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n →
    (alpha n : ℝ) ≤ C * quadraticLogLogScale n := by
  classical
  obtain ⟨C, hC, hupper⟩ := isBigO_iff'.mp mainUpperBound
  obtain ⟨N, hN⟩ := eventually_atTop.mp hupper
  let S : ℝ := ∑ n ∈ Finset.Ico 5 N, (alpha n : ℝ) / quadraticLogLogScale n
  have hpos : ∀ n : ℕ, 5 ≤ n → 0 < quadraticLogLogScale n := by
    intro n hn
    apply growth_pos_of_four_lt
    exact_mod_cast (show 4 < n by omega)
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (hpos n (Finset.mem_Ico.mp hn).1).le
  refine ⟨S + C + 1, by linarith, ?_⟩
  intro n hn
  have hg := hpos n hn
  by_cases hnN : N ≤ n
  · have h := hN n hnN
    have ha : (alpha n : ℝ) ≤ C * quadraticLogLogScale n := by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg (alpha n) : (0 : ℝ) ≤ alpha n),
        abs_of_nonneg hg.le] using h
    exact ha.trans (mul_le_mul_of_nonneg_right (by linarith) hg.le)
  · have hnmem : n ∈ Finset.Ico 5 N := Finset.mem_Ico.mpr ⟨hn, by omega⟩
    have hterm : (alpha n : ℝ) / quadraticLogLogScale n ≤ S := by
      exact Finset.single_le_sum
        (fun k hk ↦ div_nonneg (Nat.cast_nonneg _)
          (hpos k (Finset.mem_Ico.mp hk).1).le) hnmem
    have ha := (div_le_iff₀ hg).mp hterm
    exact ha.trans (mul_le_mul_of_nonneg_right (by linarith) hg.le)

theorem eventually_good_interval (hcount : CountingBoundStatement) :
    ∀ᶠ Y : ℕ in atTop, ∃ n : ℕ, Y ≤ n ∧ n < 2 * Y ∧
      (1 / 800 : ℝ) * quadraticLogLogScale n ≤ (alpha n : ℝ) := by
  classical
  have ht : Tendsto (fun Y : ℕ ↦ 2 * Y) atTop atTop :=
    tendsto_atTop_mono (fun Y ↦ by change Y ≤ 2 * Y; omega) tendsto_id
  have hsmall := (density_of_countingBound hcount).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [eventually_ge_atTop 5, ht.eventually hsmall] with Y hY hcard
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hcard' : ((exceptionalInputs (1 / 800) (2 * Y)).card : ℝ) < (Y : ℝ) := by
    have h := (div_lt_iff₀ (show (0 : ℝ) < ((2 * Y : ℕ) : ℝ) by positivity)).mp hcard
    push_cast at h
    linarith
  have hnot : ¬ Finset.Ico Y (2 * Y) ⊆ exceptionalInputs (1 / 800) (2 * Y) := by
    intro hsub
    have hle := Finset.card_le_card hsub
    have hlen : (Finset.Ico Y (2 * Y)).card = Y := by
      rw [Nat.card_Ico]
      omega
    rw [hlen] at hle
    exact (not_le_of_gt hcard') (by exact_mod_cast hle)
  obtain ⟨n, hn, hbad⟩ := Finset.not_subset.mp hnot
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hn
  refine ⟨n, hlo, hhi, ?_⟩
  apply le_of_not_gt
  intro hlt
  apply hbad
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hY.trans hlo, hhi.le⟩, hlt⟩

theorem extremal_upper :
    (fun X : ℝ ↦ (maximumBelow X : ℝ)) =O[atTop] quadraticLogLogScale := by
  obtain ⟨C, hC, hupper⟩ := isBigO_iff'.mp mainUpperBound
  obtain ⟨R, _, hmono⟩ := eventually_growth_monotone
  have hnat : ∀ᶠ n : ℕ in atTop,
      R ≤ (n : ℝ) ∧ 1 ≤ quadraticLogLogScale n ∧
        (alpha n : ℝ) ≤ C * quadraticLogLogScale n := by
    filter_upwards [hupper,
      (tendsto_growth.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1),
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop R)] with n hupper hn hR
    change 1 ≤ quadraticLogLogScale n at hn
    refine ⟨hR, hn, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (alpha n) : (0 : ℝ) ≤ alpha n),
      abs_of_nonneg (by linarith : 0 ≤ quadraticLogLogScale n)] using hupper
  obtain ⟨N, hN⟩ := eventually_atTop.mp hnat
  apply IsBigO.of_bound ((N : ℝ) + C)
  filter_upwards [tendsto_growth.eventually (eventually_ge_atTop 1)] with X hX
  have hb0 : 0 ≤ ((N : ℝ) + C) * quadraticLogLogScale X := by positivity
  have heach : ∀ n ∈ Finset.Ico 1 ⌈X⌉₊,
      (alpha n : ℝ) ≤ ((N : ℝ) + C) * quadraticLogLogScale X := by
    intro n hn
    obtain ⟨_, hnceil⟩ := Finset.mem_Ico.mp hn
    have hnX : (n : ℝ) < X := Nat.lt_ceil.mp hnceil
    by_cases hnN : N ≤ n
    · have h := hN n hnN
      have hscale := hmono n X h.1 hnX.le
      calc
        (alpha n : ℝ) ≤ C * quadraticLogLogScale n := h.2.2
        _ ≤ C * quadraticLogLogScale X := mul_le_mul_of_nonneg_left hscale hC.le
        _ ≤ ((N : ℝ) + C) * quadraticLogLogScale X :=
          mul_le_mul_of_nonneg_right (by exact le_add_of_nonneg_left (Nat.cast_nonneg N))
            (by linarith)
    · have ha : (alpha n : ℝ) ≤ N := by
        exact_mod_cast (alpha_le_self n).trans (show n ≤ N by omega)
      calc
        (alpha n : ℝ) ≤ N := ha
        _ ≤ (N : ℝ) + C := by linarith
        _ ≤ ((N : ℝ) + C) * quadraticLogLogScale X :=
          le_mul_of_one_le_right (by positivity) hX
  have hm : maximumBelow X ≤ ⌊((N : ℝ) + C) * quadraticLogLogScale X⌋₊ := by
    apply Finset.sup_le
    intro n hn
    exact Nat.le_floor (heach n hn)
  have hmc : (maximumBelow X : ℝ) ≤ ((N : ℝ) + C) * quadraticLogLogScale X :=
    (Nat.cast_le.mpr hm).trans (Nat.floor_le hb0)
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (maximumBelow X) : (0 : ℝ) ≤ maximumBelow X),
    abs_of_nonneg (by linarith : 0 ≤ quadraticLogLogScale X)] using hmc

theorem extremal_lower_of_countingBound (hcount : CountingBoundStatement) :
    quadraticLogLogScale =O[atTop] (fun X : ℝ ↦ (maximumBelow X : ℝ)) := by
  obtain ⟨R, _, hmono⟩ := eventually_growth_monotone
  have hfloor : Tendsto (fun X : ℝ ↦ ⌊X / 2⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (Tendsto.atTop_div_const (by norm_num) tendsto_id)
  apply IsBigO.of_bound 3200
  filter_upwards [hfloor.eventually (eventually_good_interval hcount),
    eventually_ge_atTop (4 : ℝ), eventually_ge_atTop (4 * R),
    eventually_growth_quarter,
    tendsto_growth.eventually (eventually_ge_atTop 0)] with X hgood hX4 hXR hquarter hg0
  obtain ⟨n, hnlo, hnhi, hnalpha⟩ := hgood
  have hfloorlo := Nat.lt_floor_add_one (X / 2)
  have hfloorhi := Nat.floor_le (show 0 ≤ X / 2 by linarith)
  have hnloR : X / 4 ≤ (n : ℝ) := by
    have hnat : (⌊X / 2⌋₊ : ℝ) ≤ n := by exact_mod_cast hnlo
    linarith
  have hnX : (n : ℝ) < X := by
    have hnat : (n : ℝ) < 2 * (⌊X / 2⌋₊ : ℝ) := by exact_mod_cast hnhi
    linarith
  have hn1 : 1 ≤ n := by
    have hnat : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast hnat
  have hnmem : n ∈ Finset.Ico 1 ⌈X⌉₊ :=
    Finset.mem_Ico.mpr ⟨hn1, Nat.lt_ceil.mpr hnX⟩
  have hmax : alpha n ≤ maximumBelow X := Finset.le_sup hnmem
  have hscale := hmono (X / 4) n (by linarith) hnloR
  have hbound : quadraticLogLogScale X ≤ 3200 * (maximumBelow X : ℝ) := by
    have hmreal : (alpha n : ℝ) ≤ maximumBelow X := by exact_mod_cast hmax
    nlinarith
  simpa only [Real.norm_eq_abs, abs_of_nonneg hg0,
    abs_of_nonneg (Nat.cast_nonneg (maximumBelow X) : (0 : ℝ) ≤ maximumBelow X)] using hbound

/-- Theorem 1.1's extremal assertion, with the exact maximum for real `X`. -/
theorem extremalOrder_of_countingBound
    (hcount : CountingBoundStatement) : ExtremalOrderStatement :=
  ⟨extremal_upper, extremal_lower_of_countingBound hcount⟩

end AntichainOfGivenSize.Paper
