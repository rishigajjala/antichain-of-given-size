import AntichainOfGivenSize.Analysis.Supporting.MainStatement
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-! Elementary real-variable estimates used for the paper's density and
extremal consequences. -/

open Filter Asymptotics
open scoped Topology

namespace AntichainOfGivenSize.Paper

noncomputable def indexScale (q : ℝ) : ℝ := q ^ 2 / Real.logb 2 q

theorem indexScale_pos {q : ℝ} (hq : 1 < q) : 0 < indexScale q := by
  exact div_pos (sq_pos_of_pos (zero_lt_one.trans hq))
    (Real.logb_pos one_lt_two hq)

/-- Beyond a fixed threshold, the comparison function is increasing. -/
theorem indexScale_monotoneOn : MonotoneOn indexScale (Set.Ici (Real.exp 1)) := by
  intro x hx y hy hxy
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have hx1 : 1 < x := he.trans_le hx
  have hy1 : 1 < y := he.trans_le hy
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hy0 : 0 < y := zero_lt_one.trans hy1
  have h := Real.log_div_self_antitoneOn hx hy hxy
  have hinv : x / Real.log x ≤ y / Real.log y := by
    have hpx : 0 < Real.log x / x := div_pos (Real.log_pos hx1) hx0
    have hpy : 0 < Real.log y / y := div_pos (Real.log_pos hy1) hy0
    simpa only [one_div_div] using (one_div_le_one_div_of_le hpy h)
  have hmul : x * (x / Real.log x) ≤ y * (y / Real.log y) :=
    mul_le_mul hxy hinv (le_of_lt (div_pos hx0 (Real.log_pos hx1))) hy0.le
  have hl2 : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
  simpa only [indexScale, Real.logb, div_div, pow_two, div_eq_mul_inv, mul_inv_rev, inv_inv,
    mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_right hmul hl2

theorem tendsto_indexScale : Tendsto indexScale atTop atTop := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  apply tendsto_atTop_mono' atTop _ ((tendsto_id.const_mul_atTop hl2))
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with q hq
  have hq1 : 1 < q := by linarith
  have hlog : 0 < Real.log q := Real.log_pos hq1
  have hle : Real.log q ≤ q := Real.log_le_self (by linarith)
  have hcomp : q ≤ q ^ 2 / Real.log q := by
    apply (le_div_iff₀ hlog).2
    nlinarith
  simpa only [indexScale, Real.logb, div_div, div_eq_mul_inv, mul_inv_rev, inv_inv, id_eq,
    mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_right hcomp hl2.le

theorem tendsto_loglog : Tendsto (fun x : ℝ ↦ Real.logb 2 (Real.logb 2 x))
    atTop atTop :=
  (Real.tendsto_logb_atTop one_lt_two).comp (Real.tendsto_logb_atTop one_lt_two)

theorem tendsto_growth : Tendsto quadraticLogLogScale atTop atTop :=
  tendsto_indexScale.comp tendsto_loglog

theorem growth_pos_of_four_lt {x : ℝ} (hx : 4 < x) : 0 < quadraticLogLogScale x := by
  have hlog4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow]
    norm_num [Real.logb_self_eq_one]
  have hlog : 2 < Real.logb 2 x := by
    calc
      (2 : ℝ) = Real.logb 2 4 := hlog4.symm
      _ < Real.logb 2 x := Real.logb_lt_logb one_lt_two (by norm_num) hx
  apply indexScale_pos
  have h := Real.logb_lt_logb one_lt_two (by norm_num : (0 : ℝ) < 2) hlog
  simpa only [Real.logb_self_eq_one one_lt_two] using h

theorem eventually_growth_monotone : ∃ R : ℝ, 1 < R ∧
    ∀ x y : ℝ, R ≤ x → x ≤ y → quadraticLogLogScale x ≤ quadraticLogLogScale y := by
  obtain ⟨R, hR⟩ := eventually_atTop.1
    (tendsto_loglog.eventually (eventually_ge_atTop (Real.exp 1)))
  refine ⟨max R 2, by simp, ?_⟩
  intro x y hx hxy
  have hx2 : 2 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.logb 2 x := Real.logb_pos one_lt_two (by linarith)
  have hlog : Real.logb 2 (Real.logb 2 x) ≤ Real.logb 2 (Real.logb 2 y) :=
    Real.logb_le_logb_of_le one_lt_two hlx
      (Real.logb_le_logb_of_le one_lt_two hx0 hxy)
  exact indexScale_monotoneOn (hR x ((le_max_left _ _).trans hx))
    (hR y ((le_max_left _ _).trans (hx.trans hxy))) hlog

theorem growth_two_pow (B : ℕ) :
    quadraticLogLogScale ((2 : ℝ) ^ B) = indexScale (Real.logb 2 (B : ℝ)) := by
  unfold quadraticLogLogScale indexScale
  rw [Real.logb_pow]
  norm_num [Real.logb_self_eq_one]

theorem indexScale_le_four_mul {p q : ℝ} (hp : 1 < p)
    (hpq : p ≤ q) (hqp : q ≤ 2 * p) : indexScale q ≤ 4 * indexScale p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hq0 : 0 < q := hp0.trans_le hpq
  have hlp : 0 < Real.logb 2 p := Real.logb_pos one_lt_two hp
  have hlq : 0 < Real.logb 2 q := Real.logb_pos one_lt_two (hp.trans_le hpq)
  have hlogs : Real.logb 2 p ≤ Real.logb 2 q :=
    Real.logb_le_logb_of_le one_lt_two hp0 hpq
  have hs : q ^ 2 ≤ 4 * p ^ 2 := by nlinarith
  calc
    indexScale q ≤ (4 * p ^ 2) / Real.logb 2 q :=
      div_le_div_of_nonneg_right hs hlq.le
    _ ≤ (4 * p ^ 2) / Real.logb 2 p :=
      div_le_div_of_nonneg_left (by positivity) hlp hlogs
    _ = 4 * indexScale p := by unfold indexScale; ring

/-- A fixed-factor reduction of the argument changes the scale by at most
a fixed factor. This estimate handles the paper's real cutoffs. -/
theorem eventually_growth_quarter : ∀ᶠ X : ℝ in atTop,
    quadraticLogLogScale X ≤ 4 * quadraticLogLogScale (X / 4) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (Real.tendsto_logb_atTop one_lt_two).eventually (eventually_ge_atTop 4),
    tendsto_loglog.eventually (eventually_ge_atTop 4)] with X hX hL hQ
  let L := Real.logb 2 X
  let Q := Real.logb 2 L
  let P := Real.logb 2 (Real.logb 2 (X / 4))
  have hlog4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow]
    norm_num [Real.logb_self_eq_one]
  have hinner : Real.logb 2 (X / 4) = L - 2 := by
    rw [Real.logb_div hX.ne' (by norm_num : (4 : ℝ) ≠ 0), hlog4]
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hhalf0 : 0 < L / 2 := by positivity
  have hhalf : Real.logb 2 (L / 2) = Q - 1 := by
    rw [Real.logb_div hL0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num [Real.logb_self_eq_one, Q]
  have hPlower : Q - 1 ≤ P := by
    rw [← hhalf]
    apply Real.logb_le_logb_of_le one_lt_two hhalf0
    rw [hinner]
    dsimp [L]
    linarith
  have hPupper : P ≤ Q := by
    apply Real.logb_le_logb_of_le one_lt_two
    · rw [hinner]; dsimp [L]; linarith
    · rw [hinner]; linarith
  have hP : 1 < P := by dsimp [Q, L] at hPlower; linarith
  have hQP : Q ≤ 2 * P := by dsimp [Q, L] at *; linarith
  exact indexScale_le_four_mul hP hPupper hQP

end AntichainOfGivenSize.Paper
