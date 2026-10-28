import AntichainOfGivenSize.Analysis.Supporting.Theorem
import AntichainOfGivenSize.Analysis.Paper.Scale

/-! The direct reduction in Lemma 6.6.  Its existential constants can also
be obtained from the checked range matching construction: choosing a range
whose lower endpoint is of order `log n / log log n` gives the required
single-step reduction, with no iteration or restriction to a subsequence. -/

open Filter Asymptotics
open scoped Topology

namespace AntichainOfGivenSize.Paper

private theorem eventually_logb_le_half :
    ∀ᶠ x : ℝ in atTop, Real.logb 2 x ≤ x / 2 := by
  have h := (Real.isLittleO_logb_id_atTop (b := 2)).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  calc
    Real.logb 2 x ≤ ‖Real.logb 2 x‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ (1 / 2 : ℝ) * ‖x‖ := hx
    _ = x / 2 := by rw [Real.norm_of_nonneg hx0]; ring

/-- A quantitative direct reduction at every input with sufficiently large
double logarithm.  This is the paper's Lemma 6.6 with constants 8 and 4096. -/
theorem directReduction_of_loglog {n : ℕ}
    (hn : 1 < n)
    (hlarge : 4096 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)))
    (hsmall : Real.logb 2 (Real.logb 2 (Real.logb 2 (n : ℝ))) ≤
      Real.logb 2 (Real.logb 2 (n : ℝ)) / 2) :
    ∃ n' : ℕ, 1 ≤ n' ∧ n' < n ∧
      (alpha n : ℝ) ≤ 8 * Real.logb 2 (Real.logb 2 (n : ℝ)) + (alpha n' : ℝ) ∧
      Real.logb 2 (n' : ℝ) ≤
        4096 * Real.logb 2 (n : ℝ) / Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  let L := Real.logb 2 (n : ℝ)
  let τ := Real.logb 2 L
  let q := τ - Real.logb 2 τ + 12
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hL : 0 < L := Real.logb_pos one_lt_two hnR
  have hτ : 4096 ≤ τ := hlarge
  have hτ0 : 0 < τ := by linarith
  have hlogτ : Real.logb 2 τ ≤ τ / 2 := hsmall
  have hlog4096 : Real.logb 2 (4096 : ℝ) = 12 := by
    rw [show (4096 : ℝ) = 2 ^ (12 : ℕ) by norm_num, Real.logb_pow]
    norm_num [Real.logb_self_eq_one]
  have hloglower : 12 ≤ Real.logb 2 τ := by
    rw [← hlog4096]
    exact Real.logb_le_logb_of_le one_lt_two (by norm_num) hτ
  have hqlo : τ / 2 ≤ q := by dsimp [q]; linarith
  have hqhi : q ≤ τ := by dsimp [q]; linarith
  have hq : 16 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hpow : (2 : ℝ) ^ q = 4096 * L / τ := by
    dsimp [q]
    rw [Real.rpow_add zero_lt_two, Real.rpow_sub zero_lt_two,
      Real.rpow_logb zero_lt_two (by norm_num) hτ0]
    rw [show (2 : ℝ) ^ τ = L from
      Real.rpow_logb zero_lt_two (by norm_num) hL]
    norm_num
    ring
  have hrange : inWideRange 10 q n := by
    constructor
    · change (2 : ℝ) ^ q ≤ L
      rw [hpow]
      apply (div_le_iff₀ hτ0).2
      nlinarith
    · rw [wideRange_upper_endpoint 10 q hq0, hpow]
      change L < (4096 * L / τ) * q / (2 : ℝ) ^ (10 : ℝ)
      norm_num
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 1024)).2
      rw [div_mul_eq_mul_div]
      apply (lt_div_iff₀ hτ0).2
      have hmul := mul_le_mul_of_nonneg_left hqlo hL.le
      nlinarith [mul_pos hL hτ0]
  obtain ⟨m, hm, hmn, hmod, halpham⟩ :=
    Section6.Construction.constructionMatching q hq n hrange
  obtain ⟨n', hn'pos, hdecomp⟩ :=
    exists_positive_quotient_of_modEq_succ hm hmn hmod
  obtain ⟨hB, hbits⟩ := constructionBits_remainderBitBound q hq n hrange
  have hn'bound := quotient_lt_doubleExp_of_remainderBits hm hmn hdecomp hB hbits
  have hn'0 : (0 : ℝ) < n' := by exact_mod_cast hn'pos
  have hlogn' : Real.logb 2 (n' : ℝ) < (2 : ℝ) ^ q := by
    have h := Real.logb_lt_logb one_lt_two hn'0 hn'bound
    simpa only [Real.logb_rpow zero_lt_two (by norm_num)] using h
  have hn'lt : n' < n := by
    have hupper : (2 : ℝ) ^ ((2 : ℝ) ^ q) ≤ n := by
      calc
        (2 : ℝ) ^ ((2 : ℝ) ^ q) ≤ (2 : ℝ) ^ L :=
          Real.rpow_le_rpow_of_exponent_le one_le_two hrange.1
        _ = n := Real.rpow_logb zero_lt_two (by norm_num) hn0
    exact_mod_cast hn'bound.trans_le hupper
  have halpha := alpha_le_of_block_decomposition hm hmn hdecomp
  have halphaR : (alpha n : ℝ) ≤ (alpha m : ℝ) + (alpha n' : ℝ) := by
    exact_mod_cast halpha
  refine ⟨n', hn'pos, hn'lt, ?_, ?_⟩
  · change (alpha n : ℝ) ≤ 8 * τ + (alpha n' : ℝ)
    linarith
  · change Real.logb 2 (n' : ℝ) ≤ 4096 * L / τ
    rw [← hpow]
    exact hlogn'.le

/-- Lemma 6.6, including positivity and strict decrease of the reduced
integer, with absolute constants and one threshold valid for all inputs. -/
theorem directReduction :
    ∃ a C₁ : ℝ, 0 < a ∧ 0 < C₁ ∧ ∃ nred : ℕ, ∀ n : ℕ, nred ≤ n →
      ∃ n' : ℕ, 1 ≤ n' ∧ n' < n ∧
        (alpha n : ℝ) ≤ a * Real.logb 2 (Real.logb 2 (n : ℝ)) + (alpha n' : ℝ) ∧
        Real.logb 2 (n' : ℝ) ≤
          C₁ * Real.logb 2 (n : ℝ) / Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  have ht : Tendsto (fun n : ℕ ↦ Real.logb 2 (Real.logb 2 (n : ℝ)))
      atTop atTop := tendsto_loglog.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in atTop, ∃ n' : ℕ, 1 ≤ n' ∧ n' < n ∧
      (alpha n : ℝ) ≤ 8 * Real.logb 2 (Real.logb 2 (n : ℝ)) + (alpha n' : ℝ) ∧
      Real.logb 2 (n' : ℝ) ≤
        4096 * Real.logb 2 (n : ℝ) / Real.logb 2 (Real.logb 2 (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ),
      ht.eventually (eventually_ge_atTop 4096), ht.eventually eventually_logb_le_half]
      with n hn hlarge hsmall
    exact directReduction_of_loglog hn hlarge hsmall
  obtain ⟨nred, hnred⟩ := eventually_atTop.1 he
  exact ⟨8, 4096, by norm_num, by norm_num, nred, hnred⟩

end AntichainOfGivenSize.Paper
