import AntichainOfGivenSize.AsymptoticBridge
import AntichainOfGivenSize.BasicLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic.NormNum

/-!
# The explicit range ladder for the improved bound

This file discharges the analytic hypotheses in
`rangeBasedImprovedReductionBound_of_rangeLadder`.  The ladder is the
closed-form real sequence

`q i = (T + i) * log₂ (T + i)`,

and its integer cutoff is exactly `⌈2 ^ (2 ^ q i)⌉₊`.  Consequently no
rounding convention for the real parameter `q` is left implicit.
-/

open Asymptotics Filter
open scoped BigOperators

namespace AntichainOfGivenSize

/-- The affine parameter underlying the concrete ladder. -/
noncomputable def ladderT (T : ℝ) (i : ℕ) : ℝ := T + i

/-- A closed-form real ladder with logarithmic consecutive spacing. -/
noncomputable def explicitQ (T : ℝ) (i : ℕ) : ℝ :=
  ladderT T i * Real.logb 2 (ladderT T i)

/-- The integer cutoff representing the lower endpoint `2 ^ (2 ^ q_i)`.
Taking the natural ceiling makes membership of integer inputs exact. -/
noncomputable def explicitCutoff (T : ℝ) (i : ℕ) : ℕ :=
  ⌈(2 : ℝ) ^ ((2 : ℝ) ^ explicitQ T i)⌉₊

/-- The one remaining Section 6 input, written with the concrete ladder.
After unfolding, its exact signature is

`∀ i n, ⌈2^(2^q_i)⌉₊ ≤ n → n < ⌈2^(2^q_(i+1))⌉₊ →`
`  ∃ n', n' < ⌈2^(2^q_i)⌉₊ ∧ α(n) ≤ C_R q_i + α(n')`.
-/
def ExplicitOneRangeReduction (T CR : ℝ) : Prop :=
  OneRangeReduction (explicitQ T) (explicitCutoff T) CR

theorem explicitOneRangeReduction_iff (T CR : ℝ) :
    ExplicitOneRangeReduction T CR ↔
      ∀ i n, explicitCutoff T i ≤ n → n < explicitCutoff T (i + 1) →
        ∃ n', n' < explicitCutoff T i ∧
          (alpha n : ℝ) ≤ CR * explicitQ T i + (alpha n' : ℝ) :=
  Iff.rfl

noncomputable def explicitLadderScale (T : ℝ) (i : ℕ) : ℝ :=
  explicitQ T i ^ 2 / Real.logb 2 (explicitQ T i)

noncomputable def doubleLog2Nat (n : ℕ) : ℝ :=
  Real.logb 2 (Real.logb 2 (n : ℝ))

theorem ladderT_monotone (T : ℝ) : Monotone (ladderT T) := by
  intro i j hij
  change T + (i : ℝ) ≤ T + (j : ℝ)
  simpa [add_comm] using add_le_add_left (Nat.cast_le.2 hij) T

theorem tendsto_ladderT_atTop (T : ℝ) : Tendsto (ladderT T) atTop atTop := by
  change Tendsto (fun i : ℕ ↦ T + (i : ℝ)) atTop atTop
  simpa only [add_comm] using
    tendsto_atTop_add_const_right atTop T (tendsto_natCast_atTop_atTop (R := ℝ))

theorem tendsto_explicitQ_atTop (T : ℝ) : Tendsto (explicitQ T) atTop atTop := by
  exact (tendsto_ladderT_atTop T).atTop_mul_atTop₀
    ((Real.tendsto_logb_atTop (show (1 : ℝ) < 2 by exact one_lt_two)).comp
      (tendsto_ladderT_atTop T))

theorem explicitQ_nonneg (T : ℝ) (hT : 1 ≤ T) (i : ℕ) :
    0 ≤ explicitQ T i := by
  have ht : 1 ≤ ladderT T i := hT.trans (by simp [ladderT])
  exact mul_nonneg (zero_le_one.trans ht) (Real.logb_nonneg one_lt_two ht)

theorem explicitQ_monotone (T : ℝ) (hT : 1 ≤ T) : Monotone (explicitQ T) := by
  intro i j hij
  have ht := ladderT_monotone T hij
  have hti : 1 ≤ ladderT T i := hT.trans (by simp [ladderT])
  have htj : 1 ≤ ladderT T j := hti.trans ht
  have hlog := Real.logb_le_logb_of_le one_lt_two (zero_lt_one.trans_le hti) ht
  exact mul_le_mul ht hlog (Real.logb_nonneg one_lt_two hti)
    (zero_le_one.trans htj)

theorem explicitCutoff_monotone (T : ℝ) (hT : 1 ≤ T) :
    Monotone (explicitCutoff T) := by
  intro i j hij
  apply Nat.ceil_mono
  apply Real.rpow_le_rpow_of_exponent_le one_le_two
  apply Real.rpow_le_rpow_of_exponent_le one_le_two
  exact explicitQ_monotone T hT hij

theorem tendsto_explicitCutoff_atTop (T : ℝ) :
    Tendsto (explicitCutoff T) atTop atTop := by
  have hinner : Tendsto (fun i ↦ (2 : ℝ) ^ explicitQ T i) atTop atTop :=
    (tendsto_rpow_atTop_of_base_gt_one 2 one_lt_two).comp
      (tendsto_explicitQ_atTop T)
  have houter : Tendsto (fun i ↦ (2 : ℝ) ^ ((2 : ℝ) ^ explicitQ T i)) atTop atTop :=
    (tendsto_rpow_atTop_of_base_gt_one 2 one_lt_two).comp hinner
  have hceil : Tendsto (Nat.ceil : ℝ → ℕ) atTop atTop :=
    Nat.ceil_mono.tendsto_atTop_atTop (fun n : ℕ ↦ ⟨(n : ℝ), by simp⟩)
  exact hceil.comp houter

theorem explicitCutoff_cofinal (T : ℝ) :
    ∀ n, ∃ i, n < explicitCutoff T i := by
  intro n
  exact ((tendsto_explicitCutoff_atTop T).eventually_gt_atTop n).exists

/-- Exact rounding equivalence for an integer below a cutoff. -/
theorem lt_explicitCutoff_iff (T : ℝ) (i n : ℕ) :
    n < explicitCutoff T i ↔
      (n : ℝ) < (2 : ℝ) ^ ((2 : ℝ) ^ explicitQ T i) := by
  exact Nat.lt_ceil

theorem explicitCutoff_le_iff (T : ℝ) (i n : ℕ) :
    explicitCutoff T i ≤ n ↔
      (2 : ℝ) ^ ((2 : ℝ) ^ explicitQ T i) ≤ (n : ℝ) := by
  exact Nat.ceil_le

/-- Integer membership in one concrete ladder range is equivalent to the
corresponding pair of real double-exponential inequalities. -/
theorem mem_explicitRange_iff (T : ℝ) (i n : ℕ) :
    explicitCutoff T i ≤ n ∧ n < explicitCutoff T (i + 1) ↔
      (2 : ℝ) ^ ((2 : ℝ) ^ explicitQ T i) ≤ (n : ℝ) ∧
        (n : ℝ) < (2 : ℝ) ^ ((2 : ℝ) ^ explicitQ T (i + 1)) := by
  exact and_congr (explicitCutoff_le_iff T i n)
    (lt_explicitCutoff_iff T (i + 1) n)

/-- This is the endpoint conversion used for the smaller output `n'` of the
block construction. -/
theorem lt_explicitCutoff_of_lt_doubleExp (T : ℝ) (i n : ℕ)
    (h : (n : ℝ) < (2 : ℝ) ^ ((2 : ℝ) ^ explicitQ T i)) :
    n < explicitCutoff T i :=
  (lt_explicitCutoff_iff T i n).2 h

/-- A bridge for constructions naturally proved using the real endpoints.
It packages all ceiling conversions and produces the exact one-range premise
used by the final theorem. -/
theorem explicitOneRangeReduction_of_realEndpoints (T CR : ℝ)
    (h : ∀ (i n : ℕ),
      (2 : ℝ) ^ ((2 : ℝ) ^ explicitQ T i) ≤ (n : ℝ) →
      (n : ℝ) < (2 : ℝ) ^ ((2 : ℝ) ^ explicitQ T (i + 1)) →
      ∃ n' : ℕ, (n' : ℝ) < (2 : ℝ) ^ ((2 : ℝ) ^ explicitQ T i) ∧
        (alpha n : ℝ) ≤ CR * explicitQ T i + (alpha n' : ℝ)) :
    ExplicitOneRangeReduction T CR := by
  rw [explicitOneRangeReduction_iff]
  intro i n hlo hhi
  have hrange := (mem_explicitRange_iff T i n).1 ⟨hlo, hhi⟩
  obtain ⟨n', hn', halpha⟩ := h i n hrange.1 hrange.2
  exact ⟨n', lt_explicitCutoff_of_lt_doubleExp T i n' hn', halpha⟩

theorem sum_explicitQ_le (T : ℝ) (hT : 1 ≤ T) (i : ℕ) :
    ∑ j ∈ Finset.range i, explicitQ T j ≤ (i : ℝ) * explicitQ T i := by
  calc
    ∑ j ∈ Finset.range i, explicitQ T j ≤
        ∑ _j ∈ Finset.range i, explicitQ T i := by
      apply Finset.sum_le_sum
      intro j hj
      exact explicitQ_monotone T hT (Finset.mem_range.1 hj).le
    _ = (i : ℝ) * explicitQ T i := by simp

theorem sum_explicitQ_le_ladderT_mul (T : ℝ) (hT : 1 ≤ T) (i : ℕ) :
    ∑ j ∈ Finset.range i, explicitQ T j ≤ ladderT T i * explicitQ T i := by
  calc
    ∑ j ∈ Finset.range i, explicitQ T j ≤ (i : ℝ) * explicitQ T i :=
      sum_explicitQ_le T hT i
    _ ≤ ladderT T i * explicitQ T i := by
      apply mul_le_mul_of_nonneg_right
      · change (i : ℝ) ≤ T + (i : ℝ)
        simpa only [add_comm] using
          (le_add_of_nonneg_right (zero_le_one.trans hT) :
            (i : ℝ) ≤ (i : ℝ) + T)
      · exact explicitQ_nonneg T hT i

/-- Along every real sequence tending to infinity, `log₂ x ≤ x`
eventually. -/
theorem eventually_logb_le_self_comp (q : ℕ → ℝ)
    (hq : Tendsto q atTop atTop) :
    ∀ᶠ i in atTop, Real.logb 2 (q i) ≤ q i := by
  have hnorm : ∀ᶠ i in atTop, ‖Real.logb 2 (q i)‖ ≤ ‖q i‖ :=
    hq.eventually (Real.isLittleO_logb_id_atTop (b := 2)).eventuallyLE
  filter_upwards [hnorm, hq.eventually_gt_atTop 0] with i hi hqi
  calc
    Real.logb 2 (q i) ≤ ‖Real.logb 2 (q i)‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ ‖q i‖ := hi
    _ = q i := Real.norm_of_nonneg hqi.le

theorem eventually_log_explicitQ_le_two_log_ladderT (T : ℝ) :
    ∀ᶠ i in atTop,
      Real.logb 2 (explicitQ T i) ≤ 2 * Real.logb 2 (ladderT T i) := by
  have hL : Tendsto (fun i ↦ Real.logb 2 (ladderT T i)) atTop atTop :=
    (Real.tendsto_logb_atTop one_lt_two).comp (tendsto_ladderT_atTop T)
  have hsmall := eventually_logb_le_self_comp
    (fun i ↦ Real.logb 2 (ladderT T i)) hL
  filter_upwards [hsmall, (tendsto_ladderT_atTop T).eventually_gt_atTop 0,
    hL.eventually_gt_atTop 0] with i hi ht hLi
  rw [explicitQ, Real.logb_mul ht.ne' hLi.ne']
  calc
    Real.logb 2 (ladderT T i) +
          Real.logb 2 (Real.logb 2 (ladderT T i)) ≤
        Real.logb 2 (ladderT T i) + Real.logb 2 (ladderT T i) := by
      gcongr
    _ = 2 * Real.logb 2 (ladderT T i) := by ring

/-- Lemma 6.9 for the concrete ladder. -/
theorem eventually_sum_explicitQ_le_two_scale (T : ℝ) (hT : 1 ≤ T) :
    ∀ᶠ i in atTop,
      ∑ j ∈ Finset.range i, explicitQ T j ≤ 2 * explicitLadderScale T i := by
  filter_upwards [eventually_log_explicitQ_le_two_log_ladderT T,
    (tendsto_explicitQ_atTop T).eventually_gt_atTop 1] with i hlog hqi
  have hlogqi : 0 < Real.logb 2 (explicitQ T i) :=
    Real.logb_pos one_lt_two hqi
  have ht0 : 0 ≤ ladderT T i :=
    zero_le_one.trans (hT.trans (by simp [ladderT]))
  have hq0 : 0 ≤ explicitQ T i := (zero_lt_one.trans hqi).le
  calc
    ∑ j ∈ Finset.range i, explicitQ T j ≤
        ladderT T i * explicitQ T i := sum_explicitQ_le_ladderT_mul T hT i
    _ ≤ (2 * explicitQ T i ^ 2) / Real.logb 2 (explicitQ T i) := by
      rw [le_div_iff₀ hlogqi]
      calc
        ladderT T i * explicitQ T i * Real.logb 2 (explicitQ T i) ≤
            ladderT T i * explicitQ T i *
              (2 * Real.logb 2 (ladderT T i)) :=
          mul_le_mul_of_nonneg_left hlog (mul_nonneg ht0 hq0)
        _ = 2 * explicitQ T i ^ 2 := by
          rw [explicitQ]
          ring
    _ = 2 * explicitLadderScale T i := by
      rw [explicitLadderScale]
      ring

theorem eventually_one_le_explicitLadderScale (T : ℝ) :
    ∀ᶠ i in atTop, 1 ≤ explicitLadderScale T i := by
  have hlogle := eventually_logb_le_self_comp (explicitQ T)
    (tendsto_explicitQ_atTop T)
  filter_upwards [hlogle, (tendsto_explicitQ_atTop T).eventually_gt_atTop 1]
    with i hlog hqi
  have hlogpos : 0 < Real.logb 2 (explicitQ T i) :=
    Real.logb_pos one_lt_two hqi
  have hq0 : 0 ≤ explicitQ T i := (zero_lt_one.trans hqi).le
  have hq_le_scale : explicitQ T i ≤ explicitLadderScale T i := by
    rw [explicitLadderScale, le_div_iff₀ hlogpos]
    calc
      explicitQ T i * Real.logb 2 (explicitQ T i) ≤
          explicitQ T i * explicitQ T i :=
        mul_le_mul_of_nonneg_left hlog hq0
      _ = explicitQ T i ^ 2 := by ring
  exact hqi.le.trans hq_le_scale

/-- Lemma 6.9 after including both the fixed initial cost and the constant
`C_R` in Lemma 6.8. -/
theorem explicit_ladder_cost_bound (T base CR : ℝ)
    (hT : 1 ≤ T) (hbase : 0 ≤ base) (hCR : 0 ≤ CR) :
    ∀ᶠ i in atTop,
      base + ∑ j ∈ Finset.range i, CR * explicitQ T j ≤
        (base + 2 * CR) * explicitLadderScale T i := by
  filter_upwards [eventually_sum_explicitQ_le_two_scale T hT,
    eventually_one_le_explicitLadderScale T] with i hsum hscale
  rw [← Finset.mul_sum]
  calc
    base + CR * ∑ j ∈ Finset.range i, explicitQ T j ≤
        base + CR * (2 * explicitLadderScale T i) := by
      gcongr
    _ ≤ base * explicitLadderScale T i +
        CR * (2 * explicitLadderScale T i) := by
      gcongr
      calc
        base = base * 1 := by ring
        _ ≤ base * explicitLadderScale T i :=
          mul_le_mul_of_nonneg_left hscale hbase
    _ = (base + 2 * CR) * explicitLadderScale T i := by ring

theorem explicitQ_succ_le_four_mul (T : ℝ) (hT : 2 ≤ T) (i : ℕ) :
    explicitQ T (i + 1) ≤ 4 * explicitQ T i := by
  have hti : 2 ≤ ladderT T i := hT.trans (by simp [ladderT])
  have hti0 : 0 < ladderT T i := zero_lt_two.trans_le hti
  have htstep : ladderT T (i + 1) = ladderT T i + 1 := by
    simp [ladderT]
    ring
  have hti1 : 1 ≤ ladderT T i := one_le_two.trans hti
  have htsucc1 : 1 ≤ ladderT T (i + 1) :=
    hti1.trans (ladderT_monotone T (Nat.le_add_right i 1))
  have ht_two : ladderT T (i + 1) ≤ 2 * ladderT T i := by
    rw [htstep]
    calc
      ladderT T i + 1 ≤ ladderT T i + ladderT T i := by
        gcongr
      _ = 2 * ladderT T i := by ring
  have hLi : 1 ≤ Real.logb 2 (ladderT T i) := by
    rw [← Real.logb_self_eq_one one_lt_two]
    exact Real.logb_le_logb_of_le one_lt_two zero_lt_two hti
  have hLstep : Real.logb 2 (ladderT T (i + 1)) ≤
      2 * Real.logb 2 (ladderT T i) := by
    calc
      Real.logb 2 (ladderT T (i + 1)) ≤
          Real.logb 2 (2 * ladderT T i) :=
        Real.logb_le_logb_of_le one_lt_two
          (zero_lt_one.trans_le htsucc1) ht_two
      _ = 1 + Real.logb 2 (ladderT T i) := by
        rw [Real.logb_mul (two_ne_zero : (2 : ℝ) ≠ 0) hti0.ne']
        rw [Real.logb_self_eq_one one_lt_two]
      _ ≤ Real.logb 2 (ladderT T i) + Real.logb 2 (ladderT T i) := by
        gcongr
      _ = 2 * Real.logb 2 (ladderT T i) := by ring
  rw [explicitQ, explicitQ]
  calc
    ladderT T (i + 1) * Real.logb 2 (ladderT T (i + 1)) ≤
        (2 * ladderT T i) * (2 * Real.logb 2 (ladderT T i)) := by
      exact mul_le_mul ht_two hLstep
        (Real.logb_nonneg one_lt_two htsucc1)
        (mul_nonneg zero_le_two (zero_le_two.trans hti))
    _ = 4 * (ladderT T i * Real.logb 2 (ladderT T i)) := by ring

theorem doubleLog2Nat_lt_of_lt_doubleExp {n : ℕ} {q : ℝ}
    (hn : 1 < n)
    (h : (n : ℝ) < (2 : ℝ) ^ ((2 : ℝ) ^ q)) :
    doubleLog2Nat n < q := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlogn : 0 < Real.logb 2 (n : ℝ) := by
    apply Real.logb_pos one_lt_two
    exact_mod_cast hn
  have h₁ := Real.logb_lt_logb one_lt_two hn0 h
  have h₁' : Real.logb 2 (n : ℝ) < (2 : ℝ) ^ q := by
    simpa using h₁
  have h₂ := Real.logb_lt_logb one_lt_two hlogn h₁'
  simpa [doubleLog2Nat] using h₂

theorem le_doubleLog2Nat_of_doubleExp_le {n : ℕ} {q : ℝ}
    (h : (2 : ℝ) ^ ((2 : ℝ) ^ q) ≤ (n : ℝ)) :
    q ≤ doubleLog2Nat n := by
  have hp₁ : 0 < (2 : ℝ) ^ q := Real.rpow_pos_of_pos zero_lt_two _
  have hp₂ : 0 < (2 : ℝ) ^ ((2 : ℝ) ^ q) :=
    Real.rpow_pos_of_pos zero_lt_two _
  have h₁ := Real.logb_le_logb_of_le one_lt_two hp₂ h
  have h₁' : (2 : ℝ) ^ q ≤ Real.logb 2 (n : ℝ) := by
    simpa using h₁
  have h₂ := Real.logb_le_logb_of_le one_lt_two hp₁ h₁'
  simpa [doubleLog2Nat] using h₂

theorem explicitQ_le_doubleLog2Nat_of_cutoff_le (T : ℝ) (i n : ℕ)
    (h : explicitCutoff T i ≤ n) :
    explicitQ T i ≤ doubleLog2Nat n :=
  le_doubleLog2Nat_of_doubleExp_le ((explicitCutoff_le_iff T i n).1 h)

theorem tendsto_doubleLog2Nat_atTop : Tendsto doubleLog2Nat atTop atTop := by
  exact (Real.tendsto_logb_atTop one_lt_two).comp
    ((Real.tendsto_logb_atTop one_lt_two).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))

/-- The least cutoff strictly above `n` brackets `log₂(log₂ n)` between the
preceding and current ladder values.  The factor four is uniform. -/
theorem explicit_index_sandwich (T : ℝ) (hT : 2 ≤ T) :
    ∀ᶠ n : ℕ in atTop,
      1 < doubleLog2Nat n ∧
        doubleLog2Nat n ≤
          explicitQ T (firstCutoffIndex (explicitCutoff T)
            (explicitCutoff_cofinal T) n) ∧
        explicitQ T (firstCutoffIndex (explicitCutoff T)
            (explicitCutoff_cofinal T) n) ≤ 4 * doubleLog2Nat n := by
  have hT1 : 1 ≤ T := one_le_two.trans hT
  have hindex : Tendsto
      (firstCutoffIndex (explicitCutoff T) (explicitCutoff_cofinal T))
      atTop atTop :=
    tendsto_firstCutoffIndex_atTop (explicitCutoff T)
      (explicitCutoff_monotone T hT1) (explicitCutoff_cofinal T)
  filter_upwards [tendsto_doubleLog2Nat_atTop.eventually_gt_atTop 1,
    hindex.eventually_gt_atTop 0, Filter.eventually_gt_atTop 1] with n hQ hnidx hn
  let k := firstCutoffIndex (explicitCutoff T) (explicitCutoff_cofinal T) n
  have hkpos : 0 < k := by simpa [k] using hnidx
  have hncut : n < explicitCutoff T k := by
    simpa [k] using lt_cutoff_firstCutoffIndex
      (explicitCutoff T) (explicitCutoff_cofinal T) n
  have hQlt : doubleLog2Nat n < explicitQ T k :=
    doubleLog2Nat_lt_of_lt_doubleExp hn
      ((lt_explicitCutoff_iff T k n).1 hncut)
  have hpredlt : k - 1 < k := Nat.sub_one_lt hkpos.ne'
  have hnotpred : ¬n < explicitCutoff T (k - 1) := by
    simpa [k, firstCutoffIndex] using
      (Nat.find_min (explicitCutoff_cofinal T n) hpredlt)
  have hpredcut : explicitCutoff T (k - 1) ≤ n := Nat.le_of_not_gt hnotpred
  have hdoublepred :
      (2 : ℝ) ^ ((2 : ℝ) ^ explicitQ T (k - 1)) ≤ (n : ℝ) := by
    calc
      (2 : ℝ) ^ ((2 : ℝ) ^ explicitQ T (k - 1)) ≤
          (explicitCutoff T (k - 1) : ℝ) := Nat.le_ceil _
      _ ≤ (n : ℝ) := by exact_mod_cast hpredcut
  have hpredQ : explicitQ T (k - 1) ≤ doubleLog2Nat n :=
    le_doubleLog2Nat_of_doubleExp_le hdoublepred
  have hk_eq : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
  have hfour : explicitQ T k ≤ 4 * explicitQ T (k - 1) := by
    simpa [hk_eq] using explicitQ_succ_le_four_mul T hT (k - 1)
  refine ⟨hQ, hQlt.le, hfour.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hpredQ (by norm_num)

/-- The analytic part of Theorem 6.10 with every ladder fact discharged.

The sole substantive premise is the one-range conclusion of Lemma 6.8 for
the explicit, rounded ranges. -/
theorem rangeBasedImprovedReductionBound_of_explicitOneRange
    (T CR : ℝ) (hT : 2 ≤ T) (hCR : 0 ≤ CR)
    (hreduce : ExplicitOneRangeReduction T CR) :
    RangeBasedImprovedReductionBound := by
  let base : ℝ := explicitCutoff T 0
  have hT1 : 1 ≤ T := one_le_two.trans hT
  have hbase_nonneg : 0 ≤ base := by simp [base]
  have hbase : ∀ n, n < explicitCutoff T 0 → (alpha n : ℝ) ≤ base := by
    intro n hn
    change (alpha n : ℝ) ≤ (explicitCutoff T 0 : ℝ)
    exact_mod_cast (alpha_le_self n).trans hn.le
  refine rangeBasedImprovedReductionBound_of_rangeLadder
      (q := explicitQ T) (cutoff := explicitCutoff T)
      (base := base) (CR := CR) (K := base + 2 * CR) (A := 4)
      (explicitQ_nonneg T hT1) hCR hbase (by simpa [ExplicitOneRangeReduction] using hreduce)
      (explicitCutoff_monotone T hT1) (explicitCutoff_cofinal T) ?_ ?_ ?_ ?_
  · simpa [explicitLadderScale] using
      explicit_ladder_cost_bound T base CR hT1 hbase_nonneg hCR
  · simpa [doubleLog2Nat] using explicit_index_sandwich T hT
  · positivity
  · norm_num

end AntichainOfGivenSize
