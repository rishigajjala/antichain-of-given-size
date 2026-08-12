import AntichainOfGivenSize.Definitions
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# The range-ladder implication in Theorem 6.10

This file proves the analytic iteration in Theorem 6.10 from precise
hypotheses corresponding to Lemmas 6.8 and 6.9.  It deliberately separates
that implication from the paper's block-matching construction.
-/

open Asymptotics Filter
open scoped BigOperators

namespace AntichainOfGivenSize

/-- The least ladder cutoff strictly above `n`. -/
noncomputable def firstCutoffIndex (cutoff : ℕ → ℕ)
    (hcofinal : ∀ n, ∃ i, n < cutoff i) (n : ℕ) : ℕ :=
  Nat.find (hcofinal n)

theorem lt_cutoff_firstCutoffIndex (cutoff : ℕ → ℕ)
    (hcofinal : ∀ n, ∃ i, n < cutoff i) (n : ℕ) :
    n < cutoff (firstCutoffIndex cutoff hcofinal n) :=
  Nat.find_spec (hcofinal n)

theorem tendsto_firstCutoffIndex_atTop (cutoff : ℕ → ℕ)
    (hmono : Monotone cutoff) (hcofinal : ∀ n, ∃ i, n < cutoff i) :
    Tendsto (firstCutoffIndex cutoff hcofinal) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b ↦ ⟨cutoff b, ?_⟩
  intro n hn
  by_contra hnot
  have hi_lt : firstCutoffIndex cutoff hcofinal n < b := Nat.lt_of_not_ge hnot
  have hcut_le : cutoff (firstCutoffIndex cutoff hcofinal n) ≤ cutoff b :=
    hmono hi_lt.le
  exact (not_lt_of_ge hn)
    ((lt_cutoff_firstCutoffIndex cutoff hcofinal n).trans_le hcut_le)

/-- A precise version of the one-range conclusion of Lemma 6.8. -/
def OneRangeReduction (q : ℕ → ℝ) (cutoff : ℕ → ℕ) (CR : ℝ) : Prop :=
  ∀ i n, cutoff i ≤ n → n < cutoff (i + 1) →
    ∃ n', n' < cutoff i ∧
      (alpha n : ℝ) ≤ CR * q i + (alpha n' : ℝ)

/-- Iteration of Lemma 6.8 up to an arbitrary ladder cutoff. -/
theorem alpha_le_base_add_ladderSum
    (q : ℕ → ℝ) (cutoff : ℕ → ℕ) (base CR : ℝ)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hCR : 0 ≤ CR)
    (hbase : ∀ n, n < cutoff 0 → (alpha n : ℝ) ≤ base)
    (hreduce : OneRangeReduction q cutoff CR) :
    ∀ i n, n < cutoff i →
      (alpha n : ℝ) ≤ base + ∑ j ∈ Finset.range i, CR * q j := by
  intro i
  induction i with
  | zero =>
      intro n hn
      simpa using hbase n hn
  | succ i ih =>
      intro n hn
      by_cases hlo : n < cutoff i
      · calc
          (alpha n : ℝ) ≤ base + ∑ j ∈ Finset.range i, CR * q j := ih n hlo
          _ ≤ base + ∑ j ∈ Finset.range (i + 1), CR * q j := by
            rw [Finset.sum_range_succ]
            gcongr
            exact le_add_of_nonneg_right (mul_nonneg hCR (hq_nonneg i))
      · obtain ⟨n', hn', hred⟩ :=
          hreduce i n (Nat.le_of_not_gt hlo) (by simpa using hn)
        calc
          (alpha n : ℝ) ≤ CR * q i + (alpha n' : ℝ) := hred
          _ ≤ CR * q i + (base + ∑ j ∈ Finset.range i, CR * q j) := by
            gcongr
            exact ih n' hn'
          _ = base + ∑ j ∈ Finset.range (i + 1), CR * q j := by
            rw [Finset.sum_range_succ]
            ring

/-- The final logarithmic comparison in Theorem 6.10. -/
theorem ladderScale_le_improvedScale
    {q Q A : ℝ} (hQ : 1 < Q) (hA : 0 ≤ A)
    (hlower : Q ≤ q) (hupper : q ≤ A * Q) :
    q ^ 2 / Real.logb 2 q ≤ A ^ 2 * (Q ^ 2 / Real.logb 2 Q) := by
  have hq0 : 0 ≤ q := (zero_lt_one.trans hQ).le.trans hlower
  have hQ0 : 0 ≤ Q := (zero_lt_one.trans hQ).le
  have hlogQ : 0 < Real.logb 2 Q := Real.logb_pos one_lt_two hQ
  have hlogq : 0 < Real.logb 2 q :=
    Real.logb_pos one_lt_two (hQ.trans_le hlower)
  have hsq : q ^ 2 ≤ (A * Q) ^ 2 :=
    (sq_le_sq₀ hq0 (mul_nonneg hA hQ0)).2 hupper
  have hlog : Real.logb 2 Q ≤ Real.logb 2 q :=
    Real.logb_le_logb_of_le one_lt_two (zero_lt_one.trans hQ) hlower
  calc
    q ^ 2 / Real.logb 2 q ≤ (A * Q) ^ 2 / Real.logb 2 q :=
      div_le_div_of_nonneg_right hsq hlogq.le
    _ ≤ (A * Q) ^ 2 / Real.logb 2 Q :=
      div_le_div_of_nonneg_left (sq_nonneg (A * Q)) hlogQ hlog
    _ = A ^ 2 * (Q ^ 2 / Real.logb 2 Q) := by ring

/-- Theorem 6.10, conditional only on precise range-ladder forms of
Lemmas 6.8 and 6.9 and the elementary ladder-placement properties.

`hladderCost` is Lemma 6.9 with the fixed base cost absorbed.  The paper first
chooses `i` with
`q_i ≤ log₂(log₂ n) < q_(i+1)`.  Here `firstCutoffIndex` is that next
index, so `hsandwich` records
`log₂(log₂ n) ≤ q_(i+1) ≤ A * log₂(log₂ n)`.
-/
theorem rangeBasedImprovedReductionBound_of_rangeLadder
    (q : ℕ → ℝ) (cutoff : ℕ → ℕ) (base CR K A : ℝ)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hCR : 0 ≤ CR)
    (hbase : ∀ n, n < cutoff 0 → (alpha n : ℝ) ≤ base)
    (hreduce : OneRangeReduction q cutoff CR)
    (hcutoff_mono : Monotone cutoff)
    (hcutoff_cofinal : ∀ n, ∃ i, n < cutoff i)
    (hladderCost : ∀ᶠ i in atTop,
      base + ∑ j ∈ Finset.range i, CR * q j ≤
        K * (q i ^ 2 / Real.logb 2 (q i)))
    (hsandwich : ∀ᶠ n : ℕ in atTop,
      let Q := Real.logb 2 (Real.logb 2 (n : ℝ))
      1 < Q ∧
        Q ≤ q (firstCutoffIndex cutoff hcutoff_cofinal n) ∧
        q (firstCutoffIndex cutoff hcutoff_cofinal n) ≤ A * Q)
    (hK : 0 ≤ K) (hA : 0 ≤ A) :
    RangeBasedImprovedReductionBound := by
  unfold RangeBasedImprovedReductionBound
  refine IsBigO.of_bound (K * A ^ 2) ?_
  have hindex : Tendsto (firstCutoffIndex cutoff hcutoff_cofinal) atTop atTop :=
    tendsto_firstCutoffIndex_atTop cutoff hcutoff_mono hcutoff_cofinal
  filter_upwards [
      (Filter.Eventually.of_forall
        (lt_cutoff_firstCutoffIndex cutoff hcutoff_cofinal)),
      hindex.eventually hladderCost, hsandwich] with n hn hcost hs
  let i := firstCutoffIndex cutoff hcutoff_cofinal n
  let Q := Real.logb 2 (Real.logb 2 (n : ℝ))
  have halpha : (alpha n : ℝ) ≤ K * (q i ^ 2 / Real.logb 2 (q i)) :=
    (alpha_le_base_add_ladderSum q cutoff base CR hq_nonneg hCR hbase hreduce
      i n (by simpa [i] using hn)).trans (by simpa [i] using hcost)
  have hscale : q i ^ 2 / Real.logb 2 (q i) ≤ A ^ 2 * improvedScale n := by
    have hs' : 1 < Q ∧ Q ≤ q i ∧ q i ≤ A * Q := by simpa [i, Q] using hs
    simpa [quadraticLogLogScale, improvedScale, Q] using
      ladderScale_le_improvedScale hs'.1 hA hs'.2.1 hs'.2.2
  have hpoint : (alpha n : ℝ) ≤ (K * A ^ 2) * improvedScale n := by
    calc
      (alpha n : ℝ) ≤ K * (q i ^ 2 / Real.logb 2 (q i)) := halpha
      _ ≤ K * (A ^ 2 * improvedScale n) :=
        mul_le_mul_of_nonneg_left hscale hK
      _ = (K * A ^ 2) * improvedScale n := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg' (alpha n))]
  calc
    (alpha n : ℝ) ≤ (K * A ^ 2) * improvedScale n := hpoint
    _ ≤ (K * A ^ 2) * |improvedScale n| :=
      mul_le_mul_of_nonneg_left (le_abs_self _)
        (mul_nonneg hK (sq_nonneg A))
    _ = (K * A ^ 2) * ‖improvedScale n‖ := by rw [Real.norm_eq_abs]

end AntichainOfGivenSize
