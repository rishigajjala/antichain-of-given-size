import AntichainOfGivenSize.Analysis.Paper.GeneralCounting
import AntichainOfGivenSize.Analysis.Paper.CountingEstimates
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Parameters for the uniform counting bound

The integer logarithm is used only to choose convenient integral powers of
two. The ambient bound `B` remains arbitrary. The auxiliary generator budget
is slightly larger than the paper's budget; monotonicity then recovers the
unchanged constant 100 in the statement.
-/

namespace AntichainOfGivenSize.Paper

def countLog (B : ℕ) : ℕ := Nat.log 2 B
def countLogLog (B : ℕ) : ℕ := Nat.log 2 (countLog B) + 1
def countBudget (B : ℕ) : ℕ := countLog B ^ 2 / (80 * countLogLog B)
def countSaving (B : ℕ) : ℕ := 2 ^ (countLog B / 2 + 1)

theorem countLog_bounds {B : ℕ} (hB : 0 < B) :
    2 ^ countLog B ≤ B ∧ B < 2 ^ (countLog B + 1) := by
  exact ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) B⟩

theorem countLog_real_bounds {B : ℕ} (hB : 0 < B) :
    (countLog B : ℝ) ≤ Real.logb 2 (B : ℝ) ∧
    Real.logb 2 (B : ℝ) < (countLog B : ℝ) + 1 := by
  refine ⟨Real.natLog_le_logb B 2, ?_⟩
  have h := (countLog_bounds hB).2
  have hcast : (B : ℝ) < (2 : ℝ) ^ (countLog B + 1) := by exact_mod_cast h
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hB) hcast
  simpa [Real.logb_pow] using hlog

theorem countSaving_bounds {B : ℕ} (hB : 0 < B) (hb : 4 ≤ countLog B) :
    countSaving B ≤ B ∧ Real.sqrt (B : ℝ) ≤ (countSaving B : ℝ) := by
  have hlog := countLog_bounds hB
  constructor
  · exact (Nat.pow_le_pow_right (by norm_num) (by omega : countLog B / 2 + 1 ≤ countLog B)).trans hlog.1
  · apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    have hexp : countLog B + 1 ≤ (countLog B / 2 + 1) * 2 := by omega
    have hsq : B ≤ countSaving B ^ 2 := by
      apply hlog.2.le.trans
      unfold countSaving
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) hexp
    exact_mod_cast hsq

theorem linear_le_two_pow {v : ℕ} (hv : 20 ≤ v) :
    4096 * (v + 1) ≤ 2 ^ v := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hv
  induction u with
  | zero => norm_num
  | succ u ih =>
      rw [show 20 + (u + 1) = (20 + u) + 1 by omega, pow_succ]
      omega

theorem countLogLog_bounds {B : ℕ} (hb : 2 ^ 20 ≤ countLog B) :
    20 ≤ countLogLog B ∧
    2 ^ (countLogLog B - 1) ≤ countLog B ∧
    countLog B < 2 ^ countLogLog B ∧
    4096 * countLogLog B ≤ countLog B := by
  have hbpos : countLog B ≠ 0 := by
    have : 0 < (2 : ℕ) ^ 20 := by positivity
    omega
  have hv : 20 ≤ Nat.log 2 (countLog B) :=
    (Nat.le_log_iff_pow_le (by norm_num) hbpos).2 hb
  have hlower := Nat.pow_log_le_self 2 hbpos
  have hupper := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (countLog B)
  dsimp [countLogLog]
  exact ⟨by omega, by simpa using hlower, hupper, (linear_le_two_pow hv).trans hlower⟩

/-- The paper's real logarithmic budget is below the auxiliary integral
budget, without changing its constant or restricting the values of `B`. -/
theorem admissibleBudget_le_countBudget {B K : ℕ} (hB : 0 < B)
    (hb : 64 ≤ countLog B) (ht : 16 ≤ countLogLog B)
    (hK : AdmissibleBudget B K) : K ≤ countBudget B := by
  let b : ℝ := countLog B
  let t : ℝ := countLogLog B
  let L := Real.logb 2 (B : ℝ)
  let T := Real.logb 2 L
  have hb64 : 64 ≤ b := by dsimp [b]; exact_mod_cast hb
  have ht16 : 16 ≤ t := by dsimp [t]; exact_mod_cast ht
  have hlogs := countLog_real_bounds hB
  have hbL : b ≤ L := hlogs.1
  have hLb : L ≤ b + 1 := hlogs.2.le
  have htT : t - 1 ≤ T := by
    have h1 := Real.natLog_le_logb (countLog B) 2
    have h2 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (show (0 : ℝ) < b by linarith) hbL
    have heq : t - 1 = (Nat.log 2 (countLog B) : ℝ) := by
      simp [t, countLogLog]
    rw [heq]
    exact h1.trans h2
  have hTpos : 0 < T := by linarith
  have hLpos : 0 ≤ L := by linarith
  have hbpos : 0 < b := by linarith
  have hLsq : L ^ 2 ≤ (65 / 64 : ℝ) ^ 2 * b ^ 2 := by
    have hL : L ≤ (65 / 64 : ℝ) * b := by linarith
    nlinarith [sq_nonneg (L - (65 / 64 : ℝ) * b)]
  have htbound : t ≤ (16 / 15 : ℝ) * T := by linarith
  have hcoeff : 80 * t * L ^ 2 ≤ 100 * b ^ 2 * T := by
    calc
      80 * t * L ^ 2 ≤ 80 * ((16 / 15 : ℝ) * T) *
          ((65 / 64 : ℝ) ^ 2 * b ^ 2) := by gcongr
      _ ≤ 100 * b ^ 2 * T := by nlinarith [sq_nonneg b]
  have hbudget : (K : ℝ) * (100 * T) ≤ L ^ 2 :=
    (le_div_iff₀ (by positivity : 0 < 100 * T)).1 hK.2
  have hmul := mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ 80 * t)
  have hresult : (K : ℝ) * (80 * t) ≤ b ^ 2 := by
    nlinarith
  apply (Nat.le_div_iff_mul_le (by dsimp [countLogLog]; positivity : 0 < 80 * countLogLog B)).2
  dsimp [b, t] at hresult
  exact_mod_cast hresult

/-- Theorem 7.1 for every sufficiently large natural `B`, with the paper's
constant 100 and its real square-root saving. -/
theorem countingBound : CountingBoundStatement := by
  refine ⟨2 ^ (2 ^ 20), ?_⟩
  intro B K hB hK
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity : 0 < (2 : ℕ) ^ (2 ^ 20)) hB
  have hb : 2 ^ 20 ≤ countLog B :=
    (Nat.le_log_iff_pow_le (by norm_num) (by omega : B ≠ 0)).2 hB
  have ht := countLogLog_bounds hb
  have hlogs := countLog_bounds hBpos
  have haux := CountingEstimates.counting_card_le
    (by omega : 16 ≤ countLogLog B) ht.2.2.2 ht.2.2.1 hlogs.1 hlogs.2
  have hkle : K ≤ countBudget B := admissibleBudget_le_countBudget hBpos
    ((show (64 : ℕ) ≤ 2 ^ 20 by norm_num).trans hb)
    (by omega) hK
  have hcard : (attainableValues B K).card ≤ 2 ^ (B - countSaving B) := by
    exact (attainableValues_card_mono hkle (by have := hK.1; omega)).trans haux
  have hs := countSaving_bounds hBpos
    ((show (4 : ℕ) ≤ 2 ^ 20 by norm_num).trans hb)
  exact attainableValues_real_card_le_of_nat_bound hs.1 hs.2 hcard

end AntichainOfGivenSize.Paper
