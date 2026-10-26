import AntichainOfGivenSize.Paper.CountingParameters

/-!
# Uniform parameters for the block construction

The construction uses ordinary binary addresses. Integral rounding of the
block length is explicit; neither `B` nor its logarithm is restricted to a
subsequence. The final constants are the manuscript's `a = 5`, `b = 3`.
-/

namespace AntichainOfGivenSize.Paper

def blockPositionBits (B : ℕ) : ℕ := Nat.log 2 (B / (countLog B + 1))
def blockCount (B : ℕ) : ℕ := 2 ^ blockPositionBits B
def blockLength (B : ℕ) : ℕ := B / blockCount B + 1
def blockGeneratorBudget (B : ℕ) : ℕ := 2 * blockPositionBits B + blockLength B + 1
def blockSizeExponent (B : ℕ) : ℕ :=
  blockLength B * (blockCount B + blockPositionBits B) + blockCount B

def BlockMatchingConstructionStatement : Prop :=
  ∀ r ell : ℕ, 0 < r → 0 < ell → ∀ y : ℤ, ∃ m : ℕ,
    0 < m ∧ Int.ModEq ((2 : ℤ) ^ (2 ^ r * ell)) (m : ℤ) y ∧
    alpha m ≤ 2 * r + ell + 1 ∧
    m ≤ (2 * r + ell + 1) * 2 ^ (ell * (2 ^ r + r) + 2 ^ r)

def BlockMatchingStatement : Prop :=
  ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B → ∀ y : ℤ, ∃ m : ℕ,
    0 < m ∧ Int.ModEq ((2 : ℤ) ^ B) (m : ℤ) y ∧
    (alpha m : ℝ) ≤ 5 * Real.logb 2 (B : ℝ) ∧
    Real.logb 2 (m : ℝ) ≤ (B : ℝ) + 3 * (B : ℝ) / Real.logb 2 (B : ℝ)

theorem double_linear_le_power {b : ℕ} (hb : 4 ≤ b) :
    2 * (b + 1) ≤ 2 ^ b := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hb
  induction v with
  | zero => norm_num
  | succ v ih =>
      rw [show 4 + (v + 1) = (4 + v) + 1 by omega, pow_succ]
      omega

theorem block_parameter_bounds {B : ℕ} (hB : 0 < B) (hb : 4 ≤ countLog B) :
    0 < blockPositionBits B ∧ 0 < blockLength B ∧
    B ≤ blockCount B * blockLength B ∧
    blockPositionBits B ≤ countLog B ∧
    blockLength B ≤ 2 * (countLog B + 1) ∧
    blockGeneratorBudget B ≤ 5 * countLog B ∧
    blockCount B * (countLog B + 1) ≤ B ∧
    blockCount B * blockLength B ≤ B + blockCount B := by
  let b := countLog B
  let q := B / (b + 1)
  have hbpow := countLog_bounds hB
  have hq2 : 2 ≤ q := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < b + 1)).2
    exact (double_linear_le_power hb).trans hbpow.1
  have hqpos : q ≠ 0 := by omega
  have hHq : blockCount B ≤ q := Nat.pow_log_le_self 2 hqpos
  have hqH : q < 2 * blockCount B := by
    simpa [blockCount, blockPositionBits, q, b, pow_succ, mul_comm] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) q
  have hHpos : 0 < blockCount B := by unfold blockCount; positivity
  have hrpos : 0 < blockPositionBits B := by
    change 0 < Nat.log 2 q
    have : 1 ≤ Nat.log 2 q :=
      (Nat.le_log_iff_pow_le (by norm_num : 1 < (2 : ℕ)) hqpos).2 (by simpa using hq2)
    omega
  have hr : blockPositionBits B ≤ b := Nat.log_mono_right (Nat.div_le_self _ _)
  have hH : blockCount B * (b + 1) ≤ B := by
    apply (Nat.mul_le_mul_right (b + 1) hHq).trans
    exact Nat.div_mul_le_self _ _
  have hBupper : B < 2 * blockCount B * (b + 1) := by
    have hdivision := Nat.lt_mul_div_succ B (by omega : 0 < b + 1)
    have hqle : q + 1 ≤ 2 * blockCount B := by omega
    have hmul := Nat.mul_le_mul_right (b + 1) hqle
    dsimp [q] at hmul
    nlinarith
  have hell : blockLength B ≤ 2 * (b + 1) := by
    have hdiv : B / blockCount B < 2 * (b + 1) := by
      apply (Nat.div_lt_iff_lt_mul hHpos).2
      nlinarith
    dsimp [blockLength]
    omega
  have hcover : B ≤ blockCount B * blockLength B := by
    have := Nat.mod_lt B hHpos
    have := Nat.mod_add_div B (blockCount B)
    dsimp [blockLength]
    nlinarith
  have hround : blockCount B * blockLength B ≤ B + blockCount B := by
    have := Nat.div_mul_le_self B (blockCount B)
    dsimp [blockLength]
    nlinarith
  refine ⟨hrpos, Nat.succ_pos _, hcover, hr, hell, ?_, hH, hround⟩
  unfold blockGeneratorBudget
  omega

theorem block_small_cost {B : ℕ} (hB : 0 < B) (hb : 2 ^ 20 ≤ countLog B) :
    (blockLength B * blockPositionBits B + blockGeneratorBudget B) *
      (countLog B + 1) ≤ B := by
  let b := countLog B
  let t := countLogLog B
  have hsmall : 4 ≤ countLog B := (show (4 : ℕ) ≤ 2 ^ 20 by norm_num).trans hb
  obtain ⟨_, _, _, hr, hell, hG, _, _⟩ := block_parameter_bounds hB hsmall
  have ht := countLogLog_bounds hb
  have hp : b ≤ 2 ^ t := ht.2.2.1.le
  have hpoly : (blockLength B * blockPositionBits B + blockGeneratorBudget B) *
      (b + 1) ≤ 32 * b ^ 3 := by
    have hmul := Nat.mul_le_mul hell hr
    have hbpos : 1 ≤ b := by dsimp [b]; omega
    have hbsq : b ≤ b ^ 2 := by nlinarith
    have hplus : b + 1 ≤ 2 * b := by omega
    have hcost : blockLength B * blockPositionBits B + blockGeneratorBudget B ≤ 9 * b ^ 2 := by
      dsimp [b] at *
      nlinarith
    exact (Nat.mul_le_mul hcost hplus).trans (by nlinarith [Nat.zero_le (b ^ 3)])
  calc
    (blockLength B * blockPositionBits B + blockGeneratorBudget B) * (countLog B + 1)
        ≤ 32 * b ^ 3 := hpoly
    _ ≤ 32 * (2 ^ t) ^ 3 := by gcongr
    _ = 2 ^ (3 * t + 5) := by
      rw [show 3 * t + 5 = t * 3 + 5 by omega, pow_add, pow_mul]
      norm_num
      ring
    _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ B := (countLog_bounds hB).1

/-- Claim 6.5 after substituting integral parameter choices. -/
theorem block_uniform_size {B m : ℕ} (hB : 0 < B) (hb : 2 ^ 20 ≤ countLog B)
    (hm : 0 < m) (ha : alpha m ≤ blockGeneratorBudget B)
    (hsize : m ≤ blockGeneratorBudget B * 2 ^ blockSizeExponent B) :
    (alpha m : ℝ) ≤ 5 * Real.logb 2 (B : ℝ) ∧
    Real.logb 2 (m : ℝ) ≤ (B : ℝ) + 3 * (B : ℝ) / Real.logb 2 (B : ℝ) := by
  let L := Real.logb 2 (B : ℝ)
  have hsmall : 4 ≤ countLog B := (show (4 : ℕ) ≤ 2 ^ 20 by norm_num).trans hb
  obtain ⟨_, _, _, hr, hell, hG, hH, hround⟩ := block_parameter_bounds hB hsmall
  have hL := countLog_real_bounds hB
  have hLpos : 0 < L := by
    have : (4 : ℝ) ≤ (countLog B : ℝ) := by exact_mod_cast hsmall
    dsimp [L]
    linarith
  constructor
  · calc
      (alpha m : ℝ) ≤ (blockGeneratorBudget B : ℝ) := by exact_mod_cast ha
      _ ≤ 5 * (countLog B : ℝ) := by exact_mod_cast hG
      _ ≤ 5 * Real.logb 2 (B : ℝ) := by gcongr; exact hL.1
  · have hmpow : m ≤ 2 ^ (blockSizeExponent B + blockGeneratorBudget B) := by
      calc
        m ≤ blockGeneratorBudget B * 2 ^ blockSizeExponent B := hsize
        _ ≤ 2 ^ blockGeneratorBudget B * 2 ^ blockSizeExponent B := by
          gcongr
          exact (blockGeneratorBudget B).lt_two_pow_self.le
        _ = 2 ^ (blockSizeExponent B + blockGeneratorBudget B) := by rw [← pow_add, Nat.add_comm]
    have hlog : Real.logb 2 (m : ℝ) ≤
        (blockSizeExponent B + blockGeneratorBudget B : ℕ) := by
      have hcast : (m : ℝ) ≤ (2 : ℝ) ^ (blockSizeExponent B + blockGeneratorBudget B) := by
        exact_mod_cast hmpow
      have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by exact_mod_cast hm) hcast
      simpa [Real.logb_pow] using this
    have hsmallcost := block_small_cost hB hb
    have hHreal : (blockCount B : ℝ) * L ≤ (B : ℝ) := by
      have hc : (blockCount B : ℝ) * ((countLog B : ℝ) + 1) ≤ (B : ℝ) := by exact_mod_cast hH
      have hnonneg : (0 : ℝ) ≤ blockCount B := by positivity
      dsimp [L]
      nlinarith [hL.2.le]
    have hcostreal : ((blockLength B * blockPositionBits B + blockGeneratorBudget B : ℕ) : ℝ) * L ≤ (B : ℝ) := by
      have hc : ((blockLength B * blockPositionBits B + blockGeneratorBudget B : ℕ) : ℝ) *
          ((countLog B : ℝ) + 1) ≤ (B : ℝ) := by exact_mod_cast hsmallcost
      exact (mul_le_mul_of_nonneg_left hL.2.le (by positivity)).trans hc
    have hroundreal : (blockCount B : ℝ) * (blockLength B : ℝ) ≤ (B : ℝ) + (blockCount B : ℝ) := by
      exact_mod_cast hround
    have hbound : (blockSizeExponent B + blockGeneratorBudget B : ℕ) ≤
        (B : ℝ) + 3 * (B : ℝ) / L := by
      have hdivH : (blockCount B : ℝ) ≤ (B : ℝ) / L := (le_div_iff₀ hLpos).2 hHreal
      have hdivcost := (le_div_iff₀ hLpos).2 hcostreal
      push_cast at hdivcost ⊢
      dsimp [blockSizeExponent]
      push_cast
      rw [mul_div_assoc]
      nlinarith
    exact hlog.trans hbound

theorem blockMatching_of_construction (hconstruction : BlockMatchingConstructionStatement) :
    BlockMatchingStatement := by
  refine ⟨2 ^ (2 ^ 20), ?_⟩
  intro B hB y
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity : 0 < (2 : ℕ) ^ (2 ^ 20)) hB
  have hb : 2 ^ 20 ≤ countLog B :=
    (Nat.le_log_iff_pow_le (by norm_num) (by omega : B ≠ 0)).2 hB
  have hsmall : 4 ≤ countLog B := (show (4 : ℕ) ≤ 2 ^ 20 by norm_num).trans hb
  obtain ⟨hr, hell, hcover, _⟩ := block_parameter_bounds hBpos hsmall
  obtain ⟨m, hm, hmod, ha, hsize⟩ := hconstruction (blockPositionBits B) (blockLength B) hr hell y
  refine ⟨m, hm, hmod.of_dvd (pow_dvd_pow 2 hcover), ?_⟩
  exact block_uniform_size hBpos hb hm ha hsize

end AntichainOfGivenSize.Paper
