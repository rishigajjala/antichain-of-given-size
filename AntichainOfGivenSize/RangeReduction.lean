import AntichainOfGivenSize.RangeArithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic

namespace AntichainOfGivenSize

/-- The binary logarithm rounded down, used for the block modulus. -/
def binaryLog (n : ℕ) : ℕ := Nat.log 2 n

/-- The paper's block exponent `B = floor(N / (1 + C_B / q))`. -/
noncomputable def blockBits (CB q : ℝ) (n : ℕ) : ℕ :=
  ⌊(binaryLog n : ℝ) / (1 + CB / q)⌋₊

/-- A repaired real-parameter version of the range in Theorem 6.1.
It is stated on logarithmic scale, avoiding the paper's invalid inference
`floor(log₂ n) ≥ 2^q` when `q` is not an integer. -/
def inWideRange (C0 q : ℝ) (n : ℕ) : Prop :=
  (2 : ℝ) ^ q ≤ Real.logb 2 (n : ℝ) ∧
    Real.logb 2 (n : ℝ) <
      (2 : ℝ) ^ (q + Real.logb 2 q - C0)

/-- Exact interface needed from Theorem 6.1. The size upper bound on `m`
from the paper is deliberately omitted: Lemma 6.8 never uses it. -/
def MatchingConclusion (C0 CB CM Q0 : ℝ) : Prop :=
  ∀ q : ℝ, Q0 ≤ q → ∀ n : ℕ, inWideRange C0 q n →
    ∀ y : ℕ,
      ∃ m : ℕ,
        0 < m ∧ m < n ∧
        Nat.ModEq (2 ^ blockBits CB q n) m y ∧
        (alpha m : ℝ) ≤ CM * q

/-- Construction interface with an arbitrary choice of block exponent.
This is the interface useful for optimized versions of Theorem 6.1. -/
def MatchingConclusionAtBits (C0 CM Q0 : ℝ)
    (bits : ℝ → ℕ → ℕ) : Prop :=
  ∀ q : ℝ, Q0 ≤ q → ∀ n : ℕ, inWideRange C0 q n →
    ∀ y : ℕ,
      ∃ m : ℕ,
        0 < m ∧ m < n ∧
        Nat.ModEq (2 ^ bits q n) m y ∧
        (alpha m : ℝ) ≤ CM * q

/-- Minimal construction interface actually consumed by Lemma 6.8: only
the successor residue `n+1` is requested. -/
def MatchingSuccessorAtBits (C0 CM Q0 : ℝ)
    (bits : ℝ → ℕ → ℕ) : Prop :=
  ∀ q : ℝ, Q0 ≤ q → ∀ n : ℕ, inWideRange C0 q n →
    ∃ m : ℕ,
      0 < m ∧ m < n ∧
      Nat.ModEq (2 ^ bits q n) m (n + 1) ∧
      (alpha m : ℝ) ≤ CM * q

theorem matchingSuccessorAtBits_of_matchingConclusionAtBits
    {C0 CM Q0 : ℝ} {bits : ℝ → ℕ → ℕ}
    (h : MatchingConclusionAtBits C0 CM Q0 bits) :
    MatchingSuccessorAtBits C0 CM Q0 bits := by
  intro q hq n hn
  exact h q hq n hn (n + 1)

/-- The complete numerical contract on a block-exponent choice needed by
Lemma 6.8. No particular formula for `bits` is built into the reduction. -/
def RemainderBitBound (C0 : ℝ) (bits : ℝ → ℕ → ℕ) : Prop :=
  ∀ q n, inWideRange C0 q n →
    bits q n ≤ binaryLog n ∧
      ((binaryLog n + 1 - bits q n : ℕ) : ℝ) < (2 : ℝ) ^ q

/-- Threshold-aware numerical contract. This is the natural form paired with
`MatchingConclusionAtBits`, whose construction is only asserted for `q≥Q0`. -/
def RemainderBitBoundAbove (C0 Q0 : ℝ)
    (bits : ℝ → ℕ → ℕ) : Prop :=
  ∀ q, Q0 ≤ q → ∀ n, inWideRange C0 q n →
    bits q n ≤ binaryLog n ∧
      ((binaryLog n + 1 - bits q n : ℕ) : ℝ) < (2 : ℝ) ^ q

theorem blockBits_le_binaryLog (CB q : ℝ) (n : ℕ)
    (hCB : 0 ≤ CB) (hq : 0 < q) :
    blockBits CB q n ≤ binaryLog n := by
  apply Nat.floor_le_of_le
  have hx : 0 ≤ CB / q := div_nonneg hCB hq.le
  have hden : 1 ≤ 1 + CB / q := by linarith
  exact div_le_of_le_mul₀ (by positivity) (by positivity) (by
    simpa using mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg' (binaryLog n)))

/-- The rounding loss in `B` costs fewer than two extra bits. -/
theorem binaryLog_succ_sub_blockBits_lt (CB q : ℝ) (n : ℕ)
    (hCB : 0 ≤ CB) (hq : 0 < q) :
    ((binaryLog n + 1 - blockBits CB q n : ℕ) : ℝ) <
      CB * (binaryLog n : ℝ) / q + 2 := by
  let N : ℕ := binaryLog n
  let x : ℝ := CB / q
  let B : ℕ := blockBits CB q n
  have hx : 0 ≤ x := by simp [x]; positivity
  have hd : 0 < 1 + x := by linarith
  have hB : B ≤ N := by
    simpa [B, N] using blockBits_le_binaryLog CB q n hCB hq
  have hfloor : (N : ℝ) / (1 + x) < (B : ℝ) + 1 := by
    simpa [B, blockBits, N, x] using
      (Nat.lt_floor_add_one ((N : ℝ) / (1 + x)))
  have hdiff : (N : ℝ) - (N : ℝ) / (1 + x) ≤ (N : ℝ) * x := by
    have heq : (N : ℝ) - (N : ℝ) / (1 + x) =
        (N : ℝ) * x / (1 + x) := by
      field_simp
      ring
    rw [heq]
    exact div_le_self (mul_nonneg (Nat.cast_nonneg' N) hx) (by linarith)
  rw [Nat.cast_sub (Nat.le_add_right_of_le hB)]
  change ((N + 1 : ℕ) : ℝ) - (B : ℝ) < CB * (N : ℝ) / q + 2
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hprod : CB * (N : ℝ) / q = (N : ℝ) * x := by
    simp only [x]
    ring
  rw [hprod]
  linarith

theorem wideRange_upper_endpoint (C0 q : ℝ) (hq : 0 < q) :
    (2 : ℝ) ^ (q + Real.logb 2 q - C0) =
      (2 : ℝ) ^ q * q / (2 : ℝ) ^ C0 := by
  rw [Real.rpow_sub zero_lt_two, Real.rpow_add zero_lt_two,
    Real.rpow_logb zero_lt_two (by norm_num) hq]

theorem binaryLog_le_logb_of_wideRange (C0 q : ℝ) (n : ℕ)
    (hrange : inWideRange C0 q n) :
    (binaryLog n : ℝ) ≤ Real.logb 2 (n : ℝ) := by
  have hlog : 0 ≤ Real.logb 2 (n : ℝ) :=
    (Real.rpow_pos_of_pos zero_lt_two q).le.trans hrange.1
  have hfloor := Nat.floor_le hlog
  have heq : ⌊Real.logb 2 (n : ℝ)⌋₊ = binaryLog n := by
    simpa [binaryLog] using Real.natFloor_logb_natCast 2 n
  rw [heq] at hfloor
  exact hfloor

/-- With the explicit choices `q ≥ 3` and `2 C_B ≤ 2^C₀`, the quotient
left after removing a `2^B` block has binary length strictly below `2^q`. -/
theorem blockRemainderBits_lt_rpow (C0 CB q : ℝ) (n : ℕ)
    (hCB : 0 ≤ CB) (hq : 3 ≤ q)
    (hconstants : 2 * CB ≤ (2 : ℝ) ^ C0)
    (hrange : inWideRange C0 q n) :
    ((binaryLog n + 1 - blockBits CB q n : ℕ) : ℝ) < (2 : ℝ) ^ q := by
  have hq0 : 0 < q := by linarith
  have hP : 0 < (2 : ℝ) ^ q := Real.rpow_pos_of_pos zero_lt_two q
  have hD : 0 < (2 : ℝ) ^ C0 := Real.rpow_pos_of_pos zero_lt_two C0
  have hN : (binaryLog n : ℝ) ≤
      (2 : ℝ) ^ q * q / (2 : ℝ) ^ C0 := by
    calc
      (binaryLog n : ℝ) ≤ Real.logb 2 (n : ℝ) :=
        binaryLog_le_logb_of_wideRange C0 q n hrange
      _ ≤ (2 : ℝ) ^ (q + Real.logb 2 q - C0) := hrange.2.le
      _ = (2 : ℝ) ^ q * q / (2 : ℝ) ^ C0 :=
        wideRange_upper_endpoint C0 q hq0
  have hmain : CB * (binaryLog n : ℝ) / q ≤ (2 : ℝ) ^ q / 2 := by
    calc
      CB * (binaryLog n : ℝ) / q ≤
          CB * ((2 : ℝ) ^ q * q / (2 : ℝ) ^ C0) / q := by
        gcongr
      _ = CB * (2 : ℝ) ^ q / (2 : ℝ) ^ C0 := by
        field_simp
      _ ≤ (2 : ℝ) ^ q / 2 := by
        apply (div_le_iff₀ hD).2
        have hm := mul_le_mul_of_nonneg_right hconstants hP.le
        nlinarith
  have hpow8 : (8 : ℝ) ≤ (2 : ℝ) ^ q := by
    have h := Real.rpow_le_rpow_of_exponent_le one_le_two hq
    norm_num [Real.rpow_natCast] at h ⊢
    exact h
  have htwo : (2 : ℝ) < (2 : ℝ) ^ q / 2 := by linarith
  have hround := binaryLog_succ_sub_blockBits_lt CB q n hCB hq0
  linarith

/-- A congruence to `n+1`, together with `m<n`, gives the exact positive
quotient used in the splitting argument. -/
theorem exists_positive_quotient_of_modEq_succ
    {d m n : ℕ} (_hm : 0 < m) (hmn : m < n)
    (hmod : Nat.ModEq d m (n + 1)) :
    ∃ k : ℕ, 0 < k ∧ n + 1 = m + d * k := by
  have hmle : m ≤ n + 1 := by omega
  have hdvd : d ∣ n + 1 - m := (Nat.modEq_iff_dvd' hmle).1 hmod
  rcases hdvd with ⟨k, hk⟩
  refine ⟨k, ?_, ?_⟩
  · by_contra hkzero
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hkzero
    subst k
    simp at hk
    omega
  · omega

/-- The exact quotient has fewer than `N+1-B` binary digits. -/
theorem quotient_lt_pow_remainderBits
    {m n k B : ℕ} (_hm : 0 < m) (_hmn : m < n)
    (hdecomp : n + 1 = m + 2 ^ B * k)
    (hB : B ≤ binaryLog n) :
    k < 2 ^ (binaryLog n + 1 - B) := by
  have hprod : 2 ^ B * k ≤ n := by omega
  have hnlog : n < 2 ^ (binaryLog n + 1) := by
    simpa [binaryLog, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  have hBle : B ≤ binaryLog n + 1 := hB.trans (Nat.le_add_right _ _)
  by_contra hk
  have hkge : 2 ^ (binaryLog n + 1 - B) ≤ k := Nat.le_of_not_gt hk
  have hmul : 2 ^ (binaryLog n + 1 - B) * 2 ^ B ≤ k * 2 ^ B := by
    gcongr
  have hpowe : 2 ^ (binaryLog n + 1 - B) * 2 ^ B =
      2 ^ (binaryLog n + 1) := Nat.pow_sub_mul_pow 2 hBle
  have : 2 ^ (binaryLog n + 1) ≤ n := by
    calc
      2 ^ (binaryLog n + 1) =
          2 ^ (binaryLog n + 1 - B) * 2 ^ B := hpowe.symm
      _ ≤ k * 2 ^ B := hmul
      _ = 2 ^ B * k := by ac_rfl
      _ ≤ n := hprod
  omega

/-- The quotient produced by the matching congruence lies below the lower
double-exponential endpoint of the current range. -/
theorem quotient_lt_doubleExp
    {C0 CB q : ℝ} {m n k : ℕ}
    (hCB : 0 ≤ CB) (hq : 3 ≤ q)
    (hconstants : 2 * CB ≤ (2 : ℝ) ^ C0)
    (hrange : inWideRange C0 q n)
    (hm : 0 < m) (hmn : m < n)
    (hdecomp : n + 1 = m + 2 ^ blockBits CB q n * k) :
    (k : ℝ) < (2 : ℝ) ^ ((2 : ℝ) ^ q) := by
  have hB := blockBits_le_binaryLog CB q n hCB (by linarith)
  have hk := quotient_lt_pow_remainderBits hm hmn hdecomp hB
  have hkreal : (k : ℝ) <
      ((2 ^ (binaryLog n + 1 - blockBits CB q n) : ℕ) : ℝ) := by
    exact_mod_cast hk
  have hbits := blockRemainderBits_lt_rpow C0 CB q n hCB hq hconstants hrange
  have hrpow := Real.rpow_lt_rpow_of_exponent_lt one_lt_two hbits
  calc
    (k : ℝ) < ((2 ^ (binaryLog n + 1 - blockBits CB q n) : ℕ) : ℝ) := hkreal
    _ = (2 : ℝ) ^ ((binaryLog n + 1 - blockBits CB q n : ℕ) : ℝ) := by
      norm_num [Real.rpow_natCast]
    _ < (2 : ℝ) ^ ((2 : ℝ) ^ q) := hrpow

/-- Formula-independent version of `quotient_lt_doubleExp`. -/
theorem quotient_lt_doubleExp_of_remainderBits
    {q : ℝ} {m n k B : ℕ}
    (hm : 0 < m) (hmn : m < n)
    (hdecomp : n + 1 = m + 2 ^ B * k)
    (hB : B ≤ binaryLog n)
    (hbits : ((binaryLog n + 1 - B : ℕ) : ℝ) < (2 : ℝ) ^ q) :
    (k : ℝ) < (2 : ℝ) ^ ((2 : ℝ) ^ q) := by
  have hk := quotient_lt_pow_remainderBits hm hmn hdecomp hB
  have hkreal : (k : ℝ) <
      ((2 ^ (binaryLog n + 1 - B) : ℕ) : ℝ) := by
    exact_mod_cast hk
  have hrpow := Real.rpow_lt_rpow_of_exponent_lt one_lt_two hbits
  calc
    (k : ℝ) < ((2 ^ (binaryLog n + 1 - B) : ℕ) : ℝ) := hkreal
    _ = (2 : ℝ) ^ ((binaryLog n + 1 - B : ℕ) : ℝ) := by
      norm_num [Real.rpow_natCast]
    _ < (2 : ℝ) ^ ((2 : ℝ) ^ q) := hrpow

/-- Splitting followed by lifting, in the exact form used in Lemma 6.8. -/
theorem alpha_le_of_block_decomposition
    {m n k B : ℕ} (hm : 0 < m) (_hmn : m < n)
    (hdecomp : n + 1 = m + 2 ^ B * k) :
    alpha n ≤ alpha m + alpha k := by
  have hk : 0 < k := by
    by_contra hkzero
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hkzero
    subst k
    simp at hdecomp
    omega
  have hprod : 0 < 2 ^ B * k := mul_pos (pow_pos (by norm_num) _) hk
  have hn : n = m + (2 ^ B * k - 1) := by omega
  have hsucc : 2 ^ B * k - 1 + 1 = 2 ^ B * k := by omega
  calc
    alpha n = alpha (m + (2 ^ B * k - 1)) := by rw [hn]
    _ ≤ alpha m + alpha (2 ^ B * k - 1 + 1) :=
      splittingLemma m (2 ^ B * k - 1) hm
    _ = alpha m + alpha (2 ^ B * k) := by rw [hsucc]
    _ ≤ alpha m + alpha k := by
      gcongr
      exact liftingLemma B k

/-- One application of the matching theorem gives the full one-range
reduction of Lemma 6.8, before choosing a particular range ladder. -/
theorem lemma6_8_step_of_matching
    {C0 CB CM Q0 q : ℝ} {n : ℕ}
    (hmatch : MatchingConclusion C0 CB CM Q0)
    (hCB : 0 ≤ CB) (hq : 3 ≤ q) (hQ : Q0 ≤ q)
    (hconstants : 2 * CB ≤ (2 : ℝ) ^ C0)
    (hrange : inWideRange C0 q n) :
    ∃ n' : ℕ,
      (n' : ℝ) < (2 : ℝ) ^ ((2 : ℝ) ^ q) ∧
      (alpha n : ℝ) ≤ CM * q + (alpha n' : ℝ) := by
  obtain ⟨m, hm, hmn, hmod, halpham⟩ := hmatch q hQ n hrange (n + 1)
  obtain ⟨n', _hn'pos, hdecomp⟩ :=
    exists_positive_quotient_of_modEq_succ hm hmn hmod
  refine ⟨n', quotient_lt_doubleExp hCB hq hconstants hrange hm hmn hdecomp, ?_⟩
  have halpha := alpha_le_of_block_decomposition hm hmn hdecomp
  have halphaR : (alpha n : ℝ) ≤ (alpha m : ℝ) + (alpha n' : ℝ) := by
    exact_mod_cast halpha
  linarith

/-- Formula-independent form of Lemma 6.8. This is the preferred bridge for
a construction using `B = H * ceil(q)` or any other block exponent. -/
theorem lemma6_8_step_of_matchingAtBits
    {C0 CM Q0 q : ℝ} {n : ℕ} {bits : ℝ → ℕ → ℕ}
    (hmatch : MatchingConclusionAtBits C0 CM Q0 bits)
    (hrem : RemainderBitBoundAbove C0 Q0 bits)
    (hQ : Q0 ≤ q) (hrange : inWideRange C0 q n) :
    ∃ n' : ℕ,
      (n' : ℝ) < (2 : ℝ) ^ ((2 : ℝ) ^ q) ∧
      (alpha n : ℝ) ≤ CM * q + (alpha n' : ℝ) := by
  obtain ⟨m, hm, hmn, hmod, halpham⟩ := hmatch q hQ n hrange (n + 1)
  obtain ⟨n', _hn'pos, hdecomp⟩ :=
    exists_positive_quotient_of_modEq_succ hm hmn hmod
  obtain ⟨hB, hbits⟩ := hrem q hQ n hrange
  refine ⟨n', quotient_lt_doubleExp_of_remainderBits hm hmn hdecomp hB hbits, ?_⟩
  have halpha := alpha_le_of_block_decomposition hm hmn hdecomp
  have halphaR : (alpha n : ℝ) ≤ (alpha m : ℝ) + (alpha n' : ℝ) := by
    exact_mod_cast halpha
  linarith

/-- Lemma 6.8 from the minimal successor-residue construction interface. -/
theorem lemma6_8_step_of_matchingSuccessorAtBits
    {C0 CM Q0 q : ℝ} {n : ℕ} {bits : ℝ → ℕ → ℕ}
    (hmatch : MatchingSuccessorAtBits C0 CM Q0 bits)
    (hrem : RemainderBitBoundAbove C0 Q0 bits)
    (hQ : Q0 ≤ q) (hrange : inWideRange C0 q n) :
    ∃ n' : ℕ,
      (n' : ℝ) < (2 : ℝ) ^ ((2 : ℝ) ^ q) ∧
      (alpha n : ℝ) ≤ CM * q + (alpha n' : ℝ) := by
  obtain ⟨m, hm, hmn, hmod, halpham⟩ := hmatch q hQ n hrange
  obtain ⟨n', _hn'pos, hdecomp⟩ :=
    exists_positive_quotient_of_modEq_succ hm hmn hmod
  obtain ⟨hB, hbits⟩ := hrem q hQ n hrange
  refine ⟨n', quotient_lt_doubleExp_of_remainderBits hm hmn hdecomp hB hbits, ?_⟩
  have halpha := alpha_le_of_block_decomposition hm hmn hdecomp
  have halphaR : (alpha n : ℝ) ≤ (alpha m : ℝ) + (alpha n' : ℝ) := by
    exact_mod_cast halpha
  linarith

/-- Consecutive real double-exponential ladder endpoints lie in the repaired
Theorem 6.1 range whenever the ladder gap has the paper's required size. -/
theorem inWideRange_of_explicitEndpoints
    {C0 T : ℝ} {i n : ℕ}
    (hlower : (2 : ℝ) ^ ((2 : ℝ) ^ explicitQ T i) ≤ (n : ℝ))
    (hupper : (n : ℝ) < (2 : ℝ) ^ ((2 : ℝ) ^ explicitQ T (i + 1)))
    (hgap : explicitQ T (i + 1) ≤
      explicitQ T i + Real.logb 2 (explicitQ T i) - C0) :
    inWideRange C0 (explicitQ T i) n := by
  have hpLower : 0 < (2 : ℝ) ^ ((2 : ℝ) ^ explicitQ T i) :=
    Real.rpow_pos_of_pos zero_lt_two _
  have hn : 0 < (n : ℝ) := hpLower.trans_le hlower
  constructor
  · have hlog := Real.logb_le_logb_of_le one_lt_two hpLower hlower
    simpa using hlog
  · have hlog := Real.logb_lt_logb one_lt_two hn hupper
    have hpowgap := Real.rpow_le_rpow_of_exponent_le one_le_two hgap
    have hlog' : Real.logb 2 (n : ℝ) <
        (2 : ℝ) ^ explicitQ T (i + 1) := by
      simpa using hlog
    exact hlog'.trans_le hpowgap

/-- The closed-form ladder has the logarithmic gap required by Theorem 6.1
once its initial double logarithm dominates the explicit constant below. -/
theorem explicitQ_succ_le_wideRangeEndpoint
    (C0 T : ℝ) (hT : 2 ≤ T)
    (hTwide : C0 + 1 + (Real.log 2)⁻¹ ≤
      Real.logb 2 (Real.logb 2 T)) :
    ∀ i, explicitQ T (i + 1) ≤
      explicitQ T i + Real.logb 2 (explicitQ T i) - C0 := by
  intro i
  let t := ladderT T i
  let L := Real.logb 2 t
  let L' := Real.logb 2 (t + 1)
  have ht2 : 2 ≤ t := hT.trans (by simp [t, ladderT])
  have ht : 0 < t := zero_lt_two.trans_le ht2
  have ht1 : 0 < t + 1 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hLpos : 0 < L := Real.logb_pos one_lt_two (one_lt_two.trans_le ht2)
  have htstep : ladderT T (i + 1) = t + 1 := by
    simp [t, ladderT]
    ring
  have hratio : Real.log ((t + 1) / t) ≤ (t + 1) / t - 1 :=
    Real.log_le_sub_one_of_pos (div_pos ht1 ht)
  have hinc : t * (L' - L) ≤ (Real.log 2)⁻¹ := by
    change t * ((Real.log (t + 1) / Real.log 2) -
      Real.log t / Real.log 2) ≤ (Real.log 2)⁻¹
    have hdiff : Real.log (t + 1) - Real.log t ≤ (t + 1) / t - 1 := by
      rw [← Real.log_div ht1.ne' ht.ne']
      exact hratio
    calc
      t * (Real.log (t + 1) / Real.log 2 - Real.log t / Real.log 2) =
          t * ((Real.log (t + 1) - Real.log t) / Real.log 2) := by ring
      _ ≤ t * (((t + 1) / t - 1) / Real.log 2) := by
        gcongr
      _ = (Real.log 2)⁻¹ := by
        field_simp
        ring
  have hL' : L' ≤ L + 1 := by
    have htupper : t + 1 ≤ 2 * t := by linarith
    calc
      L' ≤ Real.logb 2 (2 * t) :=
        Real.logb_le_logb_of_le one_lt_two ht1 htupper
      _ = Real.logb 2 2 + Real.logb 2 t := by
        rw [Real.logb_mul (by norm_num) ht.ne']
      _ = L + 1 := by simp [L, add_comm]
  have hTpos : 0 < T := zero_lt_two.trans_le hT
  have hLTpos : 0 < Real.logb 2 T :=
    Real.logb_pos one_lt_two (one_lt_two.trans_le hT)
  have hTL : Real.logb 2 T ≤ L := by
    apply Real.logb_le_logb_of_le one_lt_two hTpos
    change T ≤ T + (i : ℝ)
    exact le_add_of_nonneg_right (Nat.cast_nonneg' i)
  have hwide : C0 + 1 + (Real.log 2)⁻¹ ≤ Real.logb 2 L := by
    exact hTwide.trans
      (Real.logb_le_logb_of_le one_lt_two hLTpos hTL)
  have hlogprod : Real.logb 2 (t * L) = L + Real.logb 2 L := by
    rw [Real.logb_mul ht.ne' hLpos.ne']
  rw [explicitQ, explicitQ, htstep]
  change (t + 1) * L' ≤ t * L + Real.logb 2 (t * L) - C0
  rw [hlogprod]
  nlinarith

/-- A concrete initial value large enough for the Section 6 range ladder. -/
noncomputable def section6T : ℝ := (2 : ℝ) ^ ((2 : ℝ) ^ (16 : ℝ))

theorem section6T_ge_two : (2 : ℝ) ≤ section6T := by
  have hinner : (1 : ℝ) ≤ (2 : ℝ) ^ (16 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le one_le_two
      (show (0 : ℝ) ≤ 16 by norm_num)
    simpa using h
  calc
    (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num [Real.rpow_one]
    _ ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (16 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le one_le_two hinner
    _ = section6T := rfl

theorem inv_log_two_le_five : (Real.log 2)⁻¹ ≤ (5 : ℝ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  apply (inv_le_iff_one_le_mul₀ hlog).2
  nlinarith [Real.log_two_gt_d9]

theorem section6T_wide_for_ten :
    (10 : ℝ) + 1 + (Real.log 2)⁻¹ ≤
      Real.logb 2 (Real.logb 2 section6T) := by
  have hlog : (10 : ℝ) + 1 + (Real.log 2)⁻¹ ≤ 16 := by
    linarith [inv_log_two_le_five]
  rw [section6T, Real.logb_rpow zero_lt_two (by norm_num),
    Real.logb_rpow zero_lt_two (by norm_num)]
  exact hlog

theorem section6_explicitQ_gap :
    ∀ i, explicitQ section6T (i + 1) ≤
      explicitQ section6T i + Real.logb 2 (explicitQ section6T i) - 10 :=
  explicitQ_succ_le_wideRangeEndpoint 10 section6T section6T_ge_two
    section6T_wide_for_ten

/-- Lemma 6.8 for the exact ceiling cutoffs consumed by the analytic ladder.
All arithmetic constants and all real-parameter range conditions are explicit. -/
theorem explicitOneRangeReduction_of_matching
    (C0 CB CM Q0 T : ℝ)
    (hmatch : MatchingConclusion C0 CB CM Q0)
    (hCB : 0 ≤ CB)
    (hconstants : 2 * CB ≤ (2 : ℝ) ^ C0)
    (hq : ∀ i, 3 ≤ explicitQ T i)
    (hQ : ∀ i, Q0 ≤ explicitQ T i)
    (hgap : ∀ i, explicitQ T (i + 1) ≤
      explicitQ T i + Real.logb 2 (explicitQ T i) - C0) :
    ExplicitOneRangeReduction T CM := by
  apply explicitOneRangeReduction_of_realEndpoints
  intro i n hlower hupper
  have hrange : inWideRange C0 (explicitQ T i) n :=
    inWideRange_of_explicitEndpoints hlower hupper (hgap i)
  exact lemma6_8_step_of_matching hmatch hCB (hq i) (hQ i)
    hconstants hrange

/-- Exact ceiling-cutoff conclusion for an arbitrary block-exponent choice. -/
theorem explicitOneRangeReduction_of_matchingAtBits
    (C0 CM Q0 T : ℝ) (bits : ℝ → ℕ → ℕ)
    (hmatch : MatchingConclusionAtBits C0 CM Q0 bits)
    (hrem : RemainderBitBoundAbove C0 Q0 bits)
    (hQ : ∀ i, Q0 ≤ explicitQ T i)
    (hgap : ∀ i, explicitQ T (i + 1) ≤
      explicitQ T i + Real.logb 2 (explicitQ T i) - C0) :
    ExplicitOneRangeReduction T CM := by
  apply explicitOneRangeReduction_of_realEndpoints
  intro i n hlower hupper
  have hrange : inWideRange C0 (explicitQ T i) n :=
    inWideRange_of_explicitEndpoints hlower hupper (hgap i)
  exact lemma6_8_step_of_matchingAtBits hmatch hrem (hQ i) hrange

/-- Exact ceiling-cutoff conclusion from only successor-residue matching. -/
theorem explicitOneRangeReduction_of_matchingSuccessorAtBits
    (C0 CM Q0 T : ℝ) (bits : ℝ → ℕ → ℕ)
    (hmatch : MatchingSuccessorAtBits C0 CM Q0 bits)
    (hrem : RemainderBitBoundAbove C0 Q0 bits)
    (hQ : ∀ i, Q0 ≤ explicitQ T i)
    (hgap : ∀ i, explicitQ T (i + 1) ≤
      explicitQ T i + Real.logb 2 (explicitQ T i) - C0) :
    ExplicitOneRangeReduction T CM := by
  apply explicitOneRangeReduction_of_realEndpoints
  intro i n hlower hupper
  have hrange : inWideRange C0 (explicitQ T i) n :=
    inWideRange_of_explicitEndpoints hlower hupper (hgap i)
  exact lemma6_8_step_of_matchingSuccessorAtBits hmatch hrem (hQ i) hrange

/-- Convenience form in which the gap and lower-threshold conditions for the
explicit ladder are reduced to assumptions at its initial value. -/
theorem explicitOneRangeReduction_of_matchingAtBits_of_initial
    (C0 CM Q0 T : ℝ) (bits : ℝ → ℕ → ℕ)
    (hmatch : MatchingConclusionAtBits C0 CM Q0 bits)
    (hrem : RemainderBitBoundAbove C0 Q0 bits)
    (hT : 2 ≤ T)
    (hQ0 : Q0 ≤ explicitQ T 0)
    (hTwide : C0 + 1 + (Real.log 2)⁻¹ ≤
      Real.logb 2 (Real.logb 2 T)) :
    ExplicitOneRangeReduction T CM := by
  apply explicitOneRangeReduction_of_matchingAtBits C0 CM Q0 T bits
      hmatch hrem
  · intro i
    exact hQ0.trans (explicitQ_monotone T (one_le_two.trans hT) (Nat.zero_le i))
  · exact explicitQ_succ_le_wideRangeEndpoint C0 T hT hTwide

/-- Initial-value form of the exact bridge for successor-residue matching. -/
theorem explicitOneRangeReduction_of_matchingSuccessorAtBits_of_initial
    (C0 CM Q0 T : ℝ) (bits : ℝ → ℕ → ℕ)
    (hmatch : MatchingSuccessorAtBits C0 CM Q0 bits)
    (hrem : RemainderBitBoundAbove C0 Q0 bits)
    (hT : 2 ≤ T)
    (hQ0 : Q0 ≤ explicitQ T 0)
    (hTwide : C0 + 1 + (Real.log 2)⁻¹ ≤
      Real.logb 2 (Real.logb 2 T)) :
    ExplicitOneRangeReduction T CM := by
  apply explicitOneRangeReduction_of_matchingSuccessorAtBits C0 CM Q0 T bits
      hmatch hrem
  · intro i
    exact hQ0.trans (explicitQ_monotone T (one_le_two.trans hT) (Nat.zero_le i))
  · exact explicitQ_succ_le_wideRangeEndpoint C0 T hT hTwide

end AntichainOfGivenSize
