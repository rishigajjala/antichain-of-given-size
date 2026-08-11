import AntichainOfGivenSize.LowerBound.CarrySensitive
import AntichainOfGivenSize.LowerBound.VennProfiles

/-!
# The first missing ideal cardinality

This module packages the conductor formulation of lower bounds for `alpha`.
The unconditional quadratic-over-log lower bound is proved separately in
`LowerBound.Matching`.
-/

namespace AntichainOfGivenSize

/-- The least cardinality whose minimum generator count is greater than `q`. -/
noncomputable def firstMissingCardinality (q : ℕ) : ℕ :=
  sInf {n : ℕ | q < alpha n}

theorem alpha_alternatingOnes_two_pow_gt (q : ℕ) :
    q < alpha (alternatingOnes (2 ^ q)) := by
  let r := 2 ^ q
  let n := alternatingOnes r
  have hblocks := binaryBlockCount_add_one_le_two_pow_alpha n
  rw [binaryBlockCount_alternatingOnes] at hblocks
  have hpow : 2 ^ q < 2 ^ (alpha n) := by
    change r < 2 ^ (alpha n)
    omega
  simpa [n] using
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hpow

theorem exists_alpha_gt (q : ℕ) : ∃ n : ℕ, q < alpha n :=
  ⟨alternatingOnes (2 ^ q), alpha_alternatingOnes_two_pow_gt q⟩

/-- The defining strict lower-bound property of the first missing cardinality. -/
theorem firstMissingCardinality_spec (q : ℕ) :
    q < alpha (firstMissingCardinality q) := by
  exact Nat.sInf_mem (exists_alpha_gt q)

/-- Minimality of the first missing cardinality. -/
theorem firstMissingCardinality_le {q n : ℕ} (h : q < alpha n) :
    firstMissingCardinality q ≤ n := by
  exact Nat.sInf_le h

/-- The alternating-bit witness gives the baseline double-exponential upper
bound on the first missing cardinality. -/
theorem firstMissingCardinality_le_alternatingOnes (q : ℕ) :
    firstMissingCardinality q ≤ alternatingOnes (2 ^ q) := by
  apply firstMissingCardinality_le
  exact alpha_alternatingOnes_two_pow_gt q

/-- For `q ≥ 2`, the carry-sensitive word shortens the baseline witness by
two binary positions. -/
theorem firstMissingCardinality_le_carrySensitive (q : ℕ) (hq : 2 ≤ q) :
    firstMissingCardinality q ≤ alternatingOnes (2 ^ q - 2) := by
  apply firstMissingCardinality_le
  exact (Nat.lt_succ_self q).trans_le
    (carrySensitive_alternatingOnes_lower q hq)

/-- A concrete size bound for the baseline first-missing witness. -/
theorem firstMissingCardinality_lt_pow (q : ℕ) :
    firstMissingCardinality q < 2 ^ (2 * (2 ^ q + 1)) := by
  exact (firstMissingCardinality_le_alternatingOnes q).trans_lt
    (alternatingOnes_lt_pow (2 ^ q))

/-- Improved concrete conductor bound supplied by the carry-sensitive
witness. -/
theorem firstMissingCardinality_lt_carrySensitive_pow
    (q : ℕ) (hq : 2 ≤ q) :
    firstMissingCardinality q < 2 ^ (2 * (2 ^ q - 1)) := by
  calc
    firstMissingCardinality q ≤ alternatingOnes (2 ^ q - 2) :=
      firstMissingCardinality_le_carrySensitive q hq
    _ < 2 ^ (2 * ((2 ^ q - 2) + 1)) :=
      alternatingOnes_lt_pow (2 ^ q - 2)
    _ = 2 ^ (2 * (2 ^ q - 1)) := by
      congr 2
      have : 2 ≤ 2 ^ q := by
        calc
          2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ q := pow_le_pow_right' (by omega) (by omega)
      omega

/-- The first missing cardinality is strictly larger than its generator
threshold, hence these witnesses are cofinal. -/
theorem lt_firstMissingCardinality (q : ℕ) :
    q < firstMissingCardinality q := by
  by_contra h
  have hle : firstMissingCardinality q ≤ q := Nat.le_of_not_gt h
  have halpha := alpha_le_self (firstMissingCardinality q)
  exact (not_lt_of_ge (halpha.trans hle)) (firstMissingCardinality_spec q)

/-- Increasing the allowed generator threshold cannot make the first missing
cardinality smaller. -/
theorem firstMissingCardinality_mono : Monotone firstMissingCardinality := by
  intro q r hqr
  apply firstMissingCardinality_le
  exact hqr.trans_lt (firstMissingCardinality_spec r)

/-- Exact bounded-profile obstruction at the conductor. -/
theorem no_small_profile_at_firstMissing (q k : ℕ) (hk : k ≤ q) :
    ¬ VennProfile.HasVennProfile (firstMissingCardinality q) k := by
  intro hprofile
  have halpha : alpha (firstMissingCardinality q) ≤ k :=
    VennProfile.alpha_le_of_hasVennProfile hprofile
  exact (not_lt_of_ge (halpha.trans hk)) (firstMissingCardinality_spec q)

/-- A fixed power-scale estimate along cofinally many first-missing
cardinalities.  Proving this for positive `ε` and `c` is a sufficient
conductor formulation of the requested lower bound. -/
def FirstMissingPowerLowerBoundInfinitelyOften (ε c : ℝ) : Prop :=
  ∀ Q : ℕ, ∃ q : ℕ, Q ≤ q ∧
    c * VennProfile.superLogLogPowerScale ε (firstMissingCardinality q) ≤
      (q + 1 : ℕ)

/-- A power lower bound along first-missing cardinalities gives the desired
cofinal power lower bound for `alpha`. -/
theorem superLogLogPowerLowerBound_of_firstMissing
    {ε c : ℝ} (h : FirstMissingPowerLowerBoundInfinitelyOften ε c) :
    VennProfile.SuperLogLogPowerLowerBoundInfinitelyOften ε c := by
  intro N
  rcases h N with ⟨q, hNq, hscale⟩
  refine ⟨firstMissingCardinality q, ?_, ?_⟩
  · exact hNq.trans (lt_firstMissingCardinality q).le
  · have hqa : q + 1 ≤ alpha (firstMissingCardinality q) := by
      have hspec := firstMissingCardinality_spec q
      omega
    exact hscale.trans (by exact_mod_cast hqa)

/-! ## Converse conductor implication -/

open Filter

/-- For a positive power improvement, the iterated-log power scale tends to
infinity along the natural numbers. -/
theorem tendsto_superLogLogPowerScale_atTop {ε : ℝ} (hε : 0 < ε) :
    Tendsto (VennProfile.superLogLogPowerScale ε) atTop atTop := by
  have hcast :
      Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog :
      Tendsto (fun n : ℕ ↦ Real.logb 2 (n : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hcast
  have hloglog :
      Tendsto
        (fun n : ℕ ↦ Real.logb 2 (Real.logb 2 (n : ℝ)))
        atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hlog
  change Tendsto
    (fun n : ℕ ↦
      (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ (1 + ε))
    atTop atTop
  exact (tendsto_rpow_atTop (by linarith : 0 < 1 + ε)).comp hloglog

/-- Beyond four, the iterated-log power scale is monotone when its real
exponent is positive. -/
theorem superLogLogPowerScale_mono_of_four_le
    {ε : ℝ} (hε : 0 < ε) {m n : ℕ} (hm : 4 ≤ m) (hmn : m ≤ n) :
    VennProfile.superLogLogPowerScale ε m ≤
      VennProfile.superLogLogPowerScale ε n := by
  have hmRealPos : (0 : ℝ) < (m : ℝ) := by
    positivity
  have hmnReal : (m : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hmn
  have hlogMono :
      Real.logb 2 (m : ℝ) ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) hmRealPos hmnReal
  have htwoLeM : (2 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (show 2 ≤ m by omega)
  have honeLeLog :
      (1 : ℝ) ≤ Real.logb 2 (m : ℝ) := by
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) htwoLeM
  have hlogPos : 0 < Real.logb 2 (m : ℝ) :=
    zero_lt_one.trans_le honeLeLog
  have hlogLogMono :
      Real.logb 2 (Real.logb 2 (m : ℝ)) ≤
        Real.logb 2 (Real.logb 2 (n : ℝ)) :=
    Real.logb_le_logb_of_le (by norm_num) hlogPos hlogMono
  have hlogLogNonneg :
      0 ≤ Real.logb 2 (Real.logb 2 (m : ℝ)) :=
    Real.logb_nonneg (by norm_num) honeLeLog
  unfold VennProfile.superLogLogPowerScale
  exact Real.rpow_le_rpow hlogLogNonneg hlogLogMono (by linarith)

/-- With positive constants, the cofinal lower bound for alpha forces the
same-constant bound along cofinally many first-missing cardinalities. -/
theorem firstMissingPowerLowerBound_of_superLogLog
    {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (h : VennProfile.SuperLogLogPowerLowerBoundInfinitelyOften ε c) :
    FirstMissingPowerLowerBoundInfinitelyOften ε c := by
  intro Q
  let B : ℕ := max Q 4
  have hscaleTop :
      Tendsto
        (fun n : ℕ ↦ c * VennProfile.superLogLogPowerScale ε n)
        atTop atTop :=
    (tendsto_superLogLogPowerScale_atTop hε).const_mul_atTop hc
  obtain ⟨N₀, hN₀⟩ :=
    (tendsto_atTop_atTop.1 hscaleTop) ((B + 1 : ℕ) : ℝ)
  rcases h (max N₀ 4) with ⟨n, hn, halpha⟩
  have hN₀n : N₀ ≤ n := (le_max_left N₀ 4).trans hn
  have hlarge :
      ((B + 1 : ℕ) : ℝ) ≤
        c * VennProfile.superLogLogPowerScale ε n :=
    hN₀ n hN₀n
  have hBalpha : B + 1 ≤ alpha n := by
    exact_mod_cast hlarge.trans halpha
  have halphaPos : 0 < alpha n := by omega
  let q := alpha n - 1
  have hqSucc : q + 1 = alpha n := by
    dsimp [q]
    omega
  have hQq : Q ≤ q := by
    have hQB : Q ≤ B := le_max_left _ _
    dsimp [q]
    omega
  have hqAlpha : q < alpha n := by omega
  have hfirstLe : firstMissingCardinality q ≤ n :=
    firstMissingCardinality_le hqAlpha
  have hfirstFour : 4 ≤ firstMissingCardinality q := by
    have hBq : B ≤ q := by
      dsimp [q]
      omega
    exact (show 4 ≤ B by exact le_max_right _ _).trans
      (hBq.trans (lt_firstMissingCardinality q).le)
  have hscaleMono :
      VennProfile.superLogLogPowerScale ε (firstMissingCardinality q) ≤
        VennProfile.superLogLogPowerScale ε n :=
    superLogLogPowerScale_mono_of_four_le hε hfirstFour hfirstLe
  refine ⟨q, hQq, ?_⟩
  calc
    c * VennProfile.superLogLogPowerScale ε (firstMissingCardinality q) ≤
        c * VennProfile.superLogLogPowerScale ε n :=
      mul_le_mul_of_nonneg_left hscaleMono hc.le
    _ ≤ (alpha n : ℝ) := halpha
    _ = (q + 1 : ℕ) := by rw [hqSucc]

/-- Under the natural positivity assumptions, the infinitely-often
super-log-log target is exactly its first-missing-cardinality formulation. -/
theorem superLogLogPowerLowerBound_iff_firstMissing
    {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    VennProfile.SuperLogLogPowerLowerBoundInfinitelyOften ε c ↔
      FirstMissingPowerLowerBoundInfinitelyOften ε c := by
  constructor
  · exact firstMissingPowerLowerBound_of_superLogLog hε hc
  · exact superLogLogPowerLowerBound_of_firstMissing

/-- Existential form of the exact conductor equivalence. -/
theorem hasSuperLogLogPowerLowerBound_iff_exists_firstMissing :
    VennProfile.HasSuperLogLogPowerLowerBoundInfinitelyOften ↔
      ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
        FirstMissingPowerLowerBoundInfinitelyOften ε c := by
  constructor
  · rintro ⟨ε, c, hε, hc, hbound⟩
    exact ⟨ε, c, hε, hc,
      (superLogLogPowerLowerBound_iff_firstMissing hε hc).1 hbound⟩
  · rintro ⟨ε, c, hε, hc, hfirst⟩
    exact ⟨ε, c, hε, hc,
      (superLogLogPowerLowerBound_iff_firstMissing hε hc).2 hfirst⟩

end AntichainOfGivenSize
