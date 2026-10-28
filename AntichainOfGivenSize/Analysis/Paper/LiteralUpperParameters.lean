import AntichainOfGivenSize.Analysis.Paper.UpperConstructionBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring

open Filter Asymptotics

namespace AntichainOfGivenSize.Paper.LiteralUpperParameters

set_option maxHeartbeats 800000

/-- The exact real logarithm/floor relation used for the paper's block count. -/
theorem dyadic_floor_bounds {x : ℝ} (hx : 1 ≤ x) :
    x / 2 < (2 : ℝ) ^ ⌊Real.logb 2 x⌋₊ ∧
      (2 : ℝ) ^ ⌊Real.logb 2 x⌋₊ ≤ x := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hlog : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx
  have hlo := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (Nat.floor_le hlog)
  have hhi := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (Nat.lt_floor_add_one (Real.logb 2 x))
  rw [Real.rpow_natCast, Real.rpow_logb (by norm_num) (by norm_num) hxpos] at hlo
  rw [Real.rpow_logb (by norm_num) (by norm_num) hxpos,
    Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one] at hhi
  exact ⟨by linarith, hlo⟩

/-- One sufficiently large input satisfies all numerical small-error conditions. -/
theorem eventually_cubic_log_bound :
    ∀ᶠ B : ℝ in atTop, 2 ≤ Real.logb 2 B ∧ 9 * (Real.logb 2 B) ^ 3 ≤ B := by
  have hsmall := (Real.isLittleO_pow_logb_id_atTop (b := (2 : ℝ)) (n := 3)).bound
    (by norm_num : (0 : ℝ) < 1 / 9)
  have hlog : ∀ᶠ B : ℝ in atTop, 2 ≤ Real.logb 2 B :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).eventually
      (eventually_ge_atTop 2)
  filter_upwards [hsmall, hlog, eventually_ge_atTop (0 : ℝ)] with B hsmall hlog hB
  refine ⟨hlog, ?_⟩
  have hlog0 : 0 ≤ Real.logb 2 B := by linarith
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg (pow_nonneg hlog0 3),
    abs_of_nonneg hB] at hsmall
  linarith

/-- Exact definitions in the manuscript, using natural floor and ceiling on the
positive eventual range.  The hypothesis is explicit so this lemma is usable
independently of the asymptotic threshold. -/
theorem literal_parameter_bounds {B : ℝ}
    (hL : 2 ≤ Real.logb 2 B) (hlarge : 9 * (Real.logb 2 B) ^ 3 ≤ B) :
    let L := Real.logb 2 B
    let r : ℕ := ⌊Real.logb 2 (B / L)⌋₊
    let H : ℕ := 2 ^ r
    let ell : ℕ := ⌈B / (H : ℝ)⌉₊
    let s : ℕ := 2 * r + ell + 1
    let M : ℕ := ell * (H + r) + H
    B / (2 * L) < (H : ℝ) ∧ (H : ℝ) ≤ B / L ∧
      L ≤ (ell : ℝ) ∧ (ell : ℝ) < 2 * L + 1 ∧
      (r : ℝ) ≤ L ∧ (s : ℝ) ≤ 5 * L ∧
      ((M + s : ℕ) : ℝ) ≤ B + 3 * B / L := by
  dsimp only
  let L := Real.logb 2 B
  let r : ℕ := ⌊Real.logb 2 (B / L)⌋₊
  let H : ℕ := 2 ^ r
  let ell : ℕ := ⌈B / (H : ℝ)⌉₊
  change B / (2 * L) < (H : ℝ) ∧ (H : ℝ) ≤ B / L ∧
    L ≤ (ell : ℝ) ∧ (ell : ℝ) < 2 * L + 1 ∧
    (r : ℝ) ≤ L ∧ ((2 * r + ell + 1 : ℕ) : ℝ) ≤ 5 * L ∧
    ((ell * (H + r) + H + (2 * r + ell + 1) : ℕ) : ℝ) ≤ B + 3 * B / L
  have hL2 : 2 ≤ L := hL
  have hLpos : 0 < L := by linarith
  have hL0 : 0 ≤ L := le_of_lt hLpos
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hlarge' : 9 * L ^ 3 ≤ B := hlarge
  have hBL : L ≤ B := by
    nlinarith only [hlarge', hL0, mul_nonneg hL0 (sub_nonneg.mpr hLsq)]
  have hBpos : 0 < B := lt_of_lt_of_le hLpos hBL
  have hx : 1 ≤ B / L := (le_div_iff₀ hLpos).mpr (by simpa using hBL)
  obtain ⟨hHlo, hHhi⟩ := dyadic_floor_bounds hx
  have hHcast : (H : ℝ) = (2 : ℝ) ^ r := by simp [H]
  change B / L / 2 < (2 : ℝ) ^ r at hHlo
  change (2 : ℝ) ^ r ≤ B / L at hHhi
  rw [← hHcast] at hHlo hHhi
  have hHpos : (0 : ℝ) < H := by positivity
  have hHlo' : B / (2 * L) < (H : ℝ) := by
    simpa only [div_div, mul_comm L 2] using hHlo
  have hr : (r : ℝ) ≤ L := by
    apply (Nat.floor_le (Real.logb_nonneg (by norm_num) hx)).trans
    exact Real.logb_le_logb_of_le (by norm_num) (div_pos hBpos hLpos)
      ((div_le_iff₀ hLpos).mpr (by
        simpa using mul_le_mul_of_nonneg_left (show 1 ≤ L by linarith) (le_of_lt hBpos)))
  have hell0 : B / (H : ℝ) ≤ (ell : ℝ) := Nat.le_ceil _
  have hell1 : (ell : ℝ) < B / (H : ℝ) + 1 :=
    Nat.ceil_lt_add_one (le_of_lt (div_pos hBpos hHpos))
  have hHmul : (H : ℝ) * L ≤ B := (le_div_iff₀ hLpos).mp hHhi
  have hHtwomul : B < (H : ℝ) * (2 * L) :=
    (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * L)).mp hHlo'
  have helllo : L ≤ (ell : ℝ) :=
    ((le_div_iff₀ hHpos).mpr (by nlinarith)).trans hell0
  have hellhi : (ell : ℝ) < 2 * L + 1 := by
    have : B / (H : ℝ) < 2 * L := (div_lt_iff₀ hHpos).mpr (by nlinarith)
    linarith
  have hellH : (ell : ℝ) * H < B + H := by
    have := mul_lt_mul_of_pos_right hell1 hHpos
    simpa only [add_mul, div_mul_cancel₀ B (ne_of_gt hHpos), one_mul] using this
  have hs : ((2 * r + ell + 1 : ℕ) : ℝ) ≤ 5 * L := by
    push_cast
    linarith
  refine ⟨hHlo', hHhi, helllo, hellhi, hr, hs, ?_⟩
  have hrr : 0 ≤ (r : ℝ) := by positivity
  have hellr : (ell : ℝ) * r ≤ (2 * L + 1) * L :=
    mul_le_mul (le_of_lt hellhi) hr hrr (by positivity)
  have herr : 2 * L ^ 2 + 6 * L ≤ B / L := by
    apply (le_div_iff₀ hLpos).mpr
    have : 6 * L ^ 2 ≤ 7 * L ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg L) (show 0 ≤ 7 * L - 6 by linarith)]
    nlinarith only [hlarge', this]
  push_cast at hs ⊢
  calc
    (ell : ℝ) * (H + r) + H + (2 * r + ell + 1) ≤
        B + 2 * H + (2 * L ^ 2 + 6 * L) := by
      nlinarith only [hellH, hellr, hs]
    _ ≤ B + 2 * (B / L) + B / L := by linarith only [hHhi, herr]
    _ = B + 3 * B / L := by ring

/-- The literal numerical Claim 6.5 holds on an eventual set of integer inputs. -/
theorem eventually_literal_size_bounds :
    ∀ᶠ B : ℕ in atTop,
      let L := Real.logb 2 (B : ℝ)
      let r : ℕ := ⌊Real.logb 2 ((B : ℝ) / L)⌋₊
      let H : ℕ := 2 ^ r
      let ell : ℕ := ⌈(B : ℝ) / (H : ℝ)⌉₊
      let s : ℕ := 2 * r + ell + 1
      let M : ℕ := ell * (H + r) + H
      (s : ℝ) ≤ 5 * L ∧ ((M + s : ℕ) : ℝ) ≤ B + 3 * (B : ℝ) / L := by
  have hevent : ∀ᶠ B : ℕ in atTop,
      2 ≤ Real.logb 2 (B : ℝ) ∧ 9 * (Real.logb 2 (B : ℝ)) ^ 3 ≤ (B : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually eventually_cubic_log_bound
  filter_upwards [hevent] with B hB
  have h := literal_parameter_bounds hB.1 hB.2
  exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- A conventional absolute-threshold statement of the same numerical result. -/
theorem exists_literal_size_threshold :
    ∃ B₀ : ℕ, 1 ≤ B₀ ∧ ∀ B : ℕ, B₀ ≤ B →
      let L := Real.logb 2 (B : ℝ)
      let r : ℕ := ⌊Real.logb 2 ((B : ℝ) / L)⌋₊
      let H : ℕ := 2 ^ r
      let ell : ℕ := ⌈(B : ℝ) / (H : ℝ)⌉₊
      let s : ℕ := 2 * r + ell + 1
      let M : ℕ := ell * (H + r) + H
      (s : ℝ) ≤ 5 * L ∧ ((M + s : ℕ) : ℝ) ≤ B + 3 * (B : ℝ) / L := by
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp eventually_literal_size_bounds
  refine ⟨max B₀ 1, le_max_right _ _, ?_⟩
  intro B hB
  exact hB₀ B ((le_max_left _ _).trans hB)


end AntichainOfGivenSize.Paper.LiteralUpperParameters

namespace AntichainOfGivenSize.Paper.LiteralUpperParameters

open AntichainOfGivenSize
open AntichainOfGivenSize.Paper
open AntichainOfGivenSize.Paper.UpperConstruction

/-- The paper's literal position-bit count is positive on the same numerical range. -/
theorem literal_r_pos {B : ℝ}
    (hL : 2 ≤ Real.logb 2 B) (hlarge : 9 * (Real.logb 2 B) ^ 3 ≤ B) :
    0 < ⌊Real.logb 2 (B / Real.logb 2 B)⌋₊ := by
  let L := Real.logb 2 B
  have hL2 : 2 ≤ L := hL
  have hLp : 0 < L := by linarith
  have hbig : 9 * L ^ 3 ≤ B := hlarge
  have hBL : 2 * L ≤ B := by
    have hs : 0 ≤ L ^ 2 - 4 := by nlinarith
    have hp := mul_nonneg hLp.le hs
    nlinarith
  have hx : 2 ≤ B / L := (le_div_iff₀ hLp).mpr hBL
  have hlog : 1 ≤ Real.logb 2 (B / L) := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) hx
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h
  have hr : 1 ≤ ⌊Real.logb 2 (B / L)⌋₊ :=
    (Nat.one_le_floor_iff _).mpr hlog
  exact Nat.zero_lt_of_lt hr

/-- Positivity of the paper's floor-defined `r`, uniformly for large integer `B`. -/
theorem eventually_literal_r_pos :
    ∀ᶠ B : ℕ in atTop,
      0 < ⌊Real.logb 2 ((B : ℝ) / Real.logb 2 (B : ℝ))⌋₊ := by
  have hevent : ∀ᶠ B : ℕ in atTop,
      2 ≤ Real.logb 2 (B : ℝ) ∧ 9 * (Real.logb 2 (B : ℝ)) ^ 3 ≤ (B : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually eventually_cubic_log_bound
  filter_upwards [hevent] with B hB
  exact literal_r_pos hB.1 hB.2

/-- Connect the numerical inequalities to the actual constructed family.
The statement is uniform in every update history, hence includes the final one. -/
theorem constructed_size_of_numeric_bounds {r ell : ℕ} (hr : 0 < r)
    (B L : ℝ)
    (hs : ((2 * r + ell + 1 : ℕ) : ℝ) ≤ 5 * L)
    (hM : ((ell * (2 ^ r + r) + 2 ^ r + (2 * r + ell + 1) : ℕ) : ℝ) ≤
      B + 3 * B / L)
    (active : Finset (BitMatching.Stage r))
    (hist : BitMatching.Stage r → Finset (PatternGadget.Index ell)) :
    let m := idealCard (ell := ell) active hist PatternGadget.generator
    0 < m ∧
      (∀ p : Index r (PatternGadget.Index ell),
        (generator (ell := ell) active hist PatternGadget.generator p).card ≤
          ell * (2 ^ r + r) + 2 ^ r) ∧
      (alpha m : ℝ) ≤ 5 * L ∧ Real.logb 2 (m : ℝ) ≤ B + 3 * B / L := by
  let m := idealCard (ell := ell) active hist PatternGadget.generator
  let s := 2 * r + ell + 1
  let M := ell * (2 ^ r + r) + 2 ^ r
  have hm : 0 < m := idealCard_pos active hist
  have hsize : m ≤ s * 2 ^ M := idealCard_bound hr active hist
  have hpow : m ≤ 2 ^ (M + s) := by
    calc
      m ≤ s * 2 ^ M := hsize
      _ ≤ 2 ^ s * 2 ^ M := Nat.mul_le_mul_right _ s.lt_two_pow_self.le
      _ = 2 ^ (M + s) := by rw [← pow_add, Nat.add_comm]
  have halpha : (alpha m : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast alpha_idealCard_le active hist
  have hcast : (m : ℝ) ≤ (2 : ℝ) ^ (M + s) := by exact_mod_cast hpow
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hm : (0 : ℝ) < m) hcast
  have hlog' : Real.logb 2 (m : ℝ) ≤ ((M + s : ℕ) : ℝ) := by
    simpa only [Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using hlog
  exact ⟨hm, fun p ↦ card_generator_le hr active hist p,
    halpha.trans hs, hlog'.trans hM⟩

/-- Claim 6.5 for the actual constructed ideal, using exactly the paper's
floor/ceiling parameters. No budget or size assumption is left on the family. -/
theorem exists_literal_constructed_size_threshold :
    ∃ B₀ : ℕ, 1 ≤ B₀ ∧ ∀ B : ℕ, B₀ ≤ B →
      let L := Real.logb 2 (B : ℝ)
      let r : ℕ := ⌊Real.logb 2 ((B : ℝ) / L)⌋₊
      let H : ℕ := 2 ^ r
      let ell : ℕ := ⌈(B : ℝ) / (H : ℝ)⌉₊
      let s : ℕ := 2 * r + ell + 1
      let M : ℕ := ell * (H + r) + H
      0 < r ∧ (s : ℝ) ≤ 5 * L ∧
        ∀ (active : Finset (BitMatching.Stage r))
          (hist : BitMatching.Stage r → Finset (PatternGadget.Index ell)),
          let m := idealCard (ell := ell) active hist PatternGadget.generator
          0 < m ∧
            (∀ p : Index r (PatternGadget.Index ell),
              (generator (ell := ell) active hist PatternGadget.generator p).card ≤ M) ∧
            (alpha m : ℝ) ≤ 5 * L ∧
            Real.logb 2 (m : ℝ) ≤ (B : ℝ) + 3 * (B : ℝ) / L := by
  obtain ⟨Bnum, hBnum, hnum⟩ := exists_literal_size_threshold
  obtain ⟨Br, hr⟩ := eventually_atTop.mp eventually_literal_r_pos
  refine ⟨max Bnum Br, hBnum.trans (le_max_left _ _), ?_⟩
  intro B hB
  have hnumB := hnum B ((le_max_left _ _).trans hB)
  have hrB := hr B ((le_max_right _ _).trans hB)
  refine ⟨hrB, hnumB.1, ?_⟩
  intro active hist
  exact constructed_size_of_numeric_bounds hrB (B : ℝ) (Real.logb 2 (B : ℝ))
    hnumB.1 hnumB.2 active hist


end AntichainOfGivenSize.Paper.LiteralUpperParameters
