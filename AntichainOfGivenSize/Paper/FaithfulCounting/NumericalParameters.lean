import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Exact numerical parameters in the frozen paper, §10.1.
This independent candidate does not change the repository or its workflow. -/
namespace AntichainOfGivenSize.FaithfulLower.Numerical

noncomputable def clusterSize (L : ℝ) : ℕ := ⌊L / 4⌋₊
noncomputable def packingBound (L : ℝ) (K : ℕ) : ℕ := K / clusterSize L
noncomputable def gamma (L : ℝ) (K : ℕ) : ℝ :=
  (2 : ℝ) ^ L / L ^ (6 * packingBound L K)
noncomputable def fineCost (L : ℝ) (K : ℕ) : ℝ := 2 * (K : ℝ)^2 / L^6
noncomputable def recordCost (L : ℝ) (K : ℕ) : ℝ :=
  Real.logb 2 (packingBound L K + 1) + (K : ℝ) * Real.logb 2 K
    + Real.logb 2 ((K : ℝ) * (2 : ℝ)^L + 1)
    + (2 : ℝ)^(packingBound L K) * (1 + (K : ℝ) * (2 : ℝ)^(clusterSize L))
      * Real.logb 2 ((2 : ℝ)^L + 1) + K + 2

def Admissible (L : ℝ) (K : ℕ) : Prop :=
  1 ≤ K ∧ (K : ℝ) ≤ L^2 / (100 * Real.logb 2 L)

theorem clusterSize_bounds {L : ℝ} (hL : 20 ≤ L) :
    L / 5 ≤ (clusterSize L : ℝ) ∧ (clusterSize L : ℝ) ≤ L / 4 := by
  have hlo := Nat.lt_floor_add_one (L / 4)
  have hhi := Nat.floor_le (show 0 ≤ L / 4 by linarith)
  dsimp [clusterSize]
  constructor <;> linarith

theorem logLog_ge_one {L : ℝ} (hL : 20 ≤ L) : 1 ≤ Real.logb 2 L := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ L by linarith)
  simpa using h

theorem budget_le_square {L : ℝ} {K : ℕ} (hL : 20 ≤ L) (hK : Admissible L K) :
    (K : ℝ) ≤ L^2 := by
  have hT := logLog_ge_one hL
  exact hK.2.trans (div_le_self (sq_nonneg L) (by linarith))

theorem packing_log_bound {L : ℝ} {K : ℕ} (hL : 20 ≤ L)
    (hK : Admissible L K) :
    (packingBound L K : ℝ) * Real.logb 2 L ≤ L / 20 := by
  have hLpos : 0 < L := by linarith
  have hT := logLog_ge_one hL
  have hfloor := (clusterSize_bounds hL).1
  have hJK : (packingBound L K : ℝ) * (clusterSize L : ℝ) ≤ K := by
    exact_mod_cast Nat.div_mul_le_self K (clusterSize L)
  have hJnonneg : 0 ≤ (packingBound L K : ℝ) := by positivity
  have hscaled : (packingBound L K : ℝ) * (L / 5) ≤ K := by
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hscaled
    (show 0 ≤ Real.logb 2 L by linarith)
  have hbudget := (le_div_iff₀ (show 0 < 100 * Real.logb 2 L by linarith)).mp hK.2
  apply (mul_le_mul_iff_right₀ hLpos).mp
  nlinarith

theorem gamma_lower {L : ℝ} {K : ℕ} (hL : 20 ≤ L) (hK : Admissible L K) :
    (2 : ℝ) ^ (7 * L / 10) ≤ gamma L K := by
  have hLpos : 0 < L := by linarith
  have hJ := packing_log_bound hL hK
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity) (by unfold gamma; positivity)).mp
  unfold gamma
  rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_rpow (by norm_num) (by norm_num),
    Real.logb_rpow (by norm_num) (by norm_num), Real.logb_pow]
  push_cast
  nlinarith

theorem fineCost_le_quarter {L : ℝ} {K : ℕ} (hL : 20 ≤ L)
    (hK : Admissible L K) : fineCost L K ≤ 1/4 := by
  have hLpos : 0 < L := by linarith
  have hKsq : (K : ℝ)^2 ≤ L^4 := by
    have h := sq_le_sq₀ (by positivity : (0 : ℝ) ≤ K) (sq_nonneg L)
    have hh := h.mpr (budget_le_square hL hK)
    nlinarith
  have hLsq : (8 : ℝ) ≤ L^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hLsq (pow_nonneg hLpos.le 4)
  unfold fineCost
  apply (div_le_iff₀ (pow_pos hLpos 6)).mpr
  nlinarith

theorem gamma_quarter_ge_sqrt {L : ℝ} {K : ℕ} (hL : 20 ≤ L)
    (hK : Admissible L K) : Real.sqrt ((2 : ℝ)^L) ≤ gamma L K / 4 := by
  have hpow : 4 * (2 : ℝ)^(L/2) ≤ (2 : ℝ)^(7*L/10) := by
    calc
      4 * (2 : ℝ)^(L/2) = (2 : ℝ)^(2 + L/2) := by
        rw [Real.rpow_add (by norm_num)]
        norm_num
      _ ≤ (2 : ℝ)^(7*L/10) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hsqrt : Real.sqrt ((2 : ℝ)^L) = (2 : ℝ)^(L/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [hsqrt]
  have hg := gamma_lower hL hK
  linarith


/-- A coarse polynomial envelope suffices for the uniform asymptotic check. -/
noncomputable def envelopeConstant : ℝ := 9 + 5 * (Real.log 2)⁻¹

theorem envelopeConstant_pos : 0 < envelopeConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold envelopeConstant
  positivity

theorem logb_le_linear {x : ℝ} (hx : 0 ≤ x) :
    Real.logb 2 x ≤ x * (Real.log 2)⁻¹ := by
  rw [Real.logb, ← div_eq_mul_inv]
  exact (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))).mpr
    (Real.log_le_self hx)

theorem log_power_add_one_le {L : ℝ} (hL : 0 ≤ L) :
    Real.logb 2 ((2 : ℝ)^L + 1) ≤ L + 1 := by
  have hp : 1 ≤ (2 : ℝ)^L := Real.one_le_rpow (by norm_num) hL
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by positivity)).mpr
  rw [Real.rpow_add (by norm_num)]
  norm_num
  linarith

theorem polynomial_bounds {L : ℝ} (hL : 20 ≤ L) :
    1 ≤ L^4 ∧ L ≤ L^4 ∧ L^2 ≤ L^4 ∧ (1 + L^2)*(L+1) ≤ 4*L^4 := by
  have hLpos : 0 ≤ L := by linarith
  have hLsq : L ≤ L^2 := by
    nlinarith [mul_nonneg hLpos (show 0 ≤ L-1 by linarith)]
  have hsqq : L^2 ≤ L^4 := by
    nlinarith [sq_nonneg (L^2-1)]
  have hcube : L^3 ≤ L^4 := by
    have hh := mul_le_mul_of_nonneg_right hLsq (sq_nonneg L)
    nlinarith
  refine ⟨by linarith, hLsq.trans hsqq, hsqq, ?_⟩
  have hh := mul_le_mul (show 1+L^2 ≤ 2*L^2 by nlinarith)
    (show L+1 ≤ 2*L by linarith) (show 0 ≤ L+1 by linarith)
    (show 0 ≤ 2*L^2 by positivity)
  nlinarith

theorem recordCost_envelope {L : ℝ} {K : ℕ} (hL : 20 ≤ L)
    (hK : Admissible L K) :
    recordCost L K ≤ envelopeConstant * L^4 * (2 : ℝ)^(3*L/10) := by
  have hLpos : 0 < L := by linarith
  have hKnonneg : (0 : ℝ) ≤ K := by positivity
  have hKsq := budget_le_square hL hK
  have hKfourth : (K : ℝ)^2 ≤ L^4 := by
    have hh := (sq_le_sq₀ hKnonneg (sq_nonneg L)).mpr hKsq
    nlinarith
  obtain ⟨hone, hLfourth, hsqfourth, hpoly⟩ := polynomial_bounds hL
  have hJ : (packingBound L K : ℝ) ≤ K := by
    exact_mod_cast Nat.div_le_self K (clusterSize L)
  have hJsmall : (packingBound L K : ℝ) ≤ L/20 := by
    have hh := packing_log_bound hL hK
    have ht := logLog_ge_one hL
    have hn : (0 : ℝ) ≤ packingBound L K := by positivity
    nlinarith
  have hc : 0 ≤ (Real.log 2)⁻¹ := by
    exact (inv_pos.mpr (Real.log_pos (by norm_num))).le
  have he : 1 ≤ (2 : ℝ)^(3*L/10) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  have hlogB := log_power_add_one_le hLpos.le
  have hlogBnonneg : 0 ≤ Real.logb 2 ((2 : ℝ)^L+1) :=
    Real.logb_nonneg (by norm_num) (by
      have : 0 ≤ (2 : ℝ)^L := by positivity
      linarith)
  have hA : Real.logb 2 (packingBound L K + 1) ≤ 2*L^4*(Real.log 2)⁻¹ := by
    exact (logb_le_linear (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hc)
  have hB : (K : ℝ)*Real.logb 2 K ≤ L^4*(Real.log 2)⁻¹ := by
    have hh := mul_le_mul_of_nonneg_left (logb_le_linear hKnonneg) hKnonneg
    have hh' := mul_le_mul_of_nonneg_right hKfourth hc
    nlinarith
  have hC : Real.logb 2 ((K : ℝ)*(2 : ℝ)^L+1) ≤
      2*L^4*(Real.log 2)⁻¹ + 2*L^4 := by
    have hprod : (K : ℝ)*(2 : ℝ)^L+1 ≤ ((K : ℝ)+1)*((2 : ℝ)^L+1) := by
      have : (0 : ℝ) ≤ (2 : ℝ)^L := by positivity
      nlinarith
    calc
      Real.logb 2 ((K : ℝ)*(2 : ℝ)^L+1)
          ≤ Real.logb 2 (((K : ℝ)+1)*((2 : ℝ)^L+1)) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hprod
      _ = Real.logb 2 ((K : ℝ)+1) + Real.logb 2 ((2 : ℝ)^L+1) := by
        rw [Real.logb_mul (by positivity) (by positivity)]
      _ ≤ 2*L^4*(Real.log 2)⁻¹ + 2*L^4 := by
        have hh := logb_le_linear (show 0 ≤ (K : ℝ)+1 by positivity)
        have hh' := mul_le_mul_of_nonneg_right
          (show (K : ℝ)+1 ≤ 2*L^4 by linarith) hc
        linarith
  have hD : (2 : ℝ)^(packingBound L K) *
      (1 + (K : ℝ)*(2 : ℝ)^(clusterSize L)) * Real.logb 2 ((2 : ℝ)^L+1)
      ≤ 4*L^4*(2 : ℝ)^(3*L/10) := by
    have hh : 1 ≤ (2 : ℝ)^(clusterSize L) := one_le_pow₀ (by norm_num)
    have hjoin : (2 : ℝ)^(packingBound L K) * (2 : ℝ)^(clusterSize L)
        ≤ (2 : ℝ)^(3*L/10) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by have := (clusterSize_bounds hL).2; linarith)
    have hfirst : (2 : ℝ)^(packingBound L K) *
        (1 + (K : ℝ)*(2 : ℝ)^(clusterSize L))
        ≤ (1+L^2)*(2 : ℝ)^(3*L/10) := by
      calc
        _ ≤ (2 : ℝ)^(packingBound L K) *
            ((1+(K : ℝ))*(2 : ℝ)^(clusterSize L)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
        _ = (1+(K : ℝ))*((2 : ℝ)^(packingBound L K)*(2 : ℝ)^(clusterSize L)) := by ring
        _ ≤ (1+L^2)*(2 : ℝ)^(3*L/10) :=
          mul_le_mul (by linarith) hjoin (by positivity) (by positivity)
    calc
      _ ≤ ((1+L^2)*(2 : ℝ)^(3*L/10))*(L+1) :=
        mul_le_mul hfirst hlogB hlogBnonneg (by positivity)
      _ = ((1+L^2)*(L+1))*(2 : ℝ)^(3*L/10) := by ring
      _ ≤ 4*L^4*(2 : ℝ)^(3*L/10) :=
        mul_le_mul_of_nonneg_right hpoly (by positivity)
  have hrest : (K : ℝ)+2 ≤ 3*L^4 := by linarith
  have hsmall : (5*(Real.log 2)⁻¹+5)*L^4 ≤
      ((5*(Real.log 2)⁻¹+5)*L^4)*(2 : ℝ)^(3*L/10) := by
    exact le_mul_of_one_le_right (by positivity) he
  unfold recordCost envelopeConstant
  nlinarith

/-- All three numerical inequalities hold above one absolute threshold,
uniformly over the paper's full admissible range of `K`. -/
theorem exists_uniform_threshold : ∃ L₀ : ℕ, 20 ≤ L₀ ∧
    ∀ (L : ℝ), (L₀ : ℝ) ≤ L → ∀ K : ℕ, Admissible L K →
      fineCost L K ≤ 1/4 ∧ recordCost L K ≤ gamma L K/2 ∧
      Real.sqrt ((2 : ℝ)^L) ≤ gamma L K/4 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := envelopeConstant_pos
  have ho := isLittleO_pow_exp_pos_mul_atTop 4
    (show 0 < (2/5 : ℝ)*Real.log 2 by positivity)
  have hevent := ho.def (show 0 < 1/(2*envelopeConstant) by positivity)
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 hevent
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (max a 20)
  refine ⟨L₀, ?_, ?_⟩
  · have : (20 : ℝ) < L₀ := (le_max_right a 20).trans_lt hL₀
    exact_mod_cast this.le
  intro L hL K hK
  have h20 : 20 ≤ L := (le_max_right a 20).trans (hL₀.le.trans hL)
  refine ⟨fineCost_le_quarter h20 hK, ?_, gamma_quarter_ge_sqrt h20 hK⟩
  have hLa : a ≤ L := (le_max_left a 20).trans (hL₀.le.trans hL)
  have hpoly := ha L hLa
  have hLnonneg : 0 ≤ L := by linarith
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hLnonneg 4),
    abs_of_pos (Real.exp_pos _)] at hpoly
  have hprod := mul_le_mul_of_nonneg_left hpoly hc.le
  have hbound : envelopeConstant*L^4 ≤ (2 : ℝ)^(2*L/5)/2 := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hexp : Real.log 2 * (2*L/5) = (2/5 : ℝ)*Real.log 2*L := by ring
    rw [hexp]
    have hcancel : envelopeConstant * (1/(2*envelopeConstant)) = (1/2 : ℝ) := by
      field_simp [ne_of_gt hc]
    calc
      _ ≤ envelopeConstant * (1/(2*envelopeConstant) *
          Real.exp ((2/5 : ℝ)*Real.log 2*L)) := hprod
      _ = _ := by rw [← mul_assoc, hcancel]; ring
  have hmult := mul_le_mul_of_nonneg_right hbound
    (show 0 ≤ (2 : ℝ)^(3*L/10) by positivity)
  have hpow : (2 : ℝ)^(2*L/5)/2*(2 : ℝ)^(3*L/10) =
      (2 : ℝ)^(7*L/10)/2 := by
    rw [div_mul_eq_mul_div, ← Real.rpow_add (by norm_num)]
    congr 2
    ring
  rw [hpow] at hmult
  exact (recordCost_envelope h20 hK).trans
    (hmult.trans (div_le_div_of_nonneg_right (gamma_lower h20 hK) (by norm_num)))


/-- Recover the paper's numerator `B` after setting `L = log₂ B`. -/
theorem gamma_at_log {B : ℝ} (hB : 0 < B) (K : ℕ) :
    gamma (Real.logb 2 B) K =
      B / (Real.logb 2 B)^(6*packingBound (Real.logb 2 B) K) := by
  unfold gamma
  rw [Real.rpow_logb (by norm_num) (by norm_num) hB]

/-- The final exponent comparison in §10.1, with the original constants. -/
theorem exponent_saving {L : ℝ} {K : ℕ} (hL : 20 ≤ L)
    (hK : Admissible L K) (hrec : recordCost L K ≤ gamma L K/2) :
    (2 : ℝ)^L - (1-fineCost L K)*gamma L K + recordCost L K
      ≤ (2 : ℝ)^L - Real.sqrt ((2 : ℝ)^L) := by
  have hd := fineCost_le_quarter hL hK
  have hs := gamma_quarter_ge_sqrt hL hK
  have hg : 0 ≤ gamma L K := by
    unfold gamma
    positivity
  have hh := mul_le_mul_of_nonneg_right hd hg
  nlinarith

/-- One integer bound on `B` works for every permitted `K`. -/
theorem exists_uniform_B_threshold : ∃ B₀ : ℕ, 1 ≤ B₀ ∧
    ∀ B : ℕ, B₀ ≤ B → ∀ K : ℕ, Admissible (Real.logb 2 B) K →
      fineCost (Real.logb 2 B) K ≤ 1/4 ∧
      recordCost (Real.logb 2 B) K ≤ gamma (Real.logb 2 B) K/2 ∧
      Real.sqrt B ≤ gamma (Real.logb 2 B) K/4 := by
  obtain ⟨L₀, hL₀, hthreshold⟩ := exists_uniform_threshold
  refine ⟨2^L₀, one_le_pow₀ (by norm_num), ?_⟩
  intro B hB K hK
  have hBpos : (0 : ℝ) < B := by
    exact_mod_cast lt_of_lt_of_le (pow_pos (by norm_num : 0 < (2 : ℕ)) L₀) hB
  have hlog : (L₀ : ℝ) ≤ Real.logb 2 B := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (2 : ℝ)^L₀) (show (2 : ℝ)^L₀ ≤ B by exact_mod_cast hB)
    simpa [Real.logb_pow] using hh
  obtain ⟨hd, hr, hs⟩ := hthreshold (Real.logb 2 B) hlog K hK
  rw [Real.rpow_logb (by norm_num) (by norm_num) hBpos] at hs
  exact ⟨hd, hr, hs⟩

end AntichainOfGivenSize.FaithfulLower.Numerical

