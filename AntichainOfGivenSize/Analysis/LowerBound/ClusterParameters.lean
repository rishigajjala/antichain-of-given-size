import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Dyadic parameters for the cluster obstruction

This file contains only the elementary numerical ledger for the dyadic
subsequence used by the connected-cluster lower bound.  Its parameter is
`t`; the logarithmic facet scale is `q = 2^t`, and the load bound is
`B = 2^q`.

Taking `q` itself to be a power of two makes every loss scale an exact power
of two.  In particular, consecutive loss scales differ by the exact factor
`q^6`; no estimates involving real logarithms or floors are needed here.
-/

namespace AntichainOfGivenSize.ClusterParameters

/-- The logarithmic facet scale `q = 2^t`. -/
def dyadicQ (t : ℕ) : ℕ := 2 ^ t

/-- The maximum facet load `B = 2^q`. -/
def dyadicB (t : ℕ) : ℕ := 2 ^ dyadicQ t

/-- The cluster-size threshold `h = q / 4`. -/
def clusterH (t : ℕ) : ℕ := dyadicQ t / 4

/-- The number of facets used for the lower-bound witness.  The deliberately
large constant `1024` leaves ample room in every later counting estimate. -/
def facetBudget (t : ℕ) : ℕ :=
  dyadicQ t ^ 2 / (1024 * t)

/-- The largest possible number of disjoint clusters of size at least `h`. -/
def clusterJ (t : ℕ) : ℕ := facetBudget t / clusterH t

/-- One more than the packing bound; this is the number of adjacent scale
gaps used by the stable-gap pigeonhole argument. -/
def clusterL (t : ℕ) : ℕ := clusterJ t + 1

/-- Exponent of the `j`-th loss scale. -/
def scaleExponent (t j : ℕ) : ℕ :=
  dyadicQ t - t * (10 + 6 * j)

/-- The `j`-th loss scale, as an exact power of two. -/
def clusterRho (t j : ℕ) : ℕ := 2 ^ scaleExponent t j

/-- Uniform upper bound for the number of compressed center queries. -/
def centerQueryBound (t : ℕ) : ℕ :=
  2 ^ clusterJ t * (1 + facetBudget t * 2 ^ clusterH t)

/-- Binary transcript cost when each center exponent has at most `B+1`
possible values.  Since `B+1 ≤ 2^(q+1)`, this is the relevant exponent. -/
def centerTranscriptCost (t : ℕ) : ℕ :=
  (dyadicQ t + 1) * centerQueryBound t

@[simp] theorem dyadicQ_zero : dyadicQ 0 = 1 := by
  simp [dyadicQ]

theorem dyadicQ_pos (t : ℕ) : 0 < dyadicQ t := by
  simp [dyadicQ]

theorem dyadicB_pos (t : ℕ) : 0 < dyadicB t := by
  simp [dyadicB]

theorem clusterRho_pos (t j : ℕ) : 0 < clusterRho t j := by
  simp [clusterRho]

/-- For `t >= 2`, division by four simply removes two powers of two. -/
theorem clusterH_eq_two_pow {t : ℕ} (ht : 2 ≤ t) :
    clusterH t = 2 ^ (t - 2) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
  simp [clusterH, dyadicQ, pow_add]

theorem clusterH_pos {t : ℕ} (ht : 2 ≤ t) : 0 < clusterH t := by
  rw [clusterH_eq_two_pow ht]
  positivity

/-- The identity `q = 4h` on the dyadic subsequence. -/
theorem four_mul_clusterH {t : ℕ} (ht : 2 ≤ t) :
    4 * clusterH t = dyadicQ t := by
  rw [clusterH_eq_two_pow ht]
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
  simp [dyadicQ, pow_add]

/-- The facet budget is positive once its denominator fits below `q^2`. -/
theorem facetBudget_pos_of_denominator_le {t : ℕ}
    (ht : 0 < t) (hden : 1024 * t ≤ dyadicQ t ^ 2) :
    0 < facetBudget t := by
  unfold facetBudget
  exact Nat.div_pos hden (by positivity)

/-- A floor loses at most a factor two when the numerator is at least twice
the denominator. -/
theorem half_quotient_le_facetBudget {t : ℕ}
    (ht : 0 < t) :
    dyadicQ t ^ 2 / (2048 * t) ≤ facetBudget t := by
  unfold facetBudget
  exact Nat.div_le_div_left (by omega : 1024 * t ≤ 2048 * t) (by positivity)

/-- A convenient explicit exponential-versus-linear estimate. -/
theorem one_twenty_eight_mul_le_dyadicQ {t : ℕ} (ht : 16 ≤ t) :
    128 * t ≤ dyadicQ t := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction u with
  | zero => norm_num [dyadicQ]
  | succ u ih =>
      rw [show 16 + (u + 1) = (16 + u) + 1 by omega, dyadicQ, pow_succ]
      rw [dyadicQ] at ih
      omega

/-- A stronger estimate used only to show that the sparse-code alphabet
dominates its padding length. -/
theorem four_thousand_ninety_six_mul_le_dyadicQ {t : ℕ} (ht : 16 ≤ t) :
    4096 * t ≤ dyadicQ t := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction u with
  | zero => norm_num [dyadicQ]
  | succ u ih =>
      rw [show 16 + (u + 1) = (16 + u) + 1 by omega, dyadicQ, pow_succ]
      rw [dyadicQ] at ih
      omega

theorem two_pow_sixteen_le_dyadicQ {t : ℕ} (ht : 16 ≤ t) :
    2 ^ 16 ≤ dyadicQ t := by
  exact Nat.pow_le_pow_right (by norm_num) ht

theorem facetBudget_pos {t : ℕ} (ht : 16 ≤ t) :
    0 < facetBudget t := by
  apply facetBudget_pos_of_denominator_le (by omega)
  have hlin := one_twenty_eight_mul_le_dyadicQ ht
  have htpos : 0 < t := by omega
  nlinarith [dyadicQ_pos t]

theorem facetBudget_le_q_sq (t : ℕ) :
    facetBudget t ≤ dyadicQ t ^ 2 := by
  exact Nat.div_le_self _ _

theorem two_mul_q_le_facetBudget {t : ℕ} (ht : 16 ≤ t) :
    2 * dyadicQ t ≤ facetBudget t := by
  have hstrong := four_thousand_ninety_six_mul_le_dyadicQ ht
  have hdiv : 2 * dyadicQ t ≤ dyadicQ t ^ 2 / (2048 * t) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2048 * t)).2
    nlinarith [dyadicQ_pos t]
  exact hdiv.trans (half_quotient_le_facetBudget (by omega))

/-- On the dyadic subsequence the packing bound has a particularly simple
closed form. -/
theorem clusterJ_eq {t : ℕ} (ht : 2 ≤ t) :
    clusterJ t = dyadicQ t / (256 * t) := by
  rw [clusterJ, facetBudget, Nat.div_div_eq_div_mul]
  have hden : (1024 * t) * clusterH t = (256 * t) * dyadicQ t := by
    calc
      (1024 * t) * clusterH t = (256 * t) * (4 * clusterH t) := by ring
      _ = (256 * t) * dyadicQ t := by rw [four_mul_clusterH ht]
  rw [hden, pow_two]
  exact Nat.mul_div_mul_right (dyadicQ t) (256 * t) (dyadicQ_pos t)

theorem clusterJ_scale_le_q {t : ℕ} (ht : 2 ≤ t) :
    256 * t * clusterJ t ≤ dyadicQ t := by
  rw [clusterJ_eq ht]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    Nat.mul_div_le (dyadicQ t) (256 * t)

theorem clusterJ_le_q_div_four_thousand_ninety_six {t : ℕ}
    (ht : 16 ≤ t) :
    clusterJ t ≤ dyadicQ t / 4096 := by
  rw [clusterJ_eq (by omega)]
  exact Nat.div_le_div_left (by omega : 4096 ≤ 256 * t) (by norm_num)

/-- Every scale used by the stable-gap argument has exponent at least
three quarters of `q`.  The extra `+1` covers the smaller endpoint of the
last adjacent gap. -/
theorem scale_cost_through_L_add_one_le_quarter_q {t : ℕ}
    (ht : 16 ≤ t) :
    t * (10 + 6 * (clusterL t + 1)) ≤ clusterH t := by
  have hlin := one_twenty_eight_mul_le_dyadicQ ht
  have hJ := clusterJ_scale_le_q (t := t) (by omega)
  have hfour := four_mul_clusterH (t := t) (by omega)
  unfold clusterL
  nlinarith

theorem relevant_scale_cost_le_q {t j : ℕ}
    (ht : 16 ≤ t) (hj : j ≤ clusterL t + 1) :
    t * (10 + 6 * j) ≤ dyadicQ t := by
  have hcost := scale_cost_through_L_add_one_le_quarter_q ht
  have hjcost : t * (10 + 6 * j) ≤
      t * (10 + 6 * (clusterL t + 1)) := by gcongr
  have hfour := four_mul_clusterH (t := t) (by omega)
  omega

theorem three_mul_clusterH_le_scaleExponent {t j : ℕ}
    (ht : 16 ≤ t) (hj : j ≤ clusterL t + 1) :
    3 * clusterH t ≤ scaleExponent t j := by
  have hcost := scale_cost_through_L_add_one_le_quarter_q ht
  have hjcost : t * (10 + 6 * j) ≤ t * (10 + 6 * (clusterL t + 1)) := by
    gcongr
  have hfour := four_mul_clusterH (t := t) (by omega)
  unfold scaleExponent
  omega

theorem scaleExponent_antitone (t : ℕ) : Antitone (scaleExponent t) := by
  intro i j hij
  unfold scaleExponent
  apply Nat.sub_le_sub_left
  gcongr

theorem clusterRho_antitone (t : ℕ) : Antitone (clusterRho t) := by
  intro i j hij
  unfold clusterRho
  exact Nat.pow_le_pow_right (by norm_num) (scaleExponent_antitone t hij)

/-- The load divided by the prescribed power of `q` is exactly the
corresponding loss scale. -/
theorem dyadicB_div_q_pow {t a : ℕ} (ha : t * a ≤ dyadicQ t) :
    dyadicB t / dyadicQ t ^ a = 2 ^ (dyadicQ t - t * a) := by
  have ha' : t * a ≤ 2 ^ t := by simpa [dyadicQ] using ha
  rw [dyadicB, dyadicQ, ← pow_mul]
  conv_lhs =>
    lhs
    rw [show 2 ^ t = (2 ^ t - t * a) + t * a by omega, pow_add]
  simp

theorem clusterRho_eq_dyadicB_div {t j : ℕ}
    (hj : t * (10 + 6 * j) ≤ dyadicQ t) :
    clusterRho t j = dyadicB t / dyadicQ t ^ (10 + 6 * j) := by
  rw [dyadicB_div_q_pow hj]
  rfl

theorem clusterRho_eq_dyadicB_div_of_relevant {t j : ℕ}
    (ht : 16 ≤ t) (hj : j ≤ clusterL t + 1) :
    clusterRho t j = dyadicB t / dyadicQ t ^ (10 + 6 * j) :=
  clusterRho_eq_dyadicB_div (relevant_scale_cost_le_q ht hj)

theorem scaleExponent_succ_add {t j : ℕ}
    (hj : t * (10 + 6 * (j + 1)) ≤ dyadicQ t) :
    scaleExponent t (j + 1) + 6 * t = scaleExponent t j := by
  have hcost : t * (10 + 6 * (j + 1)) = t * (10 + 6 * j) + 6 * t := by
    ring
  rw [hcost] at hj
  unfold scaleExponent
  rw [hcost]
  omega

theorem q_pow_six (t : ℕ) : dyadicQ t ^ 6 = 2 ^ (6 * t) := by
  rw [dyadicQ, ← pow_mul]
  congr 1
  omega

/-- Consecutive loss scales differ by the exact factor `q^6`. -/
theorem clusterRho_eq_q_pow_six_mul_succ {t j : ℕ}
    (hj : t * (10 + 6 * (j + 1)) ≤ dyadicQ t) :
    clusterRho t j = dyadicQ t ^ 6 * clusterRho t (j + 1) := by
  rw [clusterRho, clusterRho, ← scaleExponent_succ_add hj, pow_add,
    q_pow_six]
  ring

theorem clusterRho_succ_eq_div_q_pow_six {t j : ℕ}
    (hj : t * (10 + 6 * (j + 1)) ≤ dyadicQ t) :
    clusterRho t (j + 1) = clusterRho t j / dyadicQ t ^ 6 := by
  rw [clusterRho_eq_q_pow_six_mul_succ hj]
  simp [dyadicQ_pos]

theorem clusterRho_eq_q_pow_six_mul_succ_of_relevant {t j : ℕ}
    (ht : 16 ≤ t) (hj : j + 1 ≤ clusterL t + 1) :
    clusterRho t j = dyadicQ t ^ 6 * clusterRho t (j + 1) :=
  clusterRho_eq_q_pow_six_mul_succ (relevant_scale_cost_le_q ht hj)

theorem clusterRho_succ_eq_div_q_pow_six_of_relevant {t j : ℕ}
    (ht : 16 ≤ t) (hj : j + 1 ≤ clusterL t + 1) :
    clusterRho t (j + 1) = clusterRho t j / dyadicQ t ^ 6 :=
  clusterRho_succ_eq_div_q_pow_six (relevant_scale_cost_le_q ht hj)

/-- Uniform exponential lower bound for every scale needed in the proof. -/
theorem two_pow_three_h_le_clusterRho {t j : ℕ}
    (ht : 16 ≤ t) (hj : j ≤ clusterL t + 1) :
    2 ^ (3 * clusterH t) ≤ clusterRho t j := by
  unfold clusterRho
  exact Nat.pow_le_pow_right (by norm_num) (three_mul_clusterH_le_scaleExponent ht hj)

/-! ## Coarse domination estimates -/

theorem budget_denominator_mul_le_q_sq (t : ℕ) :
    1024 * t * facetBudget t ≤ dyadicQ t ^ 2 := by
  unfold facetBudget
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    Nat.mul_div_le (dyadicQ t ^ 2) (1024 * t)

theorem four_mul_facetBudget_le_q_sq {t : ℕ} (ht : 16 ≤ t) :
    4 * facetBudget t ≤ dyadicQ t ^ 2 := by
  have hden := budget_denominator_mul_le_q_sq t
  have hfour : 4 * facetBudget t ≤ 1024 * t * facetBudget t := by
    gcongr
    omega
  exact hfour.trans hden

/-- The cubic exceptional-incidence cost is a tiny fraction of the exact
scale ratio `q^6`. -/
theorem sixty_four_mul_budget_cube_le_q_pow_six {t : ℕ} (ht : 16 ≤ t) :
    64 * facetBudget t ^ 3 ≤ dyadicQ t ^ 6 := by
  have hbase := four_mul_facetBudget_le_q_sq ht
  have hcub := Nat.pow_le_pow_left hbase 3
  nlinarith

theorem thirty_two_mul_t_le_clusterH {t : ℕ} (ht : 16 ≤ t) :
    32 * t ≤ clusterH t := by
  have hlin := one_twenty_eight_mul_le_dyadicQ ht
  have hfour := four_mul_clusterH (t := t) (by omega)
  nlinarith

theorem q_pow_eq_two_pow (t d : ℕ) :
    dyadicQ t ^ d = 2 ^ (t * d) := by
  rw [dyadicQ, ← pow_mul]

/-- Every power `q^d` with `d ≤ 32` is bounded by `2^h` on the chosen
subsequence, for `t ≥ 16`. -/
theorem q_pow_le_two_pow_h {t d : ℕ} (ht : 16 ≤ t) (hd : d ≤ 32) :
    dyadicQ t ^ d ≤ 2 ^ clusterH t := by
  rw [q_pow_eq_two_pow]
  apply Nat.pow_le_pow_right (by norm_num)
  exact (Nat.mul_le_mul_left t hd).trans
    (by simpa [mul_comm] using thirty_two_mul_t_le_clusterH ht)

theorem budget_pow_le_two_pow_h {t d : ℕ} (ht : 16 ≤ t) (hd : d ≤ 16) :
    facetBudget t ^ d ≤ 2 ^ clusterH t := by
  calc
    facetBudget t ^ d ≤ (dyadicQ t ^ 2) ^ d :=
      Nat.pow_le_pow_left (facetBudget_le_q_sq t) d
    _ = dyadicQ t ^ (2 * d) := by rw [pow_mul]
    _ ≤ 2 ^ clusterH t := q_pow_le_two_pow_h ht (by omega)

/-- The facet budget itself fits below `2^(h/4)`, a useful input to the
center-transcript count. -/
theorem facetBudget_le_two_pow_h_div_four {t : ℕ} (ht : 16 ≤ t) :
    facetBudget t ≤ 2 ^ (clusterH t / 4) := by
  have hexp : 2 * t ≤ clusterH t / 4 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
    have h := thirty_two_mul_t_le_clusterH ht
    omega
  calc
    facetBudget t ≤ dyadicQ t ^ 2 := facetBudget_le_q_sq t
    _ = 2 ^ (2 * t) := by simpa [mul_comm] using q_pow_eq_two_pow t 2
    _ ≤ 2 ^ (clusterH t / 4) := Nat.pow_le_pow_right (by norm_num) hexp

theorem clusterJ_le_h_div_four {t : ℕ} (ht : 16 ≤ t) :
    clusterJ t ≤ clusterH t / 4 := by
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
  have hJ := clusterJ_scale_le_q (t := t) (by omega)
  have hfour := four_mul_clusterH (t := t) (by omega)
  have hlow : 4096 * clusterJ t ≤ 256 * t * clusterJ t := by
    gcongr
    omega
  omega

theorem clusterL_le_h_div_two {t : ℕ} (ht : 16 ≤ t) :
    clusterL t ≤ clusterH t / 2 := by
  have hJ := clusterJ_le_h_div_four ht
  have hH : 4 ≤ clusterH t := by
    rw [clusterH_eq_two_pow (by omega)]
    have : 2 ≤ t - 2 := by omega
    exact (by norm_num : 4 ≤ 2 ^ 2).trans
      (Nat.pow_le_pow_right (by norm_num) this)
  unfold clusterL
  omega

/-- At every relevant scale the facet budget is negligible compared with
the loss parameter. -/
theorem thirty_two_mul_facetBudget_le_clusterRho {t j : ℕ}
    (ht : 16 ≤ t) (hj : j ≤ clusterL t + 1) :
    32 * facetBudget t ≤ clusterRho t j := by
  have hK := facetBudget_le_two_pow_h_div_four ht
  have hhpos : 5 ≤ 2 * clusterH t := by
    rw [clusterH_eq_two_pow (by omega)]
    have : 5 ≤ 2 ^ (t - 2) := by
      have ht' : 4 ≤ t - 2 := by omega
      calc
        5 ≤ 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (t - 2) := Nat.pow_le_pow_right (by norm_num) ht'
    omega
  calc
    32 * facetBudget t ≤ 2 ^ 5 * 2 ^ (clusterH t / 4) := by
      norm_num
      gcongr
    _ = 2 ^ (5 + clusterH t / 4) := by rw [pow_add]
    _ ≤ 2 ^ (3 * clusterH t) := by
      apply Nat.pow_le_pow_right (by norm_num)
      omega
    _ ≤ clusterRho t j := two_pow_three_h_le_clusterRho ht hj

theorem clusterRho_le_dyadicB (t j : ℕ) :
    clusterRho t j ≤ dyadicB t := by
  unfold clusterRho dyadicB scaleExponent
  exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)

theorem clusterRho_lt_dyadicB {t j : ℕ} (ht : 16 ≤ t) :
    clusterRho t j < dyadicB t := by
  unfold clusterRho dyadicB scaleExponent
  apply Nat.pow_lt_pow_right (by norm_num)
  apply Nat.sub_lt (dyadicQ_pos t)
  positivity

theorem dyadicB_add_one_le_two_pow_q_add_one (t : ℕ) :
    dyadicB t + 1 ≤ 2 ^ (dyadicQ t + 1) := by
  rw [pow_succ, ← show dyadicB t = 2 ^ dyadicQ t by rfl]
  have := dyadicB_pos t
  omega

theorem two_mul_q_pow_four_le_dyadicB {t : ℕ} (ht : 16 ≤ t) :
    2 * dyadicQ t ^ 4 ≤ dyadicB t := by
  have hexp : 4 * t + 1 ≤ dyadicQ t := by
    have hlin := one_twenty_eight_mul_le_dyadicQ ht
    omega
  rw [dyadicB, q_pow_eq_two_pow]
  calc
    2 * 2 ^ (t * 4) = 2 ^ (t * 4 + 1) := by
      rw [pow_succ]
      ring
    _ ≤ 2 ^ dyadicQ t := by
      apply Nat.pow_le_pow_right (by norm_num)
      omega

/-- The a priori exceptional-set bound fits inside the `2^K`-symbol sparse
alphabet.  This is what turns stars-and-bars into a `(K+2)U`-bit estimate. -/
theorem exceptional_bound_le_two_pow_budget {t j : ℕ} (ht : 16 ≤ t) :
    facetBudget t * facetBudget t * (2 * clusterRho t j) ≤
      2 ^ facetBudget t := by
  have hK : facetBudget t ≤ dyadicQ t ^ 2 := facetBudget_le_q_sq t
  have hpoly : 2 * (facetBudget t * facetBudget t) ≤ dyadicB t := by
    calc
      2 * (facetBudget t * facetBudget t) ≤ 2 * dyadicQ t ^ 4 := by
        nlinarith
      _ ≤ dyadicB t := two_mul_q_pow_four_le_dyadicB ht
  have hrho := clusterRho_le_dyadicB t j
  have hsq : facetBudget t * facetBudget t * (2 * clusterRho t j) ≤
      dyadicB t * dyadicB t := by
    calc
      facetBudget t * facetBudget t * (2 * clusterRho t j) =
          (2 * (facetBudget t * facetBudget t)) * clusterRho t j := by ring
      _ ≤ dyadicB t * dyadicB t := Nat.mul_le_mul hpoly hrho
  have hpow : dyadicB t * dyadicB t = 2 ^ (2 * dyadicQ t) := by
    rw [dyadicB, ← pow_add]
    congr 1
    omega
  rw [hpow] at hsq
  exact hsq.trans (Nat.pow_le_pow_right (by norm_num) (two_mul_q_le_facetBudget ht))

theorem thirty_two_mul_q_pow_le_clusterRho {t j d : ℕ}
    (ht : 16 ≤ t) (hj : j ≤ clusterL t + 1) (hd : d ≤ 32) :
    32 * dyadicQ t ^ d ≤ clusterRho t j := by
  have hpoly := q_pow_le_two_pow_h ht hd
  have hexp : 5 + clusterH t ≤ 3 * clusterH t := by
    have hH : 3 ≤ clusterH t := by
      rw [clusterH_eq_two_pow (by omega)]
      have : 2 ≤ t - 2 := by omega
      exact (by norm_num : 3 ≤ 2 ^ 2).trans
        (Nat.pow_le_pow_right (by norm_num) this)
    omega
  calc
    32 * dyadicQ t ^ d ≤ 2 ^ 5 * 2 ^ clusterH t := by
      norm_num
      gcongr
    _ = 2 ^ (5 + clusterH t) := by rw [pow_add]
    _ ≤ 2 ^ (3 * clusterH t) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    _ ≤ clusterRho t j := two_pow_three_h_le_clusterRho ht hj

theorem thirty_two_mul_budget_pow_le_clusterRho {t j d : ℕ}
    (ht : 16 ≤ t) (hj : j ≤ clusterL t + 1) (hd : d ≤ 16) :
    32 * facetBudget t ^ d ≤ clusterRho t j := by
  have hpoly := budget_pow_le_two_pow_h ht hd
  have hexp : 5 + clusterH t ≤ 3 * clusterH t := by
    have hH : 3 ≤ clusterH t := by
      rw [clusterH_eq_two_pow (by omega)]
      have : 2 ≤ t - 2 := by omega
      exact (by norm_num : 3 ≤ 2 ^ 2).trans
        (Nat.pow_le_pow_right (by norm_num) this)
    omega
  calc
    32 * facetBudget t ^ d ≤ 2 ^ 5 * 2 ^ clusterH t := by
      norm_num
      gcongr
    _ = 2 ^ (5 + clusterH t) := by rw [pow_add]
    _ ≤ 2 ^ (3 * clusterH t) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    _ ≤ clusterRho t j := two_pow_three_h_le_clusterRho ht hj

/-- The global exceptional-set encoding cost from
`|U| ≤ 2 K² rho_(j+1)` occupies at most one thirty-second of the
coarser loss scale. -/
theorem exceptional_encoding_cost_le_clusterRho {t j u : ℕ}
    (ht : 16 ≤ t)
    (hj : t * (10 + 6 * (j + 1)) ≤ dyadicQ t)
    (hu : u ≤ facetBudget t * facetBudget t * (2 * clusterRho t (j + 1))) :
    32 * (facetBudget t * u) ≤ clusterRho t j := by
  have hu' : 32 * (facetBudget t * u) ≤
      64 * facetBudget t ^ 3 * clusterRho t (j + 1) := by
    calc
      32 * (facetBudget t * u) ≤
          32 * (facetBudget t *
            (facetBudget t * facetBudget t * (2 * clusterRho t (j + 1)))) := by
        gcongr
      _ = 64 * facetBudget t ^ 3 * clusterRho t (j + 1) := by ring
  calc
    32 * (facetBudget t * u) ≤
        64 * facetBudget t ^ 3 * clusterRho t (j + 1) := hu'
    _ ≤ dyadicQ t ^ 6 * clusterRho t (j + 1) := by
      gcongr
      exact sixty_four_mul_budget_cube_le_q_pow_six ht
    _ = clusterRho t j := (clusterRho_eq_q_pow_six_mul_succ hj).symm

/-- Version of the exceptional encoding estimate with the harmless `+2`
needed to bound `2^K + 1 + U` by `2^(K+2)`. -/
theorem exceptional_sparse_cost_le_clusterRho {t j u : ℕ}
    (ht : 16 ≤ t)
    (hj : t * (10 + 6 * (j + 1)) ≤ dyadicQ t)
    (hu : u ≤ facetBudget t * facetBudget t * (2 * clusterRho t (j + 1))) :
    16 * ((facetBudget t + 2) * u) ≤ clusterRho t j := by
  have hK : 2 ≤ facetBudget t :=
    (by have := two_mul_q_le_facetBudget ht; have := dyadicQ_pos t; omega)
  have hfactor : facetBudget t + 2 ≤ 2 * facetBudget t := by omega
  calc
    16 * ((facetBudget t + 2) * u) ≤
        32 * (facetBudget t * u) := by nlinarith
    _ ≤ clusterRho t j := exceptional_encoding_cost_le_clusterRho ht hj hu

theorem dyadicQ_add_one_le_two_pow_h_div_four_add_one {t : ℕ}
    (ht : 16 ≤ t) :
    dyadicQ t + 1 ≤ 2 ^ (clusterH t / 4 + 1) := by
  have hexp : t ≤ clusterH t / 4 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
    have h := thirty_two_mul_t_le_clusterH ht
    omega
  have hq : dyadicQ t ≤ 2 ^ (clusterH t / 4) := by
    rw [dyadicQ]
    exact Nat.pow_le_pow_right (by norm_num) hexp
  calc
    dyadicQ t + 1 ≤ 2 * dyadicQ t := by
      have := dyadicQ_pos t
      omega
    _ ≤ 2 * 2 ^ (clusterH t / 4) := by gcongr
    _ = 2 ^ (clusterH t / 4 + 1) := by
      rw [pow_succ]
      ring

theorem centerQueryBound_le_two_pow_two_h {t : ℕ} (ht : 16 ≤ t) :
    centerQueryBound t ≤ 2 ^ (2 * clusterH t) := by
  let A := clusterH t / 4
  have hK : facetBudget t ≤ 2 ^ A := by
    simpa [A] using facetBudget_le_two_pow_h_div_four ht
  have hJ : clusterJ t ≤ A := by
    simpa [A] using clusterJ_le_h_div_four ht
  have htermPos : 0 < 2 ^ A * 2 ^ clusterH t := by positivity
  have hexp : 2 * A + clusterH t + 1 ≤ 2 * clusterH t := by
    have hH : 2 ≤ clusterH t := by
      rw [clusterH_eq_two_pow (by omega)]
      have : 1 ≤ t - 2 := by omega
      exact (by norm_num : 2 ≤ 2 ^ 1).trans
        (Nat.pow_le_pow_right (by norm_num) this)
    dsimp [A]
    omega
  calc
    centerQueryBound t =
        2 ^ clusterJ t * (1 + facetBudget t * 2 ^ clusterH t) := rfl
    _ ≤ 2 ^ A * (1 + 2 ^ A * 2 ^ clusterH t) := by
      gcongr
      norm_num
    _ ≤ 2 ^ A * (2 * (2 ^ A * 2 ^ clusterH t)) := by
      gcongr
      omega
    _ = 2 ^ (2 * A + clusterH t + 1) := by
      simp only [pow_add]
      ring
    _ ≤ 2 ^ (2 * clusterH t) :=
      Nat.pow_le_pow_right (by norm_num) hexp

/-- Center transcripts occupy at most one thirty-second of every relevant
loss scale. -/
theorem center_transcript_cost_le_clusterRho {t j : ℕ}
    (ht : 16 ≤ t) (hj : j ≤ clusterL t + 1) :
    32 * centerTranscriptCost t ≤ clusterRho t j := by
  let H := clusterH t
  let A := H / 4
  have hq := dyadicQ_add_one_le_two_pow_h_div_four_add_one ht
  have hcenter := centerQueryBound_le_two_pow_two_h ht
  have hexp : 5 + (A + 1) + 2 * H ≤ 3 * H := by
    have hH : 8 ≤ H := by
      dsimp [H]
      rw [clusterH_eq_two_pow (by omega)]
      have : 3 ≤ t - 2 := by omega
      exact (by norm_num : 8 ≤ 2 ^ 3).trans
        (Nat.pow_le_pow_right (by norm_num) this)
    dsimp [A]
    omega
  calc
    32 * centerTranscriptCost t =
        32 * ((dyadicQ t + 1) * centerQueryBound t) := rfl
    _ ≤ 2 ^ 5 *
        (2 ^ (A + 1) * 2 ^ (2 * H)) := by
      norm_num
      dsimp [A, H] at hq hcenter ⊢
      gcongr
    _ = 2 ^ (5 + (A + 1) + 2 * H) := by
      simp only [pow_add]
      ring
    _ ≤ 2 ^ (3 * H) := Nat.pow_le_pow_right (by norm_num) hexp
    _ ≤ clusterRho t j := by
      simpa [H] using two_pow_three_h_le_clusterRho ht hj

/-! ## Combined state-counting costs -/

theorem clusterJ_le_facetBudget (t : ℕ) :
    clusterJ t ≤ facetBudget t := by
  exact Nat.div_le_self _ _

/-- Cardinality base for the discrete shape part of a cluster state. -/
theorem shape_base_le_two_pow_three_budget_sq {t : ℕ} (ht : 16 ≤ t) :
    (clusterJ t + 1) * (clusterJ t + 1) ^ facetBudget t *
        (facetBudget t + 1) ^ facetBudget t ≤
      2 ^ (3 * facetBudget t ^ 2) := by
  let K := facetBudget t
  let J := clusterJ t
  have hK : 1 ≤ K := by
    have hKpos := facetBudget_pos ht
    dsimp [K]
    omega
  have hJK : J ≤ K := by simpa [J, K] using clusterJ_le_facetBudget t
  have hbaseK : K + 1 ≤ 2 ^ K := K.lt_two_pow_self
  have hbaseJ : J + 1 ≤ 2 ^ K := (Nat.add_le_add_right hJK 1).trans hbaseK
  have hexp : K + K * K + K * K ≤ 3 * K ^ 2 := by
    nlinarith
  calc
    (clusterJ t + 1) * (clusterJ t + 1) ^ facetBudget t *
        (facetBudget t + 1) ^ facetBudget t =
        (J + 1) * (J + 1) ^ K * (K + 1) ^ K := by rfl
    _ ≤ 2 ^ K * (2 ^ K) ^ K * (2 ^ K) ^ K := by gcongr
    _ = 2 ^ (K + K * K + K * K) := by
      simp only [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (3 * K ^ 2) := Nat.pow_le_pow_right (by norm_num) hexp
    _ = 2 ^ (3 * facetBudget t ^ 2) := by rfl

/-- Cardinality base for the sparse exceptional-atom code. -/
theorem exception_base_le_two_pow_budget_add_two {t j u : ℕ}
    (ht : 16 ≤ t)
    (hu : u ≤
      facetBudget t * facetBudget t * (2 * clusterRho t (j + 1))) :
    2 ^ facetBudget t + 1 + u ≤ 2 ^ (facetBudget t + 2) := by
  have hu' : u ≤ 2 ^ facetBudget t :=
    hu.trans (exceptional_bound_le_two_pow_budget (t := t) (j := j + 1) ht)
  calc
    2 ^ facetBudget t + 1 + u ≤
        2 ^ facetBudget t + 1 + 2 ^ facetBudget t := by omega
    _ ≤ 4 * 2 ^ facetBudget t := by
      have := pow_pos (by omega : 0 < (2 : ℕ)) (facetBudget t)
      omega
    _ = 2 ^ (facetBudget t + 2) := by
      rw [pow_add]
      norm_num
      ring

/-- Cardinality base for the center-exponent transcript. -/
theorem center_base_le_two_pow_four_budget {t : ℕ} (ht : 16 ≤ t) :
    2 ^ (clusterJ t + facetBudget t) * (dyadicB t + 1) + 1 +
        centerQueryBound t ≤
      2 ^ (4 * facetBudget t) := by
  let K := facetBudget t
  let J := clusterJ t
  let H := clusterH t
  let M := centerQueryBound t
  have hK : 1 ≤ K := by
    have hKpos := facetBudget_pos ht
    dsimp [K]
    omega
  have hJK : J ≤ K := by simpa [J, K] using clusterJ_le_facetBudget t
  have hqK : dyadicQ t + 1 ≤ K := by
    have htwo := two_mul_q_le_facetBudget ht
    have hq := dyadicQ_pos t
    simpa [K] using (show dyadicQ t + 1 ≤ facetBudget t by omega)
  have hB : dyadicB t + 1 ≤ 2 ^ K := by
    exact (dyadicB_add_one_le_two_pow_q_add_one t).trans
      (Nat.pow_le_pow_right (by norm_num) hqK)
  have hHK : 2 * H ≤ K := by
    have htwo := two_mul_q_le_facetBudget ht
    have hfour := four_mul_clusterH (t := t) (by omega)
    dsimp [H, K]
    omega
  have hM : M ≤ 2 ^ K := by
    calc
      M ≤ 2 ^ (2 * H) := by
        simpa [M, H] using centerQueryBound_le_two_pow_two_h ht
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hHK
  have hfirst : 2 ^ (J + K) * (dyadicB t + 1) ≤ 2 ^ (3 * K) := by
    have hexpJK : J + K ≤ 2 * K := by omega
    have hpowJK : 2 ^ (J + K) ≤ 2 ^ (2 * K) :=
      Nat.pow_le_pow_right (by norm_num) hexpJK
    calc
      2 ^ (J + K) * (dyadicB t + 1) ≤ 2 ^ (2 * K) * 2 ^ K := by
        exact Nat.mul_le_mul hpowJK hB
      _ = 2 ^ (3 * K) := by
        rw [← pow_add]
        congr 1
        omega
  have hsmall : 1 + M ≤ 2 ^ (3 * K) := by
    have hpos : 0 < 2 ^ K := by positivity
    calc
      1 + M ≤ 2 * 2 ^ K := by omega
      _ = 2 ^ (K + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (3 * K) := by
        apply Nat.pow_le_pow_right (by norm_num)
        omega
  have hexp : 3 * K + 1 ≤ 4 * K := by omega
  change 2 ^ (J + K) * (dyadicB t + 1) + 1 + M ≤ 2 ^ (4 * K)
  calc
    2 ^ (J + K) * (dyadicB t + 1) + 1 + M =
        2 ^ (J + K) * (dyadicB t + 1) + (1 + M) := by omega
    _ ≤ 2 ^ (3 * K) + 2 ^ (3 * K) := Nat.add_le_add hfirst hsmall
    _ = 2 ^ (3 * K + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ (4 * K) := Nat.pow_le_pow_right (by norm_num) hexp
    _ = 2 ^ (4 * facetBudget t) := by rfl

/-- The graph/cluster bookkeeping and all center-query data together occupy
at most one thirty-second of a relevant loss scale.  The deliberately loose
constants match the finite-state count used by the obstruction proof. -/
theorem state_center_cost_le_clusterRho {t j : ℕ}
    (ht : 16 ≤ t) (hj : j ≤ clusterL t + 1) :
    32 *
        (4 * facetBudget t * centerQueryBound t +
          3 * facetBudget t ^ 2) ≤
      clusterRho t j := by
  let H := clusterH t
  let A := H / 4
  let K := facetBudget t
  let M := centerQueryBound t
  have hK : K ≤ 2 ^ A := by
    simpa [K, A, H] using facetBudget_le_two_pow_h_div_four ht
  have hM : M ≤ 2 ^ (2 * H) := by
    simpa [M, H] using centerQueryBound_le_two_pow_two_h ht
  have hKM : K ≤ M := by
    dsimp [K, M, centerQueryBound]
    have hpow : 0 < 2 ^ clusterH t := by positivity
    have hleft : facetBudget t ≤
        1 + facetBudget t * 2 ^ clusterH t := by
      nlinarith
    exact hleft.trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hsum :
      4 * K * M + 3 * K ^ 2 ≤ 8 * K * M := by
    nlinarith
  have hexp : 8 + A + 2 * H ≤ 3 * H := by
    have hH : 11 ≤ H := by
      dsimp [H]
      rw [clusterH_eq_two_pow (by omega)]
      have : 4 ≤ t - 2 := by omega
      exact (by norm_num : 11 ≤ 2 ^ 4).trans
        (Nat.pow_le_pow_right (by norm_num) this)
    dsimp [A]
    omega
  calc
    32 *
        (4 * facetBudget t * centerQueryBound t +
          3 * facetBudget t ^ 2) =
        32 * (4 * K * M + 3 * K ^ 2) := by rfl
    _ ≤ 32 * (8 * K * M) := by gcongr
    _ = 2 ^ 8 * K * M := by ring
    _ ≤ 2 ^ 8 * 2 ^ A * 2 ^ (2 * H) := by gcongr
    _ = 2 ^ (8 + A + 2 * H) := by
      simp only [pow_add]
    _ ≤ 2 ^ (3 * H) := Nat.pow_le_pow_right (by norm_num) hexp
    _ ≤ clusterRho t j := by
      simpa [H] using two_pow_three_h_le_clusterRho ht hj

/-- One inequality containing every profile-state exponent used in the
finite union bound: graph/cluster data, sparse exceptional atoms, and center
transcripts. -/
theorem combined_state_cost_le_clusterRho {t j u : ℕ}
    (ht : 16 ≤ t) (hj : j + 1 ≤ clusterL t + 1)
    (hu : u ≤
      facetBudget t * facetBudget t * (2 * clusterRho t (j + 1))) :
    8 *
        (3 * facetBudget t ^ 2 +
          (facetBudget t + 2) * u +
          4 * facetBudget t * centerQueryBound t) ≤
      clusterRho t j := by
  have hj' : j ≤ clusterL t + 1 := by omega
  have hcenter := state_center_cost_le_clusterRho ht hj'
  have hsparse := exceptional_sparse_cost_le_clusterRho ht
    (relevant_scale_cost_le_q ht hj) hu
  omega

/-! ## Final image-cardinality ledger -/

/-- The external union over a coordinate count and a stable gap costs at
most `2^(2K)`. -/
theorem strata_prefactor_le_two_pow_two_budget (t : ℕ) :
    (facetBudget t + 1) * (clusterJ t + 1) ≤
      2 ^ (2 * facetBudget t) := by
  let K := facetBudget t
  let J := clusterJ t
  have hJK : J ≤ K := by simpa [J, K] using clusterJ_le_facetBudget t
  have hbase : K + 1 ≤ 2 ^ K := K.lt_two_pow_self
  calc
    (facetBudget t + 1) * (clusterJ t + 1) = (K + 1) * (J + 1) := by rfl
    _ ≤ 2 ^ K * 2 ^ K := by
      exact Nat.mul_le_mul hbase ((Nat.add_le_add_right hJK 1).trans hbase)
    _ = 2 ^ (2 * K) := by
      rw [← pow_add]
      congr 1
      omega
    _ = 2 ^ (2 * facetBudget t) := by rfl

/-- The diameter contribution `D+1` is absorbed by two extra binary
exponent units. -/
theorem tail_diameter_succ_le_two_pow (t j : ℕ) :
    2 *
          (2 ^ facetBudget t *
            2 ^ (dyadicB t - clusterRho t j)) + 1 ≤
      2 ^ (dyadicB t - clusterRho t j + facetBudget t + 2) := by
  let X := 2 ^ facetBudget t * 2 ^ (dyadicB t - clusterRho t j)
  have hX : 0 < X := by positivity
  calc
    2 *
          (2 ^ facetBudget t *
            2 ^ (dyadicB t - clusterRho t j)) + 1 = 2 * X + 1 := by rfl
    _ ≤ 4 * X := by omega
    _ = 2 ^ (dyadicB t - clusterRho t j + facetBudget t + 2) := by
      dsimp [X]
      simp only [pow_add]
      ring

/-- After paying for all states, fibers, coordinate counts, and gaps, the
remaining exponent still saves at least half of the selected loss scale. -/
theorem total_image_exponent_le_sub_half_rho {t j : ℕ}
    (ht : 16 ≤ t) (hj : j + 1 ≤ clusterL t + 1) :
    let U := facetBudget t * facetBudget t * (2 * clusterRho t (j + 1))
    let E := 3 * facetBudget t ^ 2 +
      (facetBudget t + 2) * U +
      4 * facetBudget t * centerQueryBound t
    dyadicB t - clusterRho t j + E + 3 * facetBudget t + 2 ≤
      dyadicB t - clusterRho t j / 2 := by
  dsimp only
  have hE := combined_state_cost_le_clusterRho ht hj
    (u := facetBudget t * facetBudget t * (2 * clusterRho t (j + 1))) le_rfl
  have hj' : j ≤ clusterL t + 1 := by omega
  have hK := thirty_two_mul_facetBudget_le_clusterRho ht hj'
  have hKtwo : 2 ≤ facetBudget t := by
    have hq := dyadicQ_pos t
    have htwo := two_mul_q_le_facetBudget ht
    omega
  have hsixtyFour : 64 ≤ clusterRho t j := by
    exact (Nat.mul_le_mul_left 32 hKtwo).trans hK
  have hrhoB := clusterRho_le_dyadicB t j
  omega

theorem total_image_exponent_le_B_sub_two {t j : ℕ}
    (ht : 16 ≤ t) (hj : j + 1 ≤ clusterL t + 1) :
    let U := facetBudget t * facetBudget t * (2 * clusterRho t (j + 1))
    let E := 3 * facetBudget t ^ 2 +
      (facetBudget t + 2) * U +
      4 * facetBudget t * centerQueryBound t
    dyadicB t - clusterRho t j + E + 3 * facetBudget t + 2 ≤
      dyadicB t - 2 := by
  dsimp only
  have hhalf := total_image_exponent_le_sub_half_rho ht hj
  dsimp only at hhalf
  have hj' : j ≤ clusterL t + 1 := by omega
  have hK := thirty_two_mul_facetBudget_le_clusterRho ht hj'
  have hKtwo : 2 ≤ facetBudget t := by
    have hq := dyadicQ_pos t
    have htwo := two_mul_q_le_facetBudget ht
    omega
  have hsixtyFour : 64 ≤ clusterRho t j :=
    (Nat.mul_le_mul_left 32 hKtwo).trans hK
  omega

theorem two_le_dyadicB (t : ℕ) : 2 ≤ dyadicB t := by
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ dyadicQ t :=
      Nat.pow_le_pow_right (by norm_num) (dyadicQ_pos t)
    _ = dyadicB t := by rfl

theorem two_pow_B_sub_two_lt_two_pow_B_sub_one (t : ℕ) :
    2 ^ (dyadicB t - 2) < 2 ^ (dyadicB t - 1) := by
  apply Nat.pow_lt_pow_right (by norm_num)
  have hB := two_le_dyadicB t
  omega

/-- The isolated zero-coordinate profile can be added after padding all
positive coordinate counts to the full facet budget, without filling the
upper dyadic half. -/
theorem two_pow_B_sub_two_add_one_lt_two_pow_B_sub_one {t : ℕ}
    (ht : 1 ≤ t) :
    2 ^ (dyadicB t - 2) + 1 < 2 ^ (dyadicB t - 1) := by
  have hq : 2 ≤ dyadicQ t := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
      _ = dyadicQ t := by rfl
  have hB : 3 ≤ dyadicB t := by
    calc
      3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ dyadicQ t :=
        Nat.pow_le_pow_right (by norm_num) hq
      _ = dyadicB t := by rfl
  have hpow : 1 < 2 ^ (dyadicB t - 2) :=
    Nat.one_lt_pow (by omega) (by omega)
  calc
    2 ^ (dyadicB t - 2) + 1 <
        2 ^ (dyadicB t - 2) + 2 ^ (dyadicB t - 2) := by omega
    _ = 2 ^ (dyadicB t - 1) := by
      rw [show dyadicB t - 1 = (dyadicB t - 2) + 1 by omega, pow_succ]
      ring

end AntichainOfGivenSize.ClusterParameters
