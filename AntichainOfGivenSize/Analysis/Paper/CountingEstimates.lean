import AntichainOfGivenSize.Analysis.Paper.GeneralCounting

/-!
# Finite arithmetic for arbitrary load bounds

Here `b` is an integer lower approximation to `log₂ B`, and `t` is an
integer upper approximation to `log₂ b`. Unlike the older dyadic ledger,
`b` and `B` are unrestricted integers satisfying the displayed inequalities.
-/

namespace AntichainOfGivenSize.Paper.CountingEstimates

open ClusterLowerBound

def budget (b t : ℕ) : ℕ := b ^ 2 / (80 * t)
def clusterSize (b : ℕ) : ℕ := b / 4
def packingBound (b t : ℕ) : ℕ := budget b t / clusterSize b
def loss (b t j : ℕ) : ℕ := 2 ^ (b - 6 * t * j)
def saving (b : ℕ) : ℕ := 2 ^ (b / 2 + 1)
def centerBound (b t : ℕ) : ℕ :=
  2 ^ packingBound b t * (1 + budget b t * 2 ^ clusterSize b)

variable {b t : ℕ}

theorem clusterSize_pos (ht : 16 ≤ t) (hb : 4096 * t ≤ b) :
    0 < clusterSize b := by
  apply Nat.div_pos <;> omega

theorem clusterSize_bounds (ht : 16 ≤ t) (hb : 4096 * t ≤ b) :
    4 * clusterSize b ≤ b ∧ b ≤ 5 * clusterSize b := by
  have hh : 3 ≤ clusterSize b := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
    omega
  have hdiv := Nat.div_add_mod b 4
  have hmod := Nat.mod_lt b (by norm_num : 0 < 4)
  dsimp [clusterSize] at *
  omega

theorem budget_mul_le : 80 * t * budget b t ≤ b ^ 2 :=
  Nat.mul_div_le _ _

theorem two_mul_b_le_budget (ht : 16 ≤ t) (hb : 4096 * t ≤ b) :
    2 * b ≤ budget b t := by
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 80 * t)).2
  have h := Nat.mul_le_mul_right b hb
  nlinarith

theorem budget_pos (ht : 16 ≤ t) (hb : 4096 * t ≤ b) :
    0 < budget b t := by
  have h := two_mul_b_le_budget ht hb
  omega

theorem packing_scale_le (ht : 16 ≤ t) (hb : 4096 * t ≤ b) :
    16 * t * packingBound b t ≤ b := by
  have hh := clusterSize_pos ht hb
  have hbh := (clusterSize_bounds ht hb).2
  have hpack : packingBound b t * clusterSize b ≤ budget b t :=
    Nat.div_mul_le_self _ _
  have hprod : (80 * t * packingBound b t) * clusterSize b ≤
      (5 * b) * clusterSize b := by
    have h₁ := (Nat.mul_le_mul_left (80 * t) hpack).trans
      (budget_mul_le (b := b) (t := t))
    have h₂ := Nat.mul_le_mul_left b hbh
    nlinarith
  have hcancel := le_of_mul_le_mul_right hprod hh
  nlinarith

theorem fine_scale_cost_le_half (ht : 16 ≤ t) (hb : 4096 * t ≤ b) :
    6 * t * (packingBound b t + 1) ≤ b / 2 := by
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
  have hp := packing_scale_le ht hb
  nlinarith

theorem center_exponent_le_half (ht : 16 ≤ t) (hb : 4096 * t ≤ b) :
    packingBound b t + clusterSize b + 4 * t + 8 ≤ b / 2 := by
  have hp := packing_scale_le ht hb
  have hJ : 8 * packingBound b t ≤ b := by
    have := Nat.mul_le_mul_right (packingBound b t)
      (show 8 ≤ 16 * t by omega)
    omega
  have hh := (clusterSize_bounds ht hb).1
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
  omega

theorem small_exponent_le_half (ht : 16 ≤ t) (hb : 4096 * t ≤ b) :
    2 * t + 4 ≤ b / 2 := by
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
  omega

theorem budget_le_power (hbt : b < 2 ^ t) : budget b t ≤ 2 ^ (2 * t) := by
  calc
    budget b t ≤ b ^ 2 := Nat.div_le_self _ _
    _ ≤ (2 ^ t) ^ 2 := Nat.pow_le_pow_left hbt.le 2
    _ = 2 ^ (2 * t) := by rw [← pow_mul]; congr 1; omega

theorem four_budget_le_power (ht : 16 ≤ t) (hbt : b < 2 ^ t) :
    4 * budget b t ≤ 2 ^ (2 * t) := by
  calc
    4 * budget b t ≤ 80 * t * budget b t :=
      Nat.mul_le_mul_right _ (by omega)
    _ ≤ b ^ 2 := budget_mul_le
    _ ≤ (2 ^ t) ^ 2 := Nat.pow_le_pow_left hbt.le 2
    _ = 2 ^ (2 * t) := by rw [← pow_mul]; congr 1; omega

theorem budget_cube_le_power (ht : 16 ≤ t) (hbt : b < 2 ^ t) :
    64 * budget b t ^ 3 ≤ 2 ^ (6 * t) := by
  calc
    64 * budget b t ^ 3 = (4 * budget b t) ^ 3 := by ring
    _ ≤ (2 ^ (2 * t)) ^ 3 := Nat.pow_le_pow_left (four_budget_le_power ht hbt) 3
    _ = 2 ^ (6 * t) := by rw [← pow_mul]; congr 1; omega

theorem loss_antitone (b t : ℕ) : Antitone (loss b t) := by
  intro i j hij
  apply Nat.pow_le_pow_right (by norm_num)
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_left (6 * t) hij) b

theorem loss_le_two_pow (b t j : ℕ) : loss b t j ≤ 2 ^ b := by
  apply Nat.pow_le_pow_right (by norm_num)
  exact Nat.sub_le _ _

theorem loss_step {j : ℕ} (ht : 16 ≤ t) (hb : 4096 * t ≤ b)
    (hj : j ≤ packingBound b t) :
    loss b t j = 2 ^ (6 * t) * loss b t (j + 1) := by
  have hf := (Nat.mul_le_mul_left (6 * t)
    (Nat.add_le_add_right hj 1)).trans (fine_scale_cost_le_half ht hb)
  have hexp : b - 6 * t * j = 6 * t + (b - 6 * t * (j + 1)) := by
    have heq : 6 * t * (j + 1) = 6 * t * j + 6 * t := by ring
    omega
  simp only [loss, hexp, pow_add]

theorem loss_ge_half_power {j : ℕ} (ht : 16 ≤ t) (hb : 4096 * t ≤ b)
    (hj : j ≤ packingBound b t) :
    2 ^ (b / 2 + 2) ≤ loss b t j := by
  have hf := (Nat.mul_le_mul_left (6 * t)
    (Nat.add_le_add_right hj 1)).trans (fine_scale_cost_le_half ht hb)
  apply Nat.pow_le_pow_right (by norm_num)
  have heq : 6 * t * (j + 1) = 6 * t * j + 6 * t := by ring
  omega

theorem centerBound_le_power (hbt : b < 2 ^ t) :
    centerBound b t ≤ 2 ^ (packingBound b t + clusterSize b + 2 * t + 1) := by
  have hK := budget_le_power hbt
  have hpow : 1 ≤ 2 ^ clusterSize b := Nat.one_le_two_pow
  have hpos : 1 ≤ 2 ^ (2 * t) := Nat.one_le_two_pow
  calc
    centerBound b t ≤
        2 ^ packingBound b t * (2 ^ (2 * t + 1) * 2 ^ clusterSize b) := by
      unfold centerBound
      apply Nat.mul_le_mul_left
      have hmul := Nat.mul_le_mul_right (2 ^ clusterSize b) hK
      rw [pow_add]
      norm_num
      nlinarith
    _ = 2 ^ (packingBound b t + clusterSize b + 2 * t + 1) := by
      simp only [← pow_add]
      congr 1
      omega

theorem centerBound_le_budget_power (ht : 16 ≤ t) (hb : 4096 * t ≤ b)
    (hbt : b < 2 ^ t) : centerBound b t ≤ 2 ^ budget b t := by
  apply (centerBound_le_power hbt).trans
  apply Nat.pow_le_pow_right (by norm_num)
  have hc := center_exponent_le_half ht hb
  have hK := two_mul_b_le_budget ht hb
  omega

theorem sixteen_center_cost_le_half_power (ht : 16 ≤ t) (hb : 4096 * t ≤ b)
    (hbt : b < 2 ^ t) :
    16 * (3 * budget b t ^ 2 + 4 * budget b t * centerBound b t) ≤ 2 ^ (b / 2) := by
  let e := packingBound b t + clusterSize b + 4 * t + 3
  have hK := budget_le_power hbt
  have hM := centerBound_le_power hbt
  have hshape : 3 * budget b t ^ 2 ≤ 2 ^ e := by
    calc
      3 * budget b t ^ 2 ≤ 2 ^ 2 * (2 ^ (2 * t)) ^ 2 := by
        apply Nat.mul_le_mul (by norm_num)
        exact Nat.pow_le_pow_left hK 2
      _ = 2 ^ (4 * t + 2) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by dsimp [e]; omega)
  have hcenter : 4 * budget b t * centerBound b t ≤ 2 ^ e := by
    calc
      4 * budget b t * centerBound b t ≤
          2 ^ 2 * 2 ^ (2 * t) *
            2 ^ (packingBound b t + clusterSize b + 2 * t + 1) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hK) hM
      _ = 2 ^ e := by
        simp only [← pow_add]
        congr 1
        dsimp [e]
        omega
  calc
    16 * (3 * budget b t ^ 2 + 4 * budget b t * centerBound b t) ≤
        2 ^ 5 * 2 ^ e := by norm_num; omega
    _ = 2 ^ (packingBound b t + clusterSize b + 4 * t + 8) := by
      rw [← pow_add]
      congr 1
      dsimp [e]
      omega
    _ ≤ 2 ^ (b / 2) :=
      Nat.pow_le_pow_right (by norm_num) (center_exponent_le_half ht hb)

theorem sixteen_exception_cost_le_loss {j : ℕ}
    (ht : 16 ≤ t) (hb : 4096 * t ≤ b) (hbt : b < 2 ^ t)
    (hj : j ≤ packingBound b t) :
    16 * ((budget b t + 2) *
      (budget b t * budget b t * (2 * loss b t (j + 1)))) ≤ loss b t j := by
  have hK : 2 ≤ budget b t := by
    have := two_mul_b_le_budget ht hb
    omega
  calc
    16 * ((budget b t + 2) *
        (budget b t * budget b t * (2 * loss b t (j + 1)))) ≤
        16 * ((2 * budget b t) *
          (budget b t * budget b t * (2 * loss b t (j + 1)))) := by
      gcongr
      omega
    _ = (64 * budget b t ^ 3) * loss b t (j + 1) := by ring
    _ ≤ 2 ^ (6 * t) * loss b t (j + 1) :=
      Nat.mul_le_mul_right _ (budget_cube_le_power ht hbt)
    _ = loss b t j := (loss_step ht hb hj).symm

/-- Instantiate the general combinatorial setup with integral power-of-two
losses, without restricting the load bound to a dyadic subsequence. -/
def setup (B b t : ℕ) (ht : 16 ≤ t) (hb : 4096 * t ≤ b) :
    CountingSetup (budget b t) B where
  h := clusterSize b
  J := packingBound b t
  h_pos := clusterSize_pos ht hb
  cover := by
    simpa [packingBound, Nat.mul_comm] using
      Nat.lt_mul_div_succ (budget b t) (clusterSize_pos ht hb)
  rho := fun j ↦ loss b t j
  rho_antitone := fun _i _j hij ↦ loss_antitone b t hij

theorem setup_centerBudget (B b t : ℕ) (ht hb) :
    (setup B b t ht hb).centerBudget = centerBound b t := rfl

/-- Finite uniform counting at the auxiliary full budget. -/
theorem counting_card_le {B b t : ℕ}
    (ht : 16 ≤ t) (hb : 4096 * t ≤ b) (hbt : b < 2 ^ t)
    (hBlo : 2 ^ b ≤ B) (hBhi : B < 2 ^ (b + 1)) :
    (attainableValues B (budget b t)).card ≤ 2 ^ (B - saving b) := by
  let P := setup B b t ht hb
  have hKpos := budget_pos ht hb
  have hKlarge := two_mul_b_le_budget ht hb
  have hKpow := budget_le_power hbt
  have hJ : packingBound b t ≤ budget b t := Nat.div_le_self _ _
  apply P.boundedValues_card_le_two_pow (saving b)
  · exact counting_shape_base_le hJ
  · intro j
    apply counting_exception_base_le
    change budget b t * budget b t * (2 * loss b t (j.val + 1)) ≤ 2 ^ budget b t
    calc
      budget b t * budget b t * (2 * loss b t (j.val + 1)) ≤
          2 ^ (2 * t) * 2 ^ (2 * t) * (2 * 2 ^ b) := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul hKpow hKpow)
          (Nat.mul_le_mul_left 2 (loss_le_two_pow b t _))
      _ = 2 ^ (b + 4 * t + 1) := by
        simp only [pow_add]
        ring
      _ ≤ 2 ^ budget b t := by
        apply Nat.pow_le_pow_right (by norm_num)
        omega
  · apply counting_center_base_le hKpos hJ
    · calc
        B + 1 ≤ 2 ^ (b + 1) := hBhi
        _ ≤ 2 ^ budget b t := Nat.pow_le_pow_right (by norm_num) (by omega)
    · exact centerBound_le_budget_power ht hb hbt
  · exact (Nat.add_le_add_right hJ 1).trans (Nat.succ_le_of_lt (budget b t).lt_two_pow_self)
  · intro j
    have hj : j.val ≤ packingBound b t := by
      have := j.isLt
      change j.val < packingBound b t + 1 at this
      omega
    have hlower := loss_ge_half_power ht hb hj
    have hhalf : 2 ^ (b / 2) ≤ loss b t j.val :=
      (Nat.pow_le_pow_right (by norm_num) (by omega : b / 2 ≤ b / 2 + 2)).trans hlower
    have hcenter := (sixteen_center_cost_le_half_power ht hb hbt).trans hhalf
    have hexc := sixteen_exception_cost_le_loss ht hb hbt hj
    have hstate : 4 * P.stateCost j ≤ loss b t j.val := by
      change 4 * (3 * budget b t ^ 2 + (budget b t + 2) *
        (budget b t * budget b t * (2 * loss b t (j.val + 1))) +
          4 * budget b t * centerBound b t) ≤ loss b t j.val
      omega
    have hsmall : 8 * (budget b t + 1) ≤ loss b t j.val := by
      calc
        8 * (budget b t + 1) ≤ 2 ^ (2 * t + 4) := by
          rw [pow_add]
          have hp : 1 ≤ 2 ^ (2 * t) := Nat.one_le_two_pow
          norm_num
          omega
        _ ≤ 2 ^ (b / 2) := Nat.pow_le_pow_right (by norm_num) (small_exponent_le_half ht hb)
        _ ≤ loss b t j.val := hhalf
    have hs : 2 * saving b ≤ loss b t j.val := by
      calc
        2 * saving b = 2 ^ (b / 2 + 2) := by simp [saving, pow_add]; ring
        _ ≤ loss b t j.val := hlower
    exact counting_exponent_absorption
      ((loss_le_two_pow b t j.val).trans hBlo) hstate hsmall hs

end AntichainOfGivenSize.Paper.CountingEstimates
