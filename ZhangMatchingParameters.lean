import ZhangLemma68

namespace Zhang

/-- Number of stages used by the repaired block construction. -/
def stageCount (N l : ℕ) : ℕ := (N - 4 * l ^ 2) / (l + 2)

/-- Number of residue bits fixed by all stages. -/
def matchingBits (N l : ℕ) : ℕ := stageCount N l * l

theorem stageCount_mul_le (N l : ℕ) :
    stageCount N l * (l + 2) ≤ N - 4 * l ^ 2 := by
  exact Nat.div_mul_le_self _ _

theorem matchingBits_le (N l : ℕ) : matchingBits N l ≤ N := by
  calc
    matchingBits N l ≤ stageCount N l * (l + 2) := by
      unfold matchingBits
      exact Nat.mul_le_mul_left _ (by omega)
    _ ≤ N - 4 * l ^ 2 := stageCount_mul_le N l
    _ ≤ N := Nat.sub_le _ _

theorem remainderExponent_le
    {N l : ℕ} (hsmall : 4 * l ^ 2 ≤ N) :
    N + 1 - matchingBits N l ≤
      2 * stageCount N l + 4 * l ^ 2 + l + 2 := by
  let H := stageCount N l
  let X := N - 4 * l ^ 2
  have hN : N = X + 4 * l ^ 2 := by
    dsimp [X]
    omega
  have hdiv : X < (H + 1) * (l + 2) := by
    dsimp [H, X, stageCount]
    apply Nat.lt_mul_of_div_lt
    all_goals omega
  have hX : X ≤ H * (l + 2) + l + 1 := by
    have hX' : X < H * (l + 2) + l + 2 := by
      calc
        X < (H + 1) * (l + 2) := hdiv
        _ = H * (l + 2) + l + 2 := by ring
    omega
  dsimp [matchingBits]
  change N + 1 - H * l ≤ 2 * H + 4 * l ^ 2 + l + 2
  rw [hN]
  rw [Nat.sub_le_iff_le_add]
  ring_nf at hX ⊢
  omega

theorem four_mul_le_two_pow {l : ℕ} (hl : 4 ≤ l) : 4 * l ≤ 2 ^ l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
      rw [pow_succ]
      omega

theorem generatorCount_le_two_pow
    {r l : ℕ} (hr : r ≤ l) (hl : 4 ≤ l) :
    2 * r + 2 * l ≤ 2 ^ l := by
  calc
    2 * r + 2 * l ≤ 4 * l := by omega
    _ ≤ 2 ^ l := four_mul_le_two_pow hl

theorem universeSize_le
    {H r l : ℕ} (hr : r ≤ l) :
    l * (H - 1) + l * r + l ^ 2 + H ≤ H * l + 2 * l ^ 2 + H := by
  have hfirst : l * (H - 1) ≤ l * H := Nat.mul_le_mul_left l (Nat.sub_le H 1)
  calc
    l * (H - 1) + l * r + l ^ 2 + H ≤ l * H + l * l + l ^ 2 + H := by
      gcongr
    _ = H * l + 2 * l ^ 2 + H := by ring

theorem constructionExponent_lt
    {N l : ℕ} (hl : 1 ≤ l) (hsmall : 4 * l ^ 2 ≤ N) :
    stageCount N l * l + 2 * l ^ 2 + stageCount N l + l < N := by
  let H := stageCount N l
  let X := N - 4 * l ^ 2
  have hN : N = X + 4 * l ^ 2 := by
    dsimp [X]
    omega
  have hHX : H * (l + 2) ≤ X := by
    simpa [H, X] using stageCount_mul_le N l
  change H * l + 2 * l ^ 2 + H + l < N
  rw [hN]
  have hlquad : l + 1 ≤ 2 * l ^ 2 := by nlinarith
  nlinarith

theorem familyCard_lt_two_pow
    {N H r l S : ℕ}
    (hr : r ≤ l) (hl4 : 4 ≤ l)
    (hS : S ≤ H * l + 2 * l ^ 2 + H)
    (hexp : H * l + 2 * l ^ 2 + H + l < N) :
    (2 * r + 2 * l) * 2 ^ S < 2 ^ N := by
  calc
    (2 * r + 2 * l) * 2 ^ S ≤ 2 ^ l * 2 ^ S := by
      gcongr
      exact generatorCount_le_two_pow hr hl4
    _ = 2 ^ (l + S) := (pow_add 2 l S).symm
    _ ≤ 2 ^ (l + (H * l + 2 * l ^ 2 + H)) := by
      gcongr
      norm_num
    _ < 2 ^ N := by
      apply Nat.pow_lt_pow_right (by omega)
      omega

/-- A concrete exponential estimate used to make the stage count nonzero. -/
theorem four_sq_le_two_pow_pred {l : ℕ} (hl : 10 ≤ l) :
    4 * l ^ 2 ≤ 2 ^ (l - 1) := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
      have he : l + 1 - 1 = (l - 1) + 1 := by omega
      rw [he, pow_succ]
      have hinc : 4 * (l + 1) ^ 2 ≤ 2 * (4 * l ^ 2) := by nlinarith
      calc
        4 * (l + 1) ^ 2 ≤ 2 * (4 * l ^ 2) := hinc
        _ ≤ 2 * 2 ^ (l - 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (l - 1) * 2 := by ring

/-- The polynomial part of the quotient exponent is below half of `2^q`. -/
theorem remainderPolynomial_lt_two_pow_sub_two {l : ℕ} (hl : 16 ≤ l) :
    4 * l ^ 2 + l + 2 < 2 ^ (l - 2) := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
      have he : l + 1 - 2 = (l - 2) + 1 := by omega
      rw [he, pow_succ]
      have hinc : 4 * (l + 1) ^ 2 + (l + 1) + 2 <
          2 * (4 * l ^ 2 + l + 2) := by nlinarith
      calc
        4 * (l + 1) ^ 2 + (l + 1) + 2 <
            2 * (4 * l ^ 2 + l + 2) := hinc
        _ ≤ 2 * 2 ^ (l - 2) := Nat.mul_le_mul_left 2 ih.le
        _ = 2 ^ (l - 2) * 2 := by ring

end Zhang

namespace ZhangImprovedBound

/-- The block exponent used by the repaired construction:
`l=⌈q⌉`, `H=(N-4l²)/(l+2)`, and `B=Hl`. -/
noncomputable def constructionBits (q : ℝ) (n : ℕ) : ℕ :=
  Zhang.matchingBits (binaryLog n) ⌈q⌉₊

/-- The repaired block exponent satisfies the complete numerical contract of
Lemma 6.8, uniformly for `q ≥ 16` in the `C₀=10` wide range. -/
theorem constructionBits_remainderBitBound :
    RemainderBitBoundAbove 10 16 constructionBits := by
  intro q hq n hrange
  let N : ℕ := binaryLog n
  let l : ℕ := ⌈q⌉₊
  let H : ℕ := Zhang.stageCount N l
  have hq0 : 0 ≤ q := by linarith
  have hqpos : 0 < q := by linarith
  have hql : q ≤ (l : ℝ) := by
    simpa [l] using (Nat.le_ceil q)
  have hlq : (l : ℝ) < q + 1 := by
    simpa [l] using (Nat.ceil_lt_add_one hq0)
  have hl16 : 16 ≤ l := by
    have : (16 : ℝ) ≤ (l : ℝ) := hq.trans hql
    exact_mod_cast this
  have hlpos : 0 < l := by omega
  have hbitsle : constructionBits q n ≤ binaryLog n := by
    simpa [constructionBits, N, l] using Zhang.matchingBits_le N l
  refine ⟨hbitsle, ?_⟩
  have hlogN : Real.logb 2 (n : ℝ) < (N : ℝ) + 1 := by
    have hfloor := Nat.lt_floor_add_one (Real.logb 2 (n : ℝ))
    have heq : ⌊Real.logb 2 (n : ℝ)⌋₊ = N := by
      simpa [N, binaryLog] using Real.natFloor_logb_natCast 2 n
    rw [heq] at hfloor
    exact hfloor
  have hpowsmall : 4 * l ^ 2 ≤ 2 ^ (l - 1) :=
    Zhang.four_sq_le_two_pow_pred (by omega)
  have hexpSmall : ((l - 1 : ℕ) : ℝ) < q := by
    rw [Nat.cast_sub (by omega)]
    norm_num
    linarith
  have hrpowSmall := Real.rpow_lt_rpow_of_exponent_lt one_lt_two hexpSmall
  have hsmallReal : ((4 * l ^ 2 : ℕ) : ℝ) < (2 : ℝ) ^ q := by
    calc
      ((4 * l ^ 2 : ℕ) : ℝ) ≤ ((2 ^ (l - 1) : ℕ) : ℝ) := by
        exact_mod_cast hpowsmall
      _ = (2 : ℝ) ^ ((l - 1 : ℕ) : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ < (2 : ℝ) ^ q := hrpowSmall
  have hsmall : 4 * l ^ 2 ≤ N := by
    have hreal : ((4 * l ^ 2 : ℕ) : ℝ) < (N : ℝ) + 1 :=
      (hsmallReal.trans_le hrange.1).trans hlogN
    have hnat : 4 * l ^ 2 < N + 1 := by
      exact_mod_cast hreal
    omega
  have hHlNat : H * l ≤ N := by
    calc
      H * l ≤ H * (l + 2) := by gcongr; omega
      _ ≤ N - 4 * l ^ 2 := by
        simpa [H] using Zhang.stageCount_mul_le N l
      _ ≤ N := Nat.sub_le _ _
  have hHq : (H : ℝ) * q ≤ (N : ℝ) := by
    calc
      (H : ℝ) * q ≤ (H : ℝ) * (l : ℝ) := by gcongr
      _ ≤ (N : ℝ) := by exact_mod_cast hHlNat
  have hHle : (H : ℝ) ≤ (N : ℝ) / q := (le_div_iff₀ hqpos).2 hHq
  have hNlog : (N : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    simpa [N] using binaryLog_le_logb_of_wideRange 10 q n hrange
  have hNupper : (N : ℝ) <
      (2 : ℝ) ^ q * q / (2 : ℝ) ^ (10 : ℝ) := by
    calc
      (N : ℝ) ≤ Real.logb 2 (n : ℝ) := hNlog
      _ < (2 : ℝ) ^ (q + Real.logb 2 q - 10) := hrange.2
      _ = (2 : ℝ) ^ q * q / (2 : ℝ) ^ (10 : ℝ) :=
        wideRange_upper_endpoint 10 q hqpos
  have hNdiv : (N : ℝ) / q < (2 : ℝ) ^ q / 1024 := by
    calc
      (N : ℝ) / q <
          ((2 : ℝ) ^ q * q / (2 : ℝ) ^ (10 : ℝ)) / q :=
        div_lt_div_of_pos_right hNupper hqpos
      _ = (2 : ℝ) ^ q / 1024 := by
        norm_num [Real.rpow_natCast]
        field_simp
  have hHlt : (H : ℝ) < (2 : ℝ) ^ q / 1024 := hHle.trans_lt hNdiv
  have hP : 0 < (2 : ℝ) ^ q := Real.rpow_pos_of_pos zero_lt_two q
  have htwoH : 2 * (H : ℝ) < (2 : ℝ) ^ q / 512 := by
    nlinarith
  have hpolyNat : 4 * l ^ 2 + l + 2 < 2 ^ (l - 2) :=
    Zhang.remainderPolynomial_lt_two_pow_sub_two hl16
  have hexpPoly : ((l - 2 : ℕ) : ℝ) < q - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
    linarith
  have hrpowPoly := Real.rpow_lt_rpow_of_exponent_lt one_lt_two hexpPoly
  have hpoly : ((4 * l ^ 2 + l + 2 : ℕ) : ℝ) < (2 : ℝ) ^ q / 2 := by
    calc
      ((4 * l ^ 2 + l + 2 : ℕ) : ℝ) < ((2 ^ (l - 2) : ℕ) : ℝ) := by
        exact_mod_cast hpolyNat
      _ = (2 : ℝ) ^ ((l - 2 : ℕ) : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ < (2 : ℝ) ^ (q - 1) := hrpowPoly
      _ = (2 : ℝ) ^ q / 2 := by
        rw [Real.rpow_sub zero_lt_two, Real.rpow_one]
  have hremNat := Zhang.remainderExponent_le (N := N) (l := l) hsmall
  have hremReal : ((N + 1 - Zhang.matchingBits N l : ℕ) : ℝ) ≤
      ((2 * H + 4 * l ^ 2 + l + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by simpa [H] using hremNat)
  calc
    ((binaryLog n + 1 - constructionBits q n : ℕ) : ℝ) =
        ((N + 1 - Zhang.matchingBits N l : ℕ) : ℝ) := by
      simp [N, l, constructionBits]
    _ ≤ ((2 * H + 4 * l ^ 2 + l + 2 : ℕ) : ℝ) := hremReal
    _ = 2 * (H : ℝ) + ((4 * l ^ 2 + l + 2 : ℕ) : ℝ) := by
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ < (2 : ℝ) ^ q := by nlinarith

theorem sixteen_le_explicitQ_section6T_zero :
    (16 : ℝ) ≤ explicitQ section6T 0 := by
  have hlog : Real.logb 2 section6T = (2 : ℝ) ^ (16 : ℝ) := by
    rw [section6T, Real.logb_rpow zero_lt_two (by norm_num)]
  have hlog8 : (8 : ℝ) ≤ Real.logb 2 section6T := by
    rw [hlog]
    have h := Real.rpow_le_rpow_of_exponent_le one_le_two
      (show (3 : ℝ) ≤ 16 by norm_num)
    norm_num [Real.rpow_natCast] at h ⊢
  have hmul := mul_le_mul section6T_ge_two hlog8
    (by norm_num : (0 : ℝ) ≤ 8) (zero_le_two.trans section6T_ge_two)
  have : (16 : ℝ) ≤ section6T * Real.logb 2 section6T := by
    nlinarith
  simpa [explicitQ, ladderT] using this

/-- With all numerical and ladder arithmetic discharged, successor matching
is the sole remaining premise for the exact one-range reduction. -/
theorem explicitOneRangeReduction_of_constructionMatching
    (CM : ℝ)
    (hmatch : MatchingSuccessorAtBits 10 CM 16 constructionBits) :
    ExplicitOneRangeReduction section6T CM := by
  exact explicitOneRangeReduction_of_matchingSuccessorAtBits_of_initial
    10 CM 16 section6T constructionBits hmatch
    constructionBits_remainderBitBound section6T_ge_two
    sixteen_le_explicitQ_section6T_zero section6T_wide_for_ten

/-- The full asymptotic theorem now follows from only the repaired matching
construction, with every analytic, rounding, splitting, and lifting step proved. -/
theorem rangeBasedImprovedReductionBound_of_constructionMatching
    (CM : ℝ) (hCM : 0 ≤ CM)
    (hmatch : MatchingSuccessorAtBits 10 CM 16 constructionBits) :
    RangeBasedImprovedReductionBound := by
  exact rangeBasedImprovedReductionBound_of_explicitOneRange
    section6T CM section6T_ge_two hCM
    (explicitOneRangeReduction_of_constructionMatching CM hmatch)

end ZhangImprovedBound
