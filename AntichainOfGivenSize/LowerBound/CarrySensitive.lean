import AntichainOfGivenSize.LowerBound.InfinitelyOften

/-!
# A carry-sensitive lower-bound family

Binary carries sharpen the signed-power argument for alternating binary
words whenever inclusion--exclusion has at least one negative term.  This
produces a shorter explicit witness.  The same subsequence also supports an
infinitely-often lower bound with coefficient `1` in front of
`log₂(log₂ n)`.

This particular argument remains on the `log log n` scale.  The stronger
quadratic-over-log lower bound is proved in `LowerBound.Matching`.
-/

open scoped BigOperators

namespace AntichainOfGivenSize

/-- Number of `1` digits in the canonical binary expansion. -/
def binaryOneCount (n : ℕ) : ℕ := n.bits.count true

@[simp] theorem binaryOneCount_zero : binaryOneCount 0 = 0 := by
  simp [binaryOneCount]

@[simp] theorem binaryOneCount_one : binaryOneCount 1 = 1 := by decide

@[simp] theorem binaryOneCount_two : binaryOneCount 2 = 1 := by decide

@[simp] theorem binaryOneCount_three : binaryOneCount 3 = 2 := by decide

@[simp] theorem binaryOneCount_bit_false (n : ℕ) :
    binaryOneCount (Nat.bit false n) = binaryOneCount n := by
  by_cases h : n = 0
  · subst n
    simp [binaryOneCount, Nat.bit]
  · rw [show Nat.bit false n = 2 * n by simp [Nat.bit_val]]
    unfold binaryOneCount
    rw [Nat.bit0_bits _ h]
    simp

@[simp] theorem binaryOneCount_bit_true (n : ℕ) :
    binaryOneCount (Nat.bit true n) = binaryOneCount n + 1 := by
  rw [show Nat.bit true n = 2 * n + 1 by simp [Nat.bit_val]]
  unfold binaryOneCount
  rw [Nat.bit1_bits]
  simp

theorem binaryOneCount_four_mul_add (n r : ℕ) (hr : r < 4) :
    binaryOneCount (4 * n + r) = binaryOneCount n + binaryOneCount r := by
  interval_cases r
  · have hnum : 4 * n = Nat.bit false (Nat.bit false n) := by
      simp [Nat.bit_val]
      omega
    calc
      binaryOneCount (4 * n) =
          binaryOneCount (Nat.bit false (Nat.bit false n)) := congrArg _ hnum
      _ = binaryOneCount (Nat.bit false n) :=
        binaryOneCount_bit_false (Nat.bit false n)
      _ = binaryOneCount n := binaryOneCount_bit_false n
  · have hnum : 4 * n + 1 = Nat.bit true (Nat.bit false n) := by
      simp [Nat.bit_val]
      omega
    calc
      binaryOneCount (4 * n + 1) =
          binaryOneCount (Nat.bit true (Nat.bit false n)) := congrArg _ hnum
      _ = binaryOneCount (Nat.bit false n) + 1 :=
        binaryOneCount_bit_true (Nat.bit false n)
      _ = binaryOneCount n + 1 := by rw [binaryOneCount_bit_false]
      _ = binaryOneCount n + binaryOneCount 1 := by
        congr 1
  · have hnum : 4 * n + 2 = Nat.bit false (Nat.bit true n) := by
      simp [Nat.bit_val]
      omega
    calc
      binaryOneCount (4 * n + 2) =
          binaryOneCount (Nat.bit false (Nat.bit true n)) := congrArg _ hnum
      _ = binaryOneCount (Nat.bit true n) :=
        binaryOneCount_bit_false (Nat.bit true n)
      _ = binaryOneCount n + 1 := binaryOneCount_bit_true n
      _ = binaryOneCount n + binaryOneCount 2 := by
        congr 1
  · have hnum : 4 * n + 3 = Nat.bit true (Nat.bit true n) := by
      simp [Nat.bit_val]
      omega
    calc
      binaryOneCount (4 * n + 3) =
          binaryOneCount (Nat.bit true (Nat.bit true n)) := congrArg _ hnum
      _ = binaryOneCount (Nat.bit true n) + 1 :=
        binaryOneCount_bit_true (Nat.bit true n)
      _ = (binaryOneCount n + 1) + 1 := by rw [binaryOneCount_bit_true]
      _ = binaryOneCount n + binaryOneCount 3 := by
        have : binaryOneCount 3 = 2 := by decide
        rw [this]

@[simp] theorem binaryOneCount_alternatingOnes (r : ℕ) :
    binaryOneCount (alternatingOnes r) = r + 1 := by
  induction r with
  | zero => norm_num [alternatingOnes, binaryOneCount]
  | succ r ih =>
      rw [alternatingOnes_succ, binaryOneCount_four_mul_add _ 1 (by omega), ih]
      norm_num [binaryOneCount]

theorem binaryOneCount_pos_of_pos {n : ℕ} (hn : 0 < n) :
    0 < binaryOneCount n := by
  induction n using Nat.binaryRec' with
  | zero => omega
  | bit b n h ih =>
      cases b with
      | false =>
          have hn' : 0 < n := by
            by_contra hn0
            have : n = 0 := Nat.eq_zero_of_not_pos hn0
            exact Bool.false_ne_true (h this)
          simpa only [binaryOneCount_bit_false] using ih hn'
      | true =>
          rw [binaryOneCount_bit_true]
          omega

/-- Adding one increases binary Hamming weight by at most one. -/
theorem binaryOneCount_succ_le (n : ℕ) :
    binaryOneCount (n + 1) ≤ binaryOneCount n + 1 := by
  induction n using Nat.binaryRec' with
  | zero => decide
  | bit b n h ih =>
      cases b with
      | false =>
          have hadd : Nat.bit false n + 1 = Nat.bit true n := by
            simp [Nat.bit_val]
          calc
            binaryOneCount (Nat.bit false n + 1) =
                binaryOneCount (Nat.bit true n) := congrArg _ hadd
            _ = binaryOneCount n + 1 := binaryOneCount_bit_true n
            _ ≤ binaryOneCount (Nat.bit false n) + 1 :=
              (congrArg (fun z ↦ z + 1)
                (binaryOneCount_bit_false n).symm).le
      | true =>
          have hadd : Nat.bit true n + 1 = Nat.bit false (n + 1) := by
            simp [Nat.bit_val]
            omega
          calc
            binaryOneCount (Nat.bit true n + 1) =
                binaryOneCount (Nat.bit false (n + 1)) := congrArg _ hadd
            _ = binaryOneCount (n + 1) := binaryOneCount_bit_false (n + 1)
            _ ≤ binaryOneCount n + 1 := ih
            _ = binaryOneCount (Nat.bit true n) :=
              (binaryOneCount_bit_true n).symm
            _ ≤ binaryOneCount (Nat.bit true n) + 1 := Nat.le_add_right _ _

/-- Adding a power of two increases binary Hamming weight by at most one. -/
theorem binaryOneCount_add_pow (n y : ℕ) :
    binaryOneCount (n + 2 ^ y) ≤ binaryOneCount n + 1 := by
  induction y generalizing n with
  | zero => simpa using binaryOneCount_succ_le n
  | succ y ih =>
      refine Nat.bitCasesOn
        (motive := fun n ↦
          binaryOneCount (n + 2 ^ (y + 1)) ≤ binaryOneCount n + 1)
        n fun b q ↦ ?_
      have hadd : Nat.bit b q + 2 ^ (y + 1) = Nat.bit b (q + 2 ^ y) := by
        cases b <;> norm_num [Nat.bit_val, pow_succ] <;> omega
      rw [hadd]
      cases b with
      | false =>
          simpa only [binaryOneCount_bit_false] using ih q
      | true =>
          rw [binaryOneCount_bit_true, binaryOneCount_bit_true]
          exact Nat.add_le_add_right (ih q) 1

theorem binaryOneCount_powerSum_le_length (exponents : List ℕ) :
    binaryOneCount (binaryPowerSum exponents) ≤ exponents.length := by
  induction exponents with
  | nil => simp [binaryPowerSum]
  | cons y ys ih =>
      rw [binaryPowerSum_cons, Nat.add_comm]
      exact (binaryOneCount_add_pow (binaryPowerSum ys) y).trans
        (by simp only [List.length_cons]; omega)

/-- Adding a positive integer to an alternating binary word forces one more
unit of total Hamming weight across the addend and the result. -/
theorem binaryOneCount_alternatingOnes_add (r b : ℕ) (hb : 0 < b) :
    r + 2 ≤ binaryOneCount (alternatingOnes r + b) + binaryOneCount b := by
  induction r generalizing b with
  | zero =>
      have hbWeight : 0 < binaryOneCount b := binaryOneCount_pos_of_pos hb
      have hsumWeight : 0 < binaryOneCount (alternatingOnes 0 + b) :=
        binaryOneCount_pos_of_pos (by simp [alternatingOnes])
      omega
  | succ r ih =>
      let c := b / 4
      let d := b % 4
      have hd : d < 4 := by
        dsimp [d]
        exact Nat.mod_lt _ (by omega)
      have hbcd : b = 4 * c + d := by
        have hdiv := Nat.mod_add_div b 4
        dsimp [c, d]
        omega
      rw [hbcd] at hb ⊢
      interval_cases d
      · have hc : 0 < c := by omega
        have hi := ih c hc
        have hsum :
            alternatingOnes (r + 1) + (4 * c + 0) =
              4 * (alternatingOnes r + c) + 1 := by
          rw [alternatingOnes_succ]
          omega
        rw [hsum, binaryOneCount_four_mul_add _ 1 (by omega),
          binaryOneCount_four_mul_add c 0 (by omega)]
        rw [binaryOneCount_one, binaryOneCount_zero]
        omega
      · have hbase :
            r + 1 ≤ binaryOneCount (alternatingOnes r + c) +
              binaryOneCount c := by
          by_cases hc : c = 0
          · simp [hc]
          · have hi := ih c (Nat.pos_of_ne_zero hc)
            omega
        have hsum :
            alternatingOnes (r + 1) + (4 * c + 1) =
              4 * (alternatingOnes r + c) + 2 := by
          rw [alternatingOnes_succ]
          omega
        rw [hsum, binaryOneCount_four_mul_add _ 2 (by omega),
          binaryOneCount_four_mul_add c 1 (by omega)]
        rw [binaryOneCount_two, binaryOneCount_one]
        omega
      · have hbase :
            r + 1 ≤ binaryOneCount (alternatingOnes r + c) +
              binaryOneCount c := by
          by_cases hc : c = 0
          · simp [hc]
          · have hi := ih c (Nat.pos_of_ne_zero hc)
            omega
        have hsum :
            alternatingOnes (r + 1) + (4 * c + 2) =
              4 * (alternatingOnes r + c) + 3 := by
          rw [alternatingOnes_succ]
          omega
        rw [hsum, binaryOneCount_four_mul_add _ 3 (by omega),
          binaryOneCount_four_mul_add c 2 (by omega)]
        rw [binaryOneCount_three, binaryOneCount_two]
        omega
      · have hi := ih (c + 1) (by omega)
        have hsucc := binaryOneCount_succ_le c
        have hsum :
            alternatingOnes (r + 1) + (4 * c + 3) =
              4 * (alternatingOnes r + (c + 1)) + 0 := by
          rw [alternatingOnes_succ]
          omega
        rw [hsum, binaryOneCount_four_mul_add _ 0 (by omega),
          binaryOneCount_four_mul_add c 3 (by omega)]
        rw [binaryOneCount_zero, binaryOneCount_three]
        omega

theorem binaryPowerSum_pos_of_nonempty {exponents : List ℕ}
    (h : exponents ≠ []) : 0 < binaryPowerSum exponents := by
  cases exponents with
  | nil => exact (h rfl).elim
  | cons y ys =>
    rw [binaryPowerSum_cons]
    have : 0 < 2 ^ y := pow_pos (by omega) _
    omega

/-- A signed-power representation of an alternating word that has at least
one negative term needs strictly more terms than the number of isolated
`1` bits. -/
theorem alternatingOnes_signedPowerSums_length
    (r : ℕ) (positive negative : List ℕ) (hnegative : negative ≠ [])
    (hbalance : binaryPowerSum positive =
      alternatingOnes r + binaryPowerSum negative) :
    r + 2 ≤ positive.length + negative.length := by
  have hnegPos : 0 < binaryPowerSum negative :=
    binaryPowerSum_pos_of_nonempty hnegative
  have hcarry := binaryOneCount_alternatingOnes_add r
    (binaryPowerSum negative) hnegPos
  have hpositive := binaryOneCount_powerSum_le_length positive
  have hnegativeWeight := binaryOneCount_powerSum_le_length negative
  have hweightEq :
      binaryOneCount (alternatingOnes r + binaryPowerSum negative) =
        binaryOneCount (binaryPowerSum positive) :=
    congrArg binaryOneCount hbalance.symm
  omega

theorem alternatingOnes_signedPowerFinsets_card
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (r : ℕ) (positive : Finset ι) (negative : Finset κ)
    (positiveExponent : ι → ℕ) (negativeExponent : κ → ℕ)
    (hnegative : negative.Nonempty)
    (hbalance : (∑ i ∈ positive, 2 ^ positiveExponent i) =
      alternatingOnes r + ∑ i ∈ negative, 2 ^ negativeExponent i) :
    r + 2 ≤ positive.card + negative.card := by
  have hlist :
      binaryPowerSum (positive.toList.map positiveExponent) =
        alternatingOnes r +
          binaryPowerSum (negative.toList.map negativeExponent) := by
    simpa only [binaryPowerSum_toList_map] using hbalance
  have hlistNegative :
      negative.toList.map negativeExponent ≠ [] := by
    intro hnil
    have hlen : negative.card = 0 := by
      have := congrArg List.length hnil
      simpa using this
    exact (Finset.card_ne_zero.mpr hnegative) hlen
  simpa using alternatingOnes_signedPowerSums_length r
    (positive.toList.map positiveExponent)
    (negative.toList.map negativeExponent) hlistNegative hlist

/-- Carry-sensitive obstruction for an ideal whose face count is an
alternating binary word. -/
theorem alternatingOnes_termCount_lower
    {V : Type*} [DecidableEq V] (r : ℕ)
    (generators : Finset (Finset V))
    (htwo : 2 ≤ generators.card)
    (hsize : (generatedIdeal generators).card = alternatingOnes r) :
    r + 2 ≤ 2 ^ generators.card - 1 := by
  let subfamilies := generators.powerset.filter (·.Nonempty)
  let exponent : ↥subfamilies → ℕ := fun t ↦
    (t.1.inf' (Finset.mem_filter.1 t.2).2 id).card
  let positive : Finset ↥subfamilies :=
    Finset.univ.filter fun t ↦ Odd t.1.card
  let negative : Finset ↥subfamilies :=
    Finset.univ.filter fun t ↦ ¬Odd t.1.card
  let term : ↥subfamilies → ℤ := fun t ↦
    (-1 : ℤ) ^ (t.1.card + 1) * (2 : ℤ) ^ exponent t

  have hIE : ((generatedIdeal generators).card : ℤ) =
      ∑ t : ↥subfamilies, term t := by
    simpa [subfamilies, exponent, term, generatedIdeal,
      Section6.generatedIdealIdx] using
        (Section6.generatedIdealIdx_card_inclusionExclusion generators id)

  have hpositive : (∑ t ∈ positive, term t) =
      ∑ t ∈ positive, (2 : ℤ) ^ exponent t := by
    apply Finset.sum_congr rfl
    intro t ht
    have htodd : Odd t.1.card := (Finset.mem_filter.1 ht).2
    simp only [term, htodd.add_one.neg_one_pow, one_mul]

  have hnegativeTerms : (∑ t ∈ negative, term t) =
      -(∑ t ∈ negative, (2 : ℤ) ^ exponent t) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hteven : Even t.1.card :=
      Nat.not_odd_iff_even.mp (Finset.mem_filter.1 ht).2
    simp only [term, hteven.add_one.neg_one_pow, neg_mul, one_mul]

  have hsplit : (∑ t : ↥subfamilies, term t) =
      (∑ t ∈ positive, (2 : ℤ) ^ exponent t) -
        ∑ t ∈ negative, (2 : ℤ) ^ exponent t := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun t : ↥subfamilies ↦ Odd t.1.card) term]
    rw [show Finset.univ.filter (fun t : ↥subfamilies ↦ Odd t.1.card) =
      positive by rfl]
    rw [show Finset.univ.filter (fun t : ↥subfamilies ↦ ¬Odd t.1.card) =
      negative by rfl]
    rw [hpositive, hnegativeTerms, sub_eq_add_neg]

  have hbalanceInt :
      (∑ t ∈ positive, (2 : ℤ) ^ exponent t) =
        (alternatingOnes r : ℤ) +
          ∑ t ∈ negative, (2 : ℤ) ^ exponent t := by
    rw [← hsize, hIE, hsplit]
    ring
  have hbalanceNat :
      (∑ t ∈ positive, (2 : ℕ) ^ exponent t) =
        alternatingOnes r +
          ∑ t ∈ negative, (2 : ℕ) ^ exponent t := by
    exact_mod_cast hbalanceInt

  have hnegativeNonempty : negative.Nonempty := by
    obtain ⟨pair, hpair, hpairCard⟩ :=
      generators.exists_subset_card_eq htwo
    have hpairNonempty : pair.Nonempty := Finset.card_pos.mp (by omega)
    have hpairMem : pair ∈ subfamilies := by
      exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hpair, hpairNonempty⟩
    let t : ↥subfamilies := ⟨pair, hpairMem⟩
    refine ⟨t, ?_⟩
    simp only [negative, Finset.mem_filter, Finset.mem_univ, true_and,
      Nat.not_odd_iff_even]
    simp [t, hpairCard]

  have hterms := alternatingOnes_signedPowerFinsets_card r
    positive negative exponent exponent hnegativeNonempty hbalanceNat
  have hcards : positive.card + negative.card = subfamilies.card := by
    simpa [positive, negative] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset ↥subfamilies))
        (p := fun t : ↥subfamilies ↦ Odd t.1.card))
  rw [hcards] at hterms
  have hsubfamilies : subfamilies.card = 2 ^ generators.card - 1 := by
    dsimp only [subfamilies]
    have hempty : generators.powerset.filter (·.Nonempty) =
        generators.powerset.erase ∅ := by
      ext s
      simp [Finset.nonempty_iff_ne_empty, and_comm]
    rw [hempty, Finset.card_erase_of_mem]
    · simp
    · simp
  rwa [hsubfamilies] at hterms

/-- The carry-sensitive alternating witness improves the block-count lower
bound by one generator. -/
theorem carrySensitive_alternatingOnes_lower (q : ℕ) (hq : 2 ≤ q) :
    q + 1 ≤ alpha (alternatingOnes (2 ^ q - 2)) := by
  have hblocks := binaryBlockCount_add_one_le_two_pow_alpha
    (alternatingOnes (2 ^ q - 2))
  rw [binaryBlockCount_alternatingOnes] at hblocks
  have hpowFour : 4 ≤ 2 ^ q := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q := pow_le_pow_right' (by omega) hq
  have hleft : (2 ^ q - 2) + 1 + 1 = 2 ^ q := by omega
  rw [hleft] at hblocks
  have hqAlpha : q ≤ alpha (alternatingOnes (2 ^ q - 2)) :=
    (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hblocks
  by_contra hnot
  have halphaQ : alpha (alternatingOnes (2 ^ q - 2)) ≤ q :=
    by omega
  have halphaEq : alpha (alternatingOnes (2 ^ q - 2)) = q :=
    Nat.le_antisymm halphaQ hqAlpha
  rcases alpha_hasGeneratorCount (alternatingOnes (2 ^ q - 2)) with
    ⟨m, generators, hsize, hcard⟩
  have htwo : 2 ≤ generators.card := by
    rw [hcard, halphaEq]
    exact hq
  have hcarry := alternatingOnes_termCount_lower
    (2 ^ q - 2) generators htwo hsize
  rw [hcard, halphaEq] at hcarry
  have hright : 2 ^ q - 1 < 2 ^ q := by omega
  omega

/-- On the shorter carry-sensitive subsequence, `alpha` dominates the
double logarithm with coefficient `1`. -/
theorem carrySensitive_alternatingOnes_logLog_lower (q : ℕ) (hq : 2 ≤ q) :
    Real.logb 2
        (Real.logb 2 (alternatingOnes (2 ^ q - 2) : ℝ)) <
      (alpha (alternatingOnes (2 ^ q - 2)) : ℝ) := by
  have hpowFour : 4 ≤ 2 ^ q := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q := pow_le_pow_right' (by omega) hq
  have hexponent :
      2 * ((2 ^ q - 2) + 1) < 2 ^ (q + 1) := by
    rw [pow_succ]
    omega
  have hlargeNat :
      alternatingOnes (2 ^ q - 2) < 2 ^ (2 ^ (q + 1)) :=
    (alternatingOnes_lt_pow (2 ^ q - 2)).trans
      (Nat.pow_lt_pow_right (by omega : 1 < (2 : ℕ)) hexponent)
  have hlargeReal :
      (alternatingOnes (2 ^ q - 2) : ℝ) <
        (2 : ℝ) ^ (2 ^ (q + 1)) := by
    exact_mod_cast hlargeNat
  have hnOneNat : 1 < alternatingOnes (2 ^ q - 2) := by
    exact (show 1 < (2 ^ q - 2) + 1 by omega).trans_le
      (index_le_alternatingOnes (2 ^ q - 2))
  have hnPos : (0 : ℝ) < alternatingOnes (2 ^ q - 2) := by
    exact_mod_cast alternatingOnes_pos (2 ^ q - 2)
  have hnOne : (1 : ℝ) < alternatingOnes (2 ^ q - 2) := by
    exact_mod_cast hnOneNat
  have hlogInnerPos :
      0 < Real.logb 2 (alternatingOnes (2 ^ q - 2) : ℝ) :=
    Real.logb_pos (by norm_num) hnOne
  have hlogFirst :
      Real.logb 2 (alternatingOnes (2 ^ q - 2) : ℝ) <
        (2 : ℝ) ^ (q + 1) := by
    calc
      Real.logb 2 (alternatingOnes (2 ^ q - 2) : ℝ) <
          Real.logb 2 ((2 : ℝ) ^ (2 ^ (q + 1))) :=
        Real.logb_lt_logb (by norm_num) hnPos hlargeReal
      _ = ((2 ^ (q + 1) : ℕ) : ℝ) := by
        rw [Real.logb_pow]
        norm_num [Real.logb_self_eq_one]
      _ = (2 : ℝ) ^ (q + 1) := by norm_num
  have hlogSecond :
      Real.logb 2
          (Real.logb 2 (alternatingOnes (2 ^ q - 2) : ℝ)) <
        (q + 1 : ℕ) := by
    calc
      Real.logb 2
          (Real.logb 2 (alternatingOnes (2 ^ q - 2) : ℝ)) <
          Real.logb 2 ((2 : ℝ) ^ (q + 1)) :=
        Real.logb_lt_logb (by norm_num) hlogInnerPos hlogFirst
      _ = (q + 1 : ℕ) := by
        rw [Real.logb_pow]
        norm_num [Real.logb_self_eq_one]
  have halphaNat :
      q + 1 ≤ alpha (alternatingOnes (2 ^ q - 2)) := by
    exact carrySensitive_alternatingOnes_lower q hq
  have halphaReal :
      ((q + 1 : ℕ) : ℝ) ≤
        (alpha (alternatingOnes (2 ^ q - 2)) : ℝ) := by
    exact_mod_cast halphaNat
  exact hlogSecond.trans_le halphaReal

/-- There are arbitrarily large cardinalities at which `alpha` dominates
the double base-2 logarithm with coefficient `1`. -/
theorem carrySensitive_logLog_lower_infinitely_often :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      Real.logb 2 (Real.logb 2 (n : ℝ)) ≤ (alpha n : ℝ) := by
  intro N
  let q := N + 2
  refine ⟨alternatingOnes (2 ^ q - 2), ?_, ?_⟩
  · have hmul := Nat.mul_le_pow (a := 2) (by omega) q
    have hNpow : N + 2 ≤ 2 ^ q := by
      dsimp only [q] at hmul ⊢
      omega
    have hindex : N ≤ (2 ^ q - 2) + 1 := by omega
    exact hindex.trans (index_le_alternatingOnes (2 ^ q - 2))
  · exact (carrySensitive_alternatingOnes_logLog_lower q (by
      dsimp only [q]
      omega)).le

end AntichainOfGivenSize
