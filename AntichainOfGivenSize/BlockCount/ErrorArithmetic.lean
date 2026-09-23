import AntichainOfGivenSize.BlockCount.ScaledIdeals

open scoped BigOperators

namespace AntichainOfGivenSize.BlockCount

/-- An exponent below `-H` contributes less than one unit at scale `H`. -/
theorem zpow_two_lt_inv_pow_of_lt_neg (e : ℤ) (H : ℕ)
    (he : e < -(H : ℤ)) :
    (2 : ℚ) ^ e < 1 / (2 : ℚ) ^ H := by
  have h := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mpr he
  simpa only [zpow_neg, zpow_natCast, one_div] using h

/-- The weak form is convenient for bounding an entire finite error sum. -/
theorem zpow_two_le_inv_pow_of_lt_neg (e : ℤ) (H : ℕ)
    (he : e < -(H : ℤ)) :
    (2 : ℚ) ^ e ≤ 1 / (2 : ℚ) ^ H :=
  (zpow_two_lt_inv_pow_of_lt_neg e H he).le

/-- The same small-term estimate in integral-power notation. -/
theorem zpow_two_le_zpow_neg_of_lt_neg (e : ℤ) (H : ℕ)
    (he : e < -(H : ℤ)) :
    (2 : ℚ) ^ e ≤ (2 : ℚ) ^ (-(H : ℤ)) := by
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mpr he.le

/-- A finite sum of quantities individually bounded by `B` is bounded by
its number of terms times `B`. No sign assumption is needed. -/
theorem finset_sum_le_card_mul_bound {ι : Type*} (s : Finset ι)
    (f : ι → ℚ) (B : ℚ) (hf : ∀ i ∈ s, f i ≤ B) :
    (∑ i ∈ s, f i) ≤ (s.card : ℚ) * B := by
  calc
    _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum hf
    _ = _ := by simp

/-- A list version which retains repeated terms in the error count. -/
theorem list_sum_map_le_length_mul_bound {ι : Type*} (l : List ι)
    (f : ι → ℚ) (B : ℚ) (hf : ∀ i ∈ l, f i ≤ B) :
    (l.map f).sum ≤ (l.length : ℚ) * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := hf a (by simp)
      have hl := ih (fun i hi => hf i (by simp [hi]))
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      nlinarith

/-- The sum of small normalized powers over a finite set is at most one
scale unit per term. -/
theorem finset_sum_zpow_two_le_card_inv_pow {ι : Type*}
    (s : Finset ι) (e : ι → ℤ) (H : ℕ)
    (he : ∀ i ∈ s, e i < -(H : ℤ)) :
    (∑ i ∈ s, (2 : ℚ) ^ e i) ≤ (s.card : ℚ) * (1 / (2 : ℚ) ^ H) := by
  apply finset_sum_le_card_mul_bound
  intro i hi
  exact zpow_two_le_inv_pow_of_lt_neg (e i) H (he i hi)

/-- The list form counts all repeated small terms. -/
theorem list_sum_zpow_two_le_length_inv_pow
    (es : List ℤ) (H : ℕ) (he : ∀ e ∈ es, e < -(H : ℤ)) :
    (es.map (fun e => (2 : ℚ) ^ e)).sum ≤
      (es.length : ℚ) * (1 / (2 : ℚ) ^ H) := by
  apply list_sum_map_le_length_mul_bound
  intro e he_mem
  exact zpow_two_le_inv_pow_of_lt_neg e H (he e he_mem)

/-- Dividing the appended-one target by its large power of two isolates
its integer part and its positive small remainder. -/
theorem normalize_two_pow_mul_add_one (p : ℚ) (t : ℕ) :
    (2 : ℚ) ^ (-(t : ℤ)) * ((2 : ℚ) ^ t * p + 1) =
      p + (2 : ℚ) ^ (-(t : ℤ)) := by
  have hcancel : (2 : ℚ) ^ (-(t : ℤ)) * (2 : ℚ) ^ t = 1 := by
    rw [zpow_neg, zpow_natCast]
    exact inv_mul_cancel₀ (by positivity)
  calc
    _ = ((2 : ℚ) ^ (-(t : ℤ)) * (2 : ℚ) ^ t) * p +
        (2 : ℚ) ^ (-(t : ℤ)) := by ring
    _ = _ := by rw [hcancel, one_mul]

/-- A cast-normalized form matching `HasDyadicIdealSum` hypotheses. -/
theorem normalize_nat_two_pow_mul_add_one (p t : ℕ) :
    (2 : ℚ) ^ (-(t : ℤ)) * ((2 ^ t * p + 1 : ℕ) : ℚ) =
      (p : ℚ) + (2 : ℚ) ^ (-(t : ℤ)) := by
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_one]
  exact normalize_two_pow_mul_add_one (p : ℚ) t

/-- Normalize any raw witness list for the appended-one target. -/
theorem normalize_sum_value_of_eq (terms : List DyadicIdeal) (p t : ℕ)
    (hv : (terms.map DyadicIdeal.value).sum = ((2 ^ t * p + 1 : ℕ) : ℚ)) :
    (2 : ℚ) ^ (-(t : ℤ)) * (terms.map DyadicIdeal.value).sum =
      (p : ℚ) + (2 : ℚ) ^ (-(t : ℤ)) := by
  rw [hv, normalize_nat_two_pow_mul_add_one]

end AntichainOfGivenSize.BlockCount
