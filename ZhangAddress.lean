import ZhangClaim64

open Finset
open scoped BigOperators

namespace Zhang

/-!
The capped binary address system used in Section 6.  There are `s + 1`
position coordinates.  The first `s` have weights `1, 2, ..., 2^(s-1)`;
the final coordinate has weight `H - 2^s`.  When
`2^s < H <= 2^(s+1)`, these weights sum to `H - 1` and represent every
integer `h < H`.
-/

def cappedWeight (H s : ℕ) (j : Fin (s + 1)) : ℕ :=
  if j = Fin.last s then H - 2 ^ s else 2 ^ j.val

def cappedLowValue (H s h : ℕ) : ℕ :=
  if 2 ^ s ≤ h then h - (H - 2 ^ s) else h

def cappedAddress (H s h : ℕ) : Finset (Fin (s + 1)) :=
  Finset.univ.filter fun j ↦
    if j = Fin.last s then 2 ^ s ≤ h
    else (cappedLowValue H s h).testBit j.val = true

@[simp] theorem last_mem_cappedAddress_iff (H s h : ℕ) :
    Fin.last s ∈ cappedAddress H s h ↔ 2 ^ s ≤ h := by
  simp [cappedAddress]

@[simp] theorem castSucc_mem_cappedAddress_iff (H s h : ℕ) (a : Fin s) :
    a.castSucc ∈ cappedAddress H s h ↔
      (cappedLowValue H s h).testBit a = true := by
  simp [cappedAddress, Fin.castSucc_ne_last]

theorem cappedLowValue_lt_two_pow
    {H s h : ℕ} (hHlo : 2 ^ s < H) (hHhi : H ≤ 2 ^ (s + 1))
    (hh : h < H) :
    cappedLowValue H s h < 2 ^ s := by
  rw [cappedLowValue]
  by_cases hp : 2 ^ s ≤ h
  · simp only [hp, if_true]
    have hwlep : H - 2 ^ s ≤ 2 ^ s := by
      rw [pow_succ] at hHhi
      omega
    have hwleh : H - 2 ^ s ≤ h := hwlep.trans hp
    apply (tsub_lt_iff_right hwleh).2
    rw [Nat.add_comm, Nat.sub_add_cancel hHlo.le]
    exact hh
  · simp only [hp, if_false]
    exact Nat.lt_of_not_ge hp

theorem sum_cappedWeight (H s : ℕ) (hHlo : 2 ^ s ≤ H) :
    ∑ j : Fin (s + 1), cappedWeight H s j = H - 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [cappedWeight, Fin.castSucc_ne_last, if_false, Fin.val_castSucc,
    Fin.val_last]
  rw [sum_two_pow_fin]
  simp only [if_true]
  rw [Nat.add_comm, ← Nat.add_sub_assoc Nat.one_le_two_pow,
    Nat.sub_add_cancel hHlo]

theorem sum_cappedAddress_weight
    {H s h : ℕ} (hHlo : 2 ^ s < H) (hHhi : H ≤ 2 ^ (s + 1))
    (hh : h < H) :
    ∑ j ∈ cappedAddress H s h, cappedWeight H s j = h := by
  rw [cappedAddress, Finset.sum_filter, Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_ne_last, if_false, cappedWeight, Fin.val_castSucc,
    Fin.val_last]
  have hlow : cappedLowValue H s h < 2 ^ s :=
    cappedLowValue_lt_two_pow hHlo hHhi hh
  have hbits := lowBitsValue_eq hlow
  change lowBitsValue s (cappedLowValue H s h) +
      (if 2 ^ s ≤ h then H - 2 ^ s else 0) = h
  rw [hbits]
  rw [cappedLowValue]
  by_cases hp : 2 ^ s ≤ h
  · simp only [hp, if_true]
    have hwle : H - 2 ^ s ≤ h := by
      have : H - 2 ^ s ≤ 2 ^ s := by omega
      exact this.trans hp
    omega
  · simp [hp]

theorem cappedAddress_injective
    {H s : ℕ} (hHlo : 2 ^ s < H) (hHhi : H ≤ 2 ^ (s + 1)) :
    Function.Injective (fun h : Fin H ↦ cappedAddress H s h) := by
  intro h g heq
  change cappedAddress H s h = cappedAddress H s g at heq
  apply Fin.ext
  have hh := sum_cappedAddress_weight hHlo hHhi h.isLt
  have hg := sum_cappedAddress_weight hHlo hHhi g.isLt
  calc
    h.val = ∑ j ∈ cappedAddress H s h, cappedWeight H s j := hh.symm
    _ = ∑ j ∈ cappedAddress H s g, cappedWeight H s j := by rw [heq]
    _ = g.val := hg

/-- Instantiate the capped address system with the ceiling binary logarithm. -/
noncomputable def addressBits (H : ℕ) : ℕ := (Nat.clog 2 H).pred

theorem two_pow_addressBits_lt {H : ℕ} (hH : 1 < H) :
    2 ^ addressBits H < H := by
  simpa [addressBits] using Nat.pow_pred_clog_lt_self Nat.one_lt_two hH

theorem H_le_two_pow_addressBits_succ (H : ℕ) :
    H ≤ 2 ^ (addressBits H + 1) := by
  by_cases hH : 1 < H
  · have hpos := Nat.clog_pos Nat.one_lt_two hH
    have hc := Nat.succ_pred_eq_of_pos hpos
    change (Nat.clog 2 H).pred + 1 = Nat.clog 2 H at hc
    rw [addressBits, hc]
    exact Nat.le_pow_clog Nat.one_lt_two H
  · have : H ≤ 1 := Nat.le_of_not_gt hH
    exact this.trans Nat.one_le_two_pow

noncomputable def canonicalWeight (H : ℕ) : Fin (addressBits H + 1) → ℕ :=
  cappedWeight H (addressBits H)

noncomputable def canonicalAddress (H : ℕ) (h : Fin H) :
    Finset (Fin (addressBits H + 1)) :=
  cappedAddress H (addressBits H) h

theorem sum_canonicalWeight {H : ℕ} (hH : 1 < H) :
    ∑ j : Fin (addressBits H + 1), canonicalWeight H j = H - 1 := by
  exact sum_cappedWeight H (addressBits H) (two_pow_addressBits_lt hH).le

theorem sum_canonicalAddress_weight {H : ℕ} (hH : 1 < H) (h : Fin H) :
    ∑ j ∈ canonicalAddress H h, canonicalWeight H j = h.val := by
  exact sum_cappedAddress_weight (two_pow_addressBits_lt hH)
    (H_le_two_pow_addressBits_succ H) h.isLt

theorem canonicalAddress_injective {H : ℕ} (hH : 1 < H) :
    Function.Injective (canonicalAddress H) :=
  cappedAddress_injective (two_pow_addressBits_lt hH)
    (H_le_two_pow_addressBits_succ H)

end Zhang
