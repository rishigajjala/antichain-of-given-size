import Mathlib

namespace Zhang

/-- One base-`b` digit extension.  If `m` already agrees with `y` modulo
`a`, and the next increment is `a*z` modulo `a*b`, choosing `z` to be the
quotient `(y-m)/a` modulo `b` makes the new value agree modulo `a*b`.

The hypothesis `m ≤ y` is exactly what the uniform `m<n+1` bound supplies
when the target is `y=n+1`; it avoids signed quotient bookkeeping. -/
theorem extend_modEq_digit
    {a b m y delta z : ℕ} (hma : m ≤ y)
    (hprev : m ≡ y [MOD a])
    (hz : z ≡ (y - m) / a [MOD b])
    (hdelta : delta ≡ a * z [MOD a * b]) :
    m + delta ≡ y [MOD a * b] := by
  have hdiv : a ∣ y - m := (Nat.modEq_iff_dvd' hma).1 hprev
  have hquot : a * ((y - m) / a) = y - m := by
    rw [Nat.mul_div_cancel' hdiv]
  calc
    m + delta ≡ m + a * z [MOD a * b] := hdelta.add_left m
    _ ≡ m + a * ((y - m) / a) [MOD a * b] := by
      exact (Nat.ModEq.mul_left' a hz).add_left m
    _ = y := by rw [hquot, Nat.add_sub_of_le hma]

theorem pow_block_succ (h q : ℕ) :
    2 ^ ((h + 1) * q) = 2 ^ (h * q) * 2 ^ q := by
  rw [Nat.add_mul, one_mul, pow_add]

/-- Power-of-two specialization used by Claim 6.6. -/
theorem extend_pow_modEq_digit
    {h q m y delta z : ℕ} (hmy : m ≤ y)
    (hprev : m ≡ y [MOD 2 ^ (h * q)])
    (hz : z ≡ (y - m) / 2 ^ (h * q) [MOD 2 ^ q])
    (hdelta : delta ≡ 2 ^ (h * q) * z [MOD 2 ^ ((h + 1) * q)]) :
    m + delta ≡ y [MOD 2 ^ ((h + 1) * q)] := by
  rw [pow_block_succ] at hdelta ⊢
  exact extend_modEq_digit hmy hprev hz hdelta

end Zhang
