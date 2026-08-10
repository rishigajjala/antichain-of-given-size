import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import AntichainOfGivenSize.Section6.Address

namespace AntichainOfGivenSize.Section6

theorem four_sq_add_two_mul_le_two_pow_pred {l : ℕ} (hl : 10 ≤ l) :
    4 * l ^ 2 + 2 * (l + 2) ≤ 2 ^ (l - 1) := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
      have he : l + 1 - 1 = (l - 1) + 1 := by omega
      rw [he]
      have hinc : 4 * (l + 1) ^ 2 + 2 * (l + 1 + 2) ≤
          2 * (4 * l ^ 2 + 2 * (l + 2)) := by
        nlinarith
      calc
        4 * (l + 1) ^ 2 + 2 * (l + 1 + 2) ≤
            2 * (4 * l ^ 2 + 2 * (l + 2)) := hinc
        _ ≤ 2 * 2 ^ (l - 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ ((l - 1) + 1) := by rw [pow_succ]; ring

theorem two_le_stageCount_of_pow_pred_le
    {N l : ℕ} (hl : 10 ≤ l) (hpow : 2 ^ (l - 1) ≤ N) :
    2 ≤ (N - 4 * l ^ 2) / (l + 2) := by
  have hpoly : 4 * l ^ 2 + 2 * (l + 2) ≤ N :=
    (four_sq_add_two_mul_le_two_pow_pred hl).trans hpow
  apply (Nat.le_div_iff_mul_le (by omega : 0 < l + 2)).2
  omega

theorem addressRank_le_of_le_two_pow
    {H l : ℕ} (hH : 1 < H) (hpow : H ≤ 2 ^ l) :
    addressBits H + 1 ≤ l := by
  have hc : Nat.clog 2 H ≤ l := Nat.clog_le_of_le_pow hpow
  have hpos : 0 < Nat.clog 2 H := Nat.clog_pos Nat.one_lt_two hH
  have heq : addressBits H + 1 = Nat.clog 2 H := by
    simp only [addressBits]
    exact Nat.succ_pred_eq_of_pos hpos
  rw [heq]
  exact hc

end AntichainOfGivenSize.Section6
