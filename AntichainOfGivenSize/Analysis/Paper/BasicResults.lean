import AntichainOfGivenSize.Analysis.Paper.Typical
import AntichainOfGivenSize.Analysis.BlockCount.Upper

/-! Small exact values and the finite base in Sections 2 and 5. All finite
checks below are evaluated by Lean's kernel (`decide`), not an external
native evaluator. -/

open Finset

namespace AntichainOfGivenSize.Paper

/-- Definition 2.1: a generated ideal is downward closed under inclusion. -/
theorem generatedIdeal_isLowerSet {V : Type*} [DecidableEq V]
    (generators : Finset (Finset V)) :
    IsLowerSet (generatedIdeal generators : Set (Finset V)) := by
  intro A B hAB hB
  obtain ⟨G, hG, hBG⟩ := Finset.mem_biUnion.mp hB
  exact Finset.mem_biUnion.mpr
    ⟨G, hG, Finset.mem_powerset.mpr (hAB.trans (Finset.mem_powerset.mp hBG))⟩

theorem alpha_one : alpha 1 = 1 := by
  have hlo := alpha_pos_of_pos (by norm_num : 0 < 1)
  have hhi := alpha_le_self 1
  omega

theorem alpha_two_pow (t : ℕ) : alpha (2 ^ t) = 1 := by
  have hlo := alpha_pos_of_pos (by positivity : 0 < 2 ^ t)
  have hhi := alpha_two_pow_le_one t
  omega

theorem alpha_add_two_le_succ (n : ℕ) : alpha (n + 2) ≤ n + 1 := by
  have htwo : alpha 2 = 1 := by simpa using alpha_two_pow 1
  induction n with
  | zero => simpa using htwo.le
  | succ n ih =>
      have hsplit := splittingLemma 2 (n + 1) (by norm_num)
      rw [htwo] at hsplit
      have hrewrite : 2 + (n + 1) = n + 1 + 2 := by omega
      rw [hrewrite] at hsplit
      rw [show n + 1 + 1 = n + 2 by omega] at hsplit
      omega

/-- The elementary bound stated in the preliminaries and used to absorb
finite initial ranges in the upper-bound argument. -/
theorem alpha_le_max_one_pred (n : ℕ) (hn : 0 < n) :
    alpha n ≤ max 1 (n - 1) := by
  by_cases hn1 : n = 1
  · subst n
    simp [alpha_one]
  · have hn2 : 2 ≤ n := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn2
    have h := alpha_add_two_le_succ k
    have heq : 2 + k = k + 2 := by omega
    rw [heq]
    omega

/-- The three sets displayed in the manuscript, relabelled onto `Fin 4`. -/
def thirteenFamily : Finset (Finset (Fin 4)) :=
  {{0, 1, 2}, {0, 1, 3}, {2, 3}}

theorem thirteenFamily_card : thirteenFamily.card = 3 := by decide

theorem thirteenFamily_ideal_card : (generatedIdeal thirteenFamily).card = 13 := by decide

private theorem no_two_power_representation (a b c : ℕ)
    (ha : a ≤ 3) (hb : b ≤ 3) (hc : c ≤ 3) :
    13 + 2 ^ c ≠ 2 ^ a + 2 ^ b := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num

theorem two_generator_ideal_ne_thirteen {V : Type*} [DecidableEq V]
    (A B : Finset V) : (generatedIdeal {A, B}).card ≠ 13 := by
  intro h
  have hunion : generatedIdeal {A, B} = A.powerset ∪ B.powerset := by
    simp [generatedIdeal]
  have hinter : A.powerset ∩ B.powerset = (A ∩ B).powerset := by
    ext S
    simp only [Finset.mem_inter, Finset.mem_powerset]
    exact ⟨fun h ↦ Finset.subset_inter h.1 h.2,
      fun h ↦ ⟨h.trans Finset.inter_subset_left, h.trans Finset.inter_subset_right⟩⟩
  have hA : 2 ^ A.card ≤ 13 := by
    rw [← h, hunion, ← Finset.card_powerset]
    exact Finset.card_le_card Finset.subset_union_left
  have hB : 2 ^ B.card ≤ 13 := by
    rw [← h, hunion, ← Finset.card_powerset]
    exact Finset.card_le_card Finset.subset_union_right
  have hA3 : A.card ≤ 3 := by
    have hp : 2 ^ A.card < 2 ^ 4 := hA.trans_lt (by norm_num)
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hp
    omega
  have hB3 : B.card ≤ 3 := by
    have hp : 2 ^ B.card < 2 ^ 4 := hB.trans_lt (by norm_num)
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hp
    omega
  have hC3 : (A ∩ B).card ≤ 3 := (Finset.card_le_card Finset.inter_subset_left).trans hA3
  have hcard := Finset.card_union_add_card_inter A.powerset B.powerset
  rw [hinter, ← hunion, h] at hcard
  simp only [Finset.card_powerset] at hcard
  exact no_two_power_representation A.card B.card (A ∩ B).card hA3 hB3 hC3 hcard

theorem alpha_thirteen : alpha 13 = 3 := by
  have hupper : alpha 13 ≤ 3 := by
    simpa only [thirteenFamily_card, thirteenFamily_ideal_card] using
      alpha_le_of_family thirteenFamily
  have hpos := alpha_pos_of_pos (by norm_num : 0 < 13)
  by_contra hne
  have htwo : alpha 13 = 1 ∨ alpha 13 = 2 := by omega
  obtain ⟨m, G, hG, hc⟩ := alpha_hasGeneratorCount 13
  rcases htwo with h1 | h2
  · obtain ⟨A, rfl⟩ := Finset.card_eq_one.mp (hc.trans h1)
    exact two_generator_ideal_ne_thirteen A A (by simpa using hG)
  · obtain ⟨A, B, _, rfl⟩ := Finset.card_eq_two.mp (hc.trans h2)
    exact two_generator_ideal_ne_thirteen A B hG

/-- The complete finite base, including both endpoints. -/
theorem alpha_le_three_of_le_sixteen {n : ℕ} (hn : n ≤ 16) : alpha n ≤ 3 := by
  have hblocks : binaryBlockCount n ≤ 2 := by
    interval_cases n <;> decide
  exact (alpha_le_binaryBlockCount_add_one n).trans (by omega)

end AntichainOfGivenSize.Paper
