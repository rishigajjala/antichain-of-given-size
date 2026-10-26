import AntichainOfGivenSize.Paper.Extremal

/-! Corollary 10.2, both as a density-zero exceptional set and as the
literal displayed limit for simultaneous good inputs. -/

open Finset Filter
open scoped Topology

namespace AntichainOfGivenSize.Paper

theorem orderExceptions_eq_exceptionalInputs {c C : ℝ}
    (hupper : ∀ n : ℕ, 5 ≤ n → (alpha n : ℝ) ≤ C * quadraticLogLogScale n)
    (X : ℕ) : orderExceptions c C X = exceptionalInputs c X := by
  classical
  apply Finset.filter_congr
  intro n hn
  rw [and_iff_left (hupper n (Finset.mem_Icc.mp hn).1), not_le]

theorem almostAllOrder_of_countingBound
    (hcount : CountingBoundStatement) : AlmostAllOrderStatement := by
  obtain ⟨C, hC, hupper⟩ := universalUpper_from_five
  refine ⟨1 / 800, C, by norm_num, hC, ?_⟩
  simpa only [orderExceptions_eq_exceptionalInputs hupper] using density_of_countingBound hcount

theorem goodInputs_card_add_orderExceptions_card (c C : ℝ) (X : ℕ) :
    (goodInputs c C X).card + (orderExceptions c C X).card = (Finset.Icc 5 X).card := by
  classical
  exact Finset.card_filter_add_card_filter_not _

/-- The finite omission of `0,1,2,3,4` disappears after normalization. -/
theorem almostAllGoodProportion_of_order
    (horder : AlmostAllOrderStatement) : AlmostAllGoodProportionStatement := by
  obtain ⟨c, C, hc, hC, hbad⟩ := horder
  refine ⟨c, C, hc, hC, ?_⟩
  have hlim : Tendsto (fun X : ℕ ↦
      1 - (4 : ℝ) / X - ((orderExceptions c C X).card : ℝ) / X) atTop (nhds 1) := by
    convert ((tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ))).sub hbad)
      using 1
    norm_num
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 5] with X hX
  have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
  have hcard := goodInputs_card_add_orderExceptions_card c C X
  have hIcc : (Finset.Icc 5 X).card = X - 4 := by rw [Nat.card_Icc]; omega
  rw [hIcc] at hcard
  have hcardR : ((goodInputs c C X).card : ℝ) +
      ((orderExceptions c C X).card : ℝ) = (X : ℝ) - 4 := by
    have h := congrArg (fun z : ℕ ↦ (z : ℝ)) hcard
    simpa only [Nat.cast_add, Nat.cast_sub (show 4 ≤ X by omega), Nat.cast_ofNat] using h
  field_simp
  nlinarith

theorem almostAllGoodProportion_of_countingBound
    (hcount : CountingBoundStatement) : AlmostAllGoodProportionStatement :=
  almostAllGoodProportion_of_order (almostAllOrder_of_countingBound hcount)

end AntichainOfGivenSize.Paper
