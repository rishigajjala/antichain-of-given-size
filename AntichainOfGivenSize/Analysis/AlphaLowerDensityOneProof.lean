import AntichainOfGivenSize.Model.Prelude
import AntichainOfGivenSize.Paper.RealDensity
import AntichainOfGivenSize.Model.Prior
import AntichainOfGivenSize.Meta.ModelClosure
import AntichainOfGivenSize.Analysis.AttainableCountProof

open Filter
open scoped Topology

/-- PAPER: paper/Generating_Antichains_Simplified.tex:1450-1475
Proof-side owner for `AntichainOfGivenSize.alpha_lower_density_one`.

Reuse `Paper.density_of_countingBound` with the checked counting interface,
then take the complement in `[5,N]`. The constant is the paper's `1/800`.
As documented in `docs/current-paper.md`, the reused density proof applies
one all-values count using eventual monotonicity, rather than summing the
paper's dyadic blocks. The four omitted positive integers contribute `4/N`.
No additional assumption is extracted from `Prior`. -/
theorem AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.lowerDensityOne
    (hprior : AntichainOfGivenSize.Prior) :
    ∃ c : ℝ, 0 < c ∧ Filter.Tendsto
      (fun N : ℕ ↦
        (((Finset.Icc 5 N).filter fun n : ℕ ↦
          c * AntichainOfGivenSize.quadraticLogLogScale (n : ℝ) ≤ (AntichainOfGivenSize.alpha n : ℝ)).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) := by
  classical
  refine ⟨1 / 800, by norm_num, ?_⟩
  have hbad := AntichainOfGivenSize.Paper.density_of_countingBound
    (AntichainOfGivenSize.Analysis.AttainableCountProof.attainableCount hprior)
  have hlim : Tendsto (fun N : ℕ ↦
      1 - (4 : ℝ) / N -
        ((AntichainOfGivenSize.Paper.exceptionalInputs (1 / 800) N).card : ℝ) / N)
      atTop (nhds 1) := by
    convert ((tendsto_const_nhds.sub
      (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ))).sub hbad) using 1
    norm_num
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 5] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hcard :
      ((Finset.Icc 5 N).filter fun n : ℕ ↦
        (1 / 800 : ℝ) * AntichainOfGivenSize.quadraticLogLogScale (n : ℝ) ≤
          (AntichainOfGivenSize.alpha n : ℝ)).card +
      (AntichainOfGivenSize.Paper.exceptionalInputs (1 / 800) N).card =
        (Finset.Icc 5 N).card := by
    simpa only [AntichainOfGivenSize.Paper.exceptionalInputs, not_le] using
      (Finset.card_filter_add_card_filter_not
        (s := Finset.Icc 5 N) (fun n : ℕ ↦
          (1 / 800 : ℝ) * AntichainOfGivenSize.quadraticLogLogScale (n : ℝ) ≤
            (AntichainOfGivenSize.alpha n : ℝ)))
  have hIcc : (Finset.Icc 5 N).card = N - 4 := by rw [Nat.card_Icc]; omega
  rw [hIcc] at hcard
  have hcardR := congrArg (fun z : ℕ ↦ (z : ℝ)) hcard
  simp only [Nat.cast_add, Nat.cast_sub (show 4 ≤ N by omega), Nat.cast_ofNat] at hcardR
  calc
    _ = ((N : ℝ) - 4 -
        ((AntichainOfGivenSize.Paper.exceptionalInputs (1 / 800) N).card : ℝ)) / N := by
      rw [sub_div, sub_div, div_self hN0]
    _ = _ := by
      congr 1
      linarith

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · reused the checked exception-density estimate and converted its complement to density one with constant `1/800`.
-/
