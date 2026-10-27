import AntichainOfGivenSize.Model.Prelude
import AntichainOfGivenSize.Paper.RealDensity
import AntichainOfGivenSize.Model.Prior
import AntichainOfGivenSize.Meta.ModelClosure
import AntichainOfGivenSize.Analysis.AttainableCountProof

/-- INTERNAL: transfers a density-one lower bound to simultaneous natural and real cutoff proportions under an eventual upper bound. -/
theorem AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.simultaneousDensityOne
    (hprior : AntichainOfGivenSize.Prior)
    (c C : ℝ) (n₀ : ℕ)
    (hupper : ∀ n : ℕ, n₀ ≤ n →
      (AntichainOfGivenSize.alpha n : ℝ) ≤ C * AntichainOfGivenSize.quadraticLogLogScale (n : ℝ))
    (hlower : Filter.Tendsto
      (fun N : ℕ ↦
        (((Finset.Icc 5 N).filter fun n : ℕ ↦
          c * AntichainOfGivenSize.quadraticLogLogScale (n : ℝ) ≤ (AntichainOfGivenSize.alpha n : ℝ)).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1)) :
    Filter.Tendsto
      (fun N : ℕ ↦ ((AntichainOfGivenSize.Paper.goodInputs c C N).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) ∧
    Filter.Tendsto
      (fun X : ℝ ↦ ((AntichainOfGivenSize.Paper.realGoodInputs c C X).card : ℝ) / X)
      Filter.atTop (nhds 1) := by
  have _ := hprior
  classical
  let S : ℕ → Finset ℕ := fun N =>
    (Finset.Icc 5 N).filter fun n : ℕ =>
      c * AntichainOfGivenSize.quadraticLogLogScale (n : ℝ) ≤
        (AntichainOfGivenSize.alpha n : ℝ)
  have hcard (N : ℕ) : (S N).card ≤
      (AntichainOfGivenSize.Paper.goodInputs c C N).card + n₀ := by
    have hsub : S N ⊆ AntichainOfGivenSize.Paper.goodInputs c C N ∪ Finset.range n₀ := by
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      by_cases h : n₀ ≤ n
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨hn'.1, hn'.2, hupper n h⟩
      · apply Finset.mem_union_right
        exact Finset.mem_range.mpr (Nat.lt_of_not_ge h)
    calc
      (S N).card ≤ (AntichainOfGivenSize.Paper.goodInputs c C N ∪ Finset.range n₀).card :=
        Finset.card_le_card hsub
      _ ≤ (AntichainOfGivenSize.Paper.goodInputs c C N).card + (Finset.range n₀).card :=
        Finset.card_union_le _ _
      _ = _ := by simp
  have hcardUpper (N : ℕ) :
      (AntichainOfGivenSize.Paper.goodInputs c C N).card ≤ N := by
    have hs : AntichainOfGivenSize.Paper.goodInputs c C N ⊆ Finset.Icc 5 N := by
      intro n hn
      exact (Finset.mem_filter.mp hn).1
    have h := Finset.card_le_card hs
    rw [Nat.card_Icc] at h
    omega
  have hlow : Filter.Tendsto
      (fun N : ℕ => ((S N).card : ℝ) / (N : ℝ) - (n₀ : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) := by
    have hz : Filter.Tendsto (fun N : ℕ => (n₀ : ℝ) / (N : ℝ))
        Filter.atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat _
    simpa [S] using hlower.sub hz
  have hnat : Filter.Tendsto
      (fun N : ℕ => ((AntichainOfGivenSize.Paper.goodInputs c C N).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
      have hc := hcard N
      have hnr : (0 : ℝ) < N := by exact_mod_cast hN
      have hc' : ((S N).card : ℝ) ≤
          ((AntichainOfGivenSize.Paper.goodInputs c C N).card : ℝ) + n₀ := by
        exact_mod_cast hc
      calc
        ((S N).card : ℝ) / (N : ℝ) - (n₀ : ℝ) / (N : ℝ) =
            (((S N).card : ℝ) - (n₀ : ℝ)) / (N : ℝ) := by ring
        _ ≤ ((AntichainOfGivenSize.Paper.goodInputs c C N).card : ℝ) / (N : ℝ) :=
            (div_le_div_iff₀ hnr hnr).2 (by nlinarith [hc'])
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
      have hc := hcardUpper N
      have hnr : (0 : ℝ) < N := by exact_mod_cast hN
      apply (div_le_iff₀ hnr).2
      have hc' : ((AntichainOfGivenSize.Paper.goodInputs c C N).card : ℝ) ≤
          (N : ℝ) := by exact_mod_cast hc
      simpa using hc'
  constructor
  · exact hnat
  · have hprod : Filter.Tendsto (fun X : ℝ =>
        (((AntichainOfGivenSize.Paper.goodInputs c C ⌊X⌋₊).card : ℝ) /
          (⌊X⌋₊ : ℝ)) * ((⌊X⌋₊ : ℝ) / X))
        Filter.atTop (nhds 1) := by
      simpa using (hnat.comp tendsto_nat_floor_atTop).mul
        (tendsto_nat_floor_div_atTop (R := ℝ))
    apply hprod.congr'
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with X hX
    have hfloor : 1 ≤ ⌊X⌋₊ := (Nat.one_le_floor_iff X).2 hX
    have hfloor0 : (⌊X⌋₊ : ℝ) ≠ 0 := by
      exact_mod_cast (show ⌊X⌋₊ ≠ 0 by omega)
    dsimp [AntichainOfGivenSize.Paper.realGoodInputs]
    field_simp

namespace AntichainOfGivenSize

/-- Internal transfer lemma. The unconditional main theorem supplies both premises
and the positive constants before applying it. -/
theorem alpha_simultaneous_density_one (hprior : Prior)
    (c C : ℝ) (n₀ : ℕ)
    (hupper : ∀ n : ℕ, n₀ ≤ n →
      (alpha n : ℝ) ≤ C * quadraticLogLogScale (n : ℝ))
    (hlower : Filter.Tendsto
      (fun N : ℕ ↦
        (((Finset.Icc 5 N).filter fun n : ℕ ↦
          c * quadraticLogLogScale (n : ℝ) ≤ (alpha n : ℝ)).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1)) :
    Filter.Tendsto
      (fun N : ℕ ↦ ((Paper.goodInputs c C N).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) ∧
    Filter.Tendsto
      (fun X : ℝ ↦ ((Paper.realGoodInputs c C X).card : ℝ) / X)
      Filter.atTop (nhds 1) := by
    exact AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.simultaneousDensityOne hprior c C n₀ hupper hlower

end AntichainOfGivenSize

#modelClosureOfType AntichainOfGivenSize.alpha_simultaneous_density_one
