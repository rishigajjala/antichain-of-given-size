import AntichainOfGivenSize.Analysis.Paper.AlmostAll

/-!
# The almost-all proportion at real cutoffs

The natural-density theorem also gives the manuscript's displayed limit
when the cutoff `X` varies over the real numbers. The exact set of good
integers below a real cutoff is obtained by taking its natural floor;
the factor `floor(X)/X` tends to one.
-/

open Finset Filter
open scoped Topology

namespace AntichainOfGivenSize.Paper

theorem mem_realGoodInputs_iff {c C X : ℝ} {n : ℕ} (hX : 0 ≤ X) :
    n ∈ realGoodInputs c C X ↔
      5 ≤ n ∧ (n : ℝ) ≤ X ∧
        c * quadraticLogLogScale (n : ℝ) ≤ (alpha n : ℝ) ∧
        (alpha n : ℝ) ≤ C * quadraticLogLogScale (n : ℝ) := by
  simp only [realGoodInputs, goodInputs, Finset.mem_filter, Finset.mem_Icc,
    Nat.le_floor_iff hX]
  tauto

/-- Corollary 10.2 with an arbitrary real cutoff. -/
def RealAlmostAllGoodProportionStatement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ Tendsto
    (fun X : ℝ ↦ ((realGoodInputs c C X).card : ℝ) / X)
    atTop (nhds 1)

theorem realAlmostAllGoodProportion_of_nat
    (hgood : AlmostAllGoodProportionStatement) : RealAlmostAllGoodProportionStatement := by
  obtain ⟨c, C, hc, hC, hlim⟩ := hgood
  refine ⟨c, C, hc, hC, ?_⟩
  have hprod : Tendsto (fun X : ℝ ↦
      (((goodInputs c C ⌊X⌋₊).card : ℝ) / (⌊X⌋₊ : ℝ)) * ((⌊X⌋₊ : ℝ) / X))
      atTop (nhds 1) := by
    simpa using (hlim.comp tendsto_nat_floor_atTop).mul
      (tendsto_nat_floor_div_atTop (R := ℝ))
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have hfloor : 1 ≤ ⌊X⌋₊ := (Nat.one_le_floor_iff X).2 hX
  have hfloor0 : (⌊X⌋₊ : ℝ) ≠ 0 := by
    exact_mod_cast (show ⌊X⌋₊ ≠ 0 by omega)
  dsimp [realGoodInputs]
  field_simp

theorem realAlmostAllGoodProportion_of_countingBound
    (hcount : CountingBoundStatement) : RealAlmostAllGoodProportionStatement :=
  realAlmostAllGoodProportion_of_nat (almostAllGoodProportion_of_countingBound hcount)

end AntichainOfGivenSize.Paper
