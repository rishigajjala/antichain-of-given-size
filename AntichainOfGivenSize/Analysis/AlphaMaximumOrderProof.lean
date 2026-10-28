import AntichainOfGivenSize.Model.Prelude
import AntichainOfGivenSize.Analysis.Paper.RealDensity
import AntichainOfGivenSize.Model.Prior
import AntichainOfGivenSize.Meta.ModelClosure
import AntichainOfGivenSize.Analysis.AttainableCountProof

/-- PAPER: paper/Generating_Antichains_Simplified.tex:166-168
Proof-side owner for `AntichainOfGivenSize.alpha_maximum_order`.

This interface reuses the real-cutoff bounds in `Paper.Extremal`, converting
their norm inequalities to explicit positive comparison constants. The lower
bound uses `attainableCount` through the existing counting-to-density argument
and a good integer in a sufficiently large interval. This differs from the
manuscript's dyadic-block argument at lines 1480-1514, as documented in
`docs/current-paper.md`. The upper bound absorbs the finite initial segment.
No additional assumption or new extremal estimate is introduced. -/
theorem AntichainOfGivenSize.Analysis.AlphaAsymptoticOrderProof.maximumOrder
    (hprior : AntichainOfGivenSize.Prior) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∃ X₀ : ℝ, 4 < X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        a * AntichainOfGivenSize.quadraticLogLogScale X ≤ (AntichainOfGivenSize.Paper.maximumBelow X : ℝ) ∧
        (AntichainOfGivenSize.Paper.maximumBelow X : ℝ) ≤ A * AntichainOfGivenSize.quadraticLogLogScale X := by
  obtain ⟨A, hA, hupper⟩ := Asymptotics.isBigO_iff'.mp
    AntichainOfGivenSize.Paper.extremal_upper
  obtain ⟨D, hD, hlower⟩ := Asymptotics.isBigO_iff'.mp
    (AntichainOfGivenSize.Paper.extremal_lower_of_countingBound
      (AntichainOfGivenSize.Analysis.AttainableCountProof.attainableCount hprior))
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.mp hupper
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hlower
  refine ⟨1 / D, A, one_div_pos.mpr hD, hA, max 5 (max U L), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  intro X hX
  have hX5 : 5 ≤ X := (le_max_left _ _).trans hX
  have hUX : U ≤ X := (le_max_left U L).trans ((le_max_right _ _).trans hX)
  have hLX : L ≤ X := (le_max_right U L).trans ((le_max_right _ _).trans hX)
  have hg : 0 ≤ AntichainOfGivenSize.quadraticLogLogScale X :=
    (AntichainOfGivenSize.Paper.growth_pos_of_four_lt (by linarith)).le
  have hmax : 0 ≤ (AntichainOfGivenSize.Paper.maximumBelow X : ℝ) := Nat.cast_nonneg _
  have hu := hU X hUX
  have hl := hL X hLX
  simp only [Real.norm_eq_abs, abs_of_nonneg hg, abs_of_nonneg hmax] at hu hl
  refine ⟨?_, hu⟩
  calc
    (1 / D) * AntichainOfGivenSize.quadraticLogLogScale X =
        AntichainOfGivenSize.quadraticLogLogScale X / D := by ring
    _ ≤ (AntichainOfGivenSize.Paper.maximumBelow X : ℝ) :=
      (div_le_iff₀ hD).2 (by simpa only [mul_comm] using hl)

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · converted the existing real extremal bounds to explicit constants, using `attainableCount` for the lower bound; no new helper lemmas.
-/
