import AntichainOfGivenSize.Analysis.Paper.CountingParameters
import AntichainOfGivenSize.Analysis.Paper.FaithfulCounting.CompleteCounting
import AntichainOfGivenSize.Analysis.Paper.LiteralBlockMatching
import AntichainOfGivenSize.Analysis.Paper.Representation
import AntichainOfGivenSize.Analysis.Paper.BitMatching
import AntichainOfGivenSize.Analysis.Paper.FirstUpper
import AntichainOfGivenSize.Analysis.Paper.PatternGadget
import AntichainOfGivenSize.Analysis.Paper.AlmostAll
import AntichainOfGivenSize.Analysis.Paper.Extremal
import AntichainOfGivenSize.Analysis.Paper.DirectReduction
import AntichainOfGivenSize.Analysis.Paper.UpperConstructionBounds
import AntichainOfGivenSize.Analysis.Paper.RealDensity

/-!
# Unconditional statements for the current manuscript

This module discharges the counting and construction hypotheses used in
the intermediate files. These public certificates retain the quantifiers
in the paper; in particular the lower bound is a density-one statement.
The correspondence and differences in proof implementation are documented
in `docs/current-paper.md`.
-/

namespace AntichainOfGivenSize.Paper

/-- Theorem 7.1, using the partition and record argument in Sections 8--10.1. -/
theorem faithfulCountingBound : CountingBoundStatement := by
  obtain ⟨B₀, _hB₀, hbound⟩ := FaithfulLower.exists_paper_counting_threshold
  refine ⟨B₀, ?_⟩
  intro B K hB hK
  exact hbound B hB K hK.1 hK.2

theorem bitMatching : BitMatchingStatement :=
  fun q y hq ↦ BitMatching.exists_matching q y hq

/-- Theorem 4.1 in its full integer-target form, including negative residues. -/
theorem bitMatchingInt (q : ℕ) (y : ℤ) (hq : 0 < q) :
    ∃ m : ℕ, 0 < m ∧ m < 2 ^ (2 ^ (q + 1)) ∧
      (m : ZMod (2 ^ (2 ^ q))) = (y : ZMod (2 ^ (2 ^ q))) ∧ alpha m ≤ 2 * q :=
  BitMatching.exists_matching_int q y hq

/-- Theorem 6.1, with the stated constants 5 and 3. -/
theorem blockMatching : BlockMatchingStatement :=
  LiteralUpperParameters.blockMatching

/-- Theorem 5.1. -/
theorem firstUpper (q n : ℕ)
    (hnlo : 2 ^ (2 ^ (q + 1)) ≤ n) (hnhi : n < 2 ^ (2 ^ (q + 2))) :
    alpha n ≤ 4 * q ^ 2 + 3 := first_upper bitMatching q n hnlo hnhi

/-- The asymptotic conclusion of Theorem 5.1, using only bit matching. -/
theorem quadraticUpper :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ ↦ (alpha n : ℝ))
      (fun n : ℕ ↦ (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 2) :=
  quadratic_upper_of_matching bitMatching

/-- Corollary 10.1 with the explicit square-root error exponent. -/
theorem typicalLowerBound : TypicalLowerBoundStatement :=
  typicalLowerBound_of_countingBound faithfulCountingBound

/-- The lower-bound assertion of Theorem 1.1(ii). -/
theorem almostAllLowerBound : AlmostAllLowerBoundStatement :=
  almostAllLowerBound_of_countingBound faithfulCountingBound

/-- Corollary 10.2: exceptions to either inequality have density zero. -/
theorem almostAllOrder : AlmostAllOrderStatement :=
  almostAllOrder_of_countingBound faithfulCountingBound

/-- Equivalently, the proportion satisfying both bounds tends to one. -/
theorem almostAllGoodProportion : AlmostAllGoodProportionStatement :=
  almostAllGoodProportion_of_countingBound faithfulCountingBound

/-- The same proportion limit for arbitrary real cutoffs, as displayed
in Corollary 10.2. -/
theorem realAlmostAllGoodProportion : RealAlmostAllGoodProportionStatement :=
  realAlmostAllGoodProportion_of_countingBound faithfulCountingBound

/-- The extremal conclusion for every sufficiently large real cutoff. -/
theorem extremalOrder : ExtremalOrderStatement :=
  extremalOrder_of_countingBound faithfulCountingBound

/-- Theorem 1.1, including the upper bound for all integers at least five,
the density-one order assertion, and the real-cutoff extremal order. -/
theorem mainTheorem :
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n →
      (alpha n : ℝ) ≤ C * quadraticLogLogScale (n : ℝ)) ∧
    AlmostAllOrderStatement ∧ ExtremalOrderStatement :=
  ⟨universalUpper_from_five, almostAllOrder, extremalOrder⟩

end AntichainOfGivenSize.Paper
