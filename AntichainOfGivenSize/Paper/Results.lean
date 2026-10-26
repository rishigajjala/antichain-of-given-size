import AntichainOfGivenSize.Paper.CountingParameters
import AntichainOfGivenSize.Paper.Representation
import AntichainOfGivenSize.Paper.BitMatching
import AntichainOfGivenSize.Paper.FirstUpper
import AntichainOfGivenSize.Paper.PatternGadget
import AntichainOfGivenSize.Paper.AlmostAll
import AntichainOfGivenSize.Paper.Extremal
import AntichainOfGivenSize.Paper.DirectReduction
import AntichainOfGivenSize.Paper.UpperConstructionBounds

/-!
# Unconditional statements for the current manuscript

This module discharges the counting and construction hypotheses used in
the intermediate files. These public certificates retain the quantifiers
in the paper; in particular the lower bound is a density-one statement.
The correspondence and differences in proof implementation are documented
in `docs/current-paper.md`.
-/

namespace AntichainOfGivenSize.Paper

theorem bitMatching : BitMatchingStatement :=
  fun q y hq ↦ BitMatching.exists_matching q y hq

/-- Theorem 6.1, with the stated constants 5 and 3. -/
theorem blockMatching : BlockMatchingStatement :=
  blockMatching_of_construction UpperConstruction.blockMatchingConstruction

/-- Theorem 5.1. -/
theorem firstUpper (q n : ℕ)
    (hnlo : 2 ^ (2 ^ (q + 1)) ≤ n) (hnhi : n < 2 ^ (2 ^ (q + 2))) :
    alpha n ≤ 4 * q ^ 2 + 3 := first_upper bitMatching q n hnlo hnhi

/-- Corollary 10.1 with the explicit square-root error exponent. -/
theorem typicalLowerBound : TypicalLowerBoundStatement :=
  typicalLowerBound_of_countingBound countingBound

/-- The lower-bound assertion of Theorem 1.1(ii). -/
theorem almostAllLowerBound : AlmostAllLowerBoundStatement :=
  almostAllLowerBound_of_countingBound countingBound

/-- Corollary 10.2: exceptions to either inequality have density zero. -/
theorem almostAllOrder : AlmostAllOrderStatement :=
  almostAllOrder_of_countingBound countingBound

/-- Equivalently, the proportion satisfying both bounds tends to one. -/
theorem almostAllGoodProportion : AlmostAllGoodProportionStatement :=
  almostAllGoodProportion_of_countingBound countingBound

/-- The extremal conclusion for every sufficiently large real cutoff. -/
theorem extremalOrder : ExtremalOrderStatement :=
  extremalOrder_of_countingBound countingBound

/-- Theorem 1.1, including the upper bound for all integers at least five,
the density-one order assertion, and the real-cutoff extremal order. -/
theorem mainTheorem :
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n →
      (alpha n : ℝ) ≤ C * quadraticLogLogScale (n : ℝ)) ∧
    AlmostAllOrderStatement ∧ ExtremalOrderStatement :=
  ⟨universalUpper_from_five, almostAllOrder, extremalOrder⟩

end AntichainOfGivenSize.Paper
