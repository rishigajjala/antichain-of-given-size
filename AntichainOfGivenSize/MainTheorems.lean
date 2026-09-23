import AntichainOfGivenSize.LowerBound.Matching
import AntichainOfGivenSize.Theorem
import AntichainOfGivenSize.AntichainReduction
import AntichainOfGivenSize.BlockCount.ExplicitWitness
import AntichainOfGivenSize.LowerBound.IdealBlockCount

/-!
# Certificates for the main statements

The full mathematical contract is in `AntichainOfGivenSize.MainStatement`.
This short file connects each named theorem claim to its proof implementation.
-/

namespace AntichainOfGivenSize

/-- The implementation-facing minimum `alpha` is attained by a generating
antichain, certifying agreement with the paper's problem definition. -/
theorem mainAlphaHasAntichainWitness : AlphaAntichainWitnessStatement :=
  fun n => alpha_hasAntichainGeneratorCount n

/-- The main upper-bound statement is proved unconditionally. -/
theorem mainUpperBound : UpperBoundStatement := by
  simpa [UpperBoundStatement, quadraticLogLogScale] using theorem6_10

/-- The explicit main lower-bound statement is proved unconditionally. -/
theorem mainLowerBound_explicit : ExplicitLowerBoundStatement := by
  simpa [ExplicitLowerBoundStatement, quadraticLogLogScale] using
    matchingLowerBoundInfinitelyOften_explicit

/-- The main infinitely-often lower-bound statement is proved
unconditionally. -/
theorem mainLowerBound : LowerBoundStatement := by
  simpa [LowerBoundStatement, quadraticLogLogScale] using
    matchingLowerBoundInfinitelyOften

/-- The pointwise logarithmic lower bound from binary blocks. -/
theorem mainBlockCountLowerBound : BlockCountLowerBoundStatement :=
  logb_binaryBlockCount_le_alpha

/-- The pointwise upper bound from binary blocks. -/
theorem mainBlockCountUpperBound : BlockCountUpperBoundStatement :=
  alpha_le_binaryBlockCount_add_one

/-- The upper bound is sharp for each positive number of blocks. -/
theorem mainBlockCountTightBound : BlockCountTightBoundStatement :=
  BlockCount.blockCount_bound_tight

/-- The explicit recursive integers attain the upper bound. -/
theorem mainExplicitBlockWitness : ExplicitBlockWitnessStatement :=
  BlockCount.explicitBlockWitness_spec

end AntichainOfGivenSize
