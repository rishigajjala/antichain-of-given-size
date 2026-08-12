import AntichainOfGivenSize.LowerBound.Matching
import AntichainOfGivenSize.Theorem
import AntichainOfGivenSize.AntichainReduction

/-!
# Certificates for the main statements

The full mathematical contract is in `AntichainOfGivenSize.MainStatement`.
This short file certifies the antichain semantics of `alpha` and connects the
three named bound propositions to their proof implementations.
-/

namespace AntichainOfGivenSize

/-- The implementation-facing minimum `alpha` is attained by a generating
antichain, certifying agreement with the paper's problem definition. -/
theorem mainAlphaHasAntichainWitness (n : ℕ) :
    HasAntichainGeneratorCount n (alpha n) :=
  alpha_hasAntichainGeneratorCount n

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

end AntichainOfGivenSize
