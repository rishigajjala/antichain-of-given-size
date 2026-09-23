import AntichainOfGivenSize.BlockCount.FiniteIncrement
import AntichainOfGivenSize.BlockCount.AssembledError

/-!
# The sharp block-count upper bound is attained

For each positive number of binary blocks, a finite dyadic-scale recurrence
produces a positive integer whose ideal needs exactly one more generator.
The proof uses no compactness or unproved asymptotic step.
-/

namespace AntichainOfGivenSize.BlockCount

/-- All normalized cluster errors are controlled by the finite gap budget. -/
theorem finiteGeometricBound_proved : FiniteGeometricBound := by
  intro terms p t k j hcost hgap
  exact assembledClusters_error_le_of_exponent_gap terms t k
    (finiteScale p k j) (finiteScale p k (j + 1)) hcost hgap

/-- The explicit finite threshold reduces cost in every concrete instance. -/
theorem finiteThreshold_costReduction_proved (p k t : ℕ)
    (ht : finiteThreshold p k ≤ t)
    (hrepr : HasDyadicIdealSum ((2 ^ t * p + 1 : ℕ) : ℚ) k) :
    HasDyadicIdealSum (p : ℚ) (k - 1) :=
  finiteThreshold_costReduction finiteGeometricBound_proved p k t ht hrepr

/-- A long enough binary gap forces one more unit of scaled-ideal cost. -/
theorem dyadicCostReduction_proved : DyadicCostReduction :=
  dyadicCostReduction_of_finiteGeometricBound finiteGeometricBound_proved

/-- For every positive block count `b`, the universal bound `b+1` is attained. -/
theorem blockCount_bound_tight : BlockCountTightBoundStatement := by
  intro b hb
  exact blockCount_bound_tight_of_costReduction dyadicCostReduction_proved b hb

end AntichainOfGivenSize.BlockCount
