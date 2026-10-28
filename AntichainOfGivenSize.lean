import AntichainOfGivenSize.Analysis.BlockCount.Tight
import AntichainOfGivenSize.Analysis.BlockCount.ExplicitWitness
import AntichainOfGivenSize.Analysis.LowerBound.InfinitelyOften
import AntichainOfGivenSize.Analysis.LowerBound.CarrySensitive
import AntichainOfGivenSize.Analysis.LowerBound.ThresholdFiltration
import AntichainOfGivenSize.Analysis.LowerBound.VennProfiles
import AntichainOfGivenSize.Analysis.LowerBound.Conductor
import AntichainOfGivenSize.Analysis.Supporting.MainTheorems
import AntichainOfGivenSize.Analysis.Paper.Results
import AntichainOfGivenSize.Analysis.Paper.FaithfulCounting.CompleteCounting
import AntichainOfGivenSize.Meta.Audit
import AntichainOfGivenSize.Analysis.Paper.TypicalGoodEvent
import AntichainOfGivenSize.Analysis.Paper.FiniteTwoGeneratorBound
import AntichainOfGivenSize.Analysis.Paper.FaithfulCounting.ExactClaimBundles
import AntichainOfGivenSize.Analysis.Paper.TypicalProbability

/-!
# Antichain of a Given Size

Umbrella module for the unconditional upper and lower bounds on the minimum
size of a family generating an ideal of prescribed cardinality, including
the current manuscript's density-one and real-cutoff extremal results.
It also exports the sharp worst-case bound at each positive binary block count.
-/
