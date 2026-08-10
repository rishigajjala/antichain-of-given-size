import AntichainOfGivenSize.Section6.Construction
import AntichainOfGivenSize.Section6.ModularIncrement

namespace AntichainOfGivenSize.Section6.Construction

open scoped BigOperators
open Finset
open AntichainOfGivenSize.Section6
open AntichainOfGivenSize.Section6.Blocks

/-- Claim 6.5 supplies the sole semantic input of the recursion. -/
theorem exactStageIncrement_proved : ExactStageIncrement := by
  intro r q h hq w T D Tnew dnew hpast hweight _hU
  rw [finiteHistoryGenerator, selectedIdeal_eq_stageIdeal]
  exact AntichainOfGivenSize.Section6.Modular.claim65_modular
    hq w T D Tnew dnew hpast hweight

/-- The concrete Section 6 construction, with no remaining hypotheses. -/
theorem constructionMatching :
    AntichainOfGivenSize.MatchingSuccessorAtBits 10 8 16
      AntichainOfGivenSize.constructionBits :=
  constructionMatching_of_exact exactStageIncrement_proved

/-- Unconditional formalization of the improved asymptotic bound. -/
theorem unconditionalRangeBasedImprovedReductionBound :
    AntichainOfGivenSize.RangeBasedImprovedReductionBound := by
  exact AntichainOfGivenSize.rangeBasedImprovedReductionBound_of_constructionMatching
    8 (by norm_num) constructionMatching

end AntichainOfGivenSize.Section6.Construction

namespace AntichainOfGivenSize

open Asymptotics Filter

/-- Theorem 6.10, exposed with the complete asymptotic formula unfolded. -/
theorem theorem6_10 :
    (fun n : ℕ ↦ (alpha n : ℝ)) =O[atTop]
      (fun n : ℕ ↦
        (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 2 /
          Real.logb 2 (Real.logb 2 (Real.logb 2 (n : ℝ)))) := by
  simpa [RangeBasedImprovedReductionBound, improvedScale] using
    AntichainOfGivenSize.Section6.Construction.unconditionalRangeBasedImprovedReductionBound

end AntichainOfGivenSize
