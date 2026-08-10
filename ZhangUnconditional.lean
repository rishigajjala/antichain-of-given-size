import ZhangSection6Construction
import ZhangClaim65Modular

namespace ZhangStageIntegration

open scoped BigOperators
open Finset
open ZhangSection6
open ZhangClaim65

/-- Claim 6.5 supplies the sole semantic input of the recursion. -/
theorem exactStageIncrement_proved : ExactStageIncrement := by
  intro r q h hq w T D Tnew dnew hpast hweight _hU
  rw [finiteHistoryGenerator, selectedIdeal_eq_stageIdeal]
  exact ZhangClaim65Modular.claim65_modular
    hq w T D Tnew dnew hpast hweight

/-- The concrete Section 6 construction, with no remaining hypotheses. -/
theorem constructionMatching :
    ZhangImprovedBound.MatchingSuccessorAtBits 10 8 16
      ZhangImprovedBound.constructionBits :=
  constructionMatching_of_exact exactStageIncrement_proved

/-- Unconditional formalization of Zhang's improved asymptotic bound. -/
theorem unconditionalRangeBasedImprovedReductionBound :
    ZhangImprovedBound.RangeBasedImprovedReductionBound := by
  exact ZhangImprovedBound.rangeBasedImprovedReductionBound_of_constructionMatching
    8 (by norm_num) constructionMatching

end ZhangStageIntegration

namespace ZhangImprovedBound

open Asymptotics Filter

/-- Theorem 6.10, exposed with the complete asymptotic formula unfolded. -/
theorem theorem6_10 :
    (fun n : ℕ ↦ (alpha n : ℝ)) =O[atTop]
      (fun n : ℕ ↦
        (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 2 /
          Real.logb 2 (Real.logb 2 (Real.logb 2 (n : ℝ)))) := by
  simpa [RangeBasedImprovedReductionBound, improvedScale] using
    ZhangStageIntegration.unconditionalRangeBasedImprovedReductionBound

end ZhangImprovedBound
