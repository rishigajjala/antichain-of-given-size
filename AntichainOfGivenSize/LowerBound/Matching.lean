import AntichainOfGivenSize.LowerBound.ClusterSparsityAssembly

/-!
# Matching lower bound

Public, hypothesis-free statements of the connected-cluster obstruction.  The
first theorem exposes the constant produced by the formal proof.  The second
states the usual infinitely-often asymptotic lower bound.
-/

namespace AntichainOfGivenSize

/-- Explicit infinitely-often lower bound at the quadratic-over-log scale. -/
theorem matchingLowerBoundInfinitelyOften_explicit :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (1 / 4096 : ℝ) *
          ((Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 2 /
            Real.logb 2 (Real.logb 2 (Real.logb 2 (n : ℝ)))) ≤
        (alpha n : ℝ) := by
  simpa [improvedScale] using
    ClusterLowerBound.matchingLowerBoundInfinitelyOften

/-- There is a fixed positive constant for which the matching lower bound
holds at arbitrarily large inputs. -/
theorem matchingLowerBoundInfinitelyOften :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      c * ((Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 2 /
          Real.logb 2 (Real.logb 2 (Real.logb 2 (n : ℝ)))) ≤
        (alpha n : ℝ) := by
  rcases ClusterLowerBound.hasMatchingLowerBoundInfinitelyOften with
    ⟨c, hc, hbound⟩
  exact ⟨c, hc, by simpa [improvedScale] using hbound⟩

end AntichainOfGivenSize
