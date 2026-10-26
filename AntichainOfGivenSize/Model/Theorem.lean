import AntichainOfGivenSize.Model.Prelude
import AntichainOfGivenSize.Model.Prior
import AntichainOfGivenSize.Meta.ModelClosure
import AntichainOfGivenSize.Analysis.AttainableCountProof

/-!
# Counting attainable ideal sizes

Theorem 7.1 (`thm:attainable-count`) has one deterministic cardinality claim.
Its intended proof interface reuses `AntichainOfGivenSize.Paper.countingBound`;
it does not rederive the counting argument. The existing proof uses the larger
clustered encoding documented in `docs/current-paper.md`, rather than a
line-by-line transcription of the manuscript's fixed-header product.

Natural parameters represent the paper's integers on the positive range:
the absolute existential threshold may be enlarged to make `B` positive,
and the budget requires `1 ≤ K`. That threshold is independent of `K` and
is not identified with the proof's preliminary bound `2 ^ 20`.
The budget also supplies `0 < K` for the membership cross-check in Prelude.

The defining vocabulary of `Paper.attainableValues` is in
`Model/CountingVocabulary.lean`, retaining the existing names and definitions.
The statement's complete quantity dependency chain therefore lies within the
audit surface, while the counting and representation proofs stay outside it.
-/

namespace AntichainOfGivenSize

/-- Theorem 7.1: one absolute threshold gives the stated bound on the number
of distinct attainable ideal sizes for every admissible pair `B, K`.
The real arithmetic and the constant `100` are expanded for comparison with
the manuscript and `scripts/CheckPaperStatements.lean`. -/
theorem attainable_count (hprior : Prior) :
    ∃ B₀ : ℕ, ∀ B K : ℕ, B₀ ≤ B →
      (1 ≤ K ∧ (K : ℝ) ≤ (Real.logb 2 (B : ℝ)) ^ 2 /
        (100 * Real.logb 2 (Real.logb 2 (B : ℝ)))) →
      ((Paper.attainableValues B K).card : ℝ) ≤
        (2 : ℝ) ^ ((B : ℝ) - Real.sqrt (B : ℝ)) := by
    exact AntichainOfGivenSize.Analysis.AttainableCountProof.attainableCount hprior

end AntichainOfGivenSize

#modelClosureOfType AntichainOfGivenSize.attainable_count
#modelClosureOfType AntichainOfGivenSize.Model.attainableValues_membership
#print axioms AntichainOfGivenSize.attainable_count

-- Meta/Audit checks Model/ for surplus after loading every registered claim.
