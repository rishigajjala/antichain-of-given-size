import AntichainOfGivenSize.Model.ProblemSetting
import AntichainOfGivenSize.Analysis.Paper.Representation

/-- PAPER: paper/Generating_Antichains_Simplified.tex:981-986
Proof-side owner for `AntichainOfGivenSize.Model.attainableValues_membership`.
Reuses the established representation equivalence, expanding its finite-family predicate. -/
theorem AntichainOfGivenSize.Analysis.AttainableCountProof.attainableValuesMembership {B K n : ℕ} (hK : 0 < K) :
    n ∈ AntichainOfGivenSize.Paper.attainableValues B K ↔
      ∃ N : ℕ, ∃ G : Finset (Finset (Fin N)),
        G.Nonempty ∧ G.card ≤ K ∧
          (∀ A ∈ G, A.card ≤ B) ∧
            (AntichainOfGivenSize.generatedIdeal G).card = n := by
  exact AntichainOfGivenSize.Paper.mem_attainableValues_iff hK

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · reused `Paper.mem_attainableValues_iff` by definitional equality.
-/
