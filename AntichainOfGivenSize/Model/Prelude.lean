import AntichainOfGivenSize.Model.CountingVocabulary
import AntichainOfGivenSize.Paper.Representation
import AntichainOfGivenSize.Analysis.AttainableValuesMembershipProof

/-!
# The attainable-size counting surface

This surface reuses the existing definitions without introducing a second
representation. Their defining vocabulary is in `Model/CountingVocabulary.lean`;
the original proof modules import those same declarations. Its sole cross-check spells out the semantics of the counted
values; the later proof pass can reuse `Paper.mem_attainableValues_iff`.
-/

namespace AntichainOfGivenSize.Model

/-! ## Vocabulary

`AntichainOfGivenSize.generatedIdeal G` is the finite union of the powersets
of the generators in `G`, implemented by `Finset.biUnion` and `Finset.powerset`.
Its `Finset.card` counts subsets, not elements in the union of the generators.

`Paper.HasBoundedGeneratingFamily B K n` quantifies an arbitrary natural
ambient size `N` and a family `G : Finset (Finset (Fin N))`. It requires
`G.Nonempty`, `G.card ≤ K`, every generator's cardinality at most `B`, and
`(generatedIdeal G).card = n`. There is no upper bound on `N`. In particular,
`Fin 0` is allowed. The family, rather than each generator, must be nonempty:
a nonempty family of empty generators has generated-ideal cardinality `1`.
Tuple order and repeated generators do not change this union of powersets;
the existing membership bridge accounts for deduplication and padding.
Redundant generators are permitted.

`Paper.AdmissibleBudget B K` is exactly `1 ≤ K` together with the real bound
`(K : ℝ) ≤ (Real.logb 2 (B : ℝ)) ^ 2 /
  (100 * Real.logb 2 (Real.logb 2 (B : ℝ)))`.
The headline expands this budget. All logarithms are base two; `Real.sqrt`
and real exponentiation retain the paper's unrounded square-root saving.
-/

/-! ## The quantity

The quantity bounded by the headline is
`((Paper.attainableValues B K).card : ℝ)`. The existing finite set
`Paper.attainableValues` is the image of the bounded profiles under their
exact generated-ideal cardinalities. Each natural value is counted once,
with no residue reduction or restriction to values below `2 ^ B`.

The cross-check below exposes the family semantics of this implementation.
It is deliberately guarded by `0 < K`; in the headline's range this follows
from the first conjunct of the budget, rather than a separate assumption.
-/

/-- Cross-check `Paper.attainableValues` against the expanded definition of
`Paper.HasBoundedGeneratingFamily`, using the existing result
`Paper.mem_attainableValues_iff`. This also matches the independent membership
contract in `scripts/CheckPaperStatements.lean`. -/
theorem attainableValues_membership {B K n : ℕ} (hK : 0 < K) :
    n ∈ Paper.attainableValues B K ↔
      ∃ N : ℕ, ∃ G : Finset (Finset (Fin N)),
        G.Nonempty ∧ G.card ≤ K ∧
          (∀ A ∈ G, A.card ≤ B) ∧ (generatedIdeal G).card = n := by
    exact AntichainOfGivenSize.Analysis.AttainableCountProof.attainableValuesMembership (B := B) (K := K) (n := n) hK

end AntichainOfGivenSize.Model
