import AntichainOfGivenSize.BasicLemmas
import AntichainOfGivenSize.Model.Prior

-- The fixed interface retains hypotheses not needed by the stronger reused lemma.
set_option linter.unusedVariables false in
/-- PAPER: paper/Generating_Antichains_Simplified.tex:240–252
Splitting for positive natural inputs, reusing `AntichainOfGivenSize.splittingLemma`.
The reused proof relabels the ground sets to be disjoint; the generated ideals
intersect in `{∅}`, so their union has size `m + (n + 1) - 1 = m + n`.
The generator-family union has cardinality at most the sum of the two counts. -/
theorem AntichainOfGivenSize.Analysis.AlphaSplittingProof.splitting (hprior : AntichainOfGivenSize.Prior) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : AntichainOfGivenSize.alpha (m + n) ≤ AntichainOfGivenSize.alpha m + AntichainOfGivenSize.alpha (n + 1) := by
  exact AntichainOfGivenSize.splittingLemma m n hm

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · reused `AntichainOfGivenSize.splittingLemma` with the statement unchanged.
-/
