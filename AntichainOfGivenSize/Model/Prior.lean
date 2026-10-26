/-!
# What this development assumes

The results this proof takes from prior work — cited, standard, or folklore —
stated as the hypotheses they are. `Prior` is a field per borrowed result, and the
theorem carries it as `(hprior : Prior)`, so what was granted is in the statement
rather than in a `sorry` somewhere under it.

When a later theorem needs assumptions the earlier theorems do not need, this
file may also hold another theorem-specific structure. Existing structures are
not widened just to state a new result.

It remains empty after reviewing the paper: the project proves the required
mathematical results using Lean and Mathlib, with no additional unproved
hypotheses. The value `hprior` is therefore discharged by `⟨⟩`.
-/

namespace AntichainOfGivenSize

/-- Every result this development takes from prior work rather than proving. -/
-- TEX2LEAN: external-prior fields
structure Prior : Prop where

end AntichainOfGivenSize
