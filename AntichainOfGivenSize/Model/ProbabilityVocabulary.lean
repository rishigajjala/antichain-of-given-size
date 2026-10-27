import Mathlib.Probability.Distributions.Uniform

namespace AntichainOfGivenSize.Paper

/-- Uniform sampling of a natural number from the paper's half-open dyadic block.
The positive index supplies a nonempty sample space. -/
noncomputable def dyadicUniformPMF (B : ℕ) (hB : 1 ≤ B) : PMF ℕ :=
  PMF.uniformOfFinset (Finset.Ico (2 ^ (B - 1)) (2 ^ B))
    (Finset.nonempty_Ico.mpr
      (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) (by omega : B - 1 < B)))

end AntichainOfGivenSize.Paper
