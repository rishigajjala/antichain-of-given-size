import AntichainOfGivenSize.Model.CountingVocabulary
import AntichainOfGivenSize.MainStatement
import AntichainOfGivenSize.LowerBound.ClusterImageBound

/-!
# Statements of the current four-author manuscript

These declarations specify the results to be proved for the manuscript
snapshot in `paper/Generating_Antichains_Simplified.tex`. A definition of a
proposition is not a proof; the theorem inventory records its proof status.
All logarithms are base two. Positive-input hypotheses explicitly reconcile
the paper's positive-natural convention with Lean's natural numbers.
-/

open Asymptotics Filter

namespace AntichainOfGivenSize.Paper

/-- The unchanged generator budget in Theorem 7.1. -/
def AdmissibleBudget (B K : ℕ) : Prop :=
  1 ≤ K ∧ (K : ℝ) ≤ (Real.logb 2 (B : ℝ)) ^ 2 /
    (100 * Real.logb 2 (Real.logb 2 (B : ℝ)))

/-- Theorem 7.1, including its uniform quantifiers and square-root saving. -/
def CountingBoundStatement : Prop :=
  ∃ B₀ : ℕ, ∀ B K : ℕ, B₀ ≤ B → AdmissibleBudget B K →
    ((attainableValues B K).card : ℝ) ≤
      (2 : ℝ) ^ ((B : ℝ) - Real.sqrt (B : ℝ))

/-- The dyadic interval used in Corollary 10.1. -/
def dyadicBlock (B : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ (B - 1)) (2 ^ B)

/-- Inputs in a dyadic interval representable with at most `K` generators. -/
noncomputable def badBlock (B K : ℕ) : Finset ℕ :=
  (dyadicBlock B).filter fun n ↦ alpha n ≤ K

/-- Corollary 10.1 expressed as the exact finite uniform probability. -/
def TypicalLowerBoundStatement : Prop :=
  ∃ B₀ : ℕ, ∀ B K : ℕ, B₀ ≤ B → AdmissibleBudget B K →
    ((badBlock B K).card : ℝ) / ((dyadicBlock B).card : ℝ) ≤
      (2 : ℝ) ^ (1 - Real.sqrt (B : ℝ))

/-- The exceptional inputs in the paper's density-one assertion. -/
noncomputable def exceptionalInputs (c : ℝ) (X : ℕ) : Finset ℕ :=
  (Finset.Icc 5 X).filter fun n ↦
    (alpha n : ℝ) < c * quadraticLogLogScale (n : ℝ)

/-- Theorem 1.1(ii): the lower-bound exceptions have natural density zero. -/
def AlmostAllLowerBoundStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ Tendsto
    (fun X : ℕ ↦ ((exceptionalInputs c X).card : ℝ) / (X : ℝ))
    atTop (nhds 0)

/-- The exceptions to the simultaneous lower and upper bounds in
Corollary 10.2. -/
noncomputable def orderExceptions (c C : ℝ) (X : ℕ) : Finset ℕ :=
  (Finset.Icc 5 X).filter fun n ↦ ¬
    (c * quadraticLogLogScale (n : ℝ) ≤ (alpha n : ℝ) ∧
      (alpha n : ℝ) ≤ C * quadraticLogLogScale (n : ℝ))

/-- Corollary 10.2: both inequalities hold outside one set of density zero. -/
def AlmostAllOrderStatement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ Tendsto
    (fun X : ℕ ↦ ((orderExceptions c C X).card : ℝ) / (X : ℝ))
    atTop (nhds 0)

/-- The displayed limit in Corollary 10.2, with the finite endpoints retained. -/
def AlmostAllGoodProportionStatement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ Tendsto
    (fun X : ℕ ↦ ((goodInputs c C X).card : ℝ) / (X : ℝ))
    atTop (nhds 1)

/-- The extremal conclusion of Theorem 1.1 with real cutoffs. -/
def ExtremalOrderStatement : Prop :=
  (fun X : ℝ ↦ (maximumBelow X : ℝ)) =Θ[atTop] quadraticLogLogScale

end AntichainOfGivenSize.Paper
