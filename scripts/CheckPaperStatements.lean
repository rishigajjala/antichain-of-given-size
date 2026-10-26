import AntichainOfGivenSize

/-!
# Manuscript statement checks

Run after `lake build --wfail`:
`lake env lean -DwarningAsError=true scripts/CheckPaperStatements.lean`.

These checks deliberately spell out the mathematical contracts, rather
than merely checking the names of the library's `...Statement` predicates.
They catch weaker constants, domains, quantifiers, or endpoints even if
the corresponding library predicate and its proof were changed together.
The interpretation of the foundational definitions still requires the
statement audit documented in `docs/current-paper.md`.
-/

open AntichainOfGivenSize AntichainOfGivenSize.Paper Filter Asymptotics
open scoped Topology

private noncomputable def paperScale (x : ℝ) : ℝ :=
  (Real.logb 2 (Real.logb 2 x)) ^ 2 /
    Real.logb 2 (Real.logb 2 (Real.logb 2 x))

-- Theorem 4.1: the full integer-target contract, with no range on y.
example (q : ℕ) (y : ℤ) (hq : 0 < q) :
    ∃ m : ℕ, 0 < m ∧ m < 2 ^ (2 ^ (q + 1)) ∧
      (m : ZMod (2 ^ (2 ^ q))) = (y : ZMod (2 ^ (2 ^ q))) ∧ alpha m ≤ 2 * q :=
  bitMatchingInt q y hq

-- Theorem 5.1: the exact finite-range bound and its independent corollary.
example (q n : ℕ) (hlo : 2 ^ (2 ^ (q + 1)) ≤ n)
    (hhi : n < 2 ^ (2 ^ (q + 2))) : alpha n ≤ 4 * q ^ 2 + 3 :=
  firstUpper q n hlo hhi

example : (fun n : ℕ ↦ (alpha n : ℝ)) =O[atTop]
    (fun n : ℕ ↦ (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 2) := quadraticUpper

-- Theorem 6.1: every sufficiently large B and every integer residue, 5 and 3.
example : ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B → ∀ y : ℤ, ∃ m : ℕ,
    0 < m ∧ Int.ModEq ((2 : ℤ) ^ B) (m : ℤ) y ∧
    (alpha m : ℝ) ≤ 5 * Real.logb 2 (B : ℝ) ∧
    Real.logb 2 (m : ℝ) ≤ (B : ℝ) + 3 * (B : ℝ) / Real.logb 2 (B : ℝ) :=
  blockMatching

-- Lemma 6.6: strict decrease and positivity of the new integer are essential.
example : ∃ a C₁ : ℝ, 0 < a ∧ 0 < C₁ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ n' : ℕ, 1 ≤ n' ∧ n' < n ∧
      (alpha n : ℝ) ≤ a * Real.logb 2 (Real.logb 2 (n : ℝ)) + (alpha n' : ℝ) ∧
      Real.logb 2 (n' : ℝ) ≤
        C₁ * Real.logb 2 (n : ℝ) / Real.logb 2 (Real.logb 2 (n : ℝ)) :=
  directReduction

-- Theorem 6.7: the upper bound includes every n≥5, not just an eventual tail.
example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n →
    (alpha n : ℝ) ≤ C * paperScale (n : ℝ) := universalUpper_from_five

-- V(B,K) counts exact ideal sizes over arbitrary finite ambient universes.
example (B K n : ℕ) (hK : 0 < K) :
    n ∈ attainableValues B K ↔
      ∃ N : ℕ, ∃ G : Finset (Finset (Fin N)),
        G.Nonempty ∧ G.card ≤ K ∧
        (∀ A ∈ G, A.card ≤ B) ∧ (generatedIdeal G).card = n :=
  mem_attainableValues_iff hK

-- Theorem 7.1: constant 100, square-root saving, all sufficiently large B.
example : ∃ B₀ : ℕ, ∀ B K : ℕ, B₀ ≤ B →
    (1 ≤ K ∧ (K : ℝ) ≤ (Real.logb 2 (B : ℝ)) ^ 2 /
      (100 * Real.logb 2 (Real.logb 2 (B : ℝ)))) →
    ((attainableValues B K).card : ℝ) ≤
      (2 : ℝ) ^ ((B : ℝ) - Real.sqrt (B : ℝ)) := countingBound

-- The same expanded contract must hold for the manuscript's shorter proof.
example : ∃ B₀ : ℕ, ∀ B K : ℕ, B₀ ≤ B →
    (1 ≤ K ∧ (K : ℝ) ≤ (Real.logb 2 (B : ℝ)) ^ 2 /
      (100 * Real.logb 2 (Real.logb 2 (B : ℝ)))) →
    ((attainableValues B K).card : ℝ) ≤
      (2 : ℝ) ^ ((B : ℝ) - Real.sqrt (B : ℝ)) := faithfulCountingBound

-- Corollary 10.1: the exact probability bound on the half-open dyadic block.
example : ∃ B₀ : ℕ, ∀ B K : ℕ, B₀ ≤ B →
    (1 ≤ K ∧ (K : ℝ) ≤ (Real.logb 2 (B : ℝ)) ^ 2 /
      (100 * Real.logb 2 (Real.logb 2 (B : ℝ)))) →
    (((Finset.Ico (2 ^ (B - 1)) (2 ^ B)).filter fun n ↦ alpha n ≤ K).card : ℝ) /
      ((Finset.Ico (2 ^ (B - 1)) (2 ^ B)).card : ℝ) ≤
      (2 : ℝ) ^ (1 - Real.sqrt (B : ℝ)) := by
  classical
  exact typicalLowerBound

-- The lower constant and density-zero assertion are stronger than infinitely often.
example : Tendsto (fun X : ℕ ↦
    (((Finset.Icc 5 X).filter fun n ↦
      (alpha n : ℝ) < (1 / 800 : ℝ) * paperScale (n : ℝ)).card : ℝ) / (X : ℝ))
    atTop (nhds 0) := by
  classical
  exact density_of_countingBound faithfulCountingBound

-- Corollary 10.2: the proportion tends to one for arbitrary real cutoffs.
example : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ Tendsto
    (fun X : ℝ ↦ (((Finset.Icc 5 ⌊X⌋₊ : Finset ℕ).filter fun n : ℕ ↦
      c * paperScale (n : ℝ) ≤ (alpha n : ℝ) ∧
        (alpha n : ℝ) ≤ C * paperScale (n : ℝ)).card : ℝ) / X)
    atTop (nhds 1) := by
  classical
  exact realAlmostAllGoodProportion

-- The extremal maximum is over all positive integers strictly below real X.
example : (fun X : ℝ ↦ (((Finset.Ico 1 ⌈X⌉₊).sup alpha : ℕ) : ℝ)) =Θ[atTop] paperScale :=
  extremalOrder
