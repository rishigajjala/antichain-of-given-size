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

-- Expanded Corollary 10.1 contract: the good event, exact budget, real square root,
-- inclusive left endpoint, exclusive right endpoint, and a K-independent threshold.
example : ∃ B₀ : ℕ, ∀ B K : ℕ, B₀ ≤ B →
    (1 ≤ K ∧ (K : ℝ) ≤ (Real.logb 2 (B : ℝ)) ^ 2 /
      (100 * Real.logb 2 (Real.logb 2 (B : ℝ)))) →
    1 - (2 : ℝ) ^ (1 - Real.sqrt (B : ℝ)) ≤
      (((Finset.Ico (2 ^ (B - 1)) (2 ^ B)).filter
        fun n : ℕ ↦ alpha n > K).card : ℝ) /
        ((Finset.Ico (2 ^ (B - 1)) (2 ^ B)).card : ℝ) :=
  Paper.typicalLowerBound_good

-- The stronger finite prose claim from the q=0 base, including the exclusion of 13.
example (n : ℕ) (hlo : 4 ≤ n) (hhi : n < 16) (h13 : n ≠ 13) :
    alpha n ≤ 2 := Paper.alpha_le_two_of_base_range hlo hhi h13

open Finset
open AntichainOfGivenSize.Section6
open AntichainOfGivenSize.FaithfulLower
open AntichainOfGivenSize.FaithfulLower.Numerical

-- Literal final-index padding, full ideal preservation, and all normalization clauses.
example {s K B : ℕ} {V : Type*} [DecidableEq V]
    (hs : 0 < s) (hsK : s ≤ K) (G : Fin s → Finset V)
    (hsize : ∀ i, (G i).card ≤ B) :
    (generatedIdealIdx univ
      (fun i : Fin K ↦ G (if hi : i.val < s then ⟨i.val, hi⟩
        else ⟨s - 1, Nat.sub_lt hs (by decide)⟩)) =
      generatedIdealIdx univ G) ∧
    (∃ N : ℕ, N = (univ.biUnion G).card ∧ N ≤ K * B ∧
      ∃ D : Fin K → Finset (Fin N),
        (∀ i, (D i).card ≤ B) ∧ univ.biUnion D = univ ∧
        (generatedIdealIdx univ D).card = (generatedIdealIdx univ G).card) :=
  paper_final_padding_and_normalization hs hsK G hsize

-- All numerical quantities are expanded here. In the B-level conclusions Gamma
-- has numerator B, and the record cost contains KB+1 and B+1 literally.
example :
    (∀ L : ℝ, 20 ≤ L → ∀ K : ℕ,
      1 ≤ K → (K : ℝ) ≤ L^2 / (100 * Real.logb 2 L) →
      (2 : ℝ)^(7*L/10) ≤ (2 : ℝ)^L / L^(6*(K / ⌊L/4⌋₊))) ∧
    (∃ B₀ : ℕ, 1 ≤ B₀ ∧ ∀ B : ℕ, B₀ ≤ B → ∀ K : ℕ,
      1 ≤ K → (K : ℝ) ≤ (Real.logb 2 B)^2 /
        (100 * Real.logb 2 (Real.logb 2 B)) →
      let L := Real.logb 2 B
      let h : ℕ := ⌊L/4⌋₊
      let J : ℕ := K / h
      let Γ : ℝ := (B : ℝ) / L^(6*J)
      (2 : ℝ)^(7*L/10) ≤ Γ ∧
      2*(K : ℝ)^2/L^6 ≤ 1/4 ∧
      (Real.logb 2 (J+1) + (K : ℝ)*Real.logb 2 K +
        Real.logb 2 ((K : ℝ)*B+1) +
        (2 : ℝ)^J * (1+(K : ℝ)*(2 : ℝ)^h)*Real.logb 2 ((B : ℝ)+1) + K+2) ≤ Γ/2 ∧
      Real.sqrt B ≤ Γ/4 ∧
      ((AntichainOfGivenSize.Paper.attainableValues B K).card : ℝ) ≤
        (2 : ℝ)^((B : ℝ)-Γ/4)) := by
  obtain ⟨hpre, B₀, hB₀, hbound⟩ := paper_numerics_full
  refine ⟨?_, B₀, hB₀, ?_⟩
  · intro L hL K hK hbudget
    exact hpre L hL K hK hbudget
  · intro B hB K hK hbudget
    have hBpos : (0 : ℝ) < B := by
      exact_mod_cast lt_of_lt_of_le (by omega : 0 < B₀) hB
    have hBL : (2 : ℝ)^(Real.logb 2 B) = B :=
      Real.rpow_logb (by norm_num) (by norm_num) hBpos
    simpa only [gamma, fineCost, recordCost, clusterSize, packingBound, hBL] using
      hbound B hB K hK hbudget
