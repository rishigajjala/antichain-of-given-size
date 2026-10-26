import AntichainOfGivenSize.Paper.FaithfulCounting.ClaimBundles

open Finset
open AntichainOfGivenSize.Section6
open AntichainOfGivenSize.FaithfulLower.Numerical

namespace AntichainOfGivenSize.FaithfulLower

/-- Row 3 with the manuscript's literal padding rule: indices below `s`
keep their generator, and every new index repeats the final generator `s-1`.
The second conjunct normalizes the active ground set without changing the size. -/
theorem paper_final_padding_and_normalization
    {s K B : ℕ} {V : Type*} [DecidableEq V]
    (hs : 0 < s) (hsK : s ≤ K) (G : Fin s → Finset V)
    (hsize : ∀ i, (G i).card ≤ B) :
    (generatedIdealIdx univ
      (fun i : Fin K ↦ G (if hi : i.val < s then ⟨i.val, hi⟩
        else ⟨s - 1, Nat.sub_lt hs (by decide)⟩)) =
      generatedIdealIdx univ G) ∧
    (∃ N : ℕ, N = (univ.biUnion G).card ∧ N ≤ K * B ∧
      ∃ D : Fin K → Finset (Fin N),
        (∀ i, (D i).card ≤ B) ∧
        univ.biUnion D = univ ∧
        (generatedIdealIdx univ D).card = (generatedIdealIdx univ G).card) := by
  classical
  refine ⟨?_, normalized_family hs hsK G hsize⟩
  ext A
  simp only [generatedIdealIdx, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨_, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨Fin.castLE hsK i, ?_⟩
    simpa only [Fin.val_castLE, dif_pos i.isLt] using hi

/-- Row 11 retains the preliminary Gamma estimate for every real `L>=20`,
and also the single absolute threshold for all numerical and counting conclusions. -/
theorem paper_numerics_full :
    (∀ L : ℝ, 20 ≤ L → ∀ K : ℕ,
      1 ≤ K → (K : ℝ) ≤ L^2 / (100 * Real.logb 2 L) →
      (2 : ℝ) ^ (7 * L / 10) ≤ gamma L K) ∧
    (∃ B₀ : ℕ, 1 ≤ B₀ ∧ ∀ B : ℕ, B₀ ≤ B → ∀ K : ℕ,
      1 ≤ K → (K : ℝ) ≤ (Real.logb 2 B)^2 /
        (100 * Real.logb 2 (Real.logb 2 B)) →
      let L := Real.logb 2 B
      (2 : ℝ) ^ (7 * L / 10) ≤ gamma L K ∧
      fineCost L K ≤ 1/4 ∧
      recordCost L K ≤ gamma L K / 2 ∧
      Real.sqrt B ≤ gamma L K / 4 ∧
      (#(AntichainOfGivenSize.Paper.attainableValues B K) : ℝ) ≤
        (2 : ℝ)^((B : ℝ) - gamma L K / 4)) := by
  refine ⟨?_, paper_numerics_and_strong_count⟩
  intro L hL K hK hbudget
  exact gamma_lower hL ⟨hK, hbudget⟩

end AntichainOfGivenSize.FaithfulLower
