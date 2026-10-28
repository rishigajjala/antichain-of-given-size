import AntichainOfGivenSize.Analysis.Paper.RealDensity

/-!
Semantic interfaces for the main theorem. The same constants are retained
through both density representations and through natural and real cutoffs.
The identities hold for arbitrary fixed real constants, hence in particular
for the positive constants in Theorem 1.1.
-/

open Finset Filter
open scoped Topology

namespace AntichainOfGivenSize.Paper

/-- The complement count on exactly `[5,N]` has density zero if and only if
the simultaneous good-input count, with the same constants, has density one.
The complement is expanded to keep the statement's defining vocabulary in Model. -/
theorem goodInputs_density_iff_complement (c C : ℝ) :
    Tendsto (fun N : ℕ ↦
      (((Finset.Icc 5 N).filter fun n : ℕ ↦ ¬
        (c * quadraticLogLogScale (n : ℝ) ≤ (alpha n : ℝ) ∧
          (alpha n : ℝ) ≤ C * quadraticLogLogScale (n : ℝ))).card : ℝ) / (N : ℝ))
      atTop (nhds 0) ↔
    Tendsto (fun N : ℕ ↦ ((goodInputs c C N).card : ℝ) / (N : ℝ))
      atTop (nhds 1) := by
  classical
  let bad : ℕ → Finset ℕ := fun N ↦ (Finset.Icc 5 N).filter fun n : ℕ ↦ ¬
    (c * quadraticLogLogScale (n : ℝ) ≤ (alpha n : ℝ) ∧
      (alpha n : ℝ) ≤ C * quadraticLogLogScale (n : ℝ))
  change Tendsto (fun N : ℕ ↦ ((bad N).card : ℝ) / (N : ℝ)) atTop (nhds 0) ↔ _
  have hsum : ∀ᶠ N : ℕ in atTop,
      ((goodInputs c C N).card : ℝ) / (N : ℝ) +
        ((bad N).card : ℝ) / (N : ℝ) = 1 - (4 : ℝ) / N := by
    filter_upwards [eventually_ge_atTop 5] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hc : (goodInputs c C N).card + (bad N).card = (Finset.Icc 5 N).card :=
      goodInputs_card_add_orderExceptions_card c C N
    have hIcc : (Finset.Icc 5 N).card = N - 4 := by rw [Nat.card_Icc]; omega
    rw [hIcc] at hc
    have hcR := congrArg (fun z : ℕ ↦ (z : ℝ)) hc
    simp only [Nat.cast_add, Nat.cast_sub (show 4 ≤ N by omega), Nat.cast_ofNat] at hcR
    rw [← add_div, hcR, sub_div, div_self hN0]
  constructor
  · intro hbad
    have hlim : Tendsto (fun N : ℕ ↦
        1 - (4 : ℝ) / N - ((bad N).card : ℝ) / N) atTop (nhds 1) := by
      convert ((tendsto_const_nhds.sub
        (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ))).sub hbad) using 1
      norm_num
    apply hlim.congr'
    filter_upwards [hsum] with N hN
    linarith
  · intro hgood
    have hlim : Tendsto (fun N : ℕ ↦
        1 - (4 : ℝ) / N - ((goodInputs c C N).card : ℝ) / N) atTop (nhds 0) := by
      convert ((tendsto_const_nhds.sub
        (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ))).sub hgood) using 1
      norm_num
    apply hlim.congr'
    filter_upwards [hsum] with N hN
    linarith

/-- Passing between natural and arbitrary real cutoffs preserves the constants.
The real proportion has denominator `X`, not its floor. -/
theorem goodInputs_density_iff_real (c C : ℝ) :
    Tendsto (fun N : ℕ ↦ ((goodInputs c C N).card : ℝ) / (N : ℝ))
      atTop (nhds 1) ↔
    Tendsto (fun X : ℝ ↦ ((realGoodInputs c C X).card : ℝ) / X)
      atTop (nhds 1) := by
  constructor
  · intro hnat
    have hprod : Tendsto (fun X : ℝ ↦
        (((goodInputs c C ⌊X⌋₊).card : ℝ) / (⌊X⌋₊ : ℝ)) *
          ((⌊X⌋₊ : ℝ) / X)) atTop (nhds 1) := by
      simpa using (hnat.comp tendsto_nat_floor_atTop).mul
        (tendsto_nat_floor_div_atTop (R := ℝ))
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hfloor : 1 ≤ ⌊X⌋₊ := (Nat.one_le_floor_iff X).2 hX
    have hfloor0 : (⌊X⌋₊ : ℝ) ≠ 0 := by
      exact_mod_cast (show ⌊X⌋₊ ≠ 0 by omega)
    dsimp [realGoodInputs]
    field_simp
  · intro hreal
    simpa only [Function.comp_def, realGoodInputs, Nat.floor_natCast] using
      hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The two main-theorem density semantics obligations, with one fixed pair
of constants and no assumption that the upper or lower bounds already hold. -/
theorem density_representations (c C : ℝ) :
    (Tendsto (fun N : ℕ ↦
      (((Finset.Icc 5 N).filter fun n : ℕ ↦ ¬
        (c * quadraticLogLogScale (n : ℝ) ≤ (alpha n : ℝ) ∧
          (alpha n : ℝ) ≤ C * quadraticLogLogScale (n : ℝ))).card : ℝ) / (N : ℝ))
      atTop (nhds 0) ↔
      Tendsto (fun N : ℕ ↦ ((goodInputs c C N).card : ℝ) / (N : ℝ))
        atTop (nhds 1)) ∧
    (Tendsto (fun N : ℕ ↦ ((goodInputs c C N).card : ℝ) / (N : ℝ))
      atTop (nhds 1) ↔
      Tendsto (fun X : ℝ ↦ ((realGoodInputs c C X).card : ℝ) / X)
        atTop (nhds 1)) :=
  ⟨goodInputs_density_iff_complement c C, goodInputs_density_iff_real c C⟩

/-- The finite set used by `maximumBelow` is exactly the strict positive
integer cutoff, including when `X` is itself an integer. -/
theorem mem_maximumBelow_domain {X : ℝ} {n : ℕ} :
    n ∈ Finset.Ico 1 ⌈X⌉₊ ↔ 1 ≤ n ∧ (n : ℝ) < X := by
  simp only [Finset.mem_Ico, Nat.lt_ceil]

/-- Above one, the maximum is attained at an allowed integer and bounds
every allowed integer. This excludes any empty-domain default value. -/
theorem maximumBelow_spec {X : ℝ} (hX : 1 < X) :
    (∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) < X ∧ alpha n = maximumBelow X) ∧
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) < X → alpha n ≤ maximumBelow X := by
  have hnonempty : (Finset.Ico 1 ⌈X⌉₊).Nonempty := by
    refine ⟨1, mem_maximumBelow_domain.mpr ⟨le_rfl, ?_⟩⟩
    simpa only [Nat.cast_one] using hX
  obtain ⟨n, hn, heq⟩ := Finset.exists_mem_eq_sup (Finset.Ico 1 ⌈X⌉₊) hnonempty alpha
  have hn' := mem_maximumBelow_domain.mp hn
  refine ⟨⟨n, hn'.1, hn'.2, heq.symm⟩, ?_⟩
  intro n hn hnx
  exact Finset.le_sup (mem_maximumBelow_domain.mpr ⟨hn, hnx⟩)

end AntichainOfGivenSize.Paper
