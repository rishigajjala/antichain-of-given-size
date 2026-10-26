import AntichainOfGivenSize.Paper.LiteralUpperParameters
import AntichainOfGivenSize.Paper.UpperConstructionIncrement

/-!
Theorem 6.1 with the manuscript's literal real-logarithm, floor, and ceiling
parameters. The existing finite-stage residue induction supplies an actual
update history, to which the proved uniform size bounds apply.
-/

namespace AntichainOfGivenSize.Paper.LiteralUpperParameters

open AntichainOfGivenSize.Paper.UpperConstruction

/-- The actual update history can match any integer target, including a
negative target, modulo all of its `H * ell` constructed bit positions. -/
theorem exists_matching_history_int (r ell : ℕ) (hr : 0 < r) (y : ℤ) :
    ∃ (active : Finset (BitMatching.Stage r))
      (hist : BitMatching.Stage r → Finset (PatternGadget.Index ell)),
      (∀ g ∈ active, g.val < 2 ^ r) ∧
      Int.ModEq ((2 : ℤ) ^ (2 ^ r * ell))
        (idealCard (ell := ell) active hist PatternGadget.generator : ℤ) y := by
  let M : ℕ := 2 ^ (2 ^ r * ell)
  letI : NeZero M := ⟨by dsimp [M]; positivity⟩
  let y₀ : ℕ := (y : ZMod M).val
  let Y := y₀ + M * (targetCeiling r ell + 1)
  have hM : 1 ≤ M := Nat.one_le_two_pow
  have hY : targetCeiling r ell ≤ Y := by dsimp [Y]; nlinarith
  obtain ⟨active, hist, hpast, hmod⟩ :=
    exists_matching_history hr Y hY (2 ^ r) le_rfl
  refine ⟨active, hist, hpast, ?_⟩
  have hmod₀ : idealCard (ell := ell) active hist PatternGadget.generator ≡
      y₀ [MOD M] := by
    apply hmod.trans
    change Y % M = y₀ % M
    simp [Y]
  have hz :
      (idealCard (ell := ell) active hist PatternGadget.generator : ZMod M) =
        (y : ZMod M) := by
    rw [← ZMod.natCast_zmod_val (y : ZMod M)]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod₀
  have hmody : Int.ModEq (M : ℤ)
      (idealCard (ell := ell) active hist PatternGadget.generator : ℤ) y :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mp (by simpa using hz)
  simpa [M] using hmody

/-- The ceiling-defined block length covers the requested number of bits. -/
theorem literal_bit_coverage (B r : ℕ) :
    B ≤ 2 ^ r * ⌈(B : ℝ) / ((2 ^ r : ℕ) : ℝ)⌉₊ := by
  have hH : (0 : ℝ) < ((2 ^ r : ℕ) : ℝ) := by positivity
  have hc := (div_le_iff₀ hH).mp
    (Nat.le_ceil ((B : ℝ) / ((2 ^ r : ℕ) : ℝ)))
  have hc' : (B : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) *
      (⌈(B : ℝ) / ((2 ^ r : ℕ) : ℝ)⌉₊ : ℝ) := by
    simpa only [mul_comm] using hc
  exact_mod_cast hc'

/-- Theorem 6.1 with the literal parameter choices and the original constants
`a = 5`, `b = 3`. All auxiliary size conditions are discharged by one absolute
threshold, independent of the integer residue. -/
theorem blockMatching : BlockMatchingStatement := by
  obtain ⟨B₀, _hB₀, hsize⟩ := exists_literal_constructed_size_threshold
  refine ⟨B₀, ?_⟩
  intro B hB y
  let L := Real.logb 2 (B : ℝ)
  let r : ℕ := ⌊Real.logb 2 ((B : ℝ) / L)⌋₊
  let H : ℕ := 2 ^ r
  let ell : ℕ := ⌈(B : ℝ) / (H : ℝ)⌉₊
  have hsizeB := hsize B hB
  change 0 < r ∧ ((2 * r + ell + 1 : ℕ) : ℝ) ≤ 5 * L ∧
    ∀ (active : Finset (BitMatching.Stage r))
      (hist : BitMatching.Stage r → Finset (PatternGadget.Index ell)),
      let m := idealCard (ell := ell) active hist PatternGadget.generator
      0 < m ∧
        (∀ p : Index r (PatternGadget.Index ell),
          (generator (ell := ell) active hist PatternGadget.generator p).card ≤
            ell * (H + r) + H) ∧
        (alpha m : ℝ) ≤ 5 * L ∧
        Real.logb 2 (m : ℝ) ≤ (B : ℝ) + 3 * (B : ℝ) / L at hsizeB
  obtain ⟨active, hist, _hpast, hmod⟩ := exists_matching_history_int r ell hsizeB.1 y
  have hm := hsizeB.2.2 active hist
  have hcover : B ≤ 2 ^ r * ell := literal_bit_coverage B r
  exact ⟨idealCard (ell := ell) active hist PatternGadget.generator,
    hm.1, hmod.of_dvd (pow_dvd_pow 2 hcover), hm.2.2.1, hm.2.2.2⟩

end AntichainOfGivenSize.Paper.LiteralUpperParameters
