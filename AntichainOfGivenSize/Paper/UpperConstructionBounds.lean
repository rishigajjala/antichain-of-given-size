import AntichainOfGivenSize.Paper.UpperConstructionSteps
import AntichainOfGivenSize.Paper.UpperParameters

/-! The finite size ledger and complete residue induction for the manuscript's
binary-address block construction. -/

open Finset
open scoped BigOperators

namespace AntichainOfGivenSize.Paper.UpperConstruction

open AntichainOfGivenSize.Section6

theorem card_oldUniverse (r : ℕ) : (oldUniverse r).card = (2 ^ r - 1) + r := by
  classical
  simp only [oldUniverse, Finset.card_disjSum, Finset.card_univ,
    Finset.card_empty, Nat.add_zero, Fintype.card_fin, BitMatching.card_blockVertex]

theorem card_initial_position {r : ℕ} (p : BitMatching.Index r) :
    (BitMatching.generator ∅ p).card ≤ (2 ^ r - 1) + (r - 1) := by
  classical
  have hold : (BitMatching.oldPart p).card ≤ 2 ^ r - 1 := by
    simpa only [BitMatching.card_blockVertex] using Finset.card_le_univ (BitMatching.oldPart p)
  rw [BitMatching.generator_decomposition]
  simpa [BitMatching.freshPart] using hold

theorem card_pattern_generator {ell : ℕ} (k : PatternGadget.Index ell) :
    (PatternGadget.generator k).card ≤ ell := by
  cases k with
  | none => simp [PatternGadget.generator]
  | some a =>
      simp only [PatternGadget.generator, Finset.card_insert_of_notMem
        (PatternGadget.inr_not_mem_initialSegment a a), PatternGadget.card_initialSegment]
      omega

theorem generator_decomposition {r ell : ℕ} {K V : Type*}
    [DecidableEq K] [Fintype V] [DecidableEq V]
    (active : Finset (BitMatching.Stage r)) (hist : BitMatching.Stage r → Finset K)
    (R : K → Finset V) (p : Index r K) :
    generator (ell := ell) active hist R p =
      ((match p with
        | Sum.inl k => BitMatching.generator ∅ k
        | Sum.inr _ => oldUniverse r).product (Finset.univ : Finset (Fin ell))).disjSum
      ((match p with
        | Sum.inl _ => Finset.univ
        | Sum.inr k => R k).disjSum
      (active.filter fun g => p ∈ selected g (hist g))) := by
  classical
  ext v
  rcases v with ⟨u,x⟩ | (v | g) <;> cases p <;> simp [Present]

/-- The generator size in Claim 6.5, before applying the parameter choices. -/
theorem card_generator_le {r ell : ℕ} (hr : 0 < r)
    (active : Finset (BitMatching.Stage r))
    (hist : BitMatching.Stage r → Finset (PatternGadget.Index ell))
    (p : Index r (PatternGadget.Index ell)) :
    (generator (ell := ell) active hist PatternGadget.generator p).card ≤
      ell * (2 ^ r + r) + 2 ^ r := by
  classical
  have hfresh : (active.filter fun g => p ∈ selected g (hist g)).card ≤ 2 ^ r := by
    simpa [BitMatching.Stage] using
      Finset.card_le_univ (active.filter fun g => p ∈ selected g (hist g))
  have hp : 1 ≤ (2 : ℕ) ^ r := Nat.one_le_two_pow
  rw [generator_decomposition]
  simp only [Finset.card_disjSum, Finset.product_eq_sprod, Finset.card_product,
    Finset.card_univ, Fintype.card_fin]
  cases p with
  | inl p =>
      dsimp only
      have hpos := Nat.mul_le_mul_right ell (card_initial_position p)
      simp only [Finset.card_univ, PatternGadget.Vertex, Fintype.card_sum, Fintype.card_fin]
      have heq : ((2 ^ r - 1) + (r - 1)) * ell + (ell + ell) =
          ell * (2 ^ r + r) := by
        have h1 : 2 ^ r - 1 + 1 = 2 ^ r := by omega
        have h2 : r - 1 + 1 = r := by omega
        nlinarith
      omega
  | inr k =>
      dsimp only
      rw [card_oldUniverse]
      have hpat := card_pattern_generator k
      have heq : ((2 ^ r - 1) + r) * ell + ell = ell * (2 ^ r + r) := by
        have h1 : 2 ^ r - 1 + 1 = 2 ^ r := by omega
        nlinarith
      omega

theorem idealCard_bound {r ell : ℕ} (hr : 0 < r)
    (active : Finset (BitMatching.Stage r))
    (hist : BitMatching.Stage r → Finset (PatternGadget.Index ell)) :
    idealCard (ell := ell) active hist PatternGadget.generator ≤
      (2 * r + ell + 1) * 2 ^ (ell * (2 ^ r + r) + 2 ^ r) := by
  classical
  unfold idealCard generatedIdealIdx
  have h := Finset.card_biUnion_le_card_mul (s := (Finset.univ :
    Finset (Index r (PatternGadget.Index ell))))
    (f := fun p => (generator (ell := ell) active hist PatternGadget.generator p).powerset)
    (n := 2 ^ (ell * (2 ^ r + r) + 2 ^ r)) (by
      intro p _hp
      rw [Finset.card_powerset]
      exact Nat.pow_le_pow_right (by norm_num) (card_generator_le hr active hist p))
  simpa [Index, BitMatching.Index, PatternGadget.Index, Nat.mul_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem idealCard_pos {r ell : ℕ}
    (active : Finset (BitMatching.Stage r))
    (hist : BitMatching.Stage r → Finset (PatternGadget.Index ell)) :
    0 < idealCard (ell := ell) active hist PatternGadget.generator := by
  apply generatedIdealIdx_card_pos
  exact ⟨Sum.inr none, Finset.mem_univ _⟩

theorem alpha_idealCard_le {r ell : ℕ}
    (active : Finset (BitMatching.Stage r))
    (hist : BitMatching.Stage r → Finset (PatternGadget.Index ell)) :
    alpha (idealCard (ell := ell) active hist PatternGadget.generator) ≤ 2 * r + ell + 1 := by
  classical
  simpa [idealCard,Index,BitMatching.Index,PatternGadget.Index,Nat.mul_comm,Nat.add_assoc] using
    alpha_generatedIdealIdx_univ_card_le
      (generator (ell := ell) active hist PatternGadget.generator)

noncomputable def targetCeiling (r ell : ℕ) : ℕ :=
  Fintype.card (Index r (PatternGadget.Index ell)) *
    2 ^ Fintype.card (Vertex r ell (PatternGadget.Vertex ell))

theorem idealCard_le_targetCeiling {r ell : ℕ}
    (active : Finset (BitMatching.Stage r))
    (hist : BitMatching.Stage r → Finset (PatternGadget.Index ell)) :
    idealCard (ell := ell) active hist PatternGadget.generator ≤ targetCeiling r ell :=
  generatedIdealIdx_univ_card_le (generator active hist PatternGadget.generator)

theorem exists_matching_history {r ell : ℕ} (hr : 0 < r) (Y : ℕ)
    (hY : targetCeiling r ell ≤ Y) :
    ∀ h : ℕ, h ≤ 2 ^ r → ∃ (active : Finset (BitMatching.Stage r))
      (hist : BitMatching.Stage r → Finset (PatternGadget.Index ell)),
      (∀ g ∈ active, g.val < h) ∧
      idealCard (ell := ell) active hist PatternGadget.generator ≡ Y [MOD 2 ^ (h * ell)] := by
  classical
  intro h
  induction h with
  | zero =>
      intro _
      refine ⟨∅, fun _ => ∅, by simp, ?_⟩
      simpa only [Nat.zero_mul, pow_zero] using
        (Nat.modEq_one : idealCard (ell := ell) ∅ (fun _ => ∅)
          PatternGadget.generator ≡ Y [MOD 1])
  | succ h ih =>
      intro hh
      obtain ⟨active,hist,hpast,hmod⟩ := ih (by omega)
      let i : BitMatching.Stage r := ⟨h,by omega⟩
      have hi : i ∉ active := by
        intro hm
        exact (Nat.lt_irrefl h) (hpast i hm)
      let m := idealCard (ell := ell) active hist PatternGadget.generator
      let c := (Y - m) / 2 ^ (h * ell)
      let d := ((-1 : ZMod (2 ^ ell)) ^ r * (c : ZMod (2 ^ ell))).val
      have hd : d < 2 ^ ell := ZMod.val_lt _
      have hz : ((2 ^ ell + d : ℕ) : ZMod (2 ^ ell)) =
          (-1 : ZMod (2 ^ ell)) ^ r * (c : ZMod (2 ^ ell)) := by
        simp [d]
      have hlift :
          (-1 : ZMod (2 ^ ((h + 1) * ell))) ^ r *
            ((2 ^ ell + d : ℕ) : ZMod (2 ^ ((h + 1) * ell))) *
            (2 : ZMod (2 ^ ((h + 1) * ell))) ^ (h * ell) =
          ((2 ^ (h * ell) * c : ℕ) : ZMod (2 ^ ((h + 1) * ell))) := by
        rw [pow_block_succ]
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using
          Construction.signed_mul_lift (a := 2 ^ (h * ell)) hz
      refine ⟨insert i active, Function.update hist i (digitSelection ell d), ?_, ?_⟩
      · intro g hg
        rcases Finset.mem_insert.mp hg with rfl | hg
        · exact Nat.lt_succ_self h
        · exact (hpast g hg).trans_le (Nat.le_succ h)
      · rw [idealCard_update active hist PatternGadget.generator i hi]
        have hdelta :
            (generatedIdealIdx (selected i (digitSelection ell d))
              (generator (ell := ell) active hist PatternGadget.generator)).card ≡
              2 ^ (h * ell) * c [MOD 2 ^ ((h + 1) * ell)] := by
          apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
          exact (block_increment hr hd active hist i hi).trans hlift
        exact extend_pow_modEq_digit (h := h) (q := ell)
          ((idealCard_le_targetCeiling active hist).trans hY) hmod (by rfl) hdelta

theorem exists_matching_nat (r ell y : ℕ) (hr : 0 < r) :
    ∃ m : ℕ, 0 < m ∧ m ≡ y [MOD 2 ^ (2 ^ r * ell)] ∧
      alpha m ≤ 2 * r + ell + 1 ∧
      m ≤ (2 * r + ell + 1) * 2 ^ (ell * (2 ^ r + r) + 2 ^ r) := by
  let M := 2 ^ (2 ^ r * ell)
  let Y := y + M * (targetCeiling r ell + 1)
  have hM : 1 ≤ M := Nat.one_le_two_pow
  have hY : targetCeiling r ell ≤ Y := by dsimp [Y]; nlinarith
  obtain ⟨active,hist,_hpast,hmod⟩ := exists_matching_history hr Y hY (2 ^ r) le_rfl
  refine ⟨idealCard (ell := ell) active hist PatternGadget.generator,
    idealCard_pos active hist, ?_, alpha_idealCard_le active hist,
    idealCard_bound hr active hist⟩
  apply hmod.trans
  change Y % M = y % M
  simp [Y]

/-- The complete finite construction consumed by the uniform block parameter
ledger. Integer residues include negative targets. -/
theorem blockMatchingConstruction : BlockMatchingConstructionStatement := by
  intro r ell hr _hell y
  let M := 2 ^ (2 ^ r * ell)
  letI : NeZero M := ⟨by dsimp [M]; positivity⟩
  obtain ⟨m,hm,hmod,ha,hsize⟩ := exists_matching_nat r ell (y : ZMod M).val hr
  refine ⟨m,hm,?_,ha,hsize⟩
  have hz : (m : ZMod M) = (y : ZMod M) := by
    rw [← ZMod.natCast_zmod_val (y : ZMod M)]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  have hmody : Int.ModEq (M : ℤ) (m : ℤ) y :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mp (by simpa using hz)
  simpa [M] using hmody

end AntichainOfGivenSize.Paper.UpperConstruction
