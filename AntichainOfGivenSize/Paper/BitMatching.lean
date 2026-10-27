import AntichainOfGivenSize.Model.ProblemSetting
import AntichainOfGivenSize.Section6.StageBridge
import AntichainOfGivenSize.Section6.IndexedBounds
import AntichainOfGivenSize.Section6.Remainder
import AntichainOfGivenSize.Section6.StageArithmetic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-!
# The paper's bit-matching construction

The index `(j,true)` is the paper's `S_(2j)` and `(j,false)` is
`S_(2j+1)`.  The three vertex species are the original binary blocks,
the flags, and the fresh vertices available at the possible stages.
`active` records precisely those stages at which an update was performed.
-/

open scoped BigOperators
open Finset

namespace AntichainOfGivenSize.Paper.BitMatching

open AntichainOfGivenSize.Section6

@[simp] theorem mem_address {q : ℕ} (i : Stage q) (p : Index q) :
    p ∈ address i ↔ p.2 = i.val.testBit p.1.val := by
  rcases p with ⟨j,b⟩
  simp [address, chosenEmbedding, chosenIndex, Prod.mk.injEq, eq_comm]

@[simp] theorem chosen_mem_address {q : ℕ} (i : Stage q) (j : Fin q) :
    chosenIndex i j ∈ address i := by simp [chosenIndex]

@[simp] theorem card_address {q : ℕ} (i : Stage q) :
    (address i).card = q := by simp [address]

theorem address_nonempty {q : ℕ} (hq : 0 < q) (i : Stage q) :
    (address i).Nonempty := by
  exact Finset.card_pos.mp (by simpa using hq)

theorem stage_eq_of_bits {q : ℕ} (i g : Stage q)
    (h : ∀ j : Fin q, i.val.testBit j = g.val.testBit j) : i = g := by
  apply Fin.ext
  rw [← lowBitsValue_eq i.isLt, ← lowBitsValue_eq g.isLt]
  unfold lowBitsValue
  apply Finset.sum_congr rfl
  intro j _
  rw [h j]

theorem address_subset_iff {q : ℕ} (i g : Stage q) :
    address i ⊆ address g ↔ i = g := by
  constructor
  · intro h
    apply stage_eq_of_bits
    intro j
    have hm := h (chosen_mem_address i j)
    simpa [chosenIndex] using (mem_address g (chosenIndex i j)).mp hm
  · rintro rfl; exact Finset.Subset.refl _

@[simp] theorem mem_generator {q : ℕ} (active : Finset (Stage q))
    (p : Index q) (v : Vertex q) : v ∈ generator active p ↔ Present active p v := by
  classical
  simp [generator]

@[simp] theorem mem_intersection {q : ℕ} (active : Finset (Stage q))
    (J : Finset (Index q)) (v : Vertex q) :
    v ∈ intersection active J ↔ ∀ p ∈ J, Present active p v := by
  classical
  simp [intersection]

theorem intersection_antitone {q : ℕ} (active : Finset (Stage q))
    {J K : Finset (Index q)} (h : J ⊆ K) :
    intersection active K ⊆ intersection active J := by
  intro v hv
  exact (mem_intersection active J v).mpr fun p hp =>
    (mem_intersection active K v).mp hv p (h hp)

theorem intersection_eq_inf' {q : ℕ} (active : Finset (Stage q))
    (J : Finset (Index q)) (hJ : J.Nonempty) :
    intersection active J = J.inf' hJ (generator active) := by
  classical
  ext v
  simp [Finset.mem_inf']

@[simp] theorem card_block {q : ℕ} (j : Fin q) : (block j).card = 2 ^ j.val := by
  simp [block]

theorem blocks_disjoint {q : ℕ} {j k : Fin q} (h : j ≠ k) :
    Disjoint (block j) (block k) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp hv
  obtain ⟨y,_,hy⟩ := Finset.mem_map.mp hw
  apply h
  have hh := congrArg (fun z : Vertex q => z) hy
  exact (congrArg Sigma.fst (Sum.inl.inj hh)).symm

@[simp] theorem mem_core_block {q : ℕ} (i : Stage q) (e : BlockVertex q) :
    Sum.inl e ∈ core i ↔ i.val.testBit e.1.val = true := by
  classical
  rcases e with ⟨j,x⟩
  simp [core, block, blockEmbedding]

@[simp] theorem inr_not_mem_core {q : ℕ} (i : Stage q) (v : Fin q ⊕ Stage q) :
    Sum.inr v ∉ core i := by
  classical
  simp [core, block, blockEmbedding]

theorem card_core {q : ℕ} (i : Stage q) : (core i).card = i.val := by
  classical
  rw [core, Finset.card_biUnion]
  · simp only [card_block]
    rw [Finset.sum_filter]
    exact lowBitsValue_eq i.isLt
  · intro j _ k _ hjk
    exact blocks_disjoint hjk

/-- Claim 4.2: fresh vertices can survive only at their own binary address. -/
theorem fresh_separation {q : ℕ} (hq : 0 < q) (active : Finset (Stage q))
    (i g : Stage q) :
    Sum.inr (Sum.inr g) ∈ intersection active (address i) ↔ g ∈ active ∧ i = g := by
  rw [mem_intersection]
  constructor
  · intro h
    have h0 := h (chosenIndex i ⟨0,hq⟩) (chosen_mem_address i ⟨0,hq⟩)
    refine ⟨h0.1, ?_⟩
    apply stage_eq_of_bits
    intro j
    exact (h (chosenIndex i j) (chosen_mem_address i j)).2
  · rintro ⟨hg,rfl⟩ p hp
    exact ⟨hg, (mem_address i p).mp hp⟩

/-- The exact primary intersection immediately before a stage. -/
theorem primary_intersection {q : ℕ} (hq : 0 < q) (active : Finset (Stage q))
    (i : Stage q) (hi : i ∉ active) :
    intersection active (address i) = core i := by
  classical
  ext v
  rcases v with e | (j | g)
  · rw [mem_core_block, mem_intersection]
    constructor
    · intro h
      have he := h (chosenIndex i e.1) (chosen_mem_address i e.1)
      simpa [Present, chosenIndex] using he
    · intro hb p hp
      change e.1 ≠ p.1 ∨ p.2 = true
      by_cases hj : e.1 = p.1
      · right
        rw [(mem_address i p).mp hp, ← hj]
        exact hb
      · exact Or.inl hj
  · simp only [inr_not_mem_core, iff_false, mem_intersection]
    intro h
    exact (h (chosenIndex i j) (chosen_mem_address i j)) rfl
  · rw [fresh_separation hq]
    simp only [inr_not_mem_core, iff_false]
    rintro ⟨hg,rfl⟩
    exact hi hg

/-- Claim 4.3: the primary exponent is exactly the stage number. -/
theorem primary_intersection_card {q : ℕ} (hq : 0 < q) (active : Finset (Stage q))
    (i : Stage q) (hi : i ∉ active) :
    (intersection active (address i)).card = i.val := by
  rw [primary_intersection hq active i hi, card_core]

/-- Claim 4.4: omitting a selected coordinate leaves a surviving flag. -/
theorem proper_intersection_card {q : ℕ} (hq : 0 < q) (active : Finset (Stage q))
    (i : Stage q) (hi : i ∉ active) (J : Finset (Index q))
    (hsub : J ⊂ address i) : i.val < (intersection active J).card := by
  classical
  obtain ⟨p,hp,hnot⟩ := Finset.exists_of_ssubset hsub
  have hflag : Sum.inr (Sum.inl p.1) ∈ intersection active J := by
    rw [mem_intersection]
    intro k hk
    change p.1 ≠ k.1
    intro heq
    have hpa := (mem_address i p).mp hp
    have hka := (mem_address i k).mp (hsub.subset hk)
    have hpk : p = k := Prod.ext heq (by rw [hpa, hka, heq])
    exact hnot (hpk ▸ hk)
  have hcore : core i ⊆ intersection active J := by
    rw [← primary_intersection hq active i hi]
    exact intersection_antitone active hsub.subset
  have hstrict : core i ⊂ intersection active J :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hcore, by
      intro heq
      have := heq ▸ hflag
      exact inr_not_mem_core i (Sum.inl p.1) this⟩
  simpa only [card_core] using Finset.card_lt_card hstrict

noncomputable def idealCard {q : ℕ} (active : Finset (Stage q)) : ℕ :=
  (generatedIdealIdx Finset.univ (generator active)).card

theorem intersection_insert {q : ℕ} (active : Finset (Stage q)) (i : Stage q)
    (J : Finset (Index q)) :
    intersection (insert i active) J =
      if J ⊆ address i then
        insert (Sum.inr (Sum.inr i)) (intersection active J)
      else intersection active J := by
  classical
  ext v
  rcases v with e | (j | g)
  · by_cases hs : J ⊆ address i <;> simp [hs, mem_intersection, Present]
  · by_cases hs : J ⊆ address i <;> simp [hs, mem_intersection, Present]
  · by_cases hgi : g = i
    · subst g
      have hsimp :
          (∀ p ∈ J, p.2 = i.val.testBit p.1.val) ↔ J ⊆ address i := by
        simp [Finset.subset_iff]
      by_cases hs : J ⊆ address i
      · rw [if_pos hs]
        constructor
        · intro _; exact Finset.mem_insert_self _ _
        · intro _
          apply (mem_intersection _ _ _).mpr
          intro p hp
          exact ⟨Finset.mem_insert_self _ _, (mem_address i p).mp (hs hp)⟩
      · simp only [hs, if_false, mem_intersection, Present, Finset.mem_insert,
          true_or, true_and]
        constructor
        · intro h
          exact False.elim (hs (hsimp.mp h))
        · intro h
          exact fun p hp => (h p hp).2
    · by_cases hs : J ⊆ address i <;>
        simp [hs, mem_intersection, Present, hgi]

theorem fresh_not_mem_intersection {q : ℕ} (active : Finset (Stage q))
    (i : Stage q) (hi : i ∉ active) {J : Finset (Index q)} (hJ : J.Nonempty) :
    Sum.inr (Sum.inr i) ∉ intersection active J := by
  intro h
  obtain ⟨p,hp⟩ := hJ
  exact hi ((mem_intersection active J _).mp h p hp).1

theorem intersection_insert_card {q : ℕ} (active : Finset (Stage q))
    (i : Stage q) (hi : i ∉ active) (J : Finset (Index q)) (hJ : J.Nonempty) :
    (intersection (insert i active) J).card =
      (intersection active J).card + if J ⊆ address i then 1 else 0 := by
  classical
  rw [intersection_insert]
  by_cases hs : J ⊆ address i
  · simp [hs, Finset.card_insert_of_notMem (fresh_not_mem_intersection active i hi hJ)]
  · simp [hs]

theorem idealCard_insert {q : ℕ} (active : Finset (Stage q))
    (i : Stage q) (hi : i ∉ active) :
    idealCard (insert i active) = idealCard active +
      (generatedIdealIdx (address i) (generator active)).card := by
  classical
  apply generatedIdealIdx_card_stage_of_intersection_cards
  · exact Finset.subset_univ _
  · intro t
    simp only [generatorIntersection, ← intersection_eq_inf']
    exact intersection_insert_card active i hi t.1 (Finset.mem_filter.mp t.2).2

theorem selected_card_zmod_signed {q : ℕ} (hq : 0 < q)
    (active : Finset (Stage q)) (i : Stage q) (hi : i ∉ active) :
    ((generatedIdealIdx (address i) (generator active)).card : ZMod (2 ^ (i.val + 1))) =
      (-1 : ZMod (2 ^ (i.val + 1))) ^ (q + 1) * 2 ^ i.val := by
  classical
  let t0 : (address i).powerset.filter (·.Nonempty) :=
    ⟨address i, by simp [address_nonempty hq i]⟩
  rw [generatedIdealIdx_card_zmod]
  calc
    (∑ t : (address i).powerset.filter (·.Nonempty),
      zmodIETerm (generator active) (i.val + 1) t) =
        zmodIETerm (generator active) (i.val + 1) t0 := by
      apply Finset.sum_eq_single_of_mem t0 (Finset.mem_univ _)
      intro t _ hne
      have hsub : t.1 ⊆ address i :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp t.2).1
      have hstrict : t.1 ⊂ address i := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
        intro heq
        exact hne (Subtype.ext heq)
      have hbig : i.val + 1 ≤ (generatorIntersection (generator active) t).card := by
        rw [generatorIntersection, ← intersection_eq_inf']
        exact Nat.succ_le_of_lt (proper_intersection_card hq active i hi t.1 hstrict)
      simp [zmodIETerm, two_pow_eq_zero_zmod _ _ hbig]
    _ = _ := by
      simp only [zmodIETerm, generatorIntersection, t0, card_address,
        ← intersection_eq_inf', primary_intersection_card hq active i hi]

theorem signed_half_modulus (r i : ℕ) :
    (-1 : ZMod (2 ^ (i + 1))) ^ r * 2 ^ i = 2 ^ i := by
  have hz : (2 : ZMod (2 ^ (i + 1))) ^ i + 2 ^ i = 0 := by
    calc
      (2 : ZMod (2 ^ (i + 1))) ^ i + 2 ^ i = 2 ^ (i + 1) := by
        rw [pow_succ]; ring
      _ = 0 := two_pow_eq_zero_zmod _ _ (le_refl _)
  rcases Nat.even_or_odd r with hr | hr
  · simp [hr.neg_one_pow]
  · rw [hr.neg_one_pow]
    simp only [neg_one_mul]
    exact (neg_eq_iff_add_eq_zero).mpr hz

theorem selected_card_modEq {q : ℕ} (hq : 0 < q)
    (active : Finset (Stage q)) (i : Stage q) (hi : i ∉ active) :
    (generatedIdealIdx (address i) (generator active)).card ≡
      2 ^ i.val [MOD 2 ^ (i.val + 1)] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [selected_card_zmod_signed hq active i hi, signed_half_modulus]
  simp

/-- A uniform target ceiling is used only to express the digit correction
with natural subtraction. It does not affect the final generator-size bound. -/
noncomputable def targetCeiling (q : ℕ) : ℕ :=
  Fintype.card (Index q) * 2 ^ Fintype.card (Vertex q)

theorem idealCard_le_targetCeiling {q : ℕ} (active : Finset (Stage q)) :
    idealCard active ≤ targetCeiling q :=
  generatedIdealIdx_univ_card_le (generator active)

/-- The staged residue induction, with exactly the paper's optional updates. -/
theorem exists_matching_active {q : ℕ} (hq : 0 < q) (Y : ℕ)
    (hY : targetCeiling q ≤ Y) :
    ∀ h : ℕ, h ≤ 2 ^ q → ∃ active : Finset (Stage q),
      (∀ g ∈ active, g.val < h) ∧ idealCard active ≡ Y [MOD 2 ^ h] := by
  classical
  intro h
  induction h with
  | zero =>
      intro _
      exact ⟨∅, by simp, by simpa using (Nat.modEq_one : idealCard ∅ ≡ Y [MOD 1])⟩
  | succ h ih =>
      intro hh
      obtain ⟨active,hpast,hmod⟩ := ih (by omega)
      let i : Stage q := ⟨h,by omega⟩
      have hi : i ∉ active := by
        intro hm
        have := hpast i hm
        exact (Nat.lt_irrefl h) this
      have hmY : idealCard active ≤ Y := (idealCard_le_targetCeiling active).trans hY
      let z : ℕ := ((Y - idealCard active) / 2 ^ h) % 2
      have hzlt : z < 2 := Nat.mod_lt _ (by norm_num)
      have hz : z ≡ (Y - idealCard active) / 2 ^ h [MOD 2] := by
        simp [Nat.ModEq, z]
      by_cases hz0 : z = 0
      · refine ⟨active, fun g hg => (hpast g hg).trans_le (Nat.le_succ h), ?_⟩
        have hdelta : 0 ≡ 2 ^ (h * 1) * z [MOD 2 ^ ((h + 1) * 1)] := by
          simpa [hz0] using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD 2 ^ (h + 1)])
        have hnext := extend_pow_modEq_digit (h := h) (q := 1)
          (delta := 0) hmY (by simpa using hmod) (by simpa using hz) hdelta
        simpa using hnext
      · have hz1 : z = 1 := by omega
        refine ⟨insert i active, ?_, ?_⟩
        · intro g hg
          rcases Finset.mem_insert.mp hg with rfl | hg
          · exact Nat.lt_succ_self h
          · exact (hpast g hg).trans_le (Nat.le_succ h)
        · rw [idealCard_insert active i hi]
          have hdelta :
              (generatedIdealIdx (address i) (generator active)).card ≡
              2 ^ (h * 1) * z [MOD 2 ^ ((h + 1) * 1)] := by
            simpa [i,hz1] using selected_card_modEq hq active i hi
          simpa using extend_pow_modEq_digit (h := h) (q := 1)
            hmY (by simpa using hmod) (by simpa using hz) hdelta

noncomputable def bitsEquiv (q : ℕ) : Stage q ≃ (Fin q → Bool) :=
  Equiv.ofBijective (fun g j => g.val.testBit j.val) <|
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨
      by intro g i h; exact stage_eq_of_bits g i (fun j => congrFun h j),
      by simp [Stage]⟩

def fixedBitEquiv {q : ℕ} (j : Fin q) (b : Bool) :
    {f : Fin q → Bool // f j = b} ≃ ({k : Fin q // k ≠ j} → Bool) where
  toFun f k := f.val k.val
  invFun f := ⟨fun k => if h : k = j then b else f ⟨k,h⟩, by simp⟩
  left_inv f := by
    apply Subtype.ext
    funext k
    by_cases h : k = j
    · subst k; simpa using f.property.symm
    · simp [h]
  right_inv f := by
    funext k
    simp [k.property]

/-- Exactly half the addresses select either generator in a fixed pair. -/
theorem card_fixed_bit {q : ℕ} (j : Fin q) (b : Bool) :
    (Finset.univ.filter fun g : Stage q => g.val.testBit j.val = b).card =
      2 ^ (q - 1) := by
  classical
  rw [← Fintype.card_subtype]
  let e : {g : Stage q // g.val.testBit j.val = b} ≃
      {f : Fin q → Bool // f j = b} :=
    (bitsEquiv q).subtypeEquiv (fun _ => Iff.rfl)
  rw [Fintype.card_congr e, Fintype.card_congr (fixedBitEquiv j b)]
  simp

def generatorBound (q : ℕ) : ℕ := (2 ^ q - 1) + (q - 1) + 2 ^ (q - 1)

noncomputable def oldPart {q : ℕ} (p : Index q) : Finset (BlockVertex q) :=
  Finset.univ.filter fun e => e.1 ≠ p.1 ∨ p.2 = true

noncomputable def freshPart {q : ℕ} (active : Finset (Stage q)) (p : Index q) :
    Finset (Stage q) :=
  active.filter fun g => p.2 = g.val.testBit p.1.val

theorem generator_decomposition {q : ℕ} (active : Finset (Stage q)) (p : Index q) :
    generator active p = (oldPart p).disjSum
      ((Finset.univ.erase p.1).disjSum (freshPart active p)) := by
  classical
  ext v
  rcases v with e | (j | g) <;>
    simp [generator, Present, oldPart, freshPart]

theorem card_blockVertex (q : ℕ) :
    Fintype.card (BlockVertex q) = 2 ^ q - 1 := by
  simp only [BlockVertex, Fintype.card_sigma, Fintype.card_fin]
  exact sum_two_pow_fin q

theorem card_freshPart_le {q : ℕ} (active : Finset (Stage q)) (p : Index q) :
    (freshPart active p).card ≤ 2 ^ (q - 1) := by
  classical
  rw [← card_fixed_bit p.1 p.2]
  apply Finset.card_le_card
  intro g hg
  simp only [freshPart, Finset.mem_filter] at hg
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg.2.symm⟩

theorem card_generator_le {q : ℕ} (active : Finset (Stage q)) (p : Index q) :
    (generator active p).card ≤ generatorBound q := by
  classical
  have hold : (oldPart p).card ≤ 2 ^ q - 1 := by
    simpa only [card_blockVertex] using Finset.card_le_univ (oldPart p)
  rw [generator_decomposition, Finset.card_disjSum, Finset.card_disjSum]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  have := card_freshPart_le active p
  unfold generatorBound
  omega

theorem card_generator_false_lt {q : ℕ} (active : Finset (Stage q)) (j : Fin q) :
    (generator active (j,false)).card < generatorBound q := by
  classical
  let e : BlockVertex q := ⟨j, ⟨0, by positivity⟩⟩
  have he : e ∉ oldPart (j,false) := by simp [oldPart,e]
  have hold : (oldPart (j,false)).card < 2 ^ q - 1 := by
    rw [← card_blockVertex]
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, by intro h; exact he (h ▸ Finset.mem_univ e)⟩)
  rw [generator_decomposition, Finset.card_disjSum, Finset.card_disjSum]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  have := card_freshPart_le active (j,false)
  unfold generatorBound
  omega

/-- The strict union estimate needs only one smaller (odd-indexed) generator. -/
theorem idealCard_lt_uniform {q : ℕ} (hq : 0 < q) (active : Finset (Stage q)) :
    idealCard active < 2 * q * 2 ^ generatorBound q := by
  classical
  calc
    idealCard active ≤ ∑ p : Index q, 2 ^ (generator active p).card := by
      simpa only [idealCard, generatedIdealIdx, Finset.card_powerset] using
        (Finset.card_biUnion_le (s := (Finset.univ : Finset (Index q)))
          (t := fun p => (generator active p).powerset))
    _ < ∑ _p : Index q, 2 ^ generatorBound q := by
      apply Finset.sum_lt_sum
      · intro p _
        exact Nat.pow_le_pow_right (by norm_num) (card_generator_le active p)
      · refine ⟨(⟨0,hq⟩,false), Finset.mem_univ _, ?_⟩
        exact Nat.pow_lt_pow_right (by norm_num) (card_generator_false_lt active ⟨0,hq⟩)
    _ = 2 * q * 2 ^ generatorBound q := by simp [Index, Nat.mul_comm]

theorem twice_le_two_pow {q : ℕ} (hq : 0 < q) : 2 * q ≤ 2 ^ q := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      have hi := ih (by omega)
      simp only [Nat.succ_eq_add_one] at *
      nlinarith [show 1 ≤ 2 ^ (k + 1) from Nat.one_le_two_pow]

theorem twice_le_half_pow_add_two {q : ℕ} (hq : 0 < q) :
    2 * q ≤ 2 ^ (q - 1) + 2 := by
  by_cases hq1 : q = 1
  · subst q; norm_num
  obtain ⟨k,rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
  induction k with
  | zero => norm_num
  | succ k ih =>
      have he : k + 1 + 2 - 1 = (k + 2 - 1) + 1 := by omega
      rw [he, pow_succ]
      have hi := ih (by omega) (by omega)
      have hlo : 2 ≤ 2 ^ (k + 2 - 1) := by
        simpa using Nat.pow_le_pow_right (n := 2) (by norm_num)
          (show 1 ≤ k + 2 - 1 by omega)
      nlinarith

theorem uniform_bound_le {q : ℕ} (hq : 0 < q) :
    2 * q * 2 ^ generatorBound q ≤ 2 ^ (2 ^ (q + 1)) := by
  have hhalf : 2 ^ q = 2 * 2 ^ (q - 1) := by
    conv_lhs => rw [show q = (q - 1) + 1 by omega]
    rw [pow_succ, Nat.mul_comm]
  have hnum := twice_le_half_pow_add_two hq
  have hpow : 1 ≤ 2 ^ q := Nat.one_le_two_pow
  have hexp : q + generatorBound q ≤ 2 ^ (q + 1) := by
    unfold generatorBound
    rw [pow_succ]
    omega
  calc
    2 * q * 2 ^ generatorBound q ≤ 2 ^ q * 2 ^ generatorBound q :=
      Nat.mul_le_mul_right _ (twice_le_two_pow hq)
    _ = 2 ^ (q + generatorBound q) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (2 ^ (q + 1)) := Nat.pow_le_pow_right (by norm_num) hexp

theorem idealCard_lt {q : ℕ} (hq : 0 < q) (active : Finset (Stage q)) :
    idealCard active < 2 ^ (2 ^ (q + 1)) :=
  (idealCard_lt_uniform hq active).trans_le (uniform_bound_le hq)

theorem idealCard_pos {q : ℕ} (hq : 0 < q) (active : Finset (Stage q)) :
    0 < idealCard active := by
  classical
  exact generatedIdealIdx_card_pos ⟨(⟨0,hq⟩,false), Finset.mem_univ _⟩ _

theorem alpha_idealCard_le {q : ℕ} (active : Finset (Stage q)) :
    alpha (idealCard active) ≤ 2 * q := by
  classical
  simpa [idealCard,Index,Nat.mul_comm] using
    alpha_generatedIdealIdx_univ_card_le (generator active)

/-- Theorem 4.1, in natural residue form.  The target has no size restriction. -/
theorem exists_matching (q y : ℕ) (hq : 0 < q) :
    ∃ m : ℕ, 0 < m ∧ m < 2 ^ (2 ^ (q + 1)) ∧
      m ≡ y [MOD 2 ^ (2 ^ q)] ∧ alpha m ≤ 2 * q := by
  classical
  let M := 2 ^ (2 ^ q)
  let Y := y + M * (targetCeiling q + 1)
  have hM : 1 ≤ M := Nat.one_le_two_pow
  have hY : targetCeiling q ≤ Y := by
    dsimp [Y]
    nlinarith
  obtain ⟨active,_,hmod⟩ := exists_matching_active hq Y hY (2 ^ q) (le_refl _)
  refine ⟨idealCard active, idealCard_pos hq active, idealCard_lt hq active, ?_,
    alpha_idealCard_le active⟩
  apply hmod.trans
  change Y % M = y % M
  simp [Y]

/-- The paper allows an arbitrary integer target.  Reducing it in the finite
residue ring gives precisely the same construction and bounds. -/
theorem exists_matching_int (q : ℕ) (y : ℤ) (hq : 0 < q) :
    ∃ m : ℕ, 0 < m ∧ m < 2 ^ (2 ^ (q + 1)) ∧
      (m : ZMod (2 ^ (2 ^ q))) = (y : ZMod (2 ^ (2 ^ q))) ∧ alpha m ≤ 2 * q := by
  letI : NeZero (2 ^ (2 ^ q)) := ⟨by positivity⟩
  obtain ⟨m,hm,hlt,hmod,ha⟩ := exists_matching q (y : ZMod (2 ^ (2 ^ q))).val hq
  refine ⟨m,hm,hlt,?_,ha⟩
  rw [← ZMod.natCast_zmod_val (y : ZMod (2 ^ (2 ^ q)))]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod

end AntichainOfGivenSize.Paper.BitMatching
