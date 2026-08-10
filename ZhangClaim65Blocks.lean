import ZhangSection6Core
import ZhangClaim64

open scoped BigOperators

namespace ZhangClaim65

open Finset
open ZhangSection6

/-! Concrete generator indices and their selected stage subfamilies. -/

abbrev BlockIndex (r q : ℕ) := (Fin r × Bool) ⊕ (Fin q × Bool)

def ePattern {r q : ℕ} (j : Fin r) : Finset (BlockIndex r q) :=
  Finset.univ.filter fun i => i ≠ Sum.inl (j, false)

def fPattern {r q : ℕ} (j : Fin r) : Finset (BlockIndex r q) :=
  Finset.univ.filter fun i =>
    i ≠ Sum.inl (j, false) ∧ i ≠ Sum.inl (j, true)

noncomputable def rPattern {r q : ℕ} (a : Fin q) (b : Bool) : Finset (BlockIndex r q) :=
  by
    classical
    exact Finset.univ.filter fun i =>
      match i with
      | Sum.inl _ => True
      | Sum.inr ab => ab = (a, b)

def chosenPos {r q : ℕ} (T : Finset (Fin r)) (j : Fin r) : BlockIndex r q :=
  Sum.inl (j, decide (j ∈ T))

def chosenPat {r q : ℕ} (d : ℕ) (a : Fin q) : BlockIndex r q :=
  Sum.inr (a, d.testBit a)

def chosenPosEmbedding {r q : ℕ} (T : Finset (Fin r)) : Fin r ↪ BlockIndex r q where
  toFun := chosenPos T
  inj' := by
    intro i j hij
    exact congrArg Prod.fst (Sum.inl.inj hij)

def chosenPatEmbedding {r q : ℕ} (d : ℕ) : Fin q ↪ BlockIndex r q where
  toFun := chosenPat d
  inj' := by
    intro a b hab
    exact congrArg Prod.fst (Sum.inr.inj hab)

def positionChoices {r q : ℕ} (T : Finset (Fin r)) : Finset (BlockIndex r q) :=
  Finset.univ.map (chosenPosEmbedding T)

def patternChoices {r q : ℕ} (d : ℕ) : Finset (BlockIndex r q) :=
  Finset.univ.map (chosenPatEmbedding d)

def selected {r q : ℕ} (T : Finset (Fin r)) (d : ℕ) :
    Finset (BlockIndex r q) :=
  positionChoices T ∪ patternChoices d

@[simp] theorem mem_positionChoices_chosenPos {r q : ℕ}
    (T : Finset (Fin r)) (j : Fin r) :
    chosenPos (q := q) T j ∈ positionChoices T := by
  simp [positionChoices, chosenPosEmbedding]

@[simp] theorem mem_patternChoices_chosenPat {r q : ℕ}
    (d : ℕ) (a : Fin q) :
    chosenPat (r := r) d a ∈ patternChoices d := by
  simp [patternChoices, chosenPatEmbedding]

theorem disjoint_position_pattern {r q : ℕ} (T : Finset (Fin r)) (d : ℕ) :
    Disjoint (positionChoices (q := q) T) (patternChoices (r := r) (q := q) d) := by
  rw [Finset.disjoint_left]
  intro i hiP hiQ
  simp only [positionChoices, Finset.mem_map, Finset.mem_univ, true_and] at hiP
  simp only [patternChoices, Finset.mem_map, Finset.mem_univ, true_and] at hiQ
  rcases hiP with ⟨j, rfl⟩
  rcases hiQ with ⟨a, ha⟩
  exact Sum.inl_ne_inr ha.symm

@[simp] theorem card_positionChoices {r q : ℕ} (T : Finset (Fin r)) :
    (positionChoices (q := q) T).card = r := by
  simp [positionChoices]

@[simp] theorem card_patternChoices {r q : ℕ} (d : ℕ) :
    (patternChoices (r := r) (q := q) d).card = q := by
  simp [patternChoices]

@[simp] theorem card_selected {r q : ℕ} (T : Finset (Fin r)) (d : ℕ) :
    (selected (q := q) T d).card = r + q := by
  rw [selected, Finset.card_union_of_disjoint (disjoint_position_pattern T d)]
  simp

theorem mem_selected_iff {r q : ℕ} {T : Finset (Fin r)} {d : ℕ}
    {i : BlockIndex r q} :
    i ∈ selected T d ↔ i ∈ positionChoices T ∨ i ∈ patternChoices d := by
  simp [selected]

@[simp] theorem positionIndex_mem_selected_iff {r q : ℕ}
    (T : Finset (Fin r)) (d : ℕ) (j : Fin r) (b : Bool) :
    Sum.inl (j, b) ∈ selected (q := q) T d ↔ b = decide (j ∈ T) := by
  simp only [selected, Finset.mem_union, positionChoices, patternChoices,
    Finset.mem_map, Finset.mem_univ, true_and, chosenPosEmbedding, chosenPatEmbedding]
  constructor
  · rintro (⟨k, hk⟩ | ⟨a, ha⟩)
    · change Sum.inl (k, decide (k ∈ T)) = Sum.inl (j, b) at hk
      have hp := Sum.inl.inj hk
      have hjk : k = j := congrArg Prod.fst hp
      subst k
      exact (congrArg Prod.snd hp).symm
    · change Sum.inr (a, d.testBit a) = Sum.inl (j, b) at ha
      exact False.elim (Sum.inr_ne_inl ha)
  · intro hb
    left
    refine ⟨j, ?_⟩
    change Sum.inl (j, decide (j ∈ T)) = Sum.inl (j, b)
    simp [hb]

@[simp] theorem patternIndex_mem_selected_iff {r q : ℕ}
    (T : Finset (Fin r)) (d : ℕ) (a : Fin q) (b : Bool) :
    Sum.inr (a, b) ∈ selected (r := r) T d ↔ b = d.testBit a := by
  simp only [selected, Finset.mem_union, positionChoices, patternChoices,
    Finset.mem_map, Finset.mem_univ, true_and, chosenPosEmbedding, chosenPatEmbedding]
  constructor
  · rintro (⟨j, hj⟩ | ⟨a', ha⟩)
    · change Sum.inl (j, decide (j ∈ T)) = Sum.inr (a, b) at hj
      exact False.elim (Sum.inl_ne_inr hj)
    · change Sum.inr (a', d.testBit a') = Sum.inr (a, b) at ha
      have hp := Sum.inr.inj ha
      have haa : a' = a := congrArg Prod.fst hp
      subst a'
      exact (congrArg Prod.snd hp).symm
  · intro hb
    right
    refine ⟨a, ?_⟩
    change Sum.inr (a, d.testBit a) = Sum.inr (a, b)
    simp [hb]

theorem chosenPos_injective {r q : ℕ} (T : Finset (Fin r)) :
    Function.Injective (chosenPos (q := q) T) :=
  (chosenPosEmbedding T).injective

theorem chosenPat_injective {r q : ℕ} (d : ℕ) :
    Function.Injective (chosenPat (r := r) (q := q) d) :=
  (chosenPatEmbedding d).injective

@[simp] theorem chosenPos_mem_selected_iff {r q : ℕ}
    (T T' : Finset (Fin r)) (d : ℕ) (j : Fin r) :
    chosenPos (q := q) T j ∈ selected T' d ↔ (j ∈ T ↔ j ∈ T') := by
  change Sum.inl (j, decide (j ∈ T)) ∈ selected T' d ↔ _
  rw [positionIndex_mem_selected_iff]
  by_cases hT : j ∈ T <;> by_cases hT' : j ∈ T' <;> simp [hT, hT']

theorem selected_position_ext {r q : ℕ}
    {T T' : Finset (Fin r)} {d : ℕ}
    (hsub : positionChoices (q := q) T ⊆ selected T' d) : T = T' := by
  ext j
  have hj := hsub (mem_positionChoices_chosenPos (q := q) T j)
  exact chosenPos_mem_selected_iff T T' d j |>.mp hj

theorem subset_ePattern_iff {r q : ℕ}
    (J : Finset (BlockIndex r q)) (j : Fin r) :
    J ⊆ ePattern j ↔ Sum.inl (j, false) ∉ J := by
  simp [ePattern, Finset.subset_iff]

theorem subset_fPattern_iff {r q : ℕ}
    (J : Finset (BlockIndex r q)) (j : Fin r) :
    J ⊆ fPattern j ↔
      Sum.inl (j, false) ∉ J ∧ Sum.inl (j, true) ∉ J := by
  constructor
  · intro h
    constructor <;> intro hj
    · have := h hj
      simp [fPattern] at this
    · have := h hj
      simp [fPattern] at this
  · rintro ⟨hfalse, htrue⟩ i hi
    simp only [fPattern, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hieq
      exact hfalse (hieq ▸ hi)
    · intro hieq
      exact htrue (hieq ▸ hi)

theorem subset_ePattern_of_subset_selected {r q : ℕ}
    {T : Finset (Fin r)} {d : ℕ} {J : Finset (BlockIndex r q)}
    (hJS : J ⊆ selected T d) (j : Fin r) (hj : j ∈ T) :
    J ⊆ ePattern j := by
  rw [subset_ePattern_iff]
  intro hbad
  have hs := hJS hbad
  have hb := positionIndex_mem_selected_iff (q := q) T d j false |>.mp hs
  simp [hj] at hb

theorem not_subset_ePattern_of_all_positions {r q : ℕ}
    {T : Finset (Fin r)} {J : Finset (BlockIndex r q)}
    (hpos : positionChoices (q := q) T ⊆ J) (j : Fin r) (hj : j ∉ T) :
    ¬ J ⊆ ePattern j := by
  rw [subset_ePattern_iff]
  simpa [chosenPos, hj] using hpos (mem_positionChoices_chosenPos (q := q) T j)

theorem not_subset_fPattern_of_all_positions {r q : ℕ}
    {T : Finset (Fin r)} {J : Finset (BlockIndex r q)}
    (hpos : positionChoices (q := q) T ⊆ J) (j : Fin r) :
    ¬ J ⊆ fPattern j := by
  rw [subset_fPattern_iff]
  by_cases hj : j ∈ T
  · have hm := hpos (mem_positionChoices_chosenPos (q := q) T j)
    have hm' : Sum.inl (j, true) ∈ J := by simpa [chosenPos, hj] using hm
    exact fun h => h.2 hm'
  · have hm := hpos (mem_positionChoices_chosenPos (q := q) T j)
    have hm' : Sum.inl (j, false) ∈ J := by simpa [chosenPos, hj] using hm
    exact fun h => h.1 hm'

theorem not_subset_past_of_all_positions {r q h : ℕ}
    {T : Finset (Fin r)} {J : Finset (BlockIndex r q)}
    (hpos : positionChoices (q := q) T ⊆ J)
    (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (hpast : ∀ g, pastT g ≠ T) (g : Fin h) :
    ¬ J ⊆ selected (pastT g) (pastD g) := by
  intro hsub
  apply hpast g
  exact (selected_position_ext (hsub.trans' hpos)).symm

/-! Typed atom species.  The type tags keep disjoint physical blocks
disjoint even if two support patterns happen to coincide in a degenerate
small parameter case. -/

abbrev AtomSpecies (r q h : ℕ) :=
  (Fin r × Bool) ⊕ ((Fin q × Bool) ⊕ Fin h)

noncomputable def speciesSupport {r q h : ℕ}
    (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ) :
    AtomSpecies r q h → Finset (BlockIndex r q)
  | Sum.inl (j, false) => ePattern j
  | Sum.inl (j, true) => fPattern j
  | Sum.inr (Sum.inl (a, b)) => rPattern a b
  | Sum.inr (Sum.inr g) => selected (pastT g) (pastD g)

def speciesCount {r q h : ℕ} (w : Fin r → ℕ) :
    AtomSpecies r q h → ℕ
  | Sum.inl (j, false) => q * w j
  | Sum.inl (_j, true) => q
  | Sum.inr (Sum.inl (a, b)) => a.val + if b then 1 else 0
  | Sum.inr (Sum.inr _g) => 1

abbrev AtomVertex (r q h : ℕ) (w : Fin r → ℕ) :=
  Σ s : AtomSpecies r q h, Fin (speciesCount w s)

noncomputable def oldGenerator {r q h : ℕ} (w : Fin r → ℕ)
    (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (i : BlockIndex r q) : Finset (AtomVertex r q h w) :=
  Finset.univ.filter fun v => i ∈ speciesSupport pastT pastD v.1

noncomputable def blockCommonCount {r q h : ℕ} (w : Fin r → ℕ)
    (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (J : Finset (BlockIndex r q)) : ℕ :=
  ∑ s : AtomSpecies r q h,
    if J ⊆ speciesSupport pastT pastD s then speciesCount w s else 0

theorem blockCommonCount_expand {r q h : ℕ} (w : Fin r → ℕ)
    (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (J : Finset (BlockIndex r q)) :
    blockCommonCount w pastT pastD J =
      (∑ j : Fin r, if J ⊆ ePattern j then q * w j else 0) +
      (∑ j : Fin r, if J ⊆ fPattern j then q else 0) +
      (∑ a : Fin q, ∑ b : Bool,
        if J ⊆ rPattern a b then a.val + if b then 1 else 0 else 0) +
      (∑ g : Fin h, if J ⊆ selected (pastT g) (pastD g) then 1 else 0) := by
  simp only [blockCommonCount, AtomSpecies, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fintype.sum_bool, speciesSupport, speciesCount,
    Finset.sum_add_distrib]
  ac_rfl

noncomputable def remainderCommon {r q : ℕ}
    (J : Finset (BlockIndex r q)) : ℕ :=
  ∑ a : Fin q, ∑ b : Bool,
    if J ⊆ rPattern a b then a.val + if b then 1 else 0 else 0

theorem blockCommonCount_of_all_positions {r q h : ℕ} (w : Fin r → ℕ)
    (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (T : Finset (Fin r)) (d : ℕ) (J : Finset (BlockIndex r q))
    (hJS : J ⊆ selected T d) (hpos : positionChoices (q := q) T ⊆ J)
    (hpast : ∀ g, pastT g ≠ T) :
    blockCommonCount w pastT pastD J =
      (∑ j ∈ T, q * w j) + remainderCommon J := by
  rw [blockCommonCount_expand]
  have he :
      (∑ j : Fin r, if J ⊆ ePattern j then q * w j else 0) =
        ∑ j ∈ T, q * w j := by
    calc
      (∑ j : Fin r, if J ⊆ ePattern j then q * w j else 0) =
          ∑ j : Fin r, if j ∈ T then q * w j else 0 := by
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hjT : j ∈ T
        · simp [hjT, subset_ePattern_of_subset_selected hJS j hjT]
        · simp [hjT, not_subset_ePattern_of_all_positions hpos j hjT]
      _ = ∑ j ∈ T, q * w j := by
        simp
  have hf : (∑ j : Fin r, if J ⊆ fPattern j then q else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _hj
    simp [not_subset_fPattern_of_all_positions hpos j]
  have hh :
      (∑ g : Fin h, if J ⊆ selected (pastT g) (pastD g) then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro g _hg
    simp [not_subset_past_of_all_positions hpos pastT pastD hpast g]
  rw [he, hf, hh]
  simp [remainderCommon]

theorem positionChoices_subset_rPattern {r q : ℕ}
    (T : Finset (Fin r)) (a : Fin q) (b : Bool) :
    positionChoices (q := q) T ⊆ rPattern a b := by
  intro i hi
  simp only [positionChoices, Finset.mem_map, Finset.mem_univ, true_and] at hi
  rcases hi with ⟨j, rfl⟩
  change chosenPos T j ∈ rPattern a b
  simp [rPattern, chosenPos]

theorem sum_range_remainder_pair_sizes (q : ℕ) :
    (Finset.range q).sum (fun a => (a + 1) + a) = q * q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ, ih]
      ring

theorem sum_remainder_pair_sizes (q : ℕ) :
    (Finset.univ : Finset (Fin q)).sum (fun a => (a.val + 1) + a.val) = q * q := by
  rw [Fin.sum_univ_eq_sum_range (fun a => (a + 1) + a)]
  exact sum_range_remainder_pair_sizes q

theorem remainderCommon_positionChoices {r q : ℕ} (T : Finset (Fin r)) :
    remainderCommon (q := q) (positionChoices T) = q * q := by
  rw [remainderCommon]
  simp only [positionChoices_subset_rPattern, if_true, Fintype.sum_bool,
    Bool.false_eq_true, if_false, Nat.add_zero]
  simpa using sum_remainder_pair_sizes q

theorem patternChoices_subset_ePattern {r q : ℕ}
    (d : ℕ) (j : Fin r) :
    patternChoices (r := r) (q := q) d ⊆ ePattern (q := q) j := by
  intro i hi
  simp only [patternChoices, Finset.mem_map, Finset.mem_univ, true_and] at hi
  rcases hi with ⟨a, rfl⟩
  change chosenPat d a ∈ ePattern j
  simp [ePattern, chosenPat]

theorem patternChoices_subset_fPattern {r q : ℕ}
    (d : ℕ) (j : Fin r) :
    patternChoices (r := r) (q := q) d ⊆ fPattern (q := q) j := by
  intro i hi
  simp only [patternChoices, Finset.mem_map, Finset.mem_univ, true_and] at hi
  rcases hi with ⟨a, rfl⟩
  change chosenPat d a ∈ fPattern j
  simp [fPattern, chosenPat]

theorem subset_patternChoices_of_no_position {r q : ℕ}
    {T : Finset (Fin r)} {d : ℕ} {J : Finset (BlockIndex r q)}
    (hJS : J ⊆ selected T d) (hnone : Disjoint J (positionChoices T)) :
    J ⊆ patternChoices d := by
  intro i hi
  rcases mem_selected_iff.mp (hJS hi) with hiP | hiQ
  · exact False.elim (Finset.disjoint_left.mp hnone hi hiP)
  · exact hiQ

theorem blockCommonCount_lower_of_no_position {r q h : ℕ} (w : Fin r → ℕ)
    (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (T : Finset (Fin r)) (d : ℕ) (J : Finset (BlockIndex r q))
    (hJS : J ⊆ selected T d) (hnone : Disjoint J (positionChoices T)) :
    (∑ j : Fin r, q * w j) + (∑ _j : Fin r, q) ≤
      blockCommonCount w pastT pastD J := by
  have hpat := subset_patternChoices_of_no_position hJS hnone
  rw [blockCommonCount_expand]
  have he :
      (∑ j : Fin r, if J ⊆ ePattern j then q * w j else 0) =
        ∑ j : Fin r, q * w j := by
    apply Finset.sum_congr rfl
    intro j _hj
    simp [hpat.trans (patternChoices_subset_ePattern d j)]
  have hf :
      (∑ j : Fin r, if J ⊆ fPattern j then q else 0) =
        ∑ _j : Fin r, q := by
    apply Finset.sum_congr rfl
    intro j _hj
    simp [hpat.trans (patternChoices_subset_fPattern d j)]
  rw [he, hf]
  omega

theorem subset_fPattern_of_missing_position {r q : ℕ}
    {T : Finset (Fin r)} {d : ℕ} {J : Finset (BlockIndex r q)}
    (hJS : J ⊆ selected T d) (j : Fin r)
    (hmiss : chosenPos (q := q) T j ∉ J) : J ⊆ fPattern j := by
  rw [subset_fPattern_iff]
  constructor
  · intro hfalse
    have hs := positionIndex_mem_selected_iff (q := q) T d j false |>.mp (hJS hfalse)
    apply hmiss
    simpa [chosenPos, hs] using hfalse
  · intro htrue
    have hs := positionIndex_mem_selected_iff (q := q) T d j true |>.mp (hJS htrue)
    apply hmiss
    simpa [chosenPos, hs] using htrue

theorem blockCommonCount_lower_of_missing_position {r q h : ℕ} (w : Fin r → ℕ)
    (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (T : Finset (Fin r)) (d : ℕ) (J : Finset (BlockIndex r q))
    (hJS : J ⊆ selected T d) (jmiss : Fin r)
    (hmiss : chosenPos (q := q) T jmiss ∉ J) :
    (∑ j ∈ T, q * w j) + q ≤ blockCommonCount w pastT pastD J := by
  rw [blockCommonCount_expand]
  have he :
      (∑ j ∈ T, q * w j) ≤
        ∑ j : Fin r, if J ⊆ ePattern j then q * w j else 0 := by
    have hfilter :
        (∑ j ∈ T, q * w j) =
          ∑ j : Fin r, if j ∈ T then q * w j else 0 := by
      simp
    rw [hfilter]
    apply Finset.sum_le_sum
    intro j _hj
    by_cases hjT : j ∈ T
    · simp [hjT, subset_ePattern_of_subset_selected hJS j hjT]
    · simp [hjT]
  have hf : q ≤ ∑ j : Fin r, if J ⊆ fPattern j then q else 0 := by
    have hfj := subset_fPattern_of_missing_position hJS jmiss hmiss
    have hs := Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin r)))
      (f := fun j : Fin r => if J ⊆ fPattern j then q else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ jmiss)
    simpa [hfj] using hs
  omega

theorem eq_positionChoices_of_no_pattern {r q : ℕ}
    {T : Finset (Fin r)} {d : ℕ} {J : Finset (BlockIndex r q)}
    (hJS : J ⊆ selected T d) (hpos : positionChoices (q := q) T ⊆ J)
    (hnopat : Disjoint J (patternChoices d)) : J = positionChoices T := by
  apply Finset.Subset.antisymm
  · intro i hi
    rcases mem_selected_iff.mp (hJS hi) with hiP | hiQ
    · exact hiP
    · exact False.elim (Finset.disjoint_left.mp hnopat hi hiQ)
  · exact hpos

theorem blockCommonCount_of_all_positions_no_pattern {r q h : ℕ}
    (w : Fin r → ℕ) (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (T : Finset (Fin r)) (d : ℕ) (J : Finset (BlockIndex r q))
    (hJS : J ⊆ selected T d) (hpos : positionChoices (q := q) T ⊆ J)
    (hnopat : Disjoint J (patternChoices d)) (hpast : ∀ g, pastT g ≠ T) :
    blockCommonCount w pastT pastD J = (∑ j ∈ T, q * w j) + q * q := by
  have hJ : J = positionChoices T := eq_positionChoices_of_no_pattern hJS hpos hnopat
  rw [blockCommonCount_of_all_positions w pastT pastD T d J hJS hpos hpast,
    hJ, remainderCommon_positionChoices]

noncomputable def oldIntersection {r q h : ℕ} (w : Fin r → ℕ)
    (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (J : Finset (BlockIndex r q)) : Finset (AtomVertex r q h w) :=
  Finset.univ.filter fun v => J ⊆ speciesSupport pastT pastD v.1

theorem generatorIntersection_oldGenerator_eq {r q h : ℕ}
    (w : Fin r → ℕ) (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (S : Finset (BlockIndex r q))
    (t : S.powerset.filter (fun J : Finset (BlockIndex r q) => J.Nonempty)) :
    generatorIntersection (oldGenerator w pastT pastD) t =
      oldIntersection w pastT pastD t.1 := by
  ext v
  simp only [generatorIntersection, Finset.mem_inf', oldIntersection, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hv i hi
    have := hv i hi
    simpa [oldGenerator] using this
  · intro hv i hi
    simp [oldGenerator, hv hi]

theorem oldIntersection_card {r q h : ℕ}
    (w : Fin r → ℕ) (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (J : Finset (BlockIndex r q)) :
    (oldIntersection w pastT pastD J).card = blockCommonCount w pastT pastD J := by
  let allAtoms : Finset (AtomVertex r q h w) :=
    Finset.univ.sigma fun s : AtomSpecies r q h => Finset.univ
  have hall : allAtoms = Finset.univ := by
    ext v
    simp [allAtoms]
  rw [oldIntersection, ← hall]
  rw [Finset.filter_sigma]
  rw [Finset.card_sigma]
  simp only [Finset.card_filter, blockCommonCount]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hsub : J ⊆ speciesSupport pastT pastD s
  · simp [hsub]
  · simp [hsub]

theorem generatorIntersection_oldGenerator_card {r q h : ℕ}
    (w : Fin r → ℕ) (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (S : Finset (BlockIndex r q))
    (t : S.powerset.filter (fun J : Finset (BlockIndex r q) => J.Nonempty)) :
    (generatorIntersection (oldGenerator w pastT pastD) t).card =
      blockCommonCount w pastT pastD t.1 := by
  rw [generatorIntersection_oldGenerator_eq, oldIntersection_card]

end ZhangClaim65
