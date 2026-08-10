import AntichainOfGivenSize.Section6.Blocks

open scoped BigOperators

namespace AntichainOfGivenSize.Section6.Blocks

open Finset
open AntichainOfGivenSize.Section6

abbrev StageIndex (r q : ℕ) := Fin r ⊕ Fin q

def stageEmbedding {r q : ℕ} (T : Finset (Fin r)) (d : ℕ) :
    StageIndex r q ↪ BlockIndex r q where
  toFun
    | Sum.inl j => chosenPos T j
    | Sum.inr a => chosenPat d a
  inj' := by
    intro i k hik
    cases i with
    | inl i =>
        cases k with
        | inl k => exact congrArg Sum.inl ((chosenPos_injective T) hik)
        | inr k => exact False.elim (Sum.inl_ne_inr hik)
    | inr i =>
        cases k with
        | inl k => exact False.elim (Sum.inr_ne_inl hik)
        | inr k => exact congrArg Sum.inr ((chosenPat_injective d) hik)

def mappedStageSubset {r q : ℕ} (T : Finset (Fin r)) (d : ℕ)
    (A : Finset (StageIndex r q)) : Finset (BlockIndex r q) :=
  A.map (stageEmbedding T d)

theorem mappedStageSubset_subset_selected {r q : ℕ}
    (T : Finset (Fin r)) (d : ℕ) (A : Finset (StageIndex r q)) :
    mappedStageSubset T d A ⊆ selected T d := by
  intro i hi
  rcases Finset.mem_map.mp hi with ⟨x, hx, rfl⟩
  cases x with
  | inl j =>
      exact Finset.mem_union_left _ (mem_positionChoices_chosenPos T j)
  | inr a =>
      exact Finset.mem_union_right _ (mem_patternChoices_chosenPat d a)

theorem stageEmbedding_univ {r q : ℕ} (T : Finset (Fin r)) (d : ℕ) :
    (Finset.univ : Finset (StageIndex r q)).map (stageEmbedding T d) = selected T d := by
  apply Finset.Subset.antisymm
  · exact mappedStageSubset_subset_selected T d Finset.univ
  · intro i hi
    rcases mem_selected_iff.mp hi with hiP | hiQ
    · simp only [positionChoices, Finset.mem_map, Finset.mem_univ, true_and] at hiP
      rcases hiP with ⟨j, rfl⟩
      exact Finset.mem_map.2 ⟨Sum.inl j, Finset.mem_univ _, rfl⟩
    · simp only [patternChoices, Finset.mem_map, Finset.mem_univ, true_and] at hiQ
      rcases hiQ with ⟨a, rfl⟩
      exact Finset.mem_map.2 ⟨Sum.inr a, Finset.mem_univ _, rfl⟩

theorem positionChoices_subset_mapped_iff {r q : ℕ}
    (T : Finset (Fin r)) (d : ℕ) (A : Finset (StageIndex r q)) :
    positionChoices (q := q) T ⊆ mappedStageSubset T d A ↔
      A.toLeft = Finset.univ := by
  constructor
  · intro h
    apply Finset.eq_univ_iff_forall.2
    intro j
    have hj := h (mem_positionChoices_chosenPos (q := q) T j)
    rcases Finset.mem_map.mp hj with ⟨x, hx, heq⟩
    cases x with
    | inl k =>
        have hjk : k = j := chosenPos_injective T heq
        subst k
        simpa using hx
    | inr a => exact False.elim (Sum.inr_ne_inl heq)
  · intro h i hi
    simp only [positionChoices, Finset.mem_map, Finset.mem_univ, true_and] at hi
    rcases hi with ⟨j, rfl⟩
    apply Finset.mem_map.2
    refine ⟨Sum.inl j, ?_, rfl⟩
    have hj : j ∈ A.toLeft := by rw [h]; simp
    simpa using hj

theorem disjoint_mapped_position_iff {r q : ℕ}
    (T : Finset (Fin r)) (d : ℕ) (A : Finset (StageIndex r q)) :
    Disjoint (mappedStageSubset T d A) (positionChoices T) ↔ A.toLeft = ∅ := by
  rw [Finset.disjoint_left]
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.2
    intro j hj
    have hjA : Sum.inl j ∈ A := by simpa using hj
    exact h (Finset.mem_map.2 ⟨Sum.inl j, hjA, rfl⟩)
      (mem_positionChoices_chosenPos T j)
  · intro h i hiA hiP
    rcases Finset.mem_map.mp hiA with ⟨x, hx, rfl⟩
    cases x with
    | inl j =>
        have : j ∈ A.toLeft := by simpa using hx
        simp [h] at this
    | inr a =>
      simp only [positionChoices, Finset.mem_map, Finset.mem_univ, true_and] at hiP
      rcases hiP with ⟨j, hj⟩
      have hraw : chosenPos T j = chosenPat d a := by
        simpa [stageEmbedding, chosenPosEmbedding, chosenPatEmbedding] using hj
      exact False.elim (Sum.inl_ne_inr hraw)

theorem disjoint_mapped_pattern_iff {r q : ℕ}
    (T : Finset (Fin r)) (d : ℕ) (A : Finset (StageIndex r q)) :
    Disjoint (mappedStageSubset T d A) (patternChoices d) ↔ A.toRight = ∅ := by
  rw [Finset.disjoint_left]
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.2
    intro a ha
    have haA : Sum.inr a ∈ A := by simpa using ha
    exact h (Finset.mem_map.2 ⟨Sum.inr a, haA, rfl⟩)
      (mem_patternChoices_chosenPat d a)
  · intro h i hiA hiP
    rcases Finset.mem_map.mp hiA with ⟨x, hx, rfl⟩
    cases x with
    | inl j =>
      simp only [patternChoices, Finset.mem_map, Finset.mem_univ, true_and] at hiP
      rcases hiP with ⟨a, ha⟩
      have hraw : chosenPat d a = chosenPos T j := by
        simpa [stageEmbedding, chosenPosEmbedding, chosenPatEmbedding] using ha
      exact False.elim (Sum.inr_ne_inl hraw)
    | inr a =>
        have : a ∈ A.toRight := by simpa using hx
        simp [h] at this

theorem chosenPos_not_mem_mapped_of_not_mem_toLeft {r q : ℕ}
    (T : Finset (Fin r)) (d : ℕ) (A : Finset (StageIndex r q))
    (j : Fin r) (hj : j ∉ A.toLeft) :
    chosenPos (q := q) T j ∉ mappedStageSubset T d A := by
  intro hm
  rcases Finset.mem_map.mp hm with ⟨x, hx, heq⟩
  cases x with
  | inl k =>
      have hkj : k = j := chosenPos_injective T heq
      subst k
      exact hj (by simpa using hx)
  | inr a => exact False.elim (Sum.inr_ne_inl heq)

noncomputable def stageOldGenerator {r q h : ℕ} (w : Fin r → ℕ)
    (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (T : Finset (Fin r)) (d : ℕ) (i : StageIndex r q) :
    Finset (AtomVertex r q h w) :=
  oldGenerator w pastT pastD (stageEmbedding T d i)

theorem stage_generatorIntersection_card {r q h : ℕ} (w : Fin r → ℕ)
    (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (T : Finset (Fin r)) (d : ℕ)
    (t : (Finset.univ : Finset (StageIndex r q)).powerset.filter
      (fun A : Finset (StageIndex r q) => A.Nonempty)) :
    (generatorIntersection (stageOldGenerator w pastT pastD T d) t).card =
      blockCommonCount w pastT pastD (mappedStageSubset T d t.1) := by
  have heq :
      generatorIntersection (stageOldGenerator w pastT pastD T d) t =
        oldIntersection w pastT pastD (mappedStageSubset T d t.1) := by
    ext v
    simp only [generatorIntersection, Finset.mem_inf', oldIntersection,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hv x hx
      rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
      have := hv i hi
      simpa [stageOldGenerator, oldGenerator] using this
    · intro hv i hi
      have := hv (Finset.mem_map.2 ⟨i, hi, rfl⟩)
      simpa [stageOldGenerator, oldGenerator] using this
  rw [heq, oldIntersection_card]

/-! The selected remainder blocks, as genuinely disjoint tagged sets. -/

abbrev RemainderVertex (q d : ℕ) :=
  Σ a : Fin q, Fin (AntichainOfGivenSize.Section6.selectedBlockSize d a)

def remainderGenerator {q : ℕ} (d : ℕ) (a : Fin q) :
    Finset (RemainderVertex q d) :=
  Finset.univ.filter fun v => v.1 = a

def remainderIntersectionCount {q : ℕ} (d : ℕ) (L : Finset (Fin q)) : ℕ :=
  ∑ a : Fin q, if L ⊆ {a} then AntichainOfGivenSize.Section6.selectedBlockSize d a else 0

theorem remainder_generatorIntersection_card {q d : ℕ}
    (t : (Finset.univ : Finset (Fin q)).powerset.filter
      (fun L : Finset (Fin q) => L.Nonempty)) :
    (generatorIntersection (remainderGenerator d) t).card =
      remainderIntersectionCount d t.1 := by
  let allAtoms : Finset (RemainderVertex q d) :=
    Finset.univ.sigma fun a : Fin q => Finset.univ
  have hall : allAtoms = Finset.univ := by
    ext v
    simp [allAtoms]
  have hinter :
      generatorIntersection (remainderGenerator d) t =
        allAtoms.filter fun v => t.1 ⊆ {v.1} := by
    ext v
    simp only [generatorIntersection, Finset.mem_inf', Finset.mem_filter]
    rw [hall]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro hv a ha
      have := hv a ha
      have heq : v.1 = a := by simpa [remainderGenerator] using this
      simpa using heq.symm
    · intro hv a ha
      have heq : a = v.1 := by simpa using hv ha
      simpa [remainderGenerator] using heq.symm
  rw [hinter, Finset.filter_sigma, Finset.card_sigma]
  simp only [Finset.card_filter, remainderIntersectionCount]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hsub : t.1 ⊆ {a} <;> simp [hsub]

theorem mappedStageSubset_subset_rPattern_iff {r q : ℕ}
    (T : Finset (Fin r)) (d : ℕ) (A : Finset (StageIndex r q))
    (hright : A.toRight.Nonempty) (a : Fin q) (b : Bool) :
    mappedStageSubset T d A ⊆ rPattern a b ↔
      A.toRight ⊆ {a} ∧ b = d.testBit a := by
  constructor
  · intro hsub
    have hrightSub : A.toRight ⊆ {a} := by
      intro a' ha'
      have haA : Sum.inr a' ∈ A := by simpa using ha'
      have hm : chosenPat (r := r) d a' ∈ mappedStageSubset T d A :=
        Finset.mem_map.2 ⟨Sum.inr a', haA, rfl⟩
      have hr := hsub hm
      have hrpair : (a', d.testBit a') = (a, b) := by
        simpa [rPattern, chosenPat] using hr
      simpa using congrArg Prod.fst hrpair
    obtain ⟨a', ha'⟩ := hright
    have haA : Sum.inr a' ∈ A := by simpa using ha'
    have hm : chosenPat (r := r) d a' ∈ mappedStageSubset T d A :=
      Finset.mem_map.2 ⟨Sum.inr a', haA, rfl⟩
    have hr := hsub hm
    have hrpair : (a', d.testBit a') = (a, b) := by
      simpa [rPattern, chosenPat] using hr
    have haa : a' = a := congrArg Prod.fst hrpair
    have hbit : d.testBit a' = b := congrArg Prod.snd hrpair
    subst a'
    exact ⟨hrightSub, hbit.symm⟩
  · rintro ⟨hsub, hb⟩ i hi
    rcases Finset.mem_map.mp hi with ⟨x, hx, rfl⟩
    cases x with
    | inl j => simp [rPattern, stageEmbedding, chosenPos]
    | inr a' =>
        have ha' : a' ∈ A.toRight := by simpa using hx
        have haa : a' = a := by simpa using hsub ha'
        subst a'
        simp [rPattern, stageEmbedding, chosenPat, hb]

theorem remainderCommon_mappedStageSubset {r q : ℕ}
    (T : Finset (Fin r)) (d : ℕ) (A : Finset (StageIndex r q))
    (hright : A.toRight.Nonempty) :
    remainderCommon (mappedStageSubset T d A) =
      remainderIntersectionCount d A.toRight := by
  rw [remainderCommon, remainderIntersectionCount]
  apply Finset.sum_congr rfl
  intro a _ha
  simp_rw [mappedStageSubset_subset_rPattern_iff T d A hright a]
  by_cases hsub : A.toRight ⊆ {a}
  · rw [if_pos hsub]
    by_cases hbit : d.testBit a
    · simp [hsub, hbit, AntichainOfGivenSize.Section6.selectedBlockSize]
    · have hfalse : d.testBit a = false := Bool.eq_false_of_not_eq_true hbit
      simp [hsub, hfalse, AntichainOfGivenSize.Section6.selectedBlockSize]
  · simp [hsub]

end AntichainOfGivenSize.Section6.Blocks
