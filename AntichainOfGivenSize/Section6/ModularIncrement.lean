import AntichainOfGivenSize.Section6.Blocks

open scoped BigOperators

namespace AntichainOfGivenSize.Section6.Modular

open Finset
open AntichainOfGivenSize.Section6
open AntichainOfGivenSize.Section6.Blocks

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
  | inl j => exact Finset.mem_union_left _ (mem_positionChoices_chosenPos T j)
  | inr a => exact Finset.mem_union_right _ (mem_patternChoices_chosenPat d a)

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

def remainderIntersectionCount {q : ℕ} (d : ℕ) (L : Finset (Fin q)) : ℕ :=
  ∑ a : Fin q, if L ⊆ {a} then AntichainOfGivenSize.Section6.selectedBlockSize d a else 0

theorem mappedStageSubset_subset_rPattern_iff {r q : ℕ}
    (T : Finset (Fin r)) (d : ℕ) (A : Finset (StageIndex r q))
    (a : Fin q) (b : Bool) :
    mappedStageSubset T d A ⊆ rPattern a b ↔
      A.toRight ⊆ {a} ∧ (A.toRight.Nonempty → b = d.testBit a) := by
  constructor
  · intro h
    constructor
    · intro c hc
      have hcA : Sum.inr c ∈ A := by simpa using hc
      have hm := h (Finset.mem_map.2 ⟨Sum.inr c, hcA, rfl⟩)
      simp only [rPattern, Finset.mem_filter, Finset.mem_univ, true_and,
        stageEmbedding, chosenPat] at hm
      exact Finset.mem_singleton.2 (congrArg Prod.fst hm)
    · intro hn
      obtain ⟨c, hc⟩ := hn
      have hcA : Sum.inr c ∈ A := by simpa using hc
      have hm := h (Finset.mem_map.2 ⟨Sum.inr c, hcA, rfl⟩)
      simp only [rPattern, Finset.mem_filter, Finset.mem_univ, true_and,
        stageEmbedding, chosenPat] at hm
      have hca : c = a := by simpa using (congrArg Prod.fst hm)
      subst c
      exact (congrArg Prod.snd hm).symm
  · rintro ⟨hsub, hb⟩ i hi
    rcases Finset.mem_map.mp hi with ⟨x, hx, rfl⟩
    cases x with
    | inl j =>
        change chosenPos T j ∈ rPattern a b
        exact positionChoices_subset_rPattern T a b
          (mem_positionChoices_chosenPos T j)
    | inr c =>
        have hc : c ∈ A.toRight := by simpa using hx
        have hca : c = a := by simpa using hsub hc
        subst c
        have hne : A.toRight.Nonempty := ⟨a, hc⟩
        simp [rPattern, stageEmbedding, chosenPat, hb hne]

theorem remainderCommon_mapped_of_right_nonempty {r q : ℕ}
    (T : Finset (Fin r)) (d : ℕ) (A : Finset (StageIndex r q))
    (hright : A.toRight.Nonempty) :
    remainderCommon (mappedStageSubset T d A) =
      remainderIntersectionCount d A.toRight := by
  rw [remainderCommon, remainderIntersectionCount]
  apply Finset.sum_congr rfl
  intro a _ha
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, Nat.add_zero]
  by_cases hsub : A.toRight ⊆ {a}
  · have hbfalse := (mappedStageSubset_subset_rPattern_iff T d A a false)
    have hbtrue := (mappedStageSubset_subset_rPattern_iff T d A a true)
    by_cases hbit : d.testBit a = true
    · have ht : mappedStageSubset T d A ⊆ rPattern a true :=
        hbtrue.2 ⟨hsub, fun _ => hbit.symm⟩
      have hf : ¬ mappedStageSubset T d A ⊆ rPattern a false := by
        intro hf
        have := (hbfalse.1 hf).2 hright
        simp [hbit] at this
      simp [hsub, ht, hf, AntichainOfGivenSize.Section6.selectedBlockSize, hbit]
    · have hbitf : d.testBit a = false := Bool.eq_false_of_not_eq_true hbit
      have hf : mappedStageSubset T d A ⊆ rPattern a false :=
        hbfalse.2 ⟨hsub, fun _ => hbitf.symm⟩
      have ht : ¬ mappedStageSubset T d A ⊆ rPattern a true := by
        intro ht
        have := (hbtrue.1 ht).2 hright
        simp [hbitf] at this
      simp [hsub, ht, hf, AntichainOfGivenSize.Section6.selectedBlockSize, hbitf]
  · have hf : ¬ mappedStageSubset T d A ⊆ rPattern a false :=
      fun hm => hsub (mappedStageSubset_subset_rPattern_iff T d A a false |>.1 hm).1
    have ht : ¬ mappedStageSubset T d A ⊆ rPattern a true :=
      fun hm => hsub (mappedStageSubset_subset_rPattern_iff T d A a true |>.1 hm).1
    simp [hsub, hf, ht]

/-! A cardinality lemma for adjoining one member to an indexed family of
pairwise-disjoint generators. -/

theorem powerset_inter_generatedIdealIdx_eq_singleton
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    {s : Finset I} {a : I} (ha : a ∉ s) (hs : s.Nonempty)
    (G : I → Finset V)
    (hdisj : ∀ i ∈ insert a s, ∀ j ∈ insert a s, i ≠ j → Disjoint (G i) (G j)) :
    (G a).powerset ∩ generatedIdealIdx s G = {∅} := by
  ext u
  simp only [Finset.mem_inter, Finset.mem_powerset, generatedIdealIdx,
    Finset.mem_biUnion, Finset.mem_singleton]
  constructor
  · rintro ⟨hua, j, hjs, huj⟩
    have haj : a ≠ j := by
      intro haj
      subst j
      exact ha hjs
    have hd : Disjoint (G a) (G j) :=
      hdisj a (by simp) j (by simp [hjs]) haj
    apply Finset.eq_empty_iff_forall_notMem.2
    intro x hxu
    exact Finset.disjoint_left.1 hd (hua hxu) (huj hxu)
  · rintro rfl
    exact ⟨Finset.empty_subset _, by
      obtain ⟨j, hjs⟩ := hs
      exact ⟨j, hjs, Finset.empty_subset _⟩⟩

theorem generatedIdealIdx_card_of_pairwise_disjoint
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (s : Finset I) (G : I → Finset V)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (G i) (G j)) :
    (generatedIdealIdx s G).card =
      if s.Nonempty then 1 + ∑ i ∈ s, (2 ^ (G i).card - 1) else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [generatedIdealIdx]
  | @insert a s ha ih =>
      have hdisjS : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (G i) (G j) := by
        intro i hi j hj hij
        exact hdisj i (by simp [hi]) j (by simp [hj]) hij
      rw [show generatedIdealIdx (insert a s) G =
          (G a).powerset ∪ generatedIdealIdx s G by simp [generatedIdealIdx]]
      by_cases hs : s.Nonempty
      · have hinter : (G a).powerset ∩ generatedIdealIdx s G = {∅} :=
          powerset_inter_generatedIdealIdx_eq_singleton ha hs G hdisj
        have hold := ih hdisjS
        have hnon : (insert a s).Nonempty := ⟨a, mem_insert_self a s⟩
        simp only [hs, if_true] at hold
        rw [Finset.card_union, Finset.card_powerset, hinter, Finset.card_singleton]
        change (2 ^ (G a).card) + (generatedIdealIdx s G).card - 1 = _
        rw [hold]
        rw [if_pos hnon, Finset.sum_insert ha]
        have hp : 1 ≤ 2 ^ (G a).card := Nat.one_le_two_pow
        omega
      · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        have hnon : (insert a (∅ : Finset I)).Nonempty :=
          ⟨a, mem_insert_self a ∅⟩
        simp only [generatedIdealIdx, Finset.biUnion_empty, Finset.union_empty,
          Finset.card_powerset]
        rw [if_pos hnon, Finset.sum_insert ha]
        simp only [Finset.sum_empty, Nat.add_zero]
        have hp : 1 ≤ 2 ^ (G a).card := Nat.one_le_two_pow
        omega

abbrev RemainderVertex (q d : ℕ) :=
  Σ a : Fin q, Fin (AntichainOfGivenSize.Section6.selectedBlockSize d a)

def remainderGenerator {q : ℕ} (d : ℕ) (a : Fin q) :
    Finset (RemainderVertex q d) :=
  Finset.univ.filter fun v => v.1 = a

theorem remainderGenerator_card {q d : ℕ} (a : Fin q) :
    (remainderGenerator d a).card = AntichainOfGivenSize.Section6.selectedBlockSize d a := by
  let allAtoms : Finset (RemainderVertex q d) :=
    Finset.univ.sigma fun a : Fin q => Finset.univ
  have hall : allAtoms = Finset.univ := by
    ext v
    simp [allAtoms]
  rw [remainderGenerator, ← hall, Finset.filter_sigma, Finset.card_sigma]
  rw [Fintype.sum_eq_single a]
  · simp
  · intro b hba
    simp [hba]

theorem remainderGenerator_pairwise_disjoint {q d : ℕ}
    (a b : Fin q) (hab : a ≠ b) :
    Disjoint (remainderGenerator d a) (remainderGenerator d b) := by
  rw [Finset.disjoint_left]
  intro v hva hvb
  have ha : v.1 = a := by simpa [remainderGenerator] using hva
  have hb : v.1 = b := by simpa [remainderGenerator] using hvb
  exact hab (ha.symm.trans hb)

theorem remainderIdeal_card {q d : ℕ} (hq : 0 < q) :
    (generatedIdealIdx (Finset.univ : Finset (Fin q))
      (remainderGenerator d)).card = AntichainOfGivenSize.Section6.remainderZ q d := by
  have hnon : (Finset.univ : Finset (Fin q)).Nonempty := by
    exact ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  rw [generatedIdealIdx_card_of_pairwise_disjoint]
  · rw [if_pos hnon]
    simp only [remainderGenerator_card, AntichainOfGivenSize.Section6.remainderZ]
  · intro a _ha b _hb hab
    exact remainderGenerator_pairwise_disjoint a b hab

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

theorem sum_ite_subtype
    {α M : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] (f : α → M) :
    (∑ x : α, if p x then f x else 0) = ∑ y : {x // p x}, f y.1 := by
  calc
    (∑ x : α, if p x then f x else 0) =
        ∑ x ∈ (Finset.univ.filter p), f x := by
      exact (Finset.sum_filter p f).symm
    _ = ∑ y : {x // p x}, f y.1 := by
      exact Finset.sum_subtype (Finset.univ.filter p) (by simp) f

abbrev StageTerm (r q : ℕ) :=
  (Finset.univ : Finset (StageIndex r q)).powerset.filter
    (fun A : Finset (StageIndex r q) => A.Nonempty)

abbrev RemainderTerm (q : ℕ) :=
  (Finset.univ : Finset (Fin q)).powerset.filter
    (fun L : Finset (Fin q) => L.Nonempty)

def stageSurvives {r q : ℕ} (t : StageTerm r q) : Prop :=
  t.1.toLeft = Finset.univ ∧ t.1.toRight.Nonempty

noncomputable def remainderTermEquivSurvivor (r q : ℕ) :
    RemainderTerm q ≃ {t : StageTerm r q // stageSurvives t} := by
  classical
  let forward : RemainderTerm q → {t : StageTerm r q // stageSurvives t} := fun L => by
    let A : Finset (StageIndex r q) :=
      (Finset.univ : Finset (Fin r)).disjSum L.1
    have hsubset : A ⊆ (Finset.univ : Finset (StageIndex r q)) := by
      intro x _hx
      exact Finset.mem_univ x
    have hnon : A.Nonempty := by
      obtain ⟨a, ha⟩ := (Finset.mem_filter.1 L.2).2
      exact ⟨Sum.inr a, by simp [A, ha]⟩
    let t : StageTerm r q :=
      ⟨A, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hsubset, hnon⟩⟩
    exact ⟨t, by simp [stageSurvives, t, A, (Finset.mem_filter.1 L.2).2]⟩
  let backward : {t : StageTerm r q // stageSurvives t} → RemainderTerm q := fun t => by
    let L : Finset (Fin q) := t.1.1.toRight
    exact ⟨L, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (fun _ _ => Finset.mem_univ _),
      t.2.2⟩⟩
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro L
        apply Subtype.ext
        simp [forward, backward]
      right_inv := by
        intro t
        apply Subtype.ext
        apply Subtype.ext
        change (Finset.univ : Finset (Fin r)).disjSum t.1.1.toRight = t.1.1
        rw [← t.2.1]
        exact Finset.toLeft_disjSum_toRight }

noncomputable instance stageSurvivesDecidablePred (r q : ℕ) :
    DecidablePred (@stageSurvives r q) := Classical.decPred _

theorem stage_survivor_sum_equiv
    {r q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : StageTerm r q → M) :
    (∑ t : {t : StageTerm r q // stageSurvives t}, f t.1) =
      ∑ L : RemainderTerm q, f ((remainderTermEquivSurvivor r q L).1) := by
  classical
  exact (Fintype.sum_equiv (remainderTermEquivSurvivor r q)
    (fun L => f ((remainderTermEquivSurvivor r q L).1))
    (fun t => f t.1) (fun _ => rfl)).symm

theorem weighted_position_count {r q h : ℕ} (w : Fin r → ℕ)
    (T : Finset (Fin r)) (hweight : ∑ j ∈ T, w j = h) :
    (∑ j ∈ T, q * w j) = h * q := by
  calc
    (∑ j ∈ T, q * w j) = q * ∑ j ∈ T, w j := by
      rw [Finset.mul_sum]
    _ = q * h := by rw [hweight]
    _ = h * q := Nat.mul_comm _ _

theorem stage_nonSurvivor_intersection_ge {r q h : ℕ} (hq : 0 < q)
    (w : Fin r → ℕ) (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (T : Finset (Fin r)) (d : ℕ)
    (hpast : ∀ g, pastT g ≠ T) (hweight : ∑ j ∈ T, w j = h)
    (t : StageTerm r q) (hn : ¬ stageSurvives t) :
    (h + 1) * q ≤
      (generatorIntersection (stageOldGenerator w pastT pastD T d) t).card := by
  rw [stage_generatorIntersection_card]
  have hJS := mappedStageSubset_subset_selected T d t.1
  have hw := weighted_position_count (q := q) w T hweight
  by_cases hleft : t.1.toLeft = (Finset.univ : Finset (Fin r))
  · have hright : t.1.toRight = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hr
      exact hn ⟨hleft, hr⟩
    have hpos : positionChoices (q := q) T ⊆ mappedStageSubset T d t.1 :=
      (positionChoices_subset_mapped_iff T d t.1).2 hleft
    have hnopat : Disjoint (mappedStageSubset T d t.1) (patternChoices d) :=
      (disjoint_mapped_pattern_iff T d t.1).2 hright
    rw [blockCommonCount_of_all_positions_no_pattern w pastT pastD T d
      (mappedStageSubset T d t.1) hJS hpos hnopat hpast, hw]
    have hqq : q ≤ q * q := by
      calc
        q = q * 1 := (Nat.mul_one q).symm
        _ ≤ q * q := Nat.mul_le_mul_left q hq
    calc
      (h + 1) * q = h * q + q := by ring
      _ ≤ h * q + q * q := Nat.add_le_add_left hqq _
  · have hex : ∃ j : Fin r, j ∉ t.1.toLeft := by
      by_contra hnone
      push Not at hnone
      exact hleft (Finset.eq_univ_iff_forall.2 hnone)
    obtain ⟨j, hj⟩ := hex
    have hmiss := chosenPos_not_mem_mapped_of_not_mem_toLeft T d t.1 j hj
    have hb := blockCommonCount_lower_of_missing_position w pastT pastD T d
      (mappedStageSubset T d t.1) hJS j hmiss
    rw [hw] at hb
    calc
      (h + 1) * q = h * q + q := by ring
      _ ≤ blockCommonCount w pastT pastD (mappedStageSubset T d t.1) := hb

theorem stage_survivor_term_eq {r q h : ℕ}
    (w : Fin r → ℕ) (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (T : Finset (Fin r)) (d : ℕ)
    (hpast : ∀ g, pastT g ≠ T) (hweight : ∑ j ∈ T, w j = h)
    (t : StageTerm r q) (hs : stageSurvives t) :
    zmodIETerm (stageOldGenerator w pastT pastD T d) ((h + 1) * q) t =
      (-1 : ZMod (2 ^ ((h + 1) * q))) ^ r *
        ((-1 : ZMod (2 ^ ((h + 1) * q))) ^ (t.1.toRight.card + 1) *
          (2 : ZMod (2 ^ ((h + 1) * q))) ^
            (remainderIntersectionCount d t.1.toRight)) *
        (2 : ZMod (2 ^ ((h + 1) * q))) ^ (h * q) := by
  have hJS := mappedStageSubset_subset_selected T d t.1
  have hpos : positionChoices (q := q) T ⊆ mappedStageSubset T d t.1 :=
    (positionChoices_subset_mapped_iff T d t.1).2 hs.1
  have hblock := blockCommonCount_of_all_positions w pastT pastD T d
    (mappedStageSubset T d t.1) hJS hpos hpast
  rw [remainderCommon_mapped_of_right_nonempty T d t.1 hs.2,
    weighted_position_count w T hweight] at hblock
  have hcard : t.1.card = r + t.1.toRight.card := by
    calc
      t.1.card = t.1.toLeft.card + t.1.toRight.card :=
        Finset.card_toLeft_add_card_toRight.symm
      _ = r + t.1.toRight.card := by rw [hs.1]; simp
  rw [zmodIETerm, stage_generatorIntersection_card, hblock, hcard]
  simp only [Nat.add_assoc, pow_add]
  ring

theorem remainder_signed_sum {q d K : ℕ} (hq : 0 < q) :
    (∑ L : RemainderTerm q,
      (-1 : ZMod (2 ^ K)) ^ (L.1.card + 1) *
        (2 : ZMod (2 ^ K)) ^ (remainderIntersectionCount d L.1)) =
      (AntichainOfGivenSize.Section6.remainderZ q d : ZMod (2 ^ K)) := by
  have hie := generatedIdealIdx_card_zmod
    (Finset.univ : Finset (Fin q)) (remainderGenerator d) K
  rw [remainderIdeal_card hq] at hie
  simpa only [zmodIETerm, remainder_generatorIntersection_card] using hie.symm

set_option maxHeartbeats 1200000 in
theorem claim65_modular {r q h : ℕ} (hq : 0 < q)
    (w : Fin r → ℕ) (pastT : Fin h → Finset (Fin r)) (pastD : Fin h → ℕ)
    (T : Finset (Fin r)) (d : ℕ)
    (hpast : ∀ g, pastT g ≠ T) (hweight : ∑ j ∈ T, w j = h) :
    ((generatedIdealIdx (Finset.univ : Finset (StageIndex r q))
      (stageOldGenerator w pastT pastD T d)).card :
        ZMod (2 ^ ((h + 1) * q))) =
      (-1 : ZMod (2 ^ ((h + 1) * q))) ^ r *
        (AntichainOfGivenSize.Section6.remainderZ q d : ZMod (2 ^ ((h + 1) * q))) *
        (2 : ZMod (2 ^ ((h + 1) * q))) ^ (h * q) := by
  classical
  rw [generatedIdealIdx_card_zmod_survivors
    (survives := stageSurvives)
    (hvanish := stage_nonSurvivor_intersection_ge hq w pastT pastD T d hpast hweight)]
  rw [sum_ite_subtype]
  calc
    (∑ y : {t : StageTerm r q // stageSurvives t},
        zmodIETerm (stageOldGenerator w pastT pastD T d) ((h + 1) * q) y.1) =
        ∑ L : RemainderTerm q,
          zmodIETerm (stageOldGenerator w pastT pastD T d) ((h + 1) * q)
            ((remainderTermEquivSurvivor r q L).1) :=
      stage_survivor_sum_equiv
        (f := fun t : StageTerm r q ↦
          zmodIETerm (stageOldGenerator w pastT pastD T d) ((h + 1) * q) t)
    _ = _ := by
      have hterm (L : RemainderTerm q) :
          zmodIETerm (stageOldGenerator w pastT pastD T d) ((h + 1) * q)
              ((remainderTermEquivSurvivor r q L).1) =
            (-1 : ZMod (2 ^ ((h + 1) * q))) ^ r *
              ((-1 : ZMod (2 ^ ((h + 1) * q))) ^ (L.1.card + 1) *
                (2 : ZMod (2 ^ ((h + 1) * q))) ^
                  (remainderIntersectionCount d L.1)) *
              (2 : ZMod (2 ^ ((h + 1) * q))) ^ (h * q) := by
        simpa [remainderTermEquivSurvivor] using
          stage_survivor_term_eq w pastT pastD T d hpast hweight
            ((remainderTermEquivSurvivor r q L).1)
            ((remainderTermEquivSurvivor r q L).2)
      simp_rw [hterm]
      calc
        (∑ L : RemainderTerm q,
            (-1 : ZMod (2 ^ ((h + 1) * q))) ^ r *
              ((-1 : ZMod (2 ^ ((h + 1) * q))) ^ (L.1.card + 1) *
                (2 : ZMod (2 ^ ((h + 1) * q))) ^
                  (remainderIntersectionCount d L.1)) *
              (2 : ZMod (2 ^ ((h + 1) * q))) ^ (h * q)) =
            (-1 : ZMod (2 ^ ((h + 1) * q))) ^ r *
              (∑ L : RemainderTerm q,
                (-1 : ZMod (2 ^ ((h + 1) * q))) ^ (L.1.card + 1) *
                  (2 : ZMod (2 ^ ((h + 1) * q))) ^
                    (remainderIntersectionCount d L.1)) *
              (2 : ZMod (2 ^ ((h + 1) * q))) ^ (h * q) := by
          rw [Finset.mul_sum, Finset.sum_mul]
        _ = _ := by rw [remainder_signed_sum hq]

end AntichainOfGivenSize.Section6.Modular
