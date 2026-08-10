import AntichainOfGivenSize.Definitions
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.EquivFin

open Finset

namespace AntichainOfGivenSize

/-! Basic API for `alpha`, including the paper's Splitting and Lifting Lemmas. -/

def finsetMapEmbedding {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) : Finset V ↪ Finset W :=
  ⟨fun s ↦ s.map f, Finset.map_injective f⟩

def mapFamily {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (G : Finset (Finset V)) : Finset (Finset W) :=
  G.map (finsetMapEmbedding f)

theorem generatedIdeal_mapFamily {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (G : Finset (Finset V)) :
    generatedIdeal (mapFamily f G) =
      (generatedIdeal G).map (finsetMapEmbedding f) := by
  ext t
  simp only [generatedIdeal, mapFamily, mem_biUnion, mem_map, mem_powerset,
    finsetMapEmbedding]
  constructor
  · rintro ⟨s', ⟨s, hs, rfl⟩, ht⟩
    rcases Finset.subset_map_iff.mp ht with ⟨u, hu, rfl⟩
    exact ⟨u, ⟨s, hs, hu⟩, rfl⟩
  · rintro ⟨u, ⟨s, hs, hu⟩, rfl⟩
    exact ⟨s.map f, ⟨s, hs, rfl⟩, Finset.map_subset_map.mpr hu⟩

def relabelFamily {V W : Type*} [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (G : Finset (Finset V)) : Finset (Finset W) :=
  mapFamily e.toEmbedding G

theorem generatedIdeal_relabel {V W : Type*} [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (G : Finset (Finset V)) :
    generatedIdeal (relabelFamily e G) =
      (generatedIdeal G).map (finsetMapEmbedding e.toEmbedding) := by
  exact generatedIdeal_mapFamily e.toEmbedding G

theorem alpha_le_of_family {V : Type*} [Fintype V] [DecidableEq V]
    (G : Finset (Finset V)) : alpha (generatedIdeal G).card ≤ G.card := by
  apply Nat.sInf_le
  refine ⟨Fintype.card V, relabelFamily (Fintype.equivFin V) G, ?_, ?_⟩
  · rw [generatedIdeal_relabel, Finset.card_map]
  · exact Finset.card_map _

def singletonGenerators (r : ℕ) : Finset (Finset (Fin r)) :=
  insert ∅ (Finset.univ.image fun i ↦ {i})

theorem singletonGenerators_card (r : ℕ) :
    (singletonGenerators r).card = r + 1 := by
  have hinj : Function.Injective (fun i : Fin r ↦ ({i} : Finset (Fin r))) := by
    intro i j hij
    simpa using hij
  have himage : (Finset.univ.image fun i : Fin r ↦ ({i} : Finset (Fin r))).card = r := by
    calc
      _ = (Finset.univ : Finset (Fin r)).card :=
        Finset.card_image_of_injective _ hinj
      _ = r := by simp
  rw [singletonGenerators]
  simp [himage]

theorem generatedIdeal_singletonGenerators (r : ℕ) :
    generatedIdeal (singletonGenerators r) = singletonGenerators r := by
  ext s
  simp only [generatedIdeal, singletonGenerators, mem_biUnion, mem_insert, mem_image,
    mem_univ, true_and, mem_powerset]
  constructor
  · rintro ⟨t, (rfl | ⟨i, rfl⟩), hst⟩
    · exact Or.inl (Finset.subset_empty.mp hst)
    · rcases Finset.subset_singleton_iff.mp hst with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨i, rfl⟩
  · intro hs
    refine ⟨s, hs, Subset.rfl⟩

theorem generatedIdeal_singletonGenerators_card (r : ℕ) :
    (generatedIdeal (singletonGenerators r)).card = r + 1 := by
  rw [generatedIdeal_singletonGenerators]
  exact singletonGenerators_card r

theorem hasGeneratorCount_nonempty (n : ℕ) :
    {k : ℕ | HasGeneratorCount n k}.Nonempty := by
  cases n with
  | zero =>
      refine ⟨0, 0, ∅, ?_, rfl⟩
      simp [generatedIdeal]
  | succ r =>
      refine ⟨r + 1, r, singletonGenerators r, ?_, singletonGenerators_card r⟩
      simpa [Nat.succ_eq_add_one] using generatedIdeal_singletonGenerators_card r

/-- The infimum in the definition of `alpha` is attained. -/
theorem alpha_hasGeneratorCount (n : ℕ) :
    HasGeneratorCount n (alpha n) := by
  exact Nat.sInf_mem (hasGeneratorCount_nonempty n)

theorem alpha_le_of_hasGeneratorCount {n k : ℕ}
    (h : HasGeneratorCount n k) : alpha n ≤ k := by
  exact Nat.sInf_le h

/-! The splitting lemma.  Its paper statement uses positive naturals. -/

theorem generatedIdeal_union {V : Type*} [DecidableEq V]
    (G H : Finset (Finset V)) :
    generatedIdeal (G ∪ H) = generatedIdeal G ∪ generatedIdeal H := by
  ext s
  simp only [generatedIdeal, mem_biUnion, mem_powerset, mem_union]
  constructor
  · rintro ⟨a, ha, hsa⟩
    rcases ha with ha | ha
    · exact Or.inl ⟨a, ha, hsa⟩
    · exact Or.inr ⟨a, ha, hsa⟩
  · rintro (⟨a, ha, hsa⟩ | ⟨a, ha, hsa⟩)
    · exact ⟨a, Or.inl ha, hsa⟩
    · exact ⟨a, Or.inr ha, hsa⟩

theorem empty_mem_generatedIdeal_of_card_pos
    {V : Type*} [DecidableEq V] {G : Finset (Finset V)}
    (h : 0 < (generatedIdeal G).card) : ∅ ∈ generatedIdeal G := by
  have hnonempty : (generatedIdeal G).Nonempty := Finset.card_pos.mp h
  rcases hnonempty with ⟨s, hs⟩
  simp only [generatedIdeal, mem_biUnion, mem_powerset] at hs ⊢
  rcases hs with ⟨g, hg, -⟩
  exact ⟨g, hg, empty_subset g⟩

theorem mapped_inl_inter_mapped_inr
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : Finset (Finset V)) (H : Finset (Finset W))
    (hG : ∅ ∈ generatedIdeal G) (hH : ∅ ∈ generatedIdeal H) :
    generatedIdeal (mapFamily (Function.Embedding.inl : V ↪ V ⊕ W) G) ∩
        generatedIdeal (mapFamily (Function.Embedding.inr : W ↪ V ⊕ W) H) = {∅} := by
  rw [generatedIdeal_mapFamily, generatedIdeal_mapFamily]
  ext s
  simp only [mem_inter, mem_map, mem_singleton]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    change b.map Function.Embedding.inr = a.map Function.Embedding.inl at hab
    have hab' : (∅ : Finset V).disjSum b = a.disjSum (∅ : Finset W) := by
      simpa using hab
    have hleft := congrArg Finset.toLeft hab'
    have haempty : a = ∅ := by
      symm
      simpa only [Finset.toLeft_disjSum] using hleft
    subst a
    simp [finsetMapEmbedding]
  · rintro rfl
    constructor
    · exact ⟨∅, hG, by simp [finsetMapEmbedding]⟩
    · exact ⟨∅, hH, by simp [finsetMapEmbedding]⟩

/-- Splitting Lemma 3.1, with the positivity convention on the paper's naturals
made explicit: `alpha (m+n) ≤ alpha m + alpha (n+1)`. -/
theorem splittingLemma (m n : ℕ) (hm : 0 < m) :
    alpha (m + n) ≤ alpha m + alpha (n + 1) := by
  rcases alpha_hasGeneratorCount m with ⟨v, G, hGsize, hGcard⟩
  rcases alpha_hasGeneratorCount (n + 1) with ⟨w, H, hHsize, hHcard⟩
  let GL : Finset (Finset (Fin v ⊕ Fin w)) :=
    mapFamily (Function.Embedding.inl : Fin v ↪ Fin v ⊕ Fin w) G
  let HR : Finset (Finset (Fin v ⊕ Fin w)) :=
    mapFamily (Function.Embedding.inr : Fin w ↪ Fin v ⊕ Fin w) H
  have hemptyG : ∅ ∈ generatedIdeal G := by
    apply empty_mem_generatedIdeal_of_card_pos
    simpa [hGsize] using hm
  have hemptyH : ∅ ∈ generatedIdeal H := by
    apply empty_mem_generatedIdeal_of_card_pos
    rw [hHsize]
    exact Nat.zero_lt_succ n
  have hGLsize : (generatedIdeal GL).card = m := by
    simp [GL, generatedIdeal_mapFamily, hGsize]
  have hHRsize : (generatedIdeal HR).card = n + 1 := by
    simp [HR, generatedIdeal_mapFamily, hHsize]
  have hinter : generatedIdeal GL ∩ generatedIdeal HR = {∅} := by
    simpa [GL, HR] using mapped_inl_inter_mapped_inr G H hemptyG hemptyH
  have hcombined : (generatedIdeal (GL ∪ HR)).card = m + n := by
    rw [generatedIdeal_union, Finset.card_union]
    rw [hGLsize, hHRsize, hinter]
    simp
  have hbound := alpha_le_of_family (GL ∪ HR)
  rw [hcombined] at hbound
  refine hbound.trans ?_
  calc
    (GL ∪ HR).card ≤ GL.card + HR.card := Finset.card_union_le _ _
    _ = G.card + H.card := by simp [GL, HR, mapFamily]
    _ = alpha m + alpha (n + 1) := by rw [hGcard, hHcard]

/-! The lifting lemma. -/

def adjoinRightEmbedding {V W : Type*} [DecidableEq V] [Fintype W] [DecidableEq W] :
    Finset V ↪ Finset (V ⊕ W) where
  toFun s := s.disjSum Finset.univ
  inj' := by
    intro s t h
    exact (Finset.disjSum_inj.mp h).1

def liftFamily {V W : Type*} [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : Finset (Finset V)) : Finset (Finset (V ⊕ W)) :=
  G.map adjoinRightEmbedding

def pairToSumEmbedding {V W : Type*} [DecidableEq V] [DecidableEq W] :
    (Finset V × Finset W) ↪ Finset (V ⊕ W) :=
  (Finset.sumEquiv : Finset (V ⊕ W) ≃o Finset V × Finset W).toEquiv.symm.toEmbedding

theorem generatedIdeal_liftFamily
    {V W : Type*} [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : Finset (Finset V)) :
    generatedIdeal (liftFamily (W := W) G) =
      ((generatedIdeal G) ×ˢ (Finset.univ : Finset W).powerset).map pairToSumEmbedding := by
  ext A
  simp only [generatedIdeal, liftFamily, mem_biUnion, mem_map, mem_powerset]
  constructor
  · rintro ⟨g', ⟨g, hg, rfl⟩, hA⟩
    rcases Finset.subset_disjSum.mp hA with ⟨hleft, hright⟩
    refine ⟨(A.toLeft, A.toRight), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · simp only [mem_biUnion, mem_powerset]
        exact ⟨g, hg, hleft⟩
      · exact Finset.mem_powerset.mpr hright
    · simpa [pairToSumEmbedding] using A.toLeft_disjSum_toRight
  · rintro ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨hpLeft, hpRight⟩
    simp only [mem_biUnion, mem_powerset] at hpLeft
    rcases hpLeft with ⟨g, hg, hpg⟩
    refine ⟨g.disjSum (Finset.univ : Finset W), ⟨g, hg, rfl⟩, ?_⟩
    change p.1.disjSum p.2 ⊆ g.disjSum (Finset.univ : Finset W)
    exact Finset.disjSum_mono hpg (Finset.mem_powerset.mp hpRight)

theorem liftFamily_card
    {V W : Type*} [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : Finset (Finset V)) : (liftFamily (W := W) G).card = G.card := by
  exact Finset.card_map _

theorem generatedIdeal_liftFamily_card
    {V : Type*} [DecidableEq V] (t : ℕ) (G : Finset (Finset V)) :
    (generatedIdeal (liftFamily (W := Fin t) G)).card =
      2 ^ t * (generatedIdeal G).card := by
  rw [generatedIdeal_liftFamily, Finset.card_map, Finset.card_product,
    Finset.card_powerset]
  simp [Nat.mul_comm]

/-- Lifting Lemma 3.2: adjoining `t` common fresh elements multiplies the
ideal cardinality by `2^t` without increasing the number of generators. -/
theorem liftingLemma (t n : ℕ) : alpha (2 ^ t * n) ≤ alpha n := by
  rcases alpha_hasGeneratorCount n with ⟨v, G, hGsize, hGcard⟩
  let L : Finset (Finset (Fin v ⊕ Fin t)) := liftFamily (W := Fin t) G
  have hLsize : (generatedIdeal L).card = 2 ^ t * n := by
    dsimp [L]
    rw [generatedIdeal_liftFamily_card, hGsize]
  have hbound := alpha_le_of_family L
  rw [hLsize] at hbound
  exact hbound.trans_eq ((liftFamily_card G).trans hGcard)

end AntichainOfGivenSize
