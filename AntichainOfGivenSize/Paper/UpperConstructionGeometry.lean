import AntichainOfGivenSize.Model.ProblemSetting
import AntichainOfGivenSize.Paper.BitMatching
import AntichainOfGivenSize.Paper.UpperConstructionCore

open Finset
open scoped BigOperators

namespace AntichainOfGivenSize.Paper.UpperConstruction

open AntichainOfGivenSize.Section6

theorem old_generator_subset {r : ℕ} (p : BitMatching.Index r) :
    BitMatching.generator ∅ p ⊆ oldUniverse r := by
  classical
  intro v hv
  rcases v with e | (j | g)
  · simp [oldUniverse]
  · simp [oldUniverse]
  · simp [BitMatching.Present] at hv

theorem core_subset_oldUniverse {r : ℕ} (i : BitMatching.Stage r) :
    BitMatching.core i ⊆ oldUniverse r := by
  classical
  intro v hv
  rcases v with e | (j | g)
  · simp [oldUniverse]
  · exact False.elim (BitMatching.inr_not_mem_core i _ hv)
  · exact False.elim (BitMatching.inr_not_mem_core i _ hv)

theorem core_subset_chosen {r : ℕ} (hr : 0 < r) (i : BitMatching.Stage r) (j : Fin r) :
    BitMatching.core i ⊆ BitMatching.generator ∅ (BitMatching.chosenIndex i j) := by
  intro v hv
  rw [← BitMatching.primary_intersection hr ∅ i (by simp)] at hv
  exact (BitMatching.mem_generator _ _ _).mpr
    ((BitMatching.mem_intersection _ _ _).mp hv _ (BitMatching.chosen_mem_address i j))

@[simp] theorem mem_generator {r ell : ℕ} {K V : Type*} [Fintype V] [DecidableEq V]
    (active : Finset (BitMatching.Stage r)) (hist : BitMatching.Stage r → Finset K) (R : K → Finset V)
    (p : Index r K) (v : Vertex r ell V) :
    v ∈ generator active hist R p ↔ Present active hist R p v := by
  classical
  simp [generator]

def stageEmbedding {r : ℕ} {K : Type*} (i : BitMatching.Stage r) (D : Finset K) :
    Fin r ⊕ D ↪ Index r K where
  toFun
    | Sum.inl j => Sum.inl (BitMatching.chosenIndex i j)
    | Sum.inr k => Sum.inr k.val
  inj' := by
    intro p q h
    cases p with
    | inl j =>
      cases q with
      | inl k => exact congrArg Sum.inl ((BitMatching.chosenEmbedding i).injective (Sum.inl.inj h))
      | inr k => exact False.elim (Sum.inl_ne_inr h)
    | inr j =>
      cases q with
      | inl k => exact False.elim (Sum.inr_ne_inl h)
      | inr k => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj h))

noncomputable def stageGenerator {r ell : ℕ} {K V : Type*} [Fintype V] [DecidableEq V]
    (active : Finset (BitMatching.Stage r)) (hist : BitMatching.Stage r → Finset K) (R : K → Finset V)
    (i : BitMatching.Stage r) (D : Finset K) (p : Fin r ⊕ D) : Finset (Vertex r ell V) :=
  generator active hist R (stageEmbedding i D p)

/-- Full position queries remove every old flag and every earlier fresh atom. -/
theorem full_position_intersection {r ell : ℕ} {K V : Type*}
    [DecidableEq K] [Fintype V] [DecidableEq V]
    (hr : 0 < r) (active : Finset (BitMatching.Stage r)) (hist : BitMatching.Stage r → Finset K)
    (R : K → Finset V) (i : BitMatching.Stage r) (hi : i ∉ active) (D : Finset K)
    (t : StageTerm r D) (hleft : t.val.toLeft = Finset.univ) :
    generatorIntersection (stageGenerator (ell := ell) active hist R i D) t =
      ((BitMatching.core i).product Finset.univ).disjSum
        ((Finset.univ.filter fun v => ∀ k ∈ t.val.toRight, v ∈ R k.val).disjSum ∅) := by
  classical
  have hchosen (j : Fin r) : Sum.inl j ∈ t.val := by
    have : j ∈ t.val.toLeft := by rw [hleft]; simp
    simpa using this
  ext v
  simp only [generatorIntersection, Finset.mem_inf']
  rcases v with ⟨u,x⟩ | (v | g)
  · simp only [Finset.inl_mem_disjSum, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ, and_true]
    constructor
    · intro h
      rw [← BitMatching.primary_intersection hr ∅ i (by simp),BitMatching.mem_intersection]
      intro p hp
      obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hp
      have hu := h (Sum.inl j) (hchosen j)
      exact (BitMatching.mem_generator _ _ _).mp ((mem_generator _ _ _ _ _).mp hu)
    · intro hu p hp
      apply (mem_generator _ _ _ _ _).mpr
      cases p with
      | inl j => exact core_subset_chosen hr i j hu
      | inr k => exact core_subset_oldUniverse i hu
  · simp only [Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h k hk
      have hmem : Sum.inr k ∈ t.val := by simpa using hk
      exact (mem_generator _ _ _ _ _).mp (h _ hmem)
    · intro h p hp
      apply (mem_generator _ _ _ _ _).mpr
      cases p with
      | inl j => trivial
      | inr k => exact h k (by simpa using hp)
  · simp only [Finset.inr_mem_disjSum, Finset.notMem_empty, iff_false]
    intro h
    have hg : g ∈ active := by
      have hm := (mem_generator _ _ _ _ _).mp (h _ (hchosen ⟨0,hr⟩))
      exact hm.1
    have heq : i = g := by
      apply BitMatching.stage_eq_of_bits
      intro j
      have hm := (mem_generator _ _ _ _ _).mp (h _ (hchosen j))
      simpa [Present,stageEmbedding,selected,BitMatching.chosenIndex] using hm.2
    exact hi (heq ▸ hg)

/-- Claim 6.3 in its literal position-only form: immediately before a stage,
the intersection is precisely the addressed original blocks together with
the whole pattern universe. In particular, it contains no fresh atom. -/
theorem position_intersection {r ell : ℕ} {K V : Type*}
    [DecidableEq K] [Fintype V] [DecidableEq V]
    (hr : 0 < r) (active : Finset (BitMatching.Stage r))
    (hist : BitMatching.Stage r → Finset K) (R : K → Finset V)
    (i : BitMatching.Stage r) (hi : i ∉ active) :
    (Finset.univ : Finset (Fin r)).inf' ⟨⟨0, hr⟩, Finset.mem_univ _⟩
        (fun j ↦ generator (ell := ell) active hist R
          (Sum.inl (BitMatching.chosenIndex i j))) =
      ((BitMatching.core i).product Finset.univ).disjSum
        ((Finset.univ : Finset V).disjSum ∅) := by
  classical
  let D : Finset K := ∅
  let t : StageTerm r D := ⟨Finset.univ, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _),
      ⟨Sum.inl ⟨0, hr⟩, Finset.mem_univ _⟩⟩⟩
  have h := full_position_intersection (ell := ell) hr active hist R i hi D t
    (by simp [t])
  have hsame : generatorIntersection (stageGenerator (ell := ell) active hist R i D) t =
      (Finset.univ : Finset (Fin r)).inf' ⟨⟨0, hr⟩, Finset.mem_univ _⟩
        (fun j ↦ generator (ell := ell) active hist R
          (Sum.inl (BitMatching.chosenIndex i j))) := by
    ext v
    simp only [generatorIntersection, Finset.mem_inf', t, Finset.mem_univ,
      forall_const]
    constructor
    · intro hv j
      exact hv (Sum.inl j)
    · intro hv p
      cases p with
      | inl j => exact hv j
      | inr k => exact (Finset.notMem_empty k.val k.property).elim
  rw [hsame] at h
  simpa [t, D] using h

/-- Every omitted selected position leaves its whole flag block. -/
theorem missing_position_intersection_ge {r ell : ℕ} {K V : Type*}
    [DecidableEq K] [Fintype V] [DecidableEq V]
    (hr : 0 < r) (active : Finset (BitMatching.Stage r)) (hist : BitMatching.Stage r → Finset K)
    (R : K → Finset V) (i : BitMatching.Stage r) (D : Finset K)
    (t : StageTerm r D) (j : Fin r) (hj : j ∉ t.val.toLeft) :
    (i.val + 1) * ell ≤
      (generatorIntersection (stageGenerator (ell := ell) active hist R i D) t).card := by
  classical
  let flag : BitMatching.Vertex r := Sum.inr (Sum.inl j)
  let W := ((insert flag (BitMatching.core i)).product (Finset.univ : Finset (Fin ell))).map
    (Function.Embedding.inl : (BitMatching.Vertex r × Fin ell) ↪ Vertex r ell V)
  have hW : W ⊆ generatorIntersection (stageGenerator active hist R i D) t := by
    intro v hv
    obtain ⟨⟨u,x⟩,hu,rfl⟩ := Finset.mem_map.mp hv
    have hu' := (Finset.mem_product.mp hu).1
    rw [generatorIntersection,Finset.mem_inf']
    intro p hp
    apply (mem_generator _ _ _ _ _).mpr
    cases p with
    | inl k =>
      rcases Finset.mem_insert.mp hu' with rfl | hc
      · have hkj : j ≠ k := by intro heq; subst k; exact hj (by simpa using hp)
        simpa [Present,stageEmbedding,flag,BitMatching.Present,BitMatching.chosenIndex] using hkj
      · exact core_subset_chosen hr i k hc
    | inr k =>
      rcases Finset.mem_insert.mp hu' with rfl | hc
      · simp [Present,stageEmbedding,flag,oldUniverse]
      · exact core_subset_oldUniverse i hc
  have hcard : W.card = (i.val + 1) * ell := by
    simp [W,flag,BitMatching.card_core,BitMatching.inr_not_mem_core]
  rw [← hcard]
  exact Finset.card_le_card hW

/-- The concrete geometric hypotheses for the full inclusion–exclusion sum. -/
theorem stage_card_zmod {r ell : ℕ} {K V : Type*}
    [DecidableEq K] [Fintype V] [DecidableEq V]
    (hr : 0 < r) (hV : ell ≤ Fintype.card V)
    (active : Finset (BitMatching.Stage r)) (hist : BitMatching.Stage r → Finset K)
    (R : K → Finset V) (i : BitMatching.Stage r) (hi : i ∉ active) (D : Finset K) :
    ((generatedIdealIdx Finset.univ
      (stageGenerator (ell := ell) active hist R i D)).card :
        ZMod (2 ^ ((i.val + 1) * ell))) =
      (-1 : ZMod (2 ^ ((i.val + 1) * ell))) ^ r *
      ((generatedIdealIdx Finset.univ (fun k : D => R k.val)).card :
        ZMod (2 ^ ((i.val + 1) * ell))) *
      (2 : ZMod (2 ^ ((i.val + 1) * ell))) ^ (i.val * ell) := by
  classical
  apply selected_card_zmod
  · intro t hn
    by_cases hleft : t.val.toLeft = Finset.univ
    · have hright : t.val.toRight = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro h
        exact hn ⟨hleft,h⟩
      rw [full_position_intersection hr active hist R i hi D t hleft]
      simp only [hright,Finset.notMem_empty,IsEmpty.forall_iff,implies_true,
        Finset.filter_true,Finset.card_disjSum,Finset.card_empty,Nat.add_zero]
      simp only [Finset.product_eq_sprod, Finset.card_product,Finset.card_univ,Fintype.card_fin,BitMatching.card_core]
      nlinarith
    · obtain ⟨j,hj⟩ : ∃ j : Fin r, j ∉ t.val.toLeft := by
        by_contra h
        push Not at h
        exact hleft (Finset.eq_univ_iff_forall.mpr h)
      exact missing_position_intersection_ge hr active hist R i D t j hj
  · intro t hs
    rw [full_position_intersection hr active hist R i hi D t hs.1]
    simp only [Finset.card_disjSum,Finset.product_eq_sprod, Finset.card_product,Finset.card_univ,
      Fintype.card_fin,Finset.card_empty,BitMatching.card_core,Nat.add_zero]
    apply congrArg (fun n => i.val * ell + n)
    apply congrArg Finset.card
    ext v
    simp [generatorIntersection,Finset.mem_inf']

end AntichainOfGivenSize.Paper.UpperConstruction
