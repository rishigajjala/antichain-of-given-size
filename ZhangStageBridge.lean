import ZhangSection6Core

open Finset

namespace ZhangSection6

variable {I V W : Type*}
  [DecidableEq I] [DecidableEq V] [DecidableEq W]

omit [DecidableEq I] in
/-- Indexed unions of principal ideals have the same cardinality whenever
all nonempty generator intersections have the same cardinality. -/
theorem generatedIdealIdx_card_eq_of_intersection_cards
    (s : Finset I) (G : I → Finset V) (H : I → Finset W)
    (hcard : ∀ t : s.powerset.filter (fun u : Finset I ↦ u.Nonempty),
      (generatorIntersection G t).card = (generatorIntersection H t).card) :
    (generatedIdealIdx s G).card = (generatedIdealIdx s H).card := by
  have hG := generatedIdealIdx_card_inclusionExclusion s G
  have hH := generatedIdealIdx_card_inclusionExclusion s H
  have hG' : ((generatedIdealIdx s G).card : ℤ) =
      (∑ t : s.powerset.filter (fun u : Finset I ↦ u.Nonempty),
        (-1 : ℤ) ^ (t.1.card + 1) *
          (2 : ℤ) ^ (generatorIntersection G t).card) := by
    simpa [generatorIntersection] using hG
  have hH' : ((generatedIdealIdx s H).card : ℤ) =
      (∑ t : s.powerset.filter (fun u : Finset I ↦ u.Nonempty),
        (-1 : ℤ) ^ (t.1.card + 1) *
          (2 : ℤ) ^ (generatorIntersection H t).card) := by
    simpa [generatorIntersection] using hH
  have hsums :
      (∑ t : s.powerset.filter (fun u : Finset I ↦ u.Nonempty),
        (-1 : ℤ) ^ (t.1.card + 1) *
          (2 : ℤ) ^ (generatorIntersection G t).card) =
      ∑ t : s.powerset.filter (fun u : Finset I ↦ u.Nonempty),
        (-1 : ℤ) ^ (t.1.card + 1) *
          (2 : ℤ) ^ (generatorIntersection H t).card := by
    apply Finset.sum_congr rfl
    intro t _ht
    rw [hcard t]
  have hint : ((generatedIdealIdx s G).card : ℤ) =
      ((generatedIdealIdx s H).card : ℤ) := hG'.trans (hsums.trans hH'.symm)
  exact_mod_cast hint

theorem generatorIntersection_adjoinFreshIdx_eq
    {s chosen : Finset I} (G : I → Finset V)
    (t : s.powerset.filter (fun u : Finset I ↦ u.Nonempty)) :
    generatorIntersection (adjoinFreshIdx chosen G) t =
      if t.1 ⊆ chosen then
        insert none (liftSet (generatorIntersection G t))
      else liftSet (generatorIntersection G t) := by
  ext x
  cases x with
  | none =>
      simp only [generatorIntersection, Finset.mem_inf',
        none_mem_adjoinFreshIdx_iff]
      by_cases hsub : t.1 ⊆ chosen
      · simp only [hsub, if_true, Finset.mem_insert, true_or]
        constructor
        · intro _hall
          trivial
        · intro _true i hi
          exact hsub hi
      · simp only [hsub, if_false, none_not_mem_liftSet]
        obtain ⟨i, hit, hichosen⟩ := Finset.not_subset.mp hsub
        constructor
        · intro hall
          exact hichosen (hall i hit)
        · intro hfalse
          contradiction
  | some x =>
      simp only [generatorIntersection, Finset.mem_inf',
        some_mem_adjoinFreshIdx_iff]
      by_cases hsub : t.1 ⊆ chosen <;> simp [hsub]

theorem generatorIntersection_adjoinFreshIdx_card
    {s chosen : Finset I} (G : I → Finset V)
    (t : s.powerset.filter (fun u : Finset I ↦ u.Nonempty)) :
    (generatorIntersection (adjoinFreshIdx chosen G) t).card =
      (generatorIntersection G t).card + if t.1 ⊆ chosen then 1 else 0 := by
  rw [generatorIntersection_adjoinFreshIdx_eq]
  by_cases hsub : t.1 ⊆ chosen
  · simp [hsub, liftSet]
  · simp [hsub, liftSet]

/-- A family whose intersection counts are obtained by adding one point
exactly to subfamilies contained in `chosen` has the expected stage-cardinal
increment. This lets a concrete typed-atom construction use the abstract
`Option` stage lemma without constructing a cumbersome vertex equivalence. -/
theorem generatedIdealIdx_card_stage_of_intersection_cards
    {all chosen : Finset I} (hchosen : chosen ⊆ all)
    (G : I → Finset V) (H : I → Finset W)
    (hcard : ∀ t : all.powerset.filter (fun u : Finset I ↦ u.Nonempty),
      (generatorIntersection H t).card =
        (generatorIntersection G t).card +
          if t.1 ⊆ chosen then 1 else 0) :
    (generatedIdealIdx all H).card =
      (generatedIdealIdx all G).card + (generatedIdealIdx chosen G).card := by
  calc
    (generatedIdealIdx all H).card =
        (generatedIdealIdx all (adjoinFreshIdx chosen G)).card := by
      apply generatedIdealIdx_card_eq_of_intersection_cards
      intro t
      rw [hcard t, generatorIntersection_adjoinFreshIdx_card]
    _ = (generatedIdealIdx all G).card + (generatedIdealIdx chosen G).card :=
      indexedStageIdeal_card hchosen

end ZhangSection6
