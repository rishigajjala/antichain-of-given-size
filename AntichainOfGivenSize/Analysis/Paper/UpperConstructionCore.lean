import AntichainOfGivenSize.Analysis.Section6.ModularIncrement
import AntichainOfGivenSize.Analysis.Section6.StageBridge

/-!
# The full inclusion–exclusion calculation for one block

This calculation applies to the actual selected position and pattern
families. The geometric hypotheses concern every nonempty subquery, not
only the primary intersection.
-/

open Finset
open scoped BigOperators

namespace AntichainOfGivenSize.Paper.UpperConstruction

open AntichainOfGivenSize.Section6

abbrev StageTerm (r : ℕ) (K : Type*) [Fintype K] :=
  (Finset.univ : Finset (Fin r ⊕ K)).powerset.filter (·.Nonempty)

abbrev PatternTerm (K : Type*) [Fintype K] :=
  (Finset.univ : Finset K).powerset.filter (·.Nonempty)

def survives {r : ℕ} {K : Type*} [Fintype K] (t : StageTerm r K) : Prop :=
  t.val.toLeft = Finset.univ ∧ t.val.toRight.Nonempty

noncomputable def patternTermEquivSurvivor (r : ℕ) (K : Type*) [Fintype K] :
    PatternTerm K ≃ {t : StageTerm r K // survives t} := by
  classical
  let forward : PatternTerm K → {t : StageTerm r K // survives t} := fun L => by
    let A : Finset (Fin r ⊕ K) := (Finset.univ : Finset (Fin r)).disjSum L.val
    have hnon : A.Nonempty := by
      obtain ⟨a,ha⟩ := (Finset.mem_filter.mp L.property).2
      exact ⟨Sum.inr a, by simp [A,ha]⟩
    let t : StageTerm r K := ⟨A, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),hnon⟩⟩
    exact ⟨t, by simp [survives,t,A,(Finset.mem_filter.mp L.property).2]⟩
  let backward : {t : StageTerm r K // survives t} → PatternTerm K := fun t =>
    ⟨t.val.val.toRight, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),t.property.2⟩⟩
  exact {
    toFun := forward
    invFun := backward
    left_inv := by intro L; apply Subtype.ext; simp [forward,backward]
    right_inv := by
      intro t
      apply Subtype.ext
      apply Subtype.ext
      change (Finset.univ : Finset (Fin r)).disjSum t.val.val.toRight = t.val.val
      rw [← t.property.1]
      exact Finset.toLeft_disjSum_toRight }

noncomputable instance survivesDecidablePred (r : ℕ) (K : Type*) [Fintype K] :
    DecidablePred (@survives r K _) := Classical.decPred _

/-- Reindex the surviving terms by their nonempty pattern subquery. -/
theorem survivor_sum {r : ℕ} {K M : Type*} [Fintype K] [AddCommMonoid M]
    (f : StageTerm r K → M) :
    (∑ t : {t : StageTerm r K // survives t}, f t.val) =
      ∑ L : PatternTerm K, f ((patternTermEquivSurvivor r K L).val) := by
  classical
  exact (Fintype.sum_equiv (patternTermEquivSurvivor r K)
    (fun L => f ((patternTermEquivSurvivor r K L).val))
    (fun t => f t.val) (fun _ => rfl)).symm

/-- The modular calculation in Claim 6.4. Missing-position and
position-only queries vanish; every mixed full-position query factors. -/
theorem selected_card_zmod {r ell i : ℕ} {K V W : Type*}
    [Fintype K] [DecidableEq K] [DecidableEq V] [DecidableEq W]
    (G : Fin r ⊕ K → Finset V) (R : K → Finset W)
    (hvanish : ∀ t : StageTerm r K, ¬ survives t →
      (i + 1) * ell ≤ (generatorIntersection G t).card)
    (hmixed : ∀ t : StageTerm r K, ∀ hs : survives t,
      (generatorIntersection G t).card = i * ell +
        (generatorIntersection R ⟨t.val.toRight,
          Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
            hs.2⟩⟩).card) :
    ((generatedIdealIdx Finset.univ G).card : ZMod (2 ^ ((i + 1) * ell))) =
      (-1 : ZMod (2 ^ ((i + 1) * ell))) ^ r *
      ((generatedIdealIdx Finset.univ R).card : ZMod (2 ^ ((i + 1) * ell))) *
      (2 : ZMod (2 ^ ((i + 1) * ell))) ^ (i * ell) := by
  classical
  rw [generatedIdealIdx_card_zmod_survivors (survives := survives) (hvanish := hvanish)]
  rw [AntichainOfGivenSize.Section6.Modular.sum_ite_subtype, survivor_sum]
  have hterm (L : PatternTerm K) :
      zmodIETerm G ((i + 1) * ell) ((patternTermEquivSurvivor r K L).val) =
        (-1 : ZMod (2 ^ ((i + 1) * ell))) ^ r *
          zmodIETerm R ((i + 1) * ell) L *
          (2 : ZMod (2 ^ ((i + 1) * ell))) ^ (i * ell) := by
    let t := (patternTermEquivSurvivor r K L).val
    have ht := (patternTermEquivSurvivor r K L).property
    have hc : t.val.card = r + L.val.card := by
      simp [t,patternTermEquivSurvivor]
    have hm := hmixed t ht
    have he : t.val.toRight = L.val := by simp [t,patternTermEquivSurvivor]
    have hr : (⟨t.val.toRight, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ht.2⟩⟩ : PatternTerm K) = L :=
      Subtype.ext he
    rw [hr] at hm
    change zmodIETerm G ((i + 1) * ell) t = _
    rw [zmodIETerm,hm,hc,zmodIETerm]
    simp only [Nat.add_assoc,pow_add]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← generatedIdealIdx_card_zmod]

end AntichainOfGivenSize.Paper.UpperConstruction
