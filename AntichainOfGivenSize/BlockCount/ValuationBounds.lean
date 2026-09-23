import AntichainOfGivenSize.BlockCount.ScaledIdeals
import AntichainOfGivenSize.Section6.Core

/-!
# Rational bounds for scaled finite ideals

These estimates retain arbitrary integral powers of two as scaling factors.
The final lemma places a cluster value on an integer dyadic grid using
inclusion-exclusion and lower bounds for every nonempty intersection.
-/

open scoped BigOperators
open Finset

namespace AntichainOfGivenSize.BlockCount

variable {V : Type*} [DecidableEq V]

/-- A scaled ideal cardinality; the family is allowed to be empty. -/
def scaledIdealValue (G : Finset (Finset V)) (d : ℤ) : ℚ :=
  (2 : ℚ) ^ d * (generatedIdeal G).card

@[simp] theorem scaledIdealValue_empty (d : ℤ) :
    scaledIdealValue (∅ : Finset (Finset V)) d = 0 := by
  simp [scaledIdealValue, generatedIdeal]

theorem scaledIdealValue_nonneg (G : Finset (Finset V)) (d : ℤ) :
    0 ≤ scaledIdealValue G d := by
  unfold scaledIdealValue
  positivity

theorem scaledIdealValue_pos {G : Finset (Finset V)} (hG : G.Nonempty) (d : ℤ) :
    0 < scaledIdealValue G d := by
  have hi : (generatedIdeal G).Nonempty := by
    obtain ⟨A, hA⟩ := hG
    refine ⟨∅, ?_⟩
    simp only [generatedIdeal, mem_biUnion, mem_powerset]
    exact ⟨A, hA, empty_subset A⟩
  unfold scaledIdealValue
  apply mul_pos (by positivity)
  exact_mod_cast Finset.card_pos.mpr hi

theorem generatedIdeal_mono {G H : Finset (Finset V)} (h : G ⊆ H) :
    generatedIdeal G ⊆ generatedIdeal H :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

theorem scaledIdealValue_mono {G H : Finset (Finset V)} (h : G ⊆ H) (d : ℤ) :
    scaledIdealValue G d ≤ scaledIdealValue H d := by
  unfold scaledIdealValue
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast Finset.card_le_card (generatedIdeal_mono h)

@[simp] theorem scaledIdealValue_singleton (A : Finset V) (d : ℤ) :
    scaledIdealValue {A} d = (2 : ℚ) ^ ((A.card : ℤ) + d) := by
  simp [scaledIdealValue, generatedIdeal, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0),
    mul_comm]

theorem cube_value_le_scaledIdealValue {G : Finset (Finset V)} {A : Finset V}
    (hA : A ∈ G) (d : ℤ) :
    (2 : ℚ) ^ ((A.card : ℤ) + d) ≤ scaledIdealValue G d := by
  simpa using scaledIdealValue_mono (Finset.singleton_subset_iff.mpr hA) d

theorem scaledIdealValue_union_le (G H : Finset (Finset V)) (d : ℤ) :
    scaledIdealValue (G ∪ H) d ≤ scaledIdealValue G d + scaledIdealValue H d := by
  unfold scaledIdealValue
  rw [generatedIdeal_union, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast Finset.card_union_le (generatedIdeal G) (generatedIdeal H)

theorem generatedIdeal_biUnion (P : Finset (Finset (Finset V))) :
    generatedIdeal (P.biUnion id) = P.biUnion generatedIdeal := by
  ext A
  simp only [generatedIdeal, mem_biUnion, mem_powerset, id_eq]
  aesop

theorem scaledIdealValue_biUnion_le (P : Finset (Finset (Finset V))) (d : ℤ) :
    scaledIdealValue (P.biUnion id) d ≤ ∑ C ∈ P, scaledIdealValue C d := by
  unfold scaledIdealValue
  rw [generatedIdeal_biUnion, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast (Finset.card_biUnion_le (s := P) (t := generatedIdeal))

/-- The intersection of two ideal unions is covered by all pairs of generator intersections. -/
theorem generatedIdeal_inter_eq_biUnion (G H : Finset (Finset V)) :
    generatedIdeal G ∩ generatedIdeal H =
      G.biUnion (fun A => H.biUnion (fun B => (A ∩ B).powerset)) := by
  ext C
  simp only [generatedIdeal, mem_inter, mem_biUnion, mem_powerset,
    Finset.subset_inter_iff]
  aesop

/-- A bound before scaling, useful for changing coefficient rings. -/
theorem generatedIdeal_inter_card_le (G H : Finset (Finset V)) :
    (generatedIdeal G ∩ generatedIdeal H).card ≤
      ∑ A ∈ G, ∑ B ∈ H, 2 ^ (A ∩ B).card := by
  rw [generatedIdeal_inter_eq_biUnion]
  calc
    _ ≤ ∑ A ∈ G, (H.biUnion (fun B => (A ∩ B).powerset)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ A ∈ G, ∑ B ∈ H, (A ∩ B).powerset.card := by
      apply Finset.sum_le_sum
      intro A hA
      exact Finset.card_biUnion_le
    _ = _ := by simp only [Finset.card_powerset]

/-- Each cross-cluster overlap is bounded by the sum of its scaled cube-pair values. -/
theorem scaledIdeal_inter_le_sum_cube_pairs (G H : Finset (Finset V)) (d : ℤ) :
    (2 : ℚ) ^ d * (generatedIdeal G ∩ generatedIdeal H).card ≤
      ∑ A ∈ G, ∑ B ∈ H, (2 : ℚ) ^ (((A ∩ B).card : ℤ) + d) := by
  have hq : ((generatedIdeal G ∩ generatedIdeal H).card : ℚ) ≤
      ∑ A ∈ G, ∑ B ∈ H, (2 : ℚ) ^ (A ∩ B).card := by
    exact_mod_cast generatedIdeal_inter_card_le G H
  calc
    _ ≤ (2 : ℚ) ^ d * (∑ A ∈ G, ∑ B ∈ H, (2 : ℚ) ^ (A ∩ B).card) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro B hB
      rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
      ring

/-- A natural power multiplied by an integral dyadic scale is integral after a sufficient shift. -/
theorem scaled_power_integer (a R : ℕ) (d : ℤ)
    (h : -(R : ℤ) ≤ (a : ℤ) + d) :
    ∃ z : ℤ, ((2 : ℚ) ^ d * (2 : ℚ) ^ a) * (2 : ℚ) ^ R = z := by
  have he : 0 ≤ d + (a : ℤ) + (R : ℤ) := by omega
  refine ⟨(2 : ℤ) ^ (d + (a : ℤ) + (R : ℤ)).toNat, ?_⟩
  calc
    _ = (2 : ℚ) ^ (d + (a : ℤ) + (R : ℤ)) := by
      rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0),
        zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      simp only [zpow_natCast]
    _ = _ := by
      rw [← Int.toNat_of_nonneg he, zpow_natCast]
      norm_cast

/-- The overcount in a finite union is bounded by the sum of ordered pair overlaps. -/
theorem sum_card_le_card_biUnion_add_pairs {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Finset V) :
    ∑ i ∈ s, (f i).card ≤ (s.biUnion f).card +
      ∑ i ∈ s, ∑ j ∈ s.erase i, (f i ∩ f j).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hcross : (f a ∩ s.biUnion f).card ≤ ∑ b ∈ s, (f a ∩ f b).card := by
      have heq : f a ∩ s.biUnion f = s.biUnion (fun b => f a ∩ f b) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_biUnion]
        aesop
      rw [heq]
      exact Finset.card_biUnion_le
    have hpairs : (∑ i ∈ s, ∑ j ∈ s.erase i, (f i ∩ f j).card) ≤
        ∑ i ∈ s, ∑ j ∈ (insert a s).erase i, (f i ∩ f j).card := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.erase_subset_erase i (Finset.subset_insert a s)
      · intros; exact Nat.zero_le _
    have hunion := Finset.card_union_add_card_inter (f a) (s.biUnion f)
    simp only [Finset.sum_insert ha, Finset.biUnion_insert, Finset.erase_insert ha]
    omega

/-- Scaled ordered-pair Bonferroni bound for a family of ideal clusters. -/
theorem sum_scaledIdealValue_le_biUnion_add_pairs
    (P : Finset (Finset (Finset V))) (d : ℤ) :
    (∑ C ∈ P, scaledIdealValue C d) ≤ scaledIdealValue (P.biUnion id) d +
      ∑ C ∈ P, ∑ D ∈ P.erase C,
        (2 : ℚ) ^ d * (generatedIdeal C ∩ generatedIdeal D).card := by
  have hq : (∑ C ∈ P, ((generatedIdeal C).card : ℚ)) ≤
      ((P.biUnion generatedIdeal).card : ℚ) +
        ∑ C ∈ P, ∑ D ∈ P.erase C,
          ((generatedIdeal C ∩ generatedIdeal D).card : ℚ) := by
    exact_mod_cast sum_card_le_card_biUnion_add_pairs P generatedIdeal
  have hm := mul_le_mul_of_nonneg_left hq (show 0 ≤ (2 : ℚ) ^ d by positivity)
  simpa only [scaledIdealValue, generatedIdeal_biUnion, mul_add, Finset.mul_sum] using hm

set_option maxHeartbeats 1000000 in
/-- Bounding every cross-cluster cube bounds the total cluster overcount. -/
theorem sum_scaledIdealValue_le_biUnion_add_error
    (P : Finset (Finset (Finset V))) (d : ℤ) (ε : ℚ) (hε : 0 ≤ ε)
    (hcross : ∀ C ∈ P, ∀ D ∈ P, C ≠ D → ∀ A ∈ C, ∀ B ∈ D,
      (2 : ℚ) ^ (((A ∩ B).card : ℤ) + d) ≤ ε) :
    (∑ C ∈ P, scaledIdealValue C d) ≤ scaledIdealValue (P.biUnion id) d +
      ((∑ C ∈ P, C.card : ℕ) : ℚ) ^ 2 * ε := by
  classical
  have hpair : ∀ C ∈ P, ∀ D ∈ P.erase C,
      (2 : ℚ) ^ d * (generatedIdeal C ∩ generatedIdeal D).card ≤
        (C.card : ℚ) * (D.card : ℚ) * ε := by
    intro C hC D hD
    apply (scaledIdeal_inter_le_sum_cube_pairs C D d).trans
    calc
      _ ≤ ∑ A ∈ C, ∑ B ∈ D, ε := by
        apply Finset.sum_le_sum
        intro A hA
        apply Finset.sum_le_sum
        intro B hB
        exact hcross C hC D (Finset.mem_of_mem_erase hD)
          (Finset.ne_of_mem_erase hD).symm A hA B hB
      _ = _ := by simp; ring
  have he : (∑ C ∈ P, ∑ D ∈ P.erase C,
      (2 : ℚ) ^ d * (generatedIdeal C ∩ generatedIdeal D).card) ≤
      ∑ C ∈ P, ∑ D ∈ P, (C.card : ℚ) * (D.card : ℚ) * ε := by
    apply Finset.sum_le_sum
    intro C hC
    apply (Finset.sum_le_sum (fun D hD => hpair C hC D hD)).trans
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset C P)
    intros; positivity
  have heq : (∑ C ∈ P, ∑ D ∈ P, (C.card : ℚ) * (D.card : ℚ) * ε) =
      ((∑ C ∈ P, C.card : ℕ) : ℚ) ^ 2 * ε := by
    simp only [Nat.cast_sum, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C hC
    apply Finset.sum_congr rfl
    intro D hD
    ring
  rw [heq] at he
  exact (sum_scaledIdealValue_le_biUnion_add_pairs P d).trans (add_le_add (le_refl _) he)

/-- A single ideal is bounded by the sum of its generator cube values. -/
theorem scaledIdealValue_le_sum_cube (G : Finset (Finset V)) (d : ℤ) :
    scaledIdealValue G d ≤ ∑ A ∈ G, (2 : ℚ) ^ ((A.card : ℤ) + d) := by
  have hn : (generatedIdeal G).card ≤ ∑ A ∈ G, 2 ^ A.card := by
    simpa only [generatedIdeal, Finset.card_powerset] using
      (Finset.card_biUnion_le (s := G) (t := fun A => A.powerset))
  have hq : ((generatedIdeal G).card : ℚ) ≤ ∑ A ∈ G, (2 : ℚ) ^ A.card := by
    exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_left hq (show 0 ≤ (2 : ℚ) ^ d by positivity)
  simpa only [scaledIdealValue, Finset.mul_sum, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0),
    zpow_natCast, mul_comm] using hm

/-- If every generator cube is small, the entire ideal has small value. -/
theorem scaledIdealValue_le_card_mul (G : Finset (Finset V)) (d : ℤ) (ε : ℚ)
    (h : ∀ A ∈ G, (2 : ℚ) ^ ((A.card : ℤ) + d) ≤ ε) :
    scaledIdealValue G d ≤ (G.card : ℚ) * ε := by
  apply (scaledIdealValue_le_sum_cube G d).trans
  calc
    _ ≤ ∑ A ∈ G, ε := Finset.sum_le_sum h
    _ = _ := by simp

/-- The normalized component and its large clusters differ only by small cubes
and cross-cluster overlaps. -/
theorem scaledIdealValue_sub_clusters_abs_le
    (G : Finset (Finset V)) (P : Finset (Finset (Finset V)))
    (d : ℤ) (ε : ℚ) (hε : 0 ≤ ε)
    (hcover : P.biUnion id ⊆ G) (hcost : ∑ C ∈ P, C.card ≤ G.card)
    (hsmall : ∀ A ∈ G \ P.biUnion id,
      (2 : ℚ) ^ ((A.card : ℤ) + d) ≤ ε)
    (hcross : ∀ C ∈ P, ∀ D ∈ P, C ≠ D → ∀ A ∈ C, ∀ B ∈ D,
      (2 : ℚ) ^ (((A ∩ B).card : ℤ) + d) ≤ ε) :
    |scaledIdealValue G d - ∑ C ∈ P, scaledIdealValue C d| ≤
      ((G.card + G.card ^ 2 : ℕ) : ℚ) * ε := by
  have hlarge := scaledIdealValue_biUnion_le P d
  have hsub := scaledIdealValue_le_card_mul (G \ P.biUnion id) d ε hsmall
  have hunion := scaledIdealValue_union_le (P.biUnion id) (G \ P.biUnion id) d
  rw [Finset.union_sdiff_of_subset hcover] at hunion
  have hsmallcard : ((G \ P.biUnion id).card : ℚ) ≤ G.card := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : G \ P.biUnion id ⊆ G)
  have hupper : scaledIdealValue G d - (∑ C ∈ P, scaledIdealValue C d) ≤
      (G.card : ℚ) * ε := by
    have hm := mul_le_mul_of_nonneg_right hsmallcard hε
    linarith
  have hover := sum_scaledIdealValue_le_biUnion_add_error P d ε hε hcross
  have hmono := scaledIdealValue_mono hcover d
  have hcostq : ((∑ C ∈ P, C.card : ℕ) : ℚ) ≤ G.card := by exact_mod_cast hcost
  have hsquare : ((∑ C ∈ P, C.card : ℕ) : ℚ) ^ 2 ≤ (G.card : ℚ) ^ 2 := by
    nlinarith [show (0 : ℚ) ≤ ((∑ C ∈ P, C.card : ℕ) : ℚ) by positivity]
  have hlower : (∑ C ∈ P, scaledIdealValue C d) - scaledIdealValue G d ≤
      (G.card : ℚ) ^ 2 * ε := by
    have hm := mul_le_mul_of_nonneg_right hsquare hε
    linarith
  rw [abs_le]
  push_cast
  constructor <;> nlinarith [show (0 : ℚ) ≤ (G.card : ℚ) * ε by positivity,
    show (0 : ℚ) ≤ (G.card : ℚ) ^ 2 * ε by positivity]

/-- Lower bounds on all nonempty intersection exponents place the entire value on a dyadic grid. -/
theorem scaledIdealValue_integer_grid (G : Finset (Finset V)) (d : ℤ) (R : ℕ)
    (h : ∀ (S : Finset (Finset V)), S ⊆ G → ∀ hS : S.Nonempty,
      -(R : ℤ) ≤ ((S.inf' hS id).card : ℤ) + d) :
    ∃ z : ℤ, scaledIdealValue G d * (2 : ℚ) ^ R = z := by
  classical
  let I := G.powerset.filter (·.Nonempty)
  have hie : ((generatedIdeal G).card : ℚ) =
      ∑ S : I, (-1 : ℚ) ^ (S.1.card + 1) *
        (2 : ℚ) ^ (S.1.inf' (Finset.mem_filter.mp S.2).2 id).card := by
    exact_mod_cast Section6.generatedIdealIdx_card_inclusionExclusion G id
  have ht : ∀ S : I, ∃ z : ℤ,
      (2 : ℚ) ^ d *
        ((-1 : ℚ) ^ (S.1.card + 1) *
          (2 : ℚ) ^ (S.1.inf' (Finset.mem_filter.mp S.2).2 id).card) *
          (2 : ℚ) ^ R = z := by
    intro S
    have hS := (Finset.mem_filter.mp S.2).2
    have hSG : S.1 ⊆ G := Finset.mem_powerset.mp (Finset.mem_filter.mp S.2).1
    obtain ⟨z, hz⟩ := scaled_power_integer (S.1.inf' hS id).card R d (h S.1 hSG hS)
    refine ⟨(-1 : ℤ) ^ (S.1.card + 1) * z, ?_⟩
    push_cast
    rw [← hz]
    ring
  choose z hz using ht
  refine ⟨∑ S : I, z S, ?_⟩
  simp only [scaledIdealValue, hie, Finset.mul_sum, Finset.sum_mul, Int.cast_sum]
  exact Finset.sum_congr rfl (fun S _ => hz S)

/-- A component's singleton generator cube never exceeds the component value. -/
theorem DyadicIdeal.cube_value_le (D : DyadicIdeal) {A : Finset ℕ}
    (hA : A ∈ D.generators) :
    (2 : ℚ) ^ ((A.card : ℤ) + D.exponent) ≤ D.value := by
  exact cube_value_le_scaledIdealValue hA D.exponent

/-- Positivity of all components bounds each component by the total list value. -/
theorem DyadicIdeal.value_le_sum_of_mem {terms : List DyadicIdeal} {D : DyadicIdeal}
    (hD : D ∈ terms) : D.value ≤ (terms.map DyadicIdeal.value).sum := by
  apply List.single_le_sum
  · intro x hx
    obtain ⟨E, _, rfl⟩ := List.mem_map.mp hx
    exact E.value_nonneg
  · exact List.mem_map.mpr ⟨D, hD, rfl⟩

end AntichainOfGivenSize.BlockCount
