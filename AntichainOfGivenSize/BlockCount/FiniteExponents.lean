import AntichainOfGivenSize.BlockCount.GapArithmetic
import AntichainOfGivenSize.BlockCount.ScaledIdeals

/-!
# The finite list of relevant exponents

For each generator we record its normalized cube exponent; for each ordered
pair in the same component we record its normalized intersection exponent.
A cost bound `k` gives an explicit bound on the number of such exponents.
-/

namespace AntichainOfGivenSize.BlockCount

open Finset

/-- Exponent of an individual generator cube after dividing by `2^t`. -/
def singletonExponent (D : DyadicIdeal) (t : ℕ) (A : Finset ℕ) : ℤ :=
  (A.card : ℤ) + D.exponent - (t : ℤ)

/-- Exponent of a pairwise generator-cube intersection after dividing by `2^t`. -/
def pairExponent (D : DyadicIdeal) (t : ℕ) (A B : Finset ℕ) : ℤ :=
  ((A ∩ B).card : ℤ) + D.exponent - (t : ℤ)

noncomputable def componentExponentSet (D : DyadicIdeal) (t : ℕ) : Finset ℤ :=
  (D.generators.image (singletonExponent D t)) ∪
    ((D.generators.product D.generators).image
      (fun P => pairExponent D t P.1 P.2))

noncomputable def exponentSet (terms : List DyadicIdeal) (t : ℕ) : Finset ℤ := by
  classical
  exact terms.toFinset.biUnion (fun D => componentExponentSet D t)

theorem singletonExponent_mem (terms : List DyadicIdeal) (t : ℕ)
    (D : DyadicIdeal) (hD : D ∈ terms) (A : Finset ℕ)
    (hA : A ∈ D.generators) :
    singletonExponent D t A ∈ exponentSet terms t := by
  classical
  unfold exponentSet componentExponentSet
  apply Finset.mem_biUnion.mpr
  refine ⟨D, List.mem_toFinset.mpr hD, Finset.mem_union.mpr (Or.inl ?_)⟩
  exact Finset.mem_image.mpr ⟨A, hA, rfl⟩

theorem pairExponent_mem (terms : List DyadicIdeal) (t : ℕ)
    (D : DyadicIdeal) (hD : D ∈ terms) (A B : Finset ℕ)
    (hA : A ∈ D.generators) (hB : B ∈ D.generators) :
    pairExponent D t A B ∈ exponentSet terms t := by
  classical
  unfold exponentSet componentExponentSet
  apply Finset.mem_biUnion.mpr
  refine ⟨D, List.mem_toFinset.mpr hD, Finset.mem_union.mpr (Or.inr ?_)⟩
  exact Finset.mem_image.mpr ⟨(A, B), Finset.mem_product.mpr ⟨hA, hB⟩, rfl⟩

theorem componentExponentSet_card_le (D : DyadicIdeal) (t : ℕ) :
    (componentExponentSet D t).card ≤ D.cost + D.cost * D.cost := by
  classical
  unfold componentExponentSet
  calc
    _ ≤ (D.generators.image (singletonExponent D t)).card +
      ((D.generators.product D.generators).image
        (fun P => pairExponent D t P.1 P.2)).card := Finset.card_union_le _ _
    _ ≤ D.generators.card + (D.generators.product D.generators).card :=
      Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ = D.cost + D.cost * D.cost := by simp [DyadicIdeal.cost]

/-- At cost at most `k`, the number of different singleton and pair exponents
is at most `k(k+k²)`. The bound is intentionally coarse. -/
theorem exponentSet_card_le (terms : List DyadicIdeal) (t k : ℕ)
    (hcost : (terms.map DyadicIdeal.cost).sum ≤ k) :
    (exponentSet terms t).card ≤ k * (k + k * k) := by
  classical
  have hlen : terms.length ≤ k :=
    (length_le_sum_cost terms).trans hcost
  have hD : ∀ D ∈ terms.toFinset, D.cost ≤ k := by
    intro D hD
    have hmem : D.cost ∈ terms.map DyadicIdeal.cost :=
      List.mem_map.mpr ⟨D, List.mem_toFinset.mp hD, rfl⟩
    exact (List.le_sum_of_mem hmem).trans hcost
  unfold exponentSet
  calc
    (terms.toFinset.biUnion (fun D => componentExponentSet D t)).card ≤
        ∑ D ∈ terms.toFinset, (componentExponentSet D t).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _D ∈ terms.toFinset, (k + k * k) := by
      apply Finset.sum_le_sum
      intro D hmem
      have hc := componentExponentSet_card_le D t
      have hd := hD D hmem
      nlinarith
    _ = terms.toFinset.card * (k + k * k) := by simp
    _ ≤ terms.length * (k + k * k) :=
      Nat.mul_le_mul_right _ (List.toFinset_card_le terms)
    _ ≤ k * (k + k * k) := Nat.mul_le_mul_right _ hlen

/-- A scale band separates every relevant singleton and pair exponent. -/
theorem exists_empty_exponent_band_of_cost (terms : List DyadicIdeal)
    (t k : ℕ) (hcost : (terms.map DyadicIdeal.cost).sum ≤ k)
    (H : ℕ → ℕ) (hH : Monotone H) :
    ∃ j : ℕ, j ≤ k * (k + k * k) ∧
      ∀ e ∈ exponentSet terms t,
        -(H j : ℤ) ≤ e ∨ e < -(H (j + 1) : ℤ) := by
  obtain ⟨j, hj, hgap⟩ :=
    exists_empty_exponent_band (exponentSet terms t) H hH
  exact ⟨j, hj.trans (exponentSet_card_le terms t k hcost), hgap⟩

end AntichainOfGivenSize.BlockCount
