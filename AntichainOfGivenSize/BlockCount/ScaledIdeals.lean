import AntichainOfGivenSize.BasicLemmas
import Mathlib.Tactic

/-!
# Positive sums of scaled ideal cardinalities

A scaling factor is an integral power of two. Empty lists represent zero;
every individual component has a nonempty generating family and positive cost.
-/

namespace AntichainOfGivenSize.BlockCount

open Finset

/-- One nonempty finite ideal, with its cardinality scaled by an integral power of two. -/
structure DyadicIdeal where
  generators : Finset (Finset ℕ)
  generators_nonempty : generators.Nonempty
  exponent : ℤ

namespace DyadicIdeal

/-- The positive rational value contributed by this component. -/
def value (D : DyadicIdeal) : ℚ :=
  (2 : ℚ) ^ D.exponent * (generatedIdeal D.generators).card

/-- The number of generating sets in this component. -/
def cost (D : DyadicIdeal) : ℕ := D.generators.card

theorem cost_pos (D : DyadicIdeal) : 0 < D.cost :=
  Finset.card_pos.mpr D.generators_nonempty

theorem generatedIdeal_nonempty (D : DyadicIdeal) :
    (generatedIdeal D.generators).Nonempty := by
  rcases D.generators_nonempty with ⟨A, hA⟩
  refine ⟨∅, ?_⟩
  simp only [generatedIdeal, Finset.mem_biUnion, Finset.mem_powerset]
  exact ⟨A, hA, Finset.empty_subset A⟩

theorem value_pos (D : DyadicIdeal) : 0 < D.value := by
  unfold value
  apply mul_pos
  · positivity
  · exact_mod_cast Finset.card_pos.mpr D.generatedIdeal_nonempty

theorem value_nonneg (D : DyadicIdeal) : 0 ≤ D.value :=
  le_of_lt D.value_pos

/-- Change only the dyadic scaling exponent. -/
def shift (D : DyadicIdeal) (d : ℤ) : DyadicIdeal :=
  { D with exponent := d + D.exponent }

@[simp] theorem shift_generators (D : DyadicIdeal) (d : ℤ) :
    (D.shift d).generators = D.generators := rfl

@[simp] theorem shift_cost (D : DyadicIdeal) (d : ℤ) :
    (D.shift d).cost = D.cost := rfl

@[simp] theorem shift_value (D : DyadicIdeal) (d : ℤ) :
    (D.shift d).value = (2 : ℚ) ^ d * D.value := by
  simp only [value, shift, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  ring

/-- A single empty generator contributes one, at cost one. -/
def one : DyadicIdeal where
  generators := {∅}
  generators_nonempty := Finset.singleton_nonempty _
  exponent := 0

@[simp] theorem one_cost : one.cost = 1 := by
  simp [one, cost]

@[simp] theorem one_value : one.value = 1 := by
  simp [one, value, generatedIdeal]

/-- A component with one generator contributes a pure integral power of two. -/
theorem value_eq_zpow_of_cost_eq_one (D : DyadicIdeal) (h : D.cost = 1) :
    ∃ e : ℤ, D.value = (2 : ℚ) ^ e := by
  rcases Finset.card_eq_one.mp h with ⟨A, hA⟩
  refine ⟨D.exponent + (A.card : ℤ), ?_⟩
  simp only [value, hA, generatedIdeal, Finset.singleton_biUnion,
    Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat,
    zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]

end DyadicIdeal

/-- A list of positive components represents `x`, using at most `k` generators.
The empty list is allowed and has value and cost zero. -/
def HasDyadicIdealSum (x : ℚ) (k : ℕ) : Prop :=
  ∃ terms : List DyadicIdeal,
    (terms.map DyadicIdeal.value).sum = x ∧
      (terms.map DyadicIdeal.cost).sum ≤ k

/-- The cost of a list dominates its length, because every component costs at least one. -/
theorem length_le_sum_cost (terms : List DyadicIdeal) :
    terms.length ≤ (terms.map DyadicIdeal.cost).sum := by
  induction terms with
  | nil => simp
  | cons D terms ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have hD := D.cost_pos
      omega

/-- A nonempty list of components has strictly positive total value. -/
theorem sum_value_pos {terms : List DyadicIdeal} (h : terms ≠ []) :
    0 < (terms.map DyadicIdeal.value).sum := by
  cases terms with
  | nil => contradiction
  | cons D terms =>
      simp only [List.map_cons, List.sum_cons]
      have htail : 0 ≤ (terms.map DyadicIdeal.value).sum := by
        apply List.sum_nonneg
        intro a ha
        rcases List.mem_map.mp ha with ⟨E, _, rfl⟩
        exact E.value_nonneg
      exact add_pos_of_pos_of_nonneg D.value_pos htail

namespace HasDyadicIdealSum

theorem mono {x : ℚ} {k l : ℕ} (h : HasDyadicIdealSum x k) (hkl : k ≤ l) :
    HasDyadicIdealSum x l := by
  rcases h with ⟨terms, hx, hk⟩
  exact ⟨terms, hx, hk.trans hkl⟩

theorem zero : HasDyadicIdealSum 0 0 := by
  exact ⟨[], by simp, by simp⟩

theorem of_single (D : DyadicIdeal) : HasDyadicIdealSum D.value D.cost := by
  exact ⟨[D], by simp, by simp⟩

theorem nonneg {x : ℚ} {k : ℕ} (h : HasDyadicIdealSum x k) : 0 ≤ x := by
  rcases h with ⟨terms, rfl, _⟩
  apply List.sum_nonneg
  intro a ha
  rcases List.mem_map.mp ha with ⟨D, _, rfl⟩
  exact D.value_nonneg

theorem eq_zero_of_cost_zero {x : ℚ} (h : HasDyadicIdealSum x 0) : x = 0 := by
  rcases h with ⟨terms, hx, hk⟩
  have hlen := length_le_sum_cost terms
  have hempty : terms = [] := List.length_eq_zero_iff.mp (by omega)
  simpa [hempty] using hx.symm

theorem cost_pos {x : ℚ} {k : ℕ} (h : HasDyadicIdealSum x k) (hx : 0 < x) :
    0 < k := by
  by_contra hk
  have hk0 : k = 0 := by omega
  subst k
  have := h.eq_zero_of_cost_zero
  linarith

theorem append {x y : ℚ} {k l : ℕ}
    (hx : HasDyadicIdealSum x k) (hy : HasDyadicIdealSum y l) :
    HasDyadicIdealSum (x + y) (k + l) := by
  rcases hx with ⟨xs, hxs, hxc⟩
  rcases hy with ⟨ys, hys, hyc⟩
  refine ⟨xs ++ ys, ?_, ?_⟩
  · simp [List.map_append, List.sum_append, hxs, hys]
  · simpa only [List.map_append, List.sum_append] using Nat.add_le_add hxc hyc

theorem shift {x : ℚ} {k : ℕ} (h : HasDyadicIdealSum x k) (d : ℤ) :
    HasDyadicIdealSum ((2 : ℚ) ^ d * x) k := by
  rcases h with ⟨terms, hx, hk⟩
  refine ⟨terms.map (fun D => D.shift d), ?_, ?_⟩
  · have hs : ((terms.map (fun D => D.shift d)).map DyadicIdeal.value).sum =
        (2 : ℚ) ^ d * (terms.map DyadicIdeal.value).sum := by
      clear hx hk
      induction terms with
      | nil => simp
      | cons D terms ih =>
          simp only [List.map_cons, List.sum_cons, DyadicIdeal.shift_value]
          rw [ih, mul_add]
    rw [hs, hx]
  · simpa only [List.map_map, Function.comp_def, DyadicIdeal.shift_cost] using hk

theorem add_one {x : ℚ} {k : ℕ} (h : HasDyadicIdealSum x k) :
    HasDyadicIdealSum (x + 1) (k + 1) := by
  have hone : HasDyadicIdealSum (1 : ℚ) 1 := by
    simpa using of_single DyadicIdeal.one
  exact h.append hone

end HasDyadicIdealSum

/-- Every ordinary positive alpha-witness is a one-component scaled-sum witness. -/
theorem hasDyadicIdealSum_alpha (n : ℕ) (hn : 0 < n) :
    HasDyadicIdealSum (n : ℚ) (alpha n) := by
  rcases alpha_hasGeneratorCount n with ⟨m, G, hsize, hcard⟩
  have hG : G.Nonempty := by
    by_contra h
    have he : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he, generatedIdeal] at hsize
    omega
  let f : Fin m ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let H : Finset (Finset ℕ) := mapFamily f G
  have hH : H.Nonempty := by
    exact Finset.map_nonempty.mpr hG
  let D : DyadicIdeal := ⟨H, hH, 0⟩
  refine ⟨[D], ?_, ?_⟩
  · simp [D, H, DyadicIdeal.value, generatedIdeal_mapFamily, hsize]
  · simp [D, H, DyadicIdeal.cost, mapFamily, hcard]

/-- Three lies strictly between consecutive integral powers of two. -/
theorem two_zpow_ne_three (e : ℤ) : (2 : ℚ) ^ e ≠ 3 := by
  intro heq
  by_cases he : e ≤ 1
  · have hp : (2 : ℚ) ^ e ≤ (2 : ℚ) ^ (1 : ℤ) :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mpr he
    norm_num [heq] at hp
  · have he' : (2 : ℤ) ≤ e := by omega
    have hp : (2 : ℚ) ^ (2 : ℤ) ≤ (2 : ℚ) ^ e :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mpr he'
    norm_num [heq] at hp

/-- No representation of three has total cost at most one. -/
theorem not_hasDyadicIdealSum_three_one : ¬ HasDyadicIdealSum (3 : ℚ) 1 := by
  rintro ⟨terms, hv, hc⟩
  cases terms with
  | nil => simp at hv
  | cons D terms =>
      cases terms with
      | nil =>
          have hD : D.cost = 1 := by
            have hpos := D.cost_pos
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
              add_zero] at hc
            omega
          rcases D.value_eq_zpow_of_cost_eq_one hD with ⟨e, he⟩
          have hv' : D.value = 3 := by simpa using hv
          exact two_zpow_ne_three e (he.symm.trans hv')
      | cons E terms =>
          have hD := D.cost_pos
          have hE := E.cost_pos
          simp only [List.map_cons, List.sum_cons] at hc
          omega

/-- The two scaled singleton components `2` and `1` represent three. -/
theorem hasDyadicIdealSum_three_two : HasDyadicIdealSum (3 : ℚ) 2 := by
  have htwo : HasDyadicIdealSum (2 : ℚ) 1 := by
    simpa using (HasDyadicIdealSum.of_single DyadicIdeal.one).shift (1 : ℤ)
  have h := htwo.add_one
  norm_num at h ⊢
  exact h

end AntichainOfGivenSize.BlockCount
