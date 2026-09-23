import AntichainOfGivenSize.LowerBound.ClusterCore
import Mathlib.Tactic

/-!
# Arithmetic for the block-count gap argument

The first theorem finds a scale interval missed by a finite set of integer
exponents. The second says that two points on an integer grid are equal when
their distance is strictly less than one grid step.
-/

namespace AntichainOfGivenSize.BlockCount

/-- Among one more successive scale bands than there are exponents, one band
contains no exponent. We allow coinciding endpoints; the intended use has
strictly increasing `H`. -/
theorem exists_empty_exponent_band (E : Finset ℤ) (H : ℕ → ℕ)
    (hH : Monotone H) :
    ∃ j : ℕ, j ≤ E.card ∧
      ∀ e ∈ E, -(H j : ℤ) ≤ e ∨ e < -(H (j + 1) : ℤ) := by
  classical
  let f : Fin E.card → ℤ := fun s => (E.equivFin.symm s).1
  obtain ⟨j, hj⟩ :=
    ClusterCore.exists_common_stable_gap E.card
      (fun s i => f s < -(H i.1 : ℤ))
      (by
        intro s i j hij hp
        have hmon : H i.1 ≤ H j.1 := hH (Fin.mk_le_mk.mp hij)
        have hneg : -(H j.1 : ℤ) ≤ -(H i.1 : ℤ) :=
          neg_le_neg (by exact_mod_cast hmon)
        exact lt_of_lt_of_le hp hneg)
  refine ⟨j.1, Nat.le_of_lt_succ j.2, ?_⟩
  intro e he
  let s : Fin E.card := E.equivFin ⟨e, he⟩
  have hs : f s = e := by simp [f, s]
  have hstable := hj s
  change (f s < -(H j.1 : ℤ) ↔ f s < -(H (j.1 + 1) : ℤ)) at hstable
  rw [hs] at hstable
  by_cases hlarge : -(H j.1 : ℤ) ≤ e
  · exact Or.inl hlarge
  · exact Or.inr (hstable.mp (lt_of_not_ge hlarge))

/-- Two rational numbers on the same grid `1/D` coincide when they are less
than one grid step apart. -/
theorem eq_of_integer_grid_distance_lt_one (p S : ℚ) (D : ℕ) (hD : 0 < D)
    (hp : ∃ a : ℤ, p * (D : ℚ) = a)
    (hS : ∃ b : ℤ, S * (D : ℚ) = b)
    (hclose : |p - S| * (D : ℚ) < 1) : p = S := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hS
  have hDq : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  have hcast : ((a - b : ℤ) : ℚ) = (p - S) * (D : ℚ) := by
    push_cast
    rw [← ha, ← hb]
    ring
  have habs : |((a - b : ℤ) : ℚ)| < 1 := by
    rw [hcast, abs_mul, abs_of_pos hDq]
    exact hclose
  have hlow : (-1 : ℤ) < a - b := by
    exact_mod_cast (abs_lt.mp habs).1
  have hupp : a - b < (1 : ℤ) := by
    exact_mod_cast (abs_lt.mp habs).2
  have hab : a = b := by omega
  have hzero : (p - S) * (D : ℚ) = 0 := by
    rw [← hcast, hab]
    simp
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (ne_of_gt hDq))

end AntichainOfGivenSize.BlockCount
