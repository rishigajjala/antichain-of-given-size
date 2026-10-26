import AntichainOfGivenSize.Paper.Statements
import AntichainOfGivenSize.LowerBound.ClusterStateConstruction
import AntichainOfGivenSize.LowerBound.ProfilePadding
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform finite clustered counting

The combinatorial argument in this file has arbitrary natural parameters
`B` and `K`. In particular, neither parameter is restricted to the sparse
dyadic sequence used by the older infinitely-often lower bound.
The final theorem isolates the finite numerical inequalities needed for
the paper's uniform counting theorem.
-/

open Finset

namespace AntichainOfGivenSize.Paper

open ClusterLowerBound ClusterCore

/-- Repeating a generator embeds every nonempty shorter indexed profile
into the exact larger-coordinate value image. -/
theorem boundedValues_subset_of_le {k K B : ℕ} (hk : k ≤ K) (hkpos : 0 < k) :
    boundedValues k B ⊆ boundedValues K B := by
  classical
  intro n hn
  rcases Finset.mem_image.1 hn with ⟨x, _hx, rfl⟩
  exact Finset.mem_image.2 ⟨x.pad hk hkpos, Finset.mem_univ _,
    BoundedProfile.value_pad x hk hkpos⟩

theorem attainableValues_card_mono {B k K : ℕ} (hk : k ≤ K) (hkpos : 0 < k) :
    (attainableValues B k).card ≤ (attainableValues B K).card :=
  Finset.card_le_card (boundedValues_subset_of_le hk hkpos)

/-- Convert an integral exponent saving to the paper's real square-root
exponent. This keeps natural subtraction and real subtraction distinct. -/
theorem attainableValues_real_card_le_of_nat_bound {B K s : ℕ}
    (hs : s ≤ B) (hsqrt : Real.sqrt (B : ℝ) ≤ (s : ℝ))
    (hcard : (attainableValues B K).card ≤ 2 ^ (B - s)) :
    ((attainableValues B K).card : ℝ) ≤
      (2 : ℝ) ^ ((B : ℝ) - Real.sqrt (B : ℝ)) := by
  calc
    ((attainableValues B K).card : ℝ) ≤ ((2 ^ (B - s) : ℕ) : ℝ) := by
      exact_mod_cast hcard
    _ = (2 : ℝ) ^ ((B : ℝ) - (s : ℝ)) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, Nat.cast_sub hs]
    _ ≤ (2 : ℝ) ^ ((B : ℝ) - Real.sqrt (B : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith

/-- The shape count needs no asymptotic assumptions. -/
theorem counting_shape_base_le {K J : ℕ} (hJ : J ≤ K) :
    (J + 1) * (J + 1) ^ K * (K + 1) ^ K ≤ 2 ^ (3 * K ^ 2) := by
  have hKpow : K + 1 ≤ 2 ^ K := K.lt_two_pow_self
  have hJpow : J + 1 ≤ 2 ^ K := (Nat.add_le_add_right hJ 1).trans hKpow
  have hKK : K ≤ K ^ 2 := by
    by_cases hK : K = 0
    · simp [hK]
    · have : 1 ≤ K := by omega
      nlinarith
  calc
    (J + 1) * (J + 1) ^ K * (K + 1) ^ K ≤
        2 ^ K * (2 ^ K) ^ K * (2 ^ K) ^ K := by gcongr
    _ = 2 ^ (K + K * K + K * K) := by
      simp only [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (3 * K ^ 2) := by
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith

theorem counting_exception_base_le {K U : ℕ} (hU : U ≤ 2 ^ K) :
    2 ^ K + 1 + U ≤ 2 ^ (K + 2) := by
  have hpos : 0 < 2 ^ K := by positivity
  calc
    2 ^ K + 1 + U ≤ 4 * 2 ^ K := by omega
    _ = 2 ^ (K + 2) := by simp [pow_add]; ring

theorem counting_center_base_le {K B J M : ℕ} (hK : 0 < K)
    (hJ : J ≤ K) (hB : B + 1 ≤ 2 ^ K) (hM : M ≤ 2 ^ K) :
    2 ^ (J + K) * (B + 1) + 1 + M ≤ 2 ^ (4 * K) := by
  have hfirst : 2 ^ (J + K) * (B + 1) ≤ 2 ^ (3 * K) := by
    calc
      2 ^ (J + K) * (B + 1) ≤ 2 ^ (K + K) * 2 ^ K := by
        exact Nat.mul_le_mul
          (Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_right hJ K)) hB
      _ = 2 ^ (3 * K) := by rw [← pow_add]; congr 1; omega
  have hrest : 1 + M ≤ 2 ^ (3 * K) := by
    calc
      1 + M ≤ 2 ^ K + 2 ^ K := by
        have : 1 ≤ 2 ^ K := Nat.one_le_two_pow
        omega
      _ = 2 ^ (K + 1) := by simp [pow_add]; ring
      _ ≤ 2 ^ (3 * K) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc
    2 ^ (J + K) * (B + 1) + 1 + M ≤
        2 ^ (3 * K) + 2 ^ (3 * K) := by omega
    _ = 2 ^ (3 * K + 1) := by simp [pow_add]; ring
    _ ≤ 2 ^ (4 * K) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Elementary absorption of the encoding, tail prefactor, and requested
saving; the conclusion is phrased with natural subtraction. -/
theorem counting_exponent_absorption {B rho E K s : ℕ}
    (hrho : rho ≤ B) (hE : 4 * E ≤ rho)
    (hK : 8 * (K + 1) ≤ rho) (hs : 2 * s ≤ rho) :
    B - rho + E + 2 * K + 2 ≤ B - s := by
  have hsum : E + 2 * K + 2 + s ≤ rho := by omega
  omega

/-- A finite decreasing list of scales long enough to force a stable
packing gap. The actual numerical choice of scales is made separately. -/
structure CountingSetup (K B : ℕ) where
  h : ℕ
  J : ℕ
  h_pos : 0 < h
  cover : K < (J + 1) * h
  rho : Fin (J + 2) → ℕ
  rho_antitone : Antitone rho

namespace CountingSetup

variable {K B : ℕ} (P : CountingSetup K B)

def centerBudget : ℕ := 2 ^ P.J * (1 + K * 2 ^ P.h)

def exceptionalBudget (j : Fin (P.J + 1)) : ℕ :=
  K * K * (2 * P.rho j.succ)

def fiberDiameter (j : Fin (P.J + 1)) : ℕ :=
  2 * (2 ^ K * 2 ^ (B - P.rho j.castSucc))

def stateCost (j : Fin (P.J + 1)) : ℕ :=
  3 * K ^ 2 + (K + 2) * P.exceptionalBudget j + 4 * K * P.centerBudget

private structure Clustering (x : BoundedProfile K B) where
  gap : Fin (P.J + 1)
  count : ℕ
  count_le : count ≤ P.J
  state : ProfileClusterState x (P.rho gap.succ) P.h count
  residual_small : ∀ C : Finset (Fin K),
    C ⊆ state.packed.residual →
    ConnectedOn (x.proximityGraph (P.rho gap.castSucc)) C → #C < P.h

private theorem nonempty_clustering (x : BoundedProfile K B) :
    Nonempty (P.Clustering x) := by
  rcases x.exists_stable_clusterState P.h P.J P.h_pos P.cover
      P.rho P.rho_antitone with ⟨j, r, S, hr, hsmall⟩
  exact ⟨⟨j, r, hr, S, hsmall⟩⟩

private noncomputable def selected (x : BoundedProfile K B) : P.Clustering x :=
  Classical.choice (P.nonempty_clustering x)

private abbrev ProfilesAtGap (j : Fin (P.J + 1)) :=
  {x : BoundedProfile K B // (P.selected x).gap = j}

private noncomputable def valuesAtGap (j : Fin (P.J + 1)) : Finset ℕ :=
  (Finset.univ : Finset (P.ProfilesAtGap j)).image fun x ↦ x.1.value

private theorem boundedValues_eq_union :
    boundedValues K B =
      (Finset.univ : Finset (Fin (P.J + 1))).biUnion P.valuesAtGap := by
  classical
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.1 hn with ⟨x, _hx, rfl⟩
    apply Finset.mem_biUnion.2
    refine ⟨(P.selected x).gap, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.2 ⟨⟨x, rfl⟩, Finset.mem_univ _, rfl⟩
  · intro hn
    rcases Finset.mem_biUnion.1 hn with ⟨j, _hj, hn⟩
    rcases Finset.mem_image.1 hn with ⟨x, _hx, rfl⟩
    exact Finset.mem_image.2 ⟨x.1, Finset.mem_univ _, rfl⟩

private theorem selected_exceptional_le (j : Fin (P.J + 1))
    (x : P.ProfilesAtGap j) :
    #(x.1.exceptionalSet (P.rho (P.selected x.1).gap.succ)) ≤
      P.exceptionalBudget j := by
  have h := x.1.exceptionalSet_card_le (P.rho (P.selected x.1).gap.succ)
  simpa [exceptionalBudget, x.2] using h

private theorem selected_centers_le (j : Fin (P.J + 1))
    (x : P.ProfilesAtGap j) :
    #((P.selected x.1).state.centerPairSet (P.rho j.castSucc)
        (P.selected x.1).count_le) ≤ P.centerBudget := by
  let C := P.selected x.1
  have hsmall : ∀ i ∈ C.state.packed.residual,
      #(C.state.packed.componentFiber (x.1.proximityGraph (P.rho j.castSucc)) i) <
        P.h := by
    intro i hi
    apply C.state.packed.componentFiber_card_lt _ _ i hi
    intro A hA hconn
    apply C.residual_small A hA
    simpa [C, x.2] using hconn
  simpa [C, centerBudget] using C.state.centerPairSet_card_le C.count_le hsmall

private noncomputable def encodeAtGap (j : Fin (P.J + 1))
    (x : P.ProfilesAtGap j) :
    ClusterEncoding K B P.J (P.exceptionalBudget j) P.centerBudget :=
  (P.selected x.1).state.toClusterEncoding j (P.selected x.1).count_le
    (P.selected_exceptional_le j x) (P.selected_centers_le j x)

private theorem encodeAtGap_diameter (j : Fin (P.J + 1))
    (x y : P.ProfilesAtGap j) (heq : P.encodeAtGap j x = P.encodeAtGap j y) :
    Int.natAbs ((x.1.value : ℤ) - (y.1.value : ℤ)) ≤ P.fiberDiameter j := by
  exact value_natAbs_sub_le_of_clusterEncoding_eq
    (P.selected x.1).state (P.selected y.1).state j j
    (P.selected x.1).count_le (P.selected y.1).count_le
    (P.selected_exceptional_le j x) (P.selected_exceptional_le j y)
    (P.selected_centers_le j x) (P.selected_centers_le j y) heq

private theorem valuesAtGap_card_le (j : Fin (P.J + 1)) :
    #(P.valuesAtGap j) ≤
      Fintype.card (ClusterEncoding K B P.J (P.exceptionalBudget j) P.centerBudget) *
        (P.fiberDiameter j + 1) := by
  classical
  exact card_image_le_card_mul_of_fiber_diameter (P.encodeAtGap j)
    (fun x : P.ProfilesAtGap j ↦ x.1.value) (P.fiberDiameter j)
    (P.encodeAtGap_diameter j)

/-- A finite cardinality estimate valid for arbitrary generator bounds and
arbitrary decreasing scales. -/
theorem boundedValues_card_le_sum :
    #(boundedValues K B) ≤
      ∑ j : Fin (P.J + 1),
        Fintype.card (ClusterEncoding K B P.J (P.exceptionalBudget j) P.centerBudget) *
          (P.fiberDiameter j + 1) := by
  classical
  rw [P.boundedValues_eq_union]
  apply (Finset.card_biUnion_le).trans
  exact Finset.sum_le_sum fun j _hj ↦ P.valuesAtGap_card_le j

theorem fiberDiameter_succ_le_two_pow (j : Fin (P.J + 1)) :
    P.fiberDiameter j + 1 ≤ 2 ^ (B - P.rho j.castSucc + K + 2) := by
  let X := 2 ^ K * 2 ^ (B - P.rho j.castSucc)
  have hX : 0 < X := by positivity
  calc
    P.fiberDiameter j + 1 = 2 * X + 1 := rfl
    _ ≤ 4 * X := by omega
    _ = 2 ^ (B - P.rho j.castSucc + K + 2) := by
      dsimp [X]
      simp only [pow_add]
      ring

/-- The finite encoding and tail estimates yield a prescribed integral
exponent saving once their explicit numerical costs fit below that target. -/
theorem boundedValues_card_le_two_pow_of_cost
    (E : Fin (P.J + 1) → ℕ) (s g : ℕ)
    (hencoding : ∀ j : Fin (P.J + 1),
      Fintype.card (ClusterEncoding K B P.J (P.exceptionalBudget j) P.centerBudget) ≤
        2 ^ E j)
    (hg : P.J + 1 ≤ 2 ^ g)
    (hcost : ∀ j : Fin (P.J + 1),
      B - P.rho j.castSucc + E j + K + 2 + g ≤ B - s) :
    #(boundedValues K B) ≤ 2 ^ (B - s) := by
  classical
  have hg_le : g ≤ B - s := by
    have := hcost ⟨0, Nat.zero_lt_succ P.J⟩
    omega
  calc
    #(boundedValues K B) ≤
        ∑ j : Fin (P.J + 1),
          Fintype.card (ClusterEncoding K B P.J (P.exceptionalBudget j) P.centerBudget) *
            (P.fiberDiameter j + 1) := P.boundedValues_card_le_sum
    _ ≤ ∑ _j : Fin (P.J + 1), 2 ^ (B - s - g) := by
      apply Finset.sum_le_sum
      intro j _hj
      calc
        Fintype.card (ClusterEncoding K B P.J (P.exceptionalBudget j) P.centerBudget) *
            (P.fiberDiameter j + 1) ≤
            2 ^ E j * 2 ^ (B - P.rho j.castSucc + K + 2) :=
          Nat.mul_le_mul (hencoding j) (P.fiberDiameter_succ_le_two_pow j)
        _ = 2 ^ (B - P.rho j.castSucc + E j + K + 2) := by
          rw [← pow_add]
          congr 1
          omega
        _ ≤ 2 ^ (B - s - g) := by
          apply Nat.pow_le_pow_right (by norm_num)
          have := hcost j
          omega
    _ = (P.J + 1) * 2 ^ (B - s - g) := by simp
    _ ≤ 2 ^ g * 2 ^ (B - s - g) := Nat.mul_le_mul_right _ hg
    _ = 2 ^ (B - s) := by
      rw [← pow_add]
      congr 1
      omega

/-- Convenient specialization using the standard three finite code costs.
The hypotheses contain only natural-number inequalities. -/
theorem boundedValues_card_le_two_pow
    (s : ℕ)
    (hshape : (P.J + 1) * (P.J + 1) ^ K * (K + 1) ^ K ≤ 2 ^ (3 * K ^ 2))
    (hexception : ∀ j : Fin (P.J + 1),
      2 ^ K + 1 + P.exceptionalBudget j ≤ 2 ^ (K + 2))
    (hcenter : 2 ^ (P.J + K) * (B + 1) + 1 + P.centerBudget ≤ 2 ^ (4 * K))
    (hgap : P.J + 1 ≤ 2 ^ K)
    (hcost : ∀ j : Fin (P.J + 1),
      B - P.rho j.castSucc + P.stateCost j + 2 * K + 2 ≤ B - s) :
    #(boundedValues K B) ≤ 2 ^ (B - s) := by
  apply P.boundedValues_card_le_two_pow_of_cost P.stateCost s K
  · intro j
    exact card_clusterEncoding_le_two_pow_of_bounds K B P.J
      (P.exceptionalBudget j) P.centerBudget hshape (hexception j) hcenter
  · exact hgap
  · intro j
    simpa only [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcost j

end CountingSetup

end AntichainOfGivenSize.Paper
