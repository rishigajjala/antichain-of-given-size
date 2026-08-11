import AntichainOfGivenSize.LowerBound.ClusterFiber
import AntichainOfGivenSize.LowerBound.ClusterImageBound
import AntichainOfGivenSize.LowerBound.ClusterParameters
import AntichainOfGivenSize.LowerBound.ClusterStateConstruction
import AntichainOfGivenSize.LowerBound.ProfilePadding
import AntichainOfGivenSize.LowerBound.QuadraticLogEndpoint

/-!
# Assembling the clustered-profile residue bound

This module combines the stable-gap decomposition, the finite cluster state,
and the diameter estimate for one state fiber.  The counting is stratified by
the selected stable gap.  This is essential: the entropy of the state at gap
`j` and the diameter of its fibers must be charged against the same loss scale
`clusterRho t j`.
-/

open Filter Finset

namespace AntichainOfGivenSize.ClusterLowerBound

open AntichainOfGivenSize.ClusterCore
open AntichainOfGivenSize.ClusterParameters

private abbrev gapExceptionalBudget (t j : ℕ) : ℕ :=
  facetBudget t * facetBudget t * (2 * clusterRho t (j + 1))

private abbrev gapStateCost (t j : ℕ) : ℕ :=
  3 * facetBudget t ^ 2 +
    (facetBudget t + 2) * gapExceptionalBudget t j +
    4 * facetBudget t * centerQueryBound t

private abbrev gapFiberDiameter (t j : ℕ) : ℕ :=
  2 * (2 ^ facetBudget t *
    2 ^ (dyadicB t - clusterRho t j))

/-! ## A deterministic stable-gap stratum -/

private theorem facetBudget_lt_cluster_cover {t : ℕ} (ht : 16 ≤ t) :
    facetBudget t < (clusterJ t + 1) * clusterH t := by
  have h := Nat.lt_mul_div_succ (facetBudget t) (clusterH_pos (by omega : 2 ≤ t))
  simpa [clusterJ, mul_comm] using h

private structure DyadicClustering
    (t k : ℕ) (x : BoundedProfile k (dyadicB t)) where
  gap : Fin (clusterJ t + 1)
  clusterCount : ℕ
  count_le : clusterCount ≤ clusterJ t
  state : ProfileClusterState x (clusterRho t gap.succ) (clusterH t)
    clusterCount
  residual_small : ∀ C : Finset (Fin k),
    C ⊆ state.packed.residual →
    ConnectedOn (x.proximityGraph (clusterRho t gap.castSucc)) C →
    #C < clusterH t

private theorem nonempty_dyadicClustering
    (t k : ℕ) (ht : 16 ≤ t) (hk : k ≤ facetBudget t)
    (x : BoundedProfile k (dyadicB t)) :
    Nonempty (DyadicClustering t k x) := by
  have hrho : Antitone
      (fun j : Fin (clusterJ t + 2) ↦ clusterRho t j) := by
    intro i j hij
    exact clusterRho_antitone t hij
  rcases x.exists_stable_clusterState (clusterH t) (clusterJ t)
      (clusterH_pos (by omega : 2 ≤ t))
      (hk.trans_lt (facetBudget_lt_cluster_cover ht)) _ hrho with
    ⟨j, r, S, hr, hsmall⟩
  exact ⟨⟨j, r, hr, S, hsmall⟩⟩

private noncomputable def selectedClustering
    (t : ℕ) (ht : 16 ≤ t)
    (x : BoundedProfile (facetBudget t) (dyadicB t)) :
    DyadicClustering t (facetBudget t) x :=
  Classical.choice (nonempty_dyadicClustering t (facetBudget t) ht le_rfl x)

private abbrev ProfilesAtGap
    (t : ℕ) (ht : 16 ≤ t)
    (j : Fin (clusterJ t + 1)) :=
  {x : BoundedProfile (facetBudget t) (dyadicB t) //
    (selectedClustering t ht x).gap = j}

private noncomputable def valuesAtGap
    (t : ℕ) (ht : 16 ≤ t)
    (j : Fin (clusterJ t + 1)) : Finset ℕ :=
  (Finset.univ : Finset (ProfilesAtGap t ht j)).image
    (fun x ↦ x.1.value)

private theorem boundedValues_eq_biUnion_valuesAtGap
    (t : ℕ) (ht : 16 ≤ t) :
    boundedValues (facetBudget t) (dyadicB t) =
      (Finset.univ : Finset (Fin (clusterJ t + 1))).biUnion
        (valuesAtGap t ht) := by
  classical
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.1 hn with ⟨x, _hx, rfl⟩
    let j := (selectedClustering t ht x).gap
    apply Finset.mem_biUnion.2
    refine ⟨j, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.2
    exact ⟨⟨x, rfl⟩, Finset.mem_univ _, rfl⟩
  · intro hn
    rcases Finset.mem_biUnion.1 hn with ⟨j, _hj, hn⟩
    rcases Finset.mem_image.1 hn with ⟨x, _hx, rfl⟩
    exact Finset.mem_image.2 ⟨x.1, Finset.mem_univ _, rfl⟩

/-! ## The state attached to one gap -/

private theorem selected_exceptional_card_le
    {t : ℕ} (ht : 16 ≤ t) (j : Fin (clusterJ t + 1))
    (x : ProfilesAtGap t ht j) :
    #(x.1.exceptionalSet
        (clusterRho t (selectedClustering t ht x.1).gap.succ)) ≤
      gapExceptionalBudget t j := by
  have h := x.1.exceptionalSet_card_le
    (clusterRho t (selectedClustering t ht x.1).gap.succ)
  simpa [gapExceptionalBudget, x.2] using h

private theorem selected_center_card_le
    {t : ℕ} (ht : 16 ≤ t) (j : Fin (clusterJ t + 1))
    (x : ProfilesAtGap t ht j) :
    #((selectedClustering t ht x.1).state.centerPairSet
        (clusterRho t j) (selectedClustering t ht x.1).count_le) ≤
      centerQueryBound t := by
  let C := selectedClustering t ht x.1
  have hsmall : ∀ i ∈ C.state.packed.residual,
      #(C.state.packed.componentFiber (x.1.proximityGraph (clusterRho t j)) i) <
        clusterH t := by
    intro i hi
    apply C.state.packed.componentFiber_card_lt _ _ i hi
    intro A hA hconn
    apply C.residual_small A hA
    simpa [C, x.2] using hconn
  have h := C.state.centerPairSet_card_le C.count_le hsmall
  simpa [C, centerQueryBound] using h

private noncomputable def encodeAtGap
    {t : ℕ} (ht : 16 ≤ t) (j : Fin (clusterJ t + 1))
    (x : ProfilesAtGap t ht j) :
    ClusterEncoding (facetBudget t) (dyadicB t) (clusterJ t)
      (gapExceptionalBudget t j) (centerQueryBound t) :=
  (selectedClustering t ht x.1).state.toClusterEncoding j
    (selectedClustering t ht x.1).count_le
    (selected_exceptional_card_le ht j x)
    (selected_center_card_le ht j x)

private theorem card_gapEncoding_le
    {t : ℕ} (ht : 16 ≤ t) (j : Fin (clusterJ t + 1)) :
    Fintype.card
        (ClusterEncoding (facetBudget t) (dyadicB t) (clusterJ t)
          (gapExceptionalBudget t j) (centerQueryBound t)) ≤
      2 ^ gapStateCost t j := by
  apply card_clusterEncoding_le_two_pow_of_bounds
  · exact shape_base_le_two_pow_three_budget_sq ht
  · exact exception_base_le_two_pow_budget_add_two ht le_rfl
  · exact center_base_le_two_pow_four_budget ht

private theorem encodeAtGap_fiber_diameter
    {t : ℕ} (ht : 16 ≤ t) (j : Fin (clusterJ t + 1))
    (x y : ProfilesAtGap t ht j)
    (hcode : encodeAtGap ht j x = encodeAtGap ht j y) :
    Int.natAbs ((x.1.value : ℤ) - (y.1.value : ℤ)) ≤
      gapFiberDiameter t j := by
  let X := selectedClustering t ht x.1
  let Y := selectedClustering t ht y.1
  have hshape :
      X.state.clusterShape j (clusterRho t j) X.count_le =
        Y.state.clusterShape j (clusterRho t j) Y.count_le := by
    exact congrArg ClusterEncoding.shape hcode
  have hexception :
      exceptionalSparseCode x.1
          (clusterRho t X.gap.succ) (selected_exceptional_card_le ht j x) =
        exceptionalSparseCode y.1
          (clusterRho t Y.gap.succ) (selected_exceptional_card_le ht j y) := by
    exact congrArg ClusterEncoding.exceptional hcode
  have hcenters :
      X.state.centerSparseCode (clusterRho t j) X.count_le
          (selected_center_card_le ht j x) =
        Y.state.centerSparseCode (clusterRho t j) Y.count_le
          (selected_center_card_le ht j y) := by
    exact congrArg ClusterEncoding.centers hcode
  apply value_natAbs_sub_le_of_codes_eq X.state Y.state
    X.count_le Y.count_le
    (selected_exceptional_card_le ht j x)
    (selected_exceptional_card_le ht j y)
    (selected_center_card_le ht j x)
    (selected_center_card_le ht j y)
    hexception hcenters
  · intro q
    exact isCenterQuery_iff_of_clusterShape_eq X.state Y.state j j
      X.count_le Y.count_le hshape q
  · intro q
    exact fixedKey_eq_of_clusterShape_eq X.state Y.state j j
      X.count_le Y.count_le hshape q

private theorem valuesAtGap_card_le
    {t : ℕ} (ht : 16 ≤ t) (j : Fin (clusterJ t + 1)) :
    #(valuesAtGap t ht j) ≤
      2 ^ (dyadicB t - clusterRho t j + gapStateCost t j +
        facetBudget t + 2) := by
  classical
  have himage := card_image_le_card_mul_of_fiber_diameter
    (encodeAtGap ht j) (fun x : ProfilesAtGap t ht j ↦ x.1.value)
    (gapFiberDiameter t j) (encodeAtGap_fiber_diameter ht j)
  calc
    #(valuesAtGap t ht j) ≤
        Fintype.card
            (ClusterEncoding (facetBudget t) (dyadicB t) (clusterJ t)
              (gapExceptionalBudget t j) (centerQueryBound t)) *
          (gapFiberDiameter t j + 1) := by
      simpa [valuesAtGap] using himage
    _ ≤ 2 ^ gapStateCost t j *
        2 ^ (dyadicB t - clusterRho t j + facetBudget t + 2) := by
      exact Nat.mul_le_mul (card_gapEncoding_le ht j)
        (tail_diameter_succ_le_two_pow t j)
    _ = 2 ^ (dyadicB t - clusterRho t j + gapStateCost t j +
        facetBudget t + 2) := by
      rw [← pow_add]
      congr 1
      omega

private theorem valuesAtGap_card_le_common
    {t : ℕ} (ht : 16 ≤ t) (j : Fin (clusterJ t + 1)) :
    #(valuesAtGap t ht j) ≤
      2 ^ (dyadicB t - 2 - facetBudget t) := by
  apply (valuesAtGap_card_le ht j).trans
  apply Nat.pow_le_pow_right (by norm_num)
  have hj : j.val + 1 ≤ clusterL t + 1 := by
    have hjlt := j.isLt
    simp only [clusterL]
    omega
  have htotal := total_image_exponent_le_B_sub_two
    (t := t) (j := j.val) ht hj
  dsimp only [gapExceptionalBudget, gapStateCost] at *
  omega

private theorem facetBudget_le_dyadicB_sub_two
    {t : ℕ} (ht : 16 ≤ t) :
    facetBudget t ≤ dyadicB t - 2 := by
  have htotal := total_image_exponent_le_B_sub_two
    (t := t) (j := 0) ht (by simp [clusterL])
  dsimp only [gapExceptionalBudget, gapStateCost] at htotal
  omega

/-- Exact-`K` profiles occupy at most a quarter of the dyadic residue ring.
The proof first partitions them by their deterministic stable gap. -/
theorem boundedValues_dyadic_card_le
    {t : ℕ} (ht : 16 ≤ t) :
    #(boundedValues (facetBudget t) (dyadicB t)) ≤
      2 ^ (dyadicB t - 2) := by
  classical
  rw [boundedValues_eq_biUnion_valuesAtGap t ht]
  have hK := facetBudget_le_dyadicB_sub_two ht
  have hJ : clusterJ t + 1 ≤ 2 ^ facetBudget t := by
    have hJK := clusterJ_le_facetBudget t
    have hpow := (facetBudget t).lt_two_pow_self
    omega
  calc
    #((Finset.univ : Finset (Fin (clusterJ t + 1))).biUnion
        (valuesAtGap t ht)) ≤
        ∑ j : Fin (clusterJ t + 1), #(valuesAtGap t ht j) :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin (clusterJ t + 1),
        2 ^ (dyadicB t - 2 - facetBudget t) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact valuesAtGap_card_le_common ht j
    _ = (clusterJ t + 1) *
        2 ^ (dyadicB t - 2 - facetBudget t) := by simp
    _ ≤ 2 ^ facetBudget t *
        2 ^ (dyadicB t - 2 - facetBudget t) := by gcongr
    _ = 2 ^ (dyadicB t - 2) := by
      rw [← pow_add]
      congr 1
      omega

/-- Exact ambient-coordinate residues satisfy the same quarter-ring bound. -/
theorem boundedResidues_dyadic_card_le
    {t : ℕ} (ht : 16 ≤ t) :
    #(boundedResidues (facetBudget t) (dyadicB t)) ≤
      2 ^ (dyadicB t - 2) :=
  (boundedResidues_card_le_boundedValues_card _ _).trans
    (boundedValues_dyadic_card_le ht)

private theorem quarter_add_one_lt_half
    {t : ℕ} (ht : 16 ≤ t) :
    2 ^ (dyadicB t - 2) + 1 < 2 ^ (dyadicB t - 1) := by
  have hq : 2 ≤ dyadicQ t := by
    have hlarge := two_pow_sixteen_le_dyadicQ ht
    norm_num at hlarge ⊢
    omega
  have hB : 3 ≤ dyadicB t := by
    calc
      3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ dyadicQ t := Nat.pow_le_pow_right (by norm_num) hq
      _ = dyadicB t := by rfl
  have hpow : 2 ≤ 2 ^ (dyadicB t - 2) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (dyadicB t - 2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show dyadicB t - 1 = (dyadicB t - 2) + 1 by omega, pow_succ]
  omega

/-- The full family of profiles with at most the facet budget occupies
strictly less than half of the dyadic residue ring. -/
theorem boundedResiduesUpTo_dyadic_card_lt
    {t : ℕ} (ht : 16 ≤ t) :
    #(boundedResiduesUpTo (facetBudget t) (dyadicB t)) <
      2 ^ (dyadicB t - 1) := by
  calc
    #(boundedResiduesUpTo (facetBudget t) (dyadicB t)) ≤
        #(boundedResidues (facetBudget t) (dyadicB t)) + 1 :=
      boundedResiduesUpTo_card_le_exact_add_one (facetBudget_pos ht)
    _ ≤ 2 ^ (dyadicB t - 2) + 1 := by
      gcongr
      exact boundedResidues_dyadic_card_le ht
    _ < 2 ^ (dyadicB t - 1) := quarter_add_one_lt_half ht

/-- The finite cluster construction discharges the residue-sparsity premise
of the analytic endpoint, without any additional hypothesis. -/
theorem eventuallySparseDyadicProfiles : EventuallySparseDyadicProfiles := by
  filter_upwards [eventually_ge_atTop (16 : ℕ)] with t ht
  exact boundedResiduesUpTo_dyadic_card_lt ht

/-- An unconditional infinitely-often lower bound with an explicit constant. -/
theorem matchingLowerBoundInfinitelyOften :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (1 / 4096 : ℝ) * AntichainOfGivenSize.improvedScale n ≤
        (AntichainOfGivenSize.alpha n : ℝ) :=
  matchingLowerBoundInfinitelyOften_of_eventuallySparse
    eventuallySparseDyadicProfiles

/-- The matching asymptotic lower bound, in named proposition form. -/
theorem hasMatchingLowerBoundInfinitelyOften :
    HasMatchingLowerBoundInfinitelyOften :=
  hasMatchingLowerBoundInfinitelyOften_of_eventuallySparse
    eventuallySparseDyadicProfiles

end AntichainOfGivenSize.ClusterLowerBound
