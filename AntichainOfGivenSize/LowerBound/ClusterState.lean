import AntichainOfGivenSize.LowerBound.SparseEncoding

/-!
# Finite states for cluster compression

This is the information retained from a bounded Venn profile after choosing a
stable connected-cluster decomposition.  The state is intentionally an
overencoding: arbitrary owner/component maps are allowed.  That makes its
cardinality transparent, while the semantic relation in the obstruction proof
only uses the states actually produced by profiles.
-/

open Finset Fintype

namespace AntichainOfGivenSize.ClusterLowerBound

/-- Structural labels: a stable gap, a possible cluster owner for every
facet, and a residual-component label. -/
structure ClusterShape (K J : ℕ) where
  gap : Fin (J + 1)
  owner : Fin K → Option (Fin J)
  component : Fin K → Fin (K + 1)

noncomputable instance (K J : ℕ) : Fintype (ClusterShape K J) :=
  Fintype.ofInjective
    (fun s ↦ (s.gap, s.owner, s.component)) (by
      intro x y h
      cases x
      cases y
      simp_all)

noncomputable instance (K J : ℕ) : DecidableEq (ClusterShape K J) :=
  Classical.decEq _

/-- Compressed query keys: cluster labels on the left and individual
residual-facet labels on the right. -/
abbrev ClusterKey (K J : ℕ) := Finset (Fin J ⊕ Fin K)

/-- A complete finite state.  `U` bounds the exceptional atom mass and `M`
bounds the number of recorded center-query/exponent pairs. -/
structure ClusterEncoding (K B J U M : ℕ) where
  shape : ClusterShape K J
  exceptional : SparseCode (Finset (Fin K)) U
  centers : SparseCode (ClusterKey K J × Fin (B + 1)) M

noncomputable instance (K B J U M : ℕ) :
    Fintype (ClusterEncoding K B J U M) :=
  Fintype.ofInjective
    (fun s ↦ (s.shape, s.exceptional, s.centers)) (by
      intro x y h
      cases x
      cases y
      simp_all)

noncomputable instance (K B J U M : ℕ) :
    DecidableEq (ClusterEncoding K B J U M) :=
  Classical.decEq _

theorem card_clusterShape (K J : ℕ) :
    Fintype.card (ClusterShape K J) =
      (J + 1) * (J + 1) ^ K * (K + 1) ^ K := by
  let e : ClusterShape K J ≃
      Fin (J + 1) × (Fin K → Option (Fin J)) × (Fin K → Fin (K + 1)) :=
    { toFun := fun s ↦ (s.gap, s.owner, s.component)
      invFun := fun s ↦ ⟨s.1, s.2.1, s.2.2⟩
      left_inv := by intro s; cases s; rfl
      right_inv := by intro s; rcases s with ⟨_, _, _⟩; rfl }
  rw [Fintype.card_congr e]
  simp [mul_assoc]

theorem card_clusterEncoding_le (K B J U M : ℕ) :
    Fintype.card (ClusterEncoding K B J U M) ≤
      ((J + 1) * (J + 1) ^ K * (K + 1) ^ K) *
      (2 ^ K + 1 + U) ^ U *
      (2 ^ (J + K) * (B + 1) + 1 + M) ^ M := by
  let e : ClusterEncoding K B J U M ≃
      ClusterShape K J × SparseCode (Finset (Fin K)) U ×
        SparseCode (ClusterKey K J × Fin (B + 1)) M :=
    { toFun := fun s ↦ (s.shape, s.exceptional, s.centers)
      invFun := fun s ↦ ⟨s.1, s.2.1, s.2.2⟩
      left_inv := by intro s; cases s; rfl
      right_inv := by intro s; rcases s with ⟨_, _, _⟩; rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod,
    card_clusterShape]
  have hU : Fintype.card (SparseCode (Finset (Fin K)) U) ≤
      (2 ^ K + 1 + U) ^ U := by
    simpa using (card_sparseCode_le (α := Finset (Fin K)) U)
  have hM : Fintype.card
      (SparseCode (ClusterKey K J × Fin (B + 1)) M) ≤
      (2 ^ (J + K) * (B + 1) + 1 + M) ^ M := by
    simpa [ClusterKey, pow_add] using
      (card_sparseCode_le (α := ClusterKey K J × Fin (B + 1)) M)
  calc
    (J + 1) * (J + 1) ^ K * (K + 1) ^ K *
        (Fintype.card (SparseCode (Finset (Fin K)) U) *
          Fintype.card (SparseCode (ClusterKey K J × Fin (B + 1)) M)) ≤
      (J + 1) * (J + 1) ^ K * (K + 1) ^ K *
        ((2 ^ K + 1 + U) ^ U *
          (2 ^ (J + K) * (B + 1) + 1 + M) ^ M) := by
      gcongr
    _ = ((J + 1) * (J + 1) ^ K * (K + 1) ^ K) *
        (2 ^ K + 1 + U) ^ U *
        (2 ^ (J + K) * (B + 1) + 1 + M) ^ M := by ring

/-- Convenient power-of-two form of the preceding cardinality estimate. -/
theorem card_clusterEncoding_le_two_pow_of_bounds (K B J U M : ℕ)
    (hshape : (J + 1) * (J + 1) ^ K * (K + 1) ^ K ≤ 2 ^ (3 * K ^ 2))
    (hexception : 2 ^ K + 1 + U ≤ 2 ^ (K + 2))
    (hcenter : 2 ^ (J + K) * (B + 1) + 1 + M ≤ 2 ^ (4 * K)) :
    Fintype.card (ClusterEncoding K B J U M) ≤
      2 ^ (3 * K ^ 2 + (K + 2) * U + 4 * K * M) := by
  calc
    Fintype.card (ClusterEncoding K B J U M) ≤
        ((J + 1) * (J + 1) ^ K * (K + 1) ^ K) *
        (2 ^ K + 1 + U) ^ U *
        (2 ^ (J + K) * (B + 1) + 1 + M) ^ M :=
      card_clusterEncoding_le K B J U M
    _ ≤ 2 ^ (3 * K ^ 2) * (2 ^ (K + 2)) ^ U *
        (2 ^ (4 * K)) ^ M := by gcongr
    _ = 2 ^ (3 * K ^ 2 + (K + 2) * U + 4 * K * M) := by
      simp only [← pow_mul, ← pow_add]

end AntichainOfGivenSize.ClusterLowerBound
