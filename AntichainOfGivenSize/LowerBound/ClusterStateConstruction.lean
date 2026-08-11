import AntichainOfGivenSize.LowerBound.ClusterFiber

/-!
# Constructing the finite cluster encoding

This module turns the semantic cluster data of `ClusterEncoding` into the
finite structural and sparse-code state of `ClusterState`.  It also proves
the uniform bound on the number of centered key/exponent pairs.
-/

open scoped BigOperators
open Finset

namespace AntichainOfGivenSize.ClusterLowerBound

open AntichainOfGivenSize.ClusterCore

/-- The right half of a compressed key is exactly the selected residual
part of the query. -/
theorem ProfileClusterState.fixedKey_toRight
    {K B rho h r J : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rho h r) (hr : r ≤ J)
    (t : IEQuery (Finset.univ : Finset (Fin K))) :
    (S.fixedKey hr t).toRight = S.packed.residualPart t := by
  classical
  ext i
  simp only [Finset.mem_toRight, ProfileClusterState.fixedKey,
    ProfileClusterState.key, compressionKey, Finset.mem_image,
    PackedClusters.residualPart, Finset.mem_inter]
  constructor
  · rintro ⟨z, ⟨j, hjt, hjz⟩, hzi⟩
    cases z with
    | inl a => simp [embedClusterRole] at hzi
    | inr k =>
      simp only [embedClusterRole, Sum.inr.injEq] at hzi
      have hrole := (S.packed.role_eq_inr_iff j k).1 hjz
      have hji : j = i := hrole.1.trans hzi
      refine ⟨?_, ?_⟩
      · simpa [hji] using hjt
      · simpa [hji] using hrole.2
  · rintro ⟨hit, hiR⟩
    refine ⟨Sum.inr i, ⟨i, hit, ?_⟩, rfl⟩
    exact (S.packed.role_eq_inr_iff i i).2 ⟨rfl, hiR⟩

/-- The left half of every fixed key is one of the `2^J` subsets of the
ambient cluster-label alphabet. -/
theorem ProfileClusterState.fixedKey_toLeft_mem_powerset
    {K B rho h r J : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rho h r) (hr : r ≤ J)
    (t : IEQuery (Finset.univ : Finset (Fin K))) :
    (S.fixedKey hr t).toLeft ∈
      (Finset.univ : Finset (Fin J)).powerset := by
  exact Finset.mem_powerset.2 (Finset.subset_univ _)

/-- All residual supports which can occur in a center key.  The empty support
is recorded separately; every nonempty support is assigned to one of its
vertices and lies in that vertex's component fiber. -/
noncomputable def PackedClusters.centerRightKeys
    {K h r : ℕ} {gFine : SimpleGraph (Fin K)}
    (g : SimpleGraph (Fin K)) (P : PackedClusters gFine h r) :
    Finset (Finset (Fin K)) :=
  insert ∅ <| P.residual.biUnion fun i ↦
    (P.componentFiber g i).powerset

theorem PackedClusters.card_centerRightKeys_le
    {K h r : ℕ} {gFine : SimpleGraph (Fin K)}
    (g : SimpleGraph (Fin K)) (P : PackedClusters gFine h r)
    (hsmall : ∀ i ∈ P.residual, #(P.componentFiber g i) < h) :
    #(P.centerRightKeys g) ≤ 1 + K * 2 ^ h := by
  classical
  unfold PackedClusters.centerRightKeys
  calc
    #(insert ∅ (P.residual.biUnion fun i ↦
        (P.componentFiber g i).powerset)) ≤
        #(P.residual.biUnion fun i ↦
          (P.componentFiber g i).powerset) + 1 := Finset.card_insert_le _ _
    _ ≤ K * 2 ^ h + 1 := by
      have hbase :
          #(P.residual.biUnion fun i ↦ (P.componentFiber g i).powerset) ≤
            K * 2 ^ h := by
        calc
          #(P.residual.biUnion fun i ↦ (P.componentFiber g i).powerset) ≤
              #P.residual * 2 ^ h := by
            apply Finset.card_biUnion_le_card_mul
            intro i hiR
            simpa using Nat.pow_le_pow_right (by omega : 0 < 2)
              (Nat.le_of_lt (hsmall i hiR))
          _ ≤ K * 2 ^ h := by
            gcongr
            simpa using Finset.card_le_univ P.residual
      exact Nat.add_le_add_right hbase 1
    _ = 1 + K * 2 ^ h := by omega

theorem ProfileClusterState.fixedKey_toRight_mem_centerRightKeys
    {K B rhoFine h r J rho : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r) (hr : r ≤ J)
    (t : IEQuery (Finset.univ : Finset (Fin K)))
    (ht : IsCenterQuery (x.proximityGraph rho) S.packed t) :
    (S.fixedKey hr t).toRight ∈
      S.packed.centerRightKeys (x.proximityGraph rho) := by
  classical
  rw [S.fixedKey_toRight hr t]
  by_cases hQ : S.packed.residualPart t = ∅
  · simp [hQ, PackedClusters.centerRightKeys]
  · have hQne : (S.packed.residualPart t).Nonempty := Finset.nonempty_iff_ne_empty.2 hQ
    obtain ⟨i, hiQ⟩ := hQne
    apply Finset.mem_insert.2
    right
    apply Finset.mem_biUnion.2
    refine ⟨i, (Finset.mem_inter.1 hiQ).2, Finset.mem_powerset.2 ?_⟩
    intro j hjQ
    have hiR : i ∈ S.packed.residual := (Finset.mem_inter.1 hiQ).2
    have hjR : j ∈ S.packed.residual := (Finset.mem_inter.1 hjQ).2
    apply (PackedClusters.mem_componentFiber
      (x.proximityGraph rho) S.packed i j).2
    refine ⟨hjR, ?_⟩
    exact (S.packed.componentLabel_eq_iff (x.proximityGraph rho) hjR hiR).2
      (ht j hjQ i hiQ)

/-- Projection to the fixed key is injective on the center transcript: role
agreement makes the regular exponent a function of that key. -/
theorem ProfileClusterState.centerPair_fst_injOn
    {K B rhoFine h r J rho : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r) (hr : r ≤ J) :
    Set.InjOn Prod.fst
      (↑(S.centerPairSet rho hr) : Set (ClusterKey K J × Fin (B + 1))) := by
  classical
  intro p hp q hq hpq
  change p ∈ S.centerPairSet rho hr at hp
  change q ∈ S.centerPairSet rho hr at hq
  unfold ProfileClusterState.centerPairSet at hp hq
  rcases Finset.mem_image.1 hp with ⟨t, ht, rfl⟩
  rcases Finset.mem_image.1 hq with ⟨u, hu, rfl⟩
  have hfixed : S.fixedKey hr t = S.fixedKey hr u := hpq
  have hraw : S.key t = S.key u :=
    (S.fixedKey_eq_iff_key_eq hr t u).1 hfixed
  have hexp := S.regularIntersectionSize_eq_of_key_eq t u hraw
  apply Prod.ext hfixed
  exact Fin.ext hexp

/-- Sharp finite count of distinct centered key/exponent pairs, assuming the
residual component fibers have size `< h`. -/
theorem ProfileClusterState.centerPairSet_card_le
    {K B rhoFine h r J rho : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r) (hr : r ≤ J)
    (hsmall : ∀ i ∈ S.packed.residual,
      #(S.packed.componentFiber (x.proximityGraph rho) i) < h) :
    #(S.centerPairSet rho hr) ≤ 2 ^ J * (1 + K * 2 ^ h) := by
  classical
  let target : Finset (Finset (Fin J) × Finset (Fin K)) :=
    (Finset.univ : Finset (Fin J)).powerset.product
      (S.packed.centerRightKeys (x.proximityGraph rho))
  let parts : ClusterKey K J × Fin (B + 1) →
      Finset (Fin J) × Finset (Fin K) := fun p ↦ Finset.sumEquiv p.1
  calc
    #(S.centerPairSet rho hr) ≤ #target := by
      apply Finset.card_le_card_of_injOn parts
      · intro p hp
        unfold ProfileClusterState.centerPairSet at hp
        rcases Finset.mem_image.1 hp with ⟨t, ht, rfl⟩
        apply Finset.mem_product.2
        refine ⟨S.fixedKey_toLeft_mem_powerset hr t, ?_⟩
        exact S.fixedKey_toRight_mem_centerRightKeys hr t
          (Finset.mem_filter.1 ht).2
      · intro p hp q hq hpq
        apply S.centerPair_fst_injOn hr hp hq
        exact Finset.sumEquiv.injective hpq
    _ = 2 ^ J * #(S.packed.centerRightKeys (x.proximityGraph rho)) := by
      simp [target]
    _ ≤ 2 ^ J * (1 + K * 2 ^ h) := by
      gcongr
      exact S.packed.card_centerRightKeys_le _ hsmall

/-- More convenient (slightly coarser) power-of-two form of the center-key
bound. -/
theorem ProfileClusterState.centerPairSet_card_le_coarse
    {K B rhoFine h r J rho : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r) (hr : r ≤ J)
    (hsmall : ∀ i ∈ S.packed.residual,
      #(S.packed.componentFiber (x.proximityGraph rho) i) < h) :
    #(S.centerPairSet rho hr) ≤ (K + 1) * 2 ^ (J + h) := by
  apply (S.centerPairSet_card_le hr hsmall).trans
  have hone : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  calc
    2 ^ J * (1 + K * 2 ^ h) ≤
        2 ^ J * ((K + 1) * 2 ^ h) := by
      gcongr
      calc
        1 + K * 2 ^ h ≤ 2 ^ h + K * 2 ^ h :=
          Nat.add_le_add_right hone _
        _ = (K + 1) * 2 ^ h := by ring
    _ = (K + 1) * 2 ^ (J + h) := by
      rw [pow_add]
      ring

/-! ## The actual finite structural state -/

/-- Read a query role from an overencoding shape. -/
def ClusterShape.queryRole {K J : ℕ} (s : ClusterShape K J)
    (i : Fin K) : Fin J ⊕ Fin K :=
  match s.owner i with
  | some a => Sum.inl a
  | none => Sum.inr i

/-- Structural state produced by a packed profile at a chosen stable gap. -/
noncomputable def ProfileClusterState.clusterShape
    {K B rhoFine h r J : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r)
    (gap : Fin (J + 1)) (rhoCoarse : ℕ) (hr : r ≤ J) :
    ClusterShape K J where
  gap := gap
  owner := fun i ↦
    match S.packed.role i with
    | Sum.inl a => some ⟨a.1, a.2.trans_le hr⟩
    | Sum.inr _ => none
  component := S.packed.componentLabel (x.proximityGraph rhoCoarse)

theorem ProfileClusterState.clusterShape_owner_eq_none_iff
    {K B rhoFine h r J : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r)
    (gap : Fin (J + 1)) (rhoCoarse : ℕ) (hr : r ≤ J)
    (i : Fin K) :
    (S.clusterShape gap rhoCoarse hr).owner i = none ↔
      i ∈ S.packed.residual := by
  classical
  by_cases hexists : ∃ a : Fin r, i ∈ S.packed.cluster a
  · have hiR : i ∉ S.packed.residual := by
      intro hi
      exact ((S.packed.mem_residual_iff i).1 hi
        (Classical.choose hexists)) (Classical.choose_spec hexists)
    simp [ProfileClusterState.clusterShape, PackedClusters.role,
      hexists, hiR]
  · have hiR : i ∈ S.packed.residual :=
      (S.packed.mem_residual_iff i).2 fun a hia ↦ hexists ⟨a, hia⟩
    simp [ProfileClusterState.clusterShape, PackedClusters.role,
      hexists, hiR]

theorem ProfileClusterState.clusterShape_queryRole
    {K B rhoFine h r J : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r)
    (gap : Fin (J + 1)) (rhoCoarse : ℕ) (hr : r ≤ J)
    (i : Fin K) :
    (S.clusterShape gap rhoCoarse hr).queryRole i =
      embedClusterRole (K := K) hr (S.packed.role i) := by
  classical
  by_cases hexists : ∃ a : Fin r, i ∈ S.packed.cluster a
  · simp [ProfileClusterState.clusterShape, ClusterShape.queryRole,
      PackedClusters.role, embedClusterRole, hexists]
  · simp [ProfileClusterState.clusterShape, ClusterShape.queryRole,
      PackedClusters.role, embedClusterRole, hexists]

theorem ProfileClusterState.fixedKey_eq_shapeKey
    {K B rhoFine h r J : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r)
    (gap : Fin (J + 1)) (rhoCoarse : ℕ) (hr : r ≤ J)
    (t : IEQuery (Finset.univ : Finset (Fin K))) :
    S.fixedKey hr t =
      compressionKey (S.clusterShape gap rhoCoarse hr).queryRole t := by
  classical
  unfold ProfileClusterState.fixedKey ProfileClusterState.key compressionKey
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i hi
  exact S.clusterShape_queryRole gap rhoCoarse hr i |>.symm

/-- Equal produced shapes force identical fixed compressed keys. -/
theorem fixedKey_eq_of_clusterShape_eq
    {K B J : ℕ}
    {rhoFineX hX rX rhoFineY hY rY rhoX rhoY : ℕ}
    {x y : BoundedProfile K B}
    (SX : ProfileClusterState x rhoFineX hX rX)
    (SY : ProfileClusterState y rhoFineY hY rY)
    (gapX gapY : Fin (J + 1)) (hrX : rX ≤ J) (hrY : rY ≤ J)
    (hshape : SX.clusterShape gapX rhoX hrX =
      SY.clusterShape gapY rhoY hrY)
    (t : IEQuery (Finset.univ : Finset (Fin K))) :
    SX.fixedKey hrX t = SY.fixedKey hrY t := by
  rw [SX.fixedKey_eq_shapeKey gapX rhoX hrX,
    SY.fixedKey_eq_shapeKey gapY rhoY hrY, hshape]

/-- Equal produced shapes also force exactly the same center-query predicate. -/
theorem isCenterQuery_iff_of_clusterShape_eq
    {K B J : ℕ}
    {rhoFineX hX rX rhoFineY hY rY rhoX rhoY : ℕ}
    {x y : BoundedProfile K B}
    (SX : ProfileClusterState x rhoFineX hX rX)
    (SY : ProfileClusterState y rhoFineY hY rY)
    (gapX gapY : Fin (J + 1)) (hrX : rX ≤ J) (hrY : rY ≤ J)
    (hshape : SX.clusterShape gapX rhoX hrX =
      SY.clusterShape gapY rhoY hrY)
    (t : IEQuery (Finset.univ : Finset (Fin K))) :
    IsCenterQuery (x.proximityGraph rhoX) SX.packed t ↔
      IsCenterQuery (y.proximityGraph rhoY) SY.packed t := by
  classical
  have howner :
      (SX.clusterShape gapX rhoX hrX).owner =
        (SY.clusterShape gapY rhoY hrY).owner :=
    congrArg ClusterShape.owner hshape
  have hcomponent :
      SX.packed.componentLabel (x.proximityGraph rhoX) =
        SY.packed.componentLabel (y.proximityGraph rhoY) :=
    congrArg ClusterShape.component hshape
  have hres : SX.packed.residual = SY.packed.residual := by
    ext i
    have hx := SX.clusterShape_owner_eq_none_iff gapX rhoX hrX i
    have hy := SY.clusterShape_owner_eq_none_iff gapY rhoY hrY i
    constructor
    · intro hi
      apply hy.1
      rw [← howner]
      exact hx.2 hi
    · intro hi
      apply hx.1
      rw [howner]
      exact hy.2 hi
  constructor
  · intro ht i hiY j hjY
    have hiX : i ∈ SX.packed.residualPart t := by
      simpa [PackedClusters.residualPart, hres] using hiY
    have hjX : j ∈ SX.packed.residualPart t := by
      simpa [PackedClusters.residualPart, hres] using hjY
    have hiRX : i ∈ SX.packed.residual := (Finset.mem_inter.1 hiX).2
    have hjRX : j ∈ SX.packed.residual := (Finset.mem_inter.1 hjX).2
    have hiRY : i ∈ SY.packed.residual := by simpa [hres] using hiRX
    have hjRY : j ∈ SY.packed.residual := by simpa [hres] using hjRX
    apply (SY.packed.componentLabel_eq_iff
      (y.proximityGraph rhoY) hiRY hjRY).1
    have hlabelX := (SX.packed.componentLabel_eq_iff
      (x.proximityGraph rhoX) hiRX hjRX).2 (ht i hiX j hjX)
    exact (congrFun hcomponent i).symm.trans
      (hlabelX.trans (congrFun hcomponent j))
  · intro ht i hiX j hjX
    have hiY : i ∈ SY.packed.residualPart t := by
      simpa [PackedClusters.residualPart, hres] using hiX
    have hjY : j ∈ SY.packed.residualPart t := by
      simpa [PackedClusters.residualPart, hres] using hjX
    have hiRX : i ∈ SX.packed.residual := (Finset.mem_inter.1 hiX).2
    have hjRX : j ∈ SX.packed.residual := (Finset.mem_inter.1 hjX).2
    have hiRY : i ∈ SY.packed.residual := by simpa [hres] using hiRX
    have hjRY : j ∈ SY.packed.residual := by simpa [hres] using hjRX
    apply (SX.packed.componentLabel_eq_iff
      (x.proximityGraph rhoX) hiRX hjRX).1
    have hlabelY := (SY.packed.componentLabel_eq_iff
      (y.proximityGraph rhoY) hiRY hjRY).2 (ht i hiY j hjY)
    exact (congrFun hcomponent i).trans
      (hlabelY.trans (congrFun hcomponent j).symm)

/-- Assemble the structural data and the two sparse transcripts into the
finite overencoding counted in `ClusterState`. -/
noncomputable def ProfileClusterState.toClusterEncoding
    {K B J U M : ℕ} {rhoFine h r rhoCoarse : ℕ}
    {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r)
    (gap : Fin (J + 1)) (hr : r ≤ J)
    (hU : #(x.exceptionalSet rhoFine) ≤ U)
    (hM : #(S.centerPairSet rhoCoarse hr) ≤ M) :
    ClusterEncoding K B J U M where
  shape := S.clusterShape gap rhoCoarse hr
  exceptional := exceptionalSparseCode x rhoFine hU
  centers := S.centerSparseCode rhoCoarse hr hM

@[simp] theorem ProfileClusterState.toClusterEncoding_shape
    {K B J U M : ℕ} {rhoFine h r rhoCoarse : ℕ}
    {x : BoundedProfile K B}
    (S : ProfileClusterState x rhoFine h r)
    (gap : Fin (J + 1)) (hr : r ≤ J)
    (hU : #(x.exceptionalSet rhoFine) ≤ U)
    (hM : #(S.centerPairSet rhoCoarse hr) ≤ M) :
    (S.toClusterEncoding gap hr hU hM).shape =
      S.clusterShape gap rhoCoarse hr := rfl

/-- Equality of the actual finite encodings supplies every semantic premise
of the cluster-fiber estimate.  Thus one state fiber has the sharp diameter
coming from the noncenter inclusion--exclusion tail. -/
theorem value_natAbs_sub_le_of_clusterEncoding_eq
    {K B J U M : ℕ}
    {rhoFineX hX rX rhoFineY hY rY rho : ℕ}
    {x y : BoundedProfile K B}
    (SX : ProfileClusterState x rhoFineX hX rX)
    (SY : ProfileClusterState y rhoFineY hY rY)
    (gapX gapY : Fin (J + 1))
    (hrX : rX ≤ J) (hrY : rY ≤ J)
    (hUX : #(x.exceptionalSet rhoFineX) ≤ U)
    (hUY : #(y.exceptionalSet rhoFineY) ≤ U)
    (hMX : #(SX.centerPairSet rho hrX) ≤ M)
    (hMY : #(SY.centerPairSet rho hrY) ≤ M)
    (hstate : SX.toClusterEncoding gapX hrX hUX hMX =
      SY.toClusterEncoding gapY hrY hUY hMY) :
    Int.natAbs ((x.value : ℤ) - (y.value : ℤ)) ≤
      2 * (2 ^ K * 2 ^ (B - rho)) := by
  have hshape : SX.clusterShape gapX rho hrX =
      SY.clusterShape gapY rho hrY :=
    congrArg ClusterEncoding.shape hstate
  have hexception : exceptionalSparseCode x rhoFineX hUX =
      exceptionalSparseCode y rhoFineY hUY :=
    congrArg ClusterEncoding.exceptional hstate
  have hcenters : SX.centerSparseCode rho hrX hMX =
      SY.centerSparseCode rho hrY hMY :=
    congrArg ClusterEncoding.centers hstate
  apply value_natAbs_sub_le_of_codes_eq SX SY hrX hrY
    hUX hUY hMX hMY hexception hcenters
  · intro t
    exact isCenterQuery_iff_of_clusterShape_eq SX SY gapX gapY
      hrX hrY hshape t
  · intro t
    exact fixedKey_eq_of_clusterShape_eq SX SY gapX gapY
      hrX hrY hshape t

end AntichainOfGivenSize.ClusterLowerBound
