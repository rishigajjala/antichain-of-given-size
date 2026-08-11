import AntichainOfGivenSize.LowerBound.BoundedProfiles
import AntichainOfGivenSize.LowerBound.ClusterCore

/-!
# Encoding a bounded profile by connected clusters

This module instantiates the finite cluster core with the canonical generator
family of a bounded Venn profile.  It defines the cluster role map, proves
agreement outside a single global exceptional set, and establishes the exact
center/noncenter exponent dichotomy used by the counting argument.
-/

open scoped BigOperators symmDiff
open Finset

namespace AntichainOfGivenSize.ClusterLowerBound

open AntichainOfGivenSize.ClusterCore

/-! ## Canonical family and proximity graph -/

/-- Ground-set type of the canonical family attached to `x`. -/
abbrev BoundedProfile.Point {K B : ℕ} (x : BoundedProfile K B) :=
  VennProfile.ProfilePoint x.toNatProfile

/-- The canonical `K` generators represented by a bounded profile. -/
noncomputable def BoundedProfile.generators {K B : ℕ} (x : BoundedProfile K B) :
    Fin K → Finset x.Point :=
  VennProfile.profileGenerator x.toNatProfile

/-- Proximity graph of the canonical generators at loss scale `ρ`. -/
noncomputable def BoundedProfile.proximityGraph {K B : ℕ}
    (x : BoundedProfile K B) (ρ : ℕ) : SimpleGraph (Fin K) :=
  intersectionProximityGraph x.generators B ρ

/-- A single global exceptional set containing symmetric differences along
all proximity edges.  Restricting to cluster edges only would make it smaller;
the global version has the same `K²ρ` bound and makes the role proof direct. -/
noncomputable def BoundedProfile.exceptionalSet {K B : ℕ}
    (x : BoundedProfile K B) (ρ : ℕ) : Finset x.Point :=
  spanningExceptionalSet (x.proximityGraph ρ) x.generators

theorem BoundedProfile.exceptionalSet_card_le {K B : ℕ}
    (x : BoundedProfile K B) (ρ : ℕ) :
    #(x.exceptionalSet ρ) ≤ K * K * (2 * ρ) := by
  classical
  simpa [BoundedProfile.exceptionalSet, BoundedProfile.proximityGraph,
    BoundedProfile.generators] using
    (spanningExceptionalSet_card_le_of_proximity
      (T := x.proximityGraph ρ) (G := x.generators)
      (B := B) (ρ := ρ) le_rfl
      (fun i ↦ x.card_profileGenerator_le i))

/-! ## Packed clusters and their role map -/

/-- An indexed packing of `r` pairwise-disjoint connected clusters, each of
cardinality at least `h`. -/
structure PackedClusters {K : ℕ} (g : SimpleGraph (Fin K)) (h r : ℕ) where
  cluster : Fin r → Finset (Fin K)
  large : ∀ a : Fin r,
    IsLargeConnectedSet g (Finset.univ : Finset (Fin K)) h (cluster a)
  pairwise_disjoint : ∀ ⦃a b : Fin r⦄, a ≠ b →
    Disjoint (cluster a) (cluster b)

/-- Reindex a finset-valued connected packing by `Fin r`. -/
noncomputable def PackedClusters.ofFinset {K h r : ℕ}
    {g : SimpleGraph (Fin K)} (P : Finset (Finset (Fin K)))
    (hP : IsConnectedPacking g (Finset.univ : Finset (Fin K)) h P)
    (hcard : #P = r) : PackedClusters g h r := by
  let e : P ≃ Fin r := Finset.equivFinOfCardEq hcard
  refine
    { cluster := fun a ↦ (e.symm a).1
      large := fun a ↦ hP.1 _ (e.symm a).2
      pairwise_disjoint := ?_ }
  intro a b hab
  have hne : (e.symm a).1 ≠ (e.symm b).1 := by
    intro heq
    apply hab
    apply e.symm.injective
    exact Subtype.ext heq
  exact hP.2 (e.symm a).2 (e.symm b).2 hne

/-- Facets not placed in a packed cluster. -/
def PackedClusters.residual {K h r : ℕ} {g : SimpleGraph (Fin K)}
    (P : PackedClusters g h r) : Finset (Fin K) :=
  Finset.univ.filter fun i ↦ ∀ a : Fin r, i ∉ P.cluster a

/-- Clustered facets receive their cluster label; each residual facet receives
its own label.  The latter choice keeps every residual coordinate distinct. -/
noncomputable def PackedClusters.role {K h r : ℕ} {g : SimpleGraph (Fin K)}
    (P : PackedClusters g h r) (i : Fin K) : Fin r ⊕ Fin K :=
  if hi : ∃ a : Fin r, i ∈ P.cluster a then
    Sum.inl (Classical.choose hi)
  else
    Sum.inr i

@[simp] theorem PackedClusters.mem_residual_iff {K h r : ℕ}
    {g : SimpleGraph (Fin K)} (P : PackedClusters g h r) (i : Fin K) :
    i ∈ P.residual ↔ ∀ a : Fin r, i ∉ P.cluster a := by
  simp [PackedClusters.residual]

theorem PackedClusters.role_eq_inr_iff {K h r : ℕ}
    {g : SimpleGraph (Fin K)} (P : PackedClusters g h r) (i j : Fin K) :
    P.role i = Sum.inr j ↔ i = j ∧ i ∈ P.residual := by
  classical
  unfold PackedClusters.role
  split
  · rename_i hexists
    constructor
    · intro hfalse
      exact False.elim (Sum.inl_ne_inr hfalse)
    · rintro ⟨_, hiR⟩
      have hnot := (P.mem_residual_iff i).1 hiR (Classical.choose hexists)
      exact False.elim (hnot (Classical.choose_spec hexists))
  · rename_i hnone
    constructor
    · intro hij
      have hieq : i = j := Sum.inr.inj hij
      refine ⟨hieq, (P.mem_residual_iff i).2 ?_⟩
      intro a hia
      exact hnone ⟨a, hia⟩
    · rintro ⟨rfl, _⟩
      rfl

/-- Connectivity propagates equality of generator incidence along a cluster,
provided all graph-edge symmetric differences are exceptional. -/
theorem connectedOn_agrees_outside_globalExceptionalSet
    {ι V : Type*} [Fintype ι] [DecidableEq V]
    {g : SimpleGraph ι} {C : Finset ι} (hC : ConnectedOn g C)
    (G : ι → Finset V) {i j : ι} (hi : i ∈ C) (hj : j ∈ C)
    {v : V} (hv : v ∉ spanningExceptionalSet g G) :
    (v ∈ G i ↔ v ∈ G j) := by
  have hC' : (g.induce (C : Set ι)).Connected := hC
  have hreach : (g.induce (C : Set ι)).Reachable ⟨i, hi⟩ ⟨j, hj⟩ :=
    hC' ⟨i, hi⟩ ⟨j, hj⟩
  have hreachGlobal : g.Reachable i j :=
    hreach.map (SimpleGraph.Embedding.induce (C : Set ι)).toHom
  let p : g.Walk i j := Classical.choice hreachGlobal
  exact mem_iff_mem_of_walk_avoiding_exceptional p hv

/-- The cluster role map satisfies precisely the agreement condition required
by `compressionKey`. -/
theorem PackedClusters.roleAgreementOutside
    {K B h r : ℕ} (x : BoundedProfile K B) (ρ : ℕ)
    (P : PackedClusters (x.proximityGraph ρ) h r) :
    RoleAgreementOutside x.generators (x.exceptionalSet ρ) P.role := by
  classical
  intro i j hrole v hv
  unfold PackedClusters.role at hrole
  split at hrole
  next hi =>
    split at hrole
    next hj =>
      have ha : Classical.choose hi = Classical.choose hj := Sum.inl.inj hrole
      have himem : i ∈ P.cluster (Classical.choose hi) := Classical.choose_spec hi
      have hjmem : j ∈ P.cluster (Classical.choose hi) := by
        rw [ha]
        exact Classical.choose_spec hj
      exact connectedOn_agrees_outside_globalExceptionalSet
        (P.large (Classical.choose hi)).2.2 x.generators himem hjmem hv
    next hj =>
      exact False.elim (Sum.inl_ne_inr hrole)
  next hi =>
    split at hrole
    next hj =>
      exact False.elim (Sum.inr_ne_inl hrole)
    next hj =>
      have hij : i = j := Sum.inr.inj hrole
      subst j
      rfl

/-! ## Stable maximal packings -/

/-- Vertices used by a finset-valued packing. -/
def packingSupport {α : Type*} [DecidableEq α]
    (P : Finset (Finset α)) : Finset α :=
  P.biUnion id

@[simp] theorem PackedClusters.ofFinset_residual
    {K h r : ℕ} {g : SimpleGraph (Fin K)}
    (P : Finset (Finset (Fin K)))
    (hP : IsConnectedPacking g (Finset.univ : Finset (Fin K)) h P)
    (hcard : #P = r) :
    (PackedClusters.ofFinset P hP hcard).residual =
      (Finset.univ : Finset (Fin K)) \ packingSupport P := by
  classical
  let e : P ≃ Fin r := Finset.equivFinOfCardEq hcard
  ext i
  simp only [PackedClusters.mem_residual_iff, Finset.mem_sdiff,
    Finset.mem_univ, true_and, packingSupport, Finset.mem_biUnion]
  constructor
  · intro hi hsupport
    rcases hsupport with ⟨C, hCP, hiC⟩
    have hnot := hi (e ⟨C, hCP⟩)
    apply hnot
    simpa [PackedClusters.ofFinset, e] using hiC
  · intro hsupport a hiC
    apply hsupport
    refine ⟨(e.symm a).1, (e.symm a).2, ?_⟩
    simpa [PackedClusters.ofFinset, e] using hiC

theorem hasConnectedPacking_zero {α : Type*} [DecidableEq α]
    (g : SimpleGraph α) (active : Finset α) (h : ℕ) :
    HasConnectedPacking g active h 0 := by
  refine ⟨∅, ?_, rfl⟩
  simp [IsConnectedPacking]

/-- At a common stable gap, choose a packing of maximal cardinality at the
fine scale.  If its cardinality is below `J`, it cannot be enlarged even at
the coarse scale. -/
theorem exists_stable_maximal_packing
    {α V : Type*} [DecidableEq α] [DecidableEq V]
    (G : α → Finset V) (active : Finset α) (B h J : ℕ)
    (ρ : Fin (J + 2) → ℕ) (hρ : Antitone ρ) :
    ∃ j : Fin (J + 1), ∃ r : ℕ,
      r ≤ J ∧
      HasConnectedPacking
        (intersectionProximityGraph G B (ρ j.succ)) active h r ∧
      (r < J → ¬HasConnectedPacking
        (intersectionProximityGraph G B (ρ j.castSucc)) active h (r + 1)) := by
  classical
  rcases exists_packing_stable_gap G active B h J ρ hρ with ⟨j, hj⟩
  let fine : SimpleGraph α := intersectionProximityGraph G B (ρ j.succ)
  let coarse : SimpleGraph α := intersectionProximityGraph G B (ρ j.castSucc)
  let good : ℕ → Prop := fun r ↦ HasConnectedPacking fine active h r
  let r : ℕ := Nat.findGreatest good J
  have hzero : good 0 := hasConnectedPacking_zero fine active h
  have hrle : r ≤ J := Nat.findGreatest_le J
  have hrgood : good r := Nat.findGreatest_spec (Nat.zero_le J) hzero
  refine ⟨j, r, hrle, hrgood, ?_⟩
  intro hrJ hcoarse
  have hfine : HasConnectedPacking fine active h (r + 1) := by
    let s : Fin J := ⟨r, hrJ⟩
    exact (hj s).1 hcoarse
  exact Nat.findGreatest_is_greatest (P := good)
    (Nat.lt_succ_self r) (Nat.succ_le_iff.2 hrJ) hfine

/-- Adding a large connected set disjoint from the current support enlarges a
packing by one. -/
theorem hasConnectedPacking_succ_of_residual_large
    {α : Type*} [DecidableEq α] {gFine gCoarse : SimpleGraph α}
    {active : Finset α} {h r : ℕ} (hpos : 0 < h)
    (hmono : gFine ≤ gCoarse) {P : Finset (Finset α)}
    (hP : IsConnectedPacking gFine active h P) (hcard : #P = r)
    {C : Finset α} (hC : IsLargeConnectedSet gCoarse active h C)
    (hCres : C ⊆ active \ packingSupport P) :
    HasConnectedPacking gCoarse active h (r + 1) := by
  classical
  have hdisj : ∀ D ∈ P, Disjoint C D := by
    intro D hDP
    rw [Finset.disjoint_left]
    intro v hvC hvD
    have hvRes := Finset.mem_sdiff.1 (hCres hvC)
    apply hvRes.2
    exact Finset.mem_biUnion.2 ⟨D, hDP, hvD⟩
  have hCnot : C ∉ P := by
    intro hCP
    have hself : Disjoint C C := hdisj C hCP
    have hCempty : C = ∅ := (Finset.disjoint_self_iff_empty C).1 hself
    have : h ≤ 0 := by simpa [hCempty] using hC.2.1
    omega
  refine ⟨insert C P, ?_, by simp [hCnot, hcard]⟩
  constructor
  · intro D hD
    rcases Finset.mem_insert.1 hD with rfl | hDP
    · exact hC
    · exact (hP.1 D hDP).mono hmono
  · simpa only [Finset.coe_insert] using
      hP.2.insert_of_notMem hCnot (fun D hDP ↦ hdisj D hDP)

/-- If no `(r+1)`-packing exists at the coarse scale, every connected subset
of the residual vertices has fewer than `h` vertices. -/
theorem residual_connected_card_lt_of_no_succ_packing
    {α : Type*} [DecidableEq α] {gFine gCoarse : SimpleGraph α}
    {active : Finset α} {h r : ℕ} (hpos : 0 < h)
    (hmono : gFine ≤ gCoarse) {P : Finset (Finset α)}
    (hP : IsConnectedPacking gFine active h P) (hcard : #P = r)
    (hmax : ¬HasConnectedPacking gCoarse active h (r + 1))
    {C : Finset α} (hCres : C ⊆ active \ packingSupport P)
    (hCconn : ConnectedOn gCoarse C) :
    #C < h := by
  by_contra hnot
  have hlarge : IsLargeConnectedSet gCoarse active h C :=
    ⟨fun v hv ↦ (Finset.mem_sdiff.1 (hCres hv)).1,
      Nat.le_of_not_gt hnot, hCconn⟩
  exact hmax (hasConnectedPacking_succ_of_residual_large
    hpos hmono hP hcard hlarge hCres)

/-- In the terminal case `|P| = J`, the arithmetic hypothesis
`K < (J+1)h` forces the entire residual set to have size below `h`. -/
theorem residual_card_lt_of_terminal_packing
    {K h J : ℕ} (hcover : K < (J + 1) * h)
    {g : SimpleGraph (Fin K)} {P : Finset (Finset (Fin K))}
    (hP : IsConnectedPacking g (Finset.univ : Finset (Fin K)) h P)
    (hcard : #P = J) :
    #((Finset.univ : Finset (Fin K)) \ packingSupport P) < h := by
  classical
  have hsupportSubset : packingSupport P ⊆ (Finset.univ : Finset (Fin K)) := by
    intro i _
    exact Finset.mem_univ i
  have hsupportCard : J * h ≤ #(packingSupport P) := by
    rw [packingSupport, Finset.card_biUnion hP.2]
    calc
      J * h = ∑ _C ∈ P, h := by simp [hcard]
      _ ≤ ∑ C ∈ P, #C := by
        apply Finset.sum_le_sum
        intro C hCP
        exact (hP.1 C hCP).2.1
  have hsupportLe : #(packingSupport P) ≤ K := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_mono hsupportSubset
  rw [Finset.card_sdiff_of_subset hsupportSubset,
    Finset.card_univ, Fintype.card_fin]
  have hcover' : K < J * h + h := by
    simpa [Nat.add_mul] using hcover
  omega

/-- Stable-gap packing extraction in the form used by the component-center
argument.  Every connected set in the coarse residual graph has size `< h`,
including the terminal `r = J` case. -/
theorem exists_stable_packing_with_small_residual_components
    {K V : Type*} [Fintype K] [DecidableEq K] [DecidableEq V]
    (G : K → Finset V) (B h J : ℕ) (hpos : 0 < h)
    (hcover : Fintype.card K < (J + 1) * h)
    (ρ : Fin (J + 2) → ℕ) (hρ : Antitone ρ) :
    ∃ j : Fin (J + 1), ∃ r : ℕ, ∃ P : Finset (Finset K),
      r ≤ J ∧ #P = r ∧
      IsConnectedPacking
        (intersectionProximityGraph G B (ρ j.succ)) Finset.univ h P ∧
      ∀ C : Finset K,
        C ⊆ (Finset.univ : Finset K) \ packingSupport P →
        ConnectedOn (intersectionProximityGraph G B (ρ j.castSucc)) C →
        #C < h := by
  classical
  rcases exists_stable_maximal_packing G Finset.univ B h J ρ hρ with
    ⟨j, r, hrJ, hrpack, hrmax⟩
  rcases hrpack with ⟨P, hP, hcard⟩
  refine ⟨j, r, P, hrJ, hcard, hP, ?_⟩
  intro C hCres hCconn
  have hmono :
      intersectionProximityGraph G B (ρ j.succ) ≤
        intersectionProximityGraph G B (ρ j.castSucc) := by
    apply intersectionProximityGraph_mono
    exact hρ j.castSucc_le_succ
  by_cases hrlt : r < J
  · exact residual_connected_card_lt_of_no_succ_packing hpos hmono hP hcard
      (hrmax hrlt) hCres hCconn
  · have hre : r = J := Nat.le_antisymm hrJ (Nat.le_of_not_gt hrlt)
    have hres : #((Finset.univ : Finset K) \ packingSupport P) < h := by
      have hsupportSubset : packingSupport P ⊆ (Finset.univ : Finset K) := by
        intro i _
        exact Finset.mem_univ i
      rw [Finset.card_sdiff_of_subset hsupportSubset]
      have hsum : r * h ≤ #(packingSupport P) := by
        rw [packingSupport, Finset.card_biUnion hP.2]
        calc
          r * h = ∑ _D ∈ P, h := by simp [hcard]
          _ ≤ ∑ D ∈ P, #D := by
            apply Finset.sum_le_sum
            intro D hDP
            exact (hP.1 D hDP).2.1
      have hsupportLe : #(packingSupport P) ≤ Fintype.card K := by
        simpa only [Finset.card_univ] using Finset.card_mono hsupportSubset
      rw [Finset.card_univ]
      rw [hre] at hsum
      have hcover' : Fintype.card K < J * h + h := by
        simpa [Nat.add_mul] using hcover
      omega
    exact (Finset.card_mono hCres).trans_lt hres

/-! ## A profile cluster state and its exact compressed expression -/

/-- A bounded profile together with a fine-scale connected packing. -/
structure ProfileClusterState {K B : ℕ} (x : BoundedProfile K B)
    (ρ h r : ℕ) where
  packed : PackedClusters (x.proximityGraph ρ) h r

/-- Stable-gap extraction directly as an indexed profile cluster state. -/
theorem BoundedProfile.exists_stable_clusterState
    {K B : ℕ} (x : BoundedProfile K B) (h J : ℕ)
    (hpos : 0 < h) (hcover : K < (J + 1) * h)
    (ρ : Fin (J + 2) → ℕ) (hρ : Antitone ρ) :
    ∃ j : Fin (J + 1), ∃ r : ℕ,
      ∃ S : ProfileClusterState x (ρ j.succ) h r,
        r ≤ J ∧
        ∀ C : Finset (Fin K),
          C ⊆ S.packed.residual →
          ConnectedOn (x.proximityGraph (ρ j.castSucc)) C →
          #C < h := by
  classical
  rcases exists_stable_packing_with_small_residual_components
      x.generators B h J hpos (by simpa using hcover) ρ hρ with
    ⟨j, r, P, hrJ, hcard, hP, hsmall⟩
  let packed : PackedClusters (x.proximityGraph (ρ j.succ)) h r :=
    PackedClusters.ofFinset P (by
      simpa [BoundedProfile.proximityGraph] using hP) hcard
  refine ⟨j, r, ⟨packed⟩, hrJ, ?_⟩
  intro C hC hconn
  apply hsmall C
  · simpa [packed, BoundedProfile.proximityGraph] using hC
  · simpa [BoundedProfile.proximityGraph] using hconn

noncomputable def ProfileClusterState.key {K B ρ h r : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x ρ h r)
    (t : IEQuery (Finset.univ : Finset (Fin K))) : Finset (Fin r ⊕ Fin K) :=
  compressionKey S.packed.role t

noncomputable def ProfileClusterState.outsideExponent
    {K B ρ h r : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x ρ h r) (k : Finset (Fin r ⊕ Fin K)) : ℕ :=
  if hk : ∃ t : IEQuery (Finset.univ : Finset (Fin K)), S.key t = k then
    regularIntersectionSize x.generators (x.exceptionalSet ρ) (Classical.choose hk)
  else 0

theorem ProfileClusterState.regularIntersectionSize_eq_of_key_eq
    {K B ρ h r : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x ρ h r)
    (t u : IEQuery (Finset.univ : Finset (Fin K)))
    (hkey : S.key t = S.key u) :
    regularIntersectionSize x.generators (x.exceptionalSet ρ) t =
      regularIntersectionSize x.generators (x.exceptionalSet ρ) u := by
  apply regularIntersectionSize_eq_of_compressionKey_eq
    (S.packed.roleAgreementOutside x ρ) t u
  exact hkey

theorem ProfileClusterState.regularIntersectionSize_eq_outsideExponent
    {K B ρ h r : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x ρ h r)
    (t : IEQuery (Finset.univ : Finset (Fin K))) :
    regularIntersectionSize x.generators (x.exceptionalSet ρ) t =
      S.outsideExponent (S.key t) := by
  classical
  let hex : ∃ u : IEQuery (Finset.univ : Finset (Fin K)),
      S.key u = S.key t := ⟨t, rfl⟩
  rw [ProfileClusterState.outsideExponent, dif_pos hex]
  apply S.regularIntersectionSize_eq_of_key_eq t (Classical.choose hex)
  exact (Classical.choose_spec hex).symm

/-- The profile value is an exact sum indexed by compressed cluster/residual
supports. -/
theorem ProfileClusterState.value_grouped_compression
    {K B ρ h r : ℕ} {x : BoundedProfile K B}
    (S : ProfileClusterState x ρ h r) :
    (x.value : ℤ) =
      ∑ k ∈ (Finset.univ :
          Finset (IEQuery (Finset.univ : Finset (Fin K)))).image S.key,
        (2 : ℤ) ^ S.outsideExponent k *
          groupedCoefficient x.generators (x.exceptionalSet ρ) S.key k := by
  rw [BoundedProfile.value]
  exact generatedIdealIdx_card_grouped_compression
    (Finset.univ : Finset (Fin K)) x.generators (x.exceptionalSet ρ)
      S.key S.outsideExponent
      S.regularIntersectionSize_eq_outsideExponent

/-! ## Residual components and the noncenter exponent bound -/

def PackedClusters.residualPart {K h r : ℕ} {g : SimpleGraph (Fin K)}
    (P : PackedClusters g h r)
    {s : Finset (Fin K)} (t : IEQuery s) : Finset (Fin K) :=
  t.1 ∩ P.residual

/-- Two residual vertices lie in the same component of the graph induced on
the residual set. -/
def SameResidualComponent {K h r : ℕ} {gFine : SimpleGraph (Fin K)}
    (g : SimpleGraph (Fin K)) (P : PackedClusters gFine h r)
    (i j : Fin K) : Prop :=
  ∃ hi : i ∈ P.residual, ∃ hj : j ∈ P.residual,
    (g.induce (P.residual : Set (Fin K))).Reachable ⟨i, hi⟩ ⟨j, hj⟩

/-- The residual induced graph has at most `K` connected components. -/
theorem PackedClusters.residualComponent_count_le
    {K h r : ℕ} {gFine : SimpleGraph (Fin K)}
    (g : SimpleGraph (Fin K)) (P : PackedClusters gFine h r) :
    Fintype.card
      (g.induce (P.residual : Set (Fin K))).ConnectedComponent ≤ K := by
  classical
  let H := g.induce (P.residual : Set (Fin K))
  have hsurj : Function.Surjective H.connectedComponentMk := by
    intro c
    exact Quot.exists_rep c
  calc
    Fintype.card H.ConnectedComponent ≤
        Fintype.card {i : Fin K // i ∈ P.residual} :=
      Fintype.card_le_of_surjective H.connectedComponentMk hsurj
    _ = #P.residual := Fintype.card_coe _
    _ ≤ K := by simpa using Finset.card_le_univ P.residual

/-- Canonical finite label of a residual connected component.  Labels of
residual vertices lie below `K`; the extra label `K` is reserved for packed
vertices. -/
noncomputable def PackedClusters.componentLabel
    {K h r : ℕ} {gFine : SimpleGraph (Fin K)}
    (g : SimpleGraph (Fin K)) (P : PackedClusters gFine h r)
    (i : Fin K) : Fin (K + 1) :=
  if hi : i ∈ P.residual then
    let H := g.induce (P.residual : Set (Fin K))
    let e := Fintype.equivFin H.ConnectedComponent
    let c := H.connectedComponentMk ⟨i, hi⟩
    ⟨(e c).1, ((e c).2.trans_le (P.residualComponent_count_le g)).trans
      (Nat.lt_succ_self K)⟩
  else
    ⟨K, Nat.lt_succ_self K⟩

/-- On residual vertices, the canonical component labels agree exactly when
the vertices are connected in the residual induced graph. -/
theorem PackedClusters.componentLabel_eq_iff
    {K h r : ℕ} {gFine : SimpleGraph (Fin K)}
    (g : SimpleGraph (Fin K)) (P : PackedClusters gFine h r)
    {i j : Fin K} (hi : i ∈ P.residual) (hj : j ∈ P.residual) :
    P.componentLabel g i = P.componentLabel g j ↔
      SameResidualComponent g P i j := by
  classical
  let H := g.induce (P.residual : Set (Fin K))
  let e := Fintype.equivFin H.ConnectedComponent
  constructor
  · intro hij
    have hval := congrArg Fin.val hij
    simp only [PackedClusters.componentLabel, dif_pos hi, dif_pos hj] at hval
    have heq :
        e (H.connectedComponentMk ⟨i, hi⟩) =
          e (H.connectedComponentMk ⟨j, hj⟩) := Fin.ext hval
    have hcomp :
        H.connectedComponentMk ⟨i, hi⟩ =
          H.connectedComponentMk ⟨j, hj⟩ := e.injective heq
    exact ⟨hi, hj, SimpleGraph.ConnectedComponent.exact hcomp⟩
  · rintro ⟨hi', hj', hreach⟩
    have hreach' : H.Reachable ⟨i, hi⟩ ⟨j, hj⟩ := by
      simpa only using hreach
    have hcomp :
        H.connectedComponentMk ⟨i, hi⟩ =
          H.connectedComponentMk ⟨j, hj⟩ :=
      SimpleGraph.ConnectedComponent.sound hreach'
    apply Fin.ext
    simp only [PackedClusters.componentLabel, dif_pos hi, dif_pos hj]
    exact congrArg (fun c ↦ (e c).1) hcomp

/-- The residual vertices carrying the same canonical component label as
`i`. -/
noncomputable def PackedClusters.componentFiber
    {K h r : ℕ} {gFine : SimpleGraph (Fin K)}
    (g : SimpleGraph (Fin K)) (P : PackedClusters gFine h r)
    (i : Fin K) : Finset (Fin K) :=
  P.residual.filter fun j ↦ P.componentLabel g j = P.componentLabel g i

@[simp] theorem PackedClusters.mem_componentFiber
    {K h r : ℕ} {gFine : SimpleGraph (Fin K)}
    (g : SimpleGraph (Fin K)) (P : PackedClusters gFine h r)
    (i j : Fin K) :
    j ∈ P.componentFiber g i ↔
      j ∈ P.residual ∧ P.componentLabel g j = P.componentLabel g i := by
  simp [PackedClusters.componentFiber]

/-- A component fiber is connected in the coarse graph whenever it is
rooted at a residual vertex. -/
theorem PackedClusters.componentFiber_connectedOn
    {K h r : ℕ} {gFine : SimpleGraph (Fin K)}
    (g : SimpleGraph (Fin K)) (P : PackedClusters gFine h r)
    {i : Fin K} (hi : i ∈ P.residual) :
    ConnectedOn g (P.componentFiber g i) := by
  classical
  let H := g.induce (P.residual : Set (Fin K))
  let c : H.ConnectedComponent := H.connectedComponentMk ⟨i, hi⟩
  let C := P.componentFiber g i
  let e : c.supp ≃ {j : Fin K // j ∈ C} :=
    { toFun := fun v ↦
        ⟨v.1.1, by
          apply (PackedClusters.mem_componentFiber g P i v.1.1).2
          refine ⟨v.1.2, ?_⟩
          apply (P.componentLabel_eq_iff g v.1.2 hi).2
          refine ⟨v.1.2, hi, ?_⟩
          apply SimpleGraph.ConnectedComponent.exact
          exact v.2⟩
      invFun := fun j ↦
        ⟨⟨j.1, (PackedClusters.mem_componentFiber g P i j).1 j.2 |>.1⟩, by
          have hsame := (P.componentLabel_eq_iff g
            ((PackedClusters.mem_componentFiber g P i j).1 j.2 |>.1) hi).1
              ((PackedClusters.mem_componentFiber g P i j).1 j.2 |>.2)
          rcases hsame with ⟨_hj, _hi, hreach⟩
          apply SimpleGraph.ConnectedComponent.sound
          simpa only using hreach⟩
      left_inv := by
        intro v
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro j
        apply Subtype.ext
        rfl }
  let eg : c.toSimpleGraph ≃g g.induce (C : Set (Fin K)) :=
    ⟨e, by
      intro u v
      change g.Adj u.1.1 v.1.1 ↔ g.Adj (e u).1 (e v).1
      rfl⟩
  exact (SimpleGraph.Iso.connected_iff eg).1
    (SimpleGraph.ConnectedComponent.connected_toSimpleGraph c)

/-- The stable residual-set hypothesis immediately bounds every canonical
component fiber. -/
theorem PackedClusters.componentFiber_card_lt
    {K h r : ℕ} {gFine : SimpleGraph (Fin K)}
    (g : SimpleGraph (Fin K)) (P : PackedClusters gFine h r)
    (hsmall : ∀ C : Finset (Fin K),
      C ⊆ P.residual → ConnectedOn g C → #C < h)
    (i : Fin K) (hi : i ∈ P.residual) :
    #(P.componentFiber g i) < h := by
  apply hsmall (P.componentFiber g i)
  · intro j hj
    exact (P.mem_componentFiber g i j).1 hj |>.1
  · exact P.componentFiber_connectedOn g hi

/-- A center query is one whose selected residual facets all lie in a single
component.  Empty and singleton residual parts are centers automatically. -/
def IsCenterQuery {K h r : ℕ} {gFine : SimpleGraph (Fin K)}
    (g : SimpleGraph (Fin K)) (P : PackedClusters gFine h r)
    {s : Finset (Fin K)} (t : IEQuery s) : Prop :=
  ∀ i ∈ P.residualPart t, ∀ j ∈ P.residualPart t,
    SameResidualComponent g P i j

/-- A noncenter query contains two selected residual facets which are not
adjacent at the coarse scale. -/
theorem exists_residual_nonedge_of_not_center
    {K h r : ℕ} {gFine g : SimpleGraph (Fin K)}
    (P : PackedClusters gFine h r)
    {s : Finset (Fin K)} (t : IEQuery s)
    (ht : ¬ IsCenterQuery g P t) :
    ∃ i ∈ P.residualPart t, ∃ j ∈ P.residualPart t,
      i ≠ j ∧ ¬g.Adj i j := by
  classical
  unfold IsCenterQuery at ht
  push Not at ht
  rcases ht with ⟨i, hi, j, hj, hcomponent⟩
  have hiR : i ∈ P.residual := (Finset.mem_inter.1 hi).2
  have hjR : j ∈ P.residual := (Finset.mem_inter.1 hj).2
  have hne : i ≠ j := by
    intro hij
    subst j
    apply hcomponent
    exact ⟨hiR, hiR, ⟨SimpleGraph.Walk.nil⟩⟩
  refine ⟨i, hi, j, hj, hne, ?_⟩
  intro hij
  apply hcomponent
  have hinduced :
      (g.induce (P.residual : Set (Fin K))).Adj ⟨i, hiR⟩ ⟨j, hjR⟩ := hij
  exact ⟨hiR, hjR, SimpleGraph.Adj.reachable hinduced⟩

/-- Sharp exponent bound for every noncenter query: its full generator
intersection has size at most `B - ρ`. -/
theorem noncenter_generatorIntersection_card_le
    {K B ρFine h r : ℕ} (x : BoundedProfile K B)
    (S : ProfileClusterState x ρFine h r) (ρ : ℕ)
    (t : IEQuery (Finset.univ : Finset (Fin K)))
    (ht : ¬ IsCenterQuery (x.proximityGraph ρ) S.packed t) :
    #(AntichainOfGivenSize.Section6.generatorIntersection x.generators t) ≤ B - ρ := by
  classical
  rcases exists_residual_nonedge_of_not_center S.packed t ht with
    ⟨i, hi, j, hj, hij, hnonedge⟩
  have hiT : i ∈ t.1 := (Finset.mem_inter.1 hi).1
  have hjT : j ∈ t.1 := (Finset.mem_inter.1 hj).1
  have hinter : #(x.generators i ∩ x.generators j) ≤ B - ρ := by
    by_contra hnot
    have hlt : B - ρ < #(x.generators i ∩ x.generators j) :=
      Nat.lt_of_not_ge hnot
    exact hnonedge (intersectionProximityGraph_adj x.generators B ρ i j |>.2
      ⟨hij, hlt⟩)
  apply (Finset.card_mono ?_).trans hinter
  intro v hv
  have hvall : ∀ a ∈ t.1, v ∈ x.generators a := by
    simpa [AntichainOfGivenSize.Section6.generatorIntersection] using hv
  exact Finset.mem_inter.2 ⟨hvall i hiT, hvall j hjT⟩

/-- The regular (outside-exceptional) part of a noncenter intersection obeys
the same sharp bound. -/
theorem noncenter_regularIntersectionSize_le
    {K B ρFine h r : ℕ} (x : BoundedProfile K B)
    (S : ProfileClusterState x ρFine h r) (ρ : ℕ)
    (t : IEQuery (Finset.univ : Finset (Fin K)))
    (ht : ¬ IsCenterQuery (x.proximityGraph ρ) S.packed t) :
    regularIntersectionSize x.generators (x.exceptionalSet ρFine) t ≤ B - ρ := by
  exact (Finset.card_mono Finset.sdiff_subset).trans
    (noncenter_generatorIntersection_card_le x S ρ t ht)

/-- Every compressed query is either a center, or has the sharp coarse-scale
exponent bound. -/
theorem center_or_regularIntersectionSize_le
    {K B ρFine h r : ℕ} (x : BoundedProfile K B)
    (S : ProfileClusterState x ρFine h r) (ρ : ℕ)
    (t : IEQuery (Finset.univ : Finset (Fin K))) :
    IsCenterQuery (x.proximityGraph ρ) S.packed t ∨
      regularIntersectionSize x.generators (x.exceptionalSet ρFine) t ≤ B - ρ := by
  by_cases ht : IsCenterQuery (x.proximityGraph ρ) S.packed t
  · exact Or.inl ht
  · exact Or.inr (noncenter_regularIntersectionSize_le x S ρ t ht)

end AntichainOfGivenSize.ClusterLowerBound
