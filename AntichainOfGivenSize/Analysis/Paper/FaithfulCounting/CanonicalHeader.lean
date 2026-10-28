import AntichainOfGivenSize.Analysis.Paper.FaithfulCounting.HeaderExistence
import AntichainOfGivenSize.Analysis.Paper.FaithfulCounting.PartitionHeader
import AntichainOfGivenSize.Analysis.Paper.FaithfulCounting.OriginalQueryReconstruction
open Finset
open AntichainOfGivenSize.ClusterCore
open AntichainOfGivenSize.ClusterLowerBound

namespace AntichainOfGivenSize.FaithfulLower

/-- Cluster blocks can be read from the partition by their size alone. -/
noncomputable def canonicalClusterFamily {K : ℕ} (H : Partition K) (h : ℕ) :
    Finset (Finset (Fin K)) := by
  classical
  exact H.parts.filter (fun C ↦ C.card = h)

/-- A cluster is named by its least vertex; a residual vertex keeps its own
index. This definition uses no graph, packing witness, or ground-set labels. -/
noncomputable def canonicalRole {K : ℕ} (H : Partition K) (h : ℕ)
    (i : Fin K) : Fin K ⊕ Fin K :=
  if (H.part i).card = h then Sum.inl (partitionCode H i) else Sum.inr i

/-- Selected residual indices must lie in the same partition block. -/
def CanonicalIsCenter {K : ℕ} (H : Partition K) (h : ℕ)
    (t : IEQuery (univ : Finset (Fin K))) : Prop :=
  ∀ i ∈ t.1, (H.part i).card ≠ h →
    ∀ j ∈ t.1, (H.part j).card ≠ h → H.part i = H.part j

noncomputable def canonicalCenters {K : ℕ} (H : Partition K) (h : ℕ) :
    Finset (IEQuery (univ : Finset (Fin K))) := by
  classical
  exact univ.filter (CanonicalIsCenter H h)

/-- The exceptional set is determined by the family and the recorded partition. -/
noncomputable def canonicalExceptional {K : ℕ} {V : Type*} [DecidableEq V]
    (G : Fin K → Finset V) (H : Partition K) (h : ℕ) : Finset V :=
  intrinsicExceptional G (canonicalClusterFamily H h)

/-- Role agreement follows from the definition of the intrinsic exceptional
set for every partition, before any graph witness is chosen. -/
theorem canonicalRole_agreement {K : ℕ} {V : Type*} [DecidableEq V]
    (G : Fin K → Finset V) (H : Partition K) (h : ℕ) :
    RoleAgreementOutside G (canonicalExceptional G H h) (canonicalRole H h) := by
  classical
  intro i j heq v hv
  unfold canonicalRole at heq
  split at heq
  next hi =>
    split at heq
    next hj =>
      have hpart : H.part i = H.part j :=
        (partitionCode_eq_iff_part_eq H i j).mp (Sum.inl.inj heq)
      apply cluster_agrees_off_intrinsicExceptional G
        (C := H.part i) (P := canonicalClusterFamily H h)
      · exact mem_filter.mpr ⟨H.part_mem.mpr (mem_univ i), hi⟩
      · exact H.mem_part (mem_univ i)
      · rw [hpart]
        exact H.mem_part (mem_univ j)
      · exact hv
    next hj => exact False.elim (Sum.inl_ne_inr heq)
  next hi =>
    split at heq
    next hj => exact False.elim (Sum.inr_ne_inl heq)
    next hj =>
      have hij : i = j := Sum.inr.inj heq
      subst j
      rfl

section Witness

variable {K h r : ℕ} {fine : SimpleGraph (Fin K)}
  (P : PackedClusters fine h r) (coarse : SimpleGraph (Fin K))
  (hexact : ∀ a, (P.cluster a).card = h)
  (hsmall : ∀ i ∈ P.residual, (P.componentFiber coarse i).card < h)

theorem eq_headerPartition_of_parts (H : Partition K) (hpos : 0 < h)
    (hparts : H.parts = univ.image P.cluster ∪
      P.residual.image (P.componentFiber coarse)) :
    H = headerPartition P coarse := by
  apply Finpartition.ext
  exact hparts.trans (headerPartition_parts P coarse hpos).symm

include hexact hsmall in
theorem header_part_card_eq_iff (i : Fin K) :
    ((headerPartition P coarse).part i).card = h ↔ i ∉ P.residual := by
  by_cases hi : i ∈ P.residual
  · rw [headerPartition_part_residual P coarse hi]
    exact iff_of_false (Nat.ne_of_lt (hsmall i hi)) (not_not_intro hi)
  · have hex : ∃ a, i ∈ P.cluster a := by
      simpa only [P.mem_residual_iff, not_forall, not_not] using hi
    obtain ⟨a, ha⟩ := hex
    rw [headerPartition_part_cluster P coarse ha, hexact a]
    exact iff_of_true rfl hi

include hexact hsmall in
theorem canonicalClusterFamily_eq (hpos : 0 < h) :
    canonicalClusterFamily (headerPartition P coarse) h = packedClusterFamily P := by
  classical
  ext C
  simp only [canonicalClusterFamily, mem_filter, packedClusterFamily,
    headerPartition_parts P coarse hpos, mem_union]
  constructor
  · rintro ⟨hC, hcard⟩
    rcases hC with hcluster | hres
    · exact hcluster
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hres
      exact False.elim ((Nat.ne_of_lt (hsmall i hi)) hcard)
  · intro hC
    refine ⟨Or.inl hC, ?_⟩
    obtain ⟨a, _, rfl⟩ := mem_image.mp hC
    exact hexact a

include hexact hsmall in
theorem canonicalExceptional_eq {V : Type*} [DecidableEq V]
    (G : Fin K → Finset V) (hpos : 0 < h) :
    canonicalExceptional G (headerPartition P coarse) h =
      intrinsicExceptional G (packedClusterFamily P) := by
  unfold canonicalExceptional
  rw [canonicalClusterFamily_eq P coarse hexact hsmall hpos]

noncomputable def clusterRoot (hpos : 0 < h) (a : Fin r) : Fin K :=
  (P.cluster a).min' (card_pos.mp (hpos.trans_le (P.large a).2.1))

theorem clusterRoot_injective (hpos : 0 < h) :
    Function.Injective (clusterRoot P hpos) := by
  intro a b heq
  by_contra hne
  have ha : clusterRoot P hpos a ∈ P.cluster a := min'_mem _ _
  have hb : clusterRoot P hpos b ∈ P.cluster b := min'_mem _ _
  rw [← heq] at hb
  exact Finset.disjoint_left.mp (P.pairwise_disjoint hne) ha hb

noncomputable def rootRename (hpos : 0 < h) : Fin r ⊕ Fin K → Fin K ⊕ Fin K :=
  Sum.map (clusterRoot P hpos) id

theorem rootRename_injective (hpos : 0 < h) :
    Function.Injective (rootRename P hpos) :=
  Sum.map_injective.mpr ⟨clusterRoot_injective P hpos, Function.injective_id⟩

include hexact hsmall in
theorem canonicalRole_eq_renamed (hpos : 0 < h) :
    canonicalRole (headerPartition P coarse) h = rootRename P hpos ∘ P.role := by
  funext i
  cases heq : P.role i with
  | inl a =>
    have hi := (packed_role_eq_inl_iff P i a).mp heq
    have hc : ((headerPartition P coarse).part i).card = h := by
      rw [headerPartition_part_cluster P coarse hi, hexact a]
    simp only [canonicalRole, hc, if_pos, Function.comp_apply, heq,
      rootRename, Sum.map_inl]
    congr 1
    simp only [partitionCode, clusterRoot, headerPartition_part_cluster P coarse hi]
  | inr j =>
    have hi := (P.role_eq_inr_iff i j).mp heq
    rcases hi with ⟨rfl, hiR⟩
    have hc : ((headerPartition P coarse).part i).card ≠ h := by
      intro hc
      exact ((header_part_card_eq_iff P coarse hexact hsmall i).mp hc) hiR
    simp [canonicalRole, hc, Function.comp_apply, heq, rootRename]

theorem header_part_eq_iff_sameResidual {i j : Fin K}
    (hi : i ∈ P.residual) (hj : j ∈ P.residual) :
    (headerPartition P coarse).part i = (headerPartition P coarse).part j ↔
      SameResidualComponent coarse P i j := by
  calc
    (headerPartition P coarse).part i = (headerPartition P coarse).part j ↔
        i ∈ (headerPartition P coarse).part j :=
      ((headerPartition P coarse).mem_part_iff_part_eq_part (mem_univ i) (mem_univ j)).symm
    _ ↔ headerLabel P coarse j = headerLabel P coarse i :=
      mem_headerPartition_part_iff P coarse j i
    _ ↔ P.componentLabel coarse i = P.componentLabel coarse j := by
      rw [(headerLabel_eq_inr_iff P coarse i _).mpr ⟨hi, rfl⟩,
        (headerLabel_eq_inr_iff P coarse j _).mpr ⟨hj, rfl⟩, Sum.inr.injEq]
      exact eq_comm
    _ ↔ SameResidualComponent coarse P i j := P.componentLabel_eq_iff coarse hi hj

include hexact hsmall in
theorem canonicalIsCenter_iff (t : IEQuery (univ : Finset (Fin K))) :
    CanonicalIsCenter (headerPartition P coarse) h t ↔ IsCenterQuery coarse P t := by
  have hres (i : Fin K) : ((headerPartition P coarse).part i).card ≠ h ↔
      i ∈ P.residual := by
    simpa only [not_not] using
      not_congr (header_part_card_eq_iff P coarse hexact hsmall i)
  constructor
  · intro hc i hi j hj
    have hi' := mem_inter.mp hi
    have hj' := mem_inter.mp hj
    exact (header_part_eq_iff_sameResidual P coarse hi'.2 hj'.2).mp
      (hc i hi'.1 ((hres i).mpr hi'.2) j hj'.1 ((hres j).mpr hj'.2))
  · intro hc i hi hiR j hj hjR
    have hi' := (hres i).mp hiR
    have hj' := (hres j).mp hjR
    exact (header_part_eq_iff_sameResidual P coarse hi' hj').mpr
      (hc i (mem_inter.mpr ⟨hi, hi'⟩) j (mem_inter.mpr ⟨hj, hj'⟩))

include hexact hsmall in
theorem canonicalCenters_eq :
    canonicalCenters (headerPartition P coarse) h = packedCenters P coarse := by
  classical
  ext t
  simp only [canonicalCenters, packedCenters, mem_filter, mem_univ, true_and]
  exact canonicalIsCenter_iff P coarse hexact hsmall t

include hexact hsmall in
theorem canonicalCentralKeys_eq_image (hpos : 0 < h) :
    centralKeys (canonicalRole (headerPartition P coarse) h)
        (canonicalCenters (headerPartition P coarse) h) =
      (centralKeys P.role (packedCenters P coarse)).image
        (fun k ↦ k.image (rootRename P hpos)) := by
  classical
  rw [canonicalRole_eq_renamed P coarse hexact hsmall hpos,
    canonicalCenters_eq P coarse hexact hsmall]
  simp only [centralKeys, Finset.image_image]
  congr 1
  funext t
  simp only [Function.comp_apply, compressionKey, Finset.image_image]

include hexact hsmall in
theorem canonicalCentralKeys_card_le {J : ℕ} (hpos : 0 < h) (hr : r ≤ J) :
    (centralKeys (canonicalRole (headerPartition P coarse) h)
      (canonicalCenters (headerPartition P coarse) h)).card ≤
        2 ^ J * (1 + K * 2 ^ h) := by
  rw [canonicalCentralKeys_eq_image P coarse hexact hsmall hpos]
  exact (card_image_le).trans (packedCentralKeys_card_le_of_le P coarse hr hsmall)

end Witness

/-- The common header makes records comparable even when the families have
different finite ground sets. No equality of graph witnesses is required. -/
theorem canonical_central_sum_eq_of_records
    {K B u : ℕ} {V W : Type*} [DecidableEq V] [DecidableEq W]
    (H : Partition K) (h : ℕ) (G : Fin K → Finset V) (D : Fin K → Finset W)
    (hG : ∀ i, (G i).card ≤ B) (hD : ∀ i, (D i).card ≤ B)
    (hU : (canonicalExceptional G H h).card ≤ u)
    (hZ : (canonicalExceptional D H h).card ≤ u)
    (hcode : incidenceSparseCode G (canonicalExceptional G H h) u hU =
      incidenceSparseCode D (canonicalExceptional D H h) u hZ)
    (hexp : centralExponentVector G (canonicalExceptional G H h)
        (canonicalRole H h) (canonicalCenters H h) B hG =
      centralExponentVector D (canonicalExceptional D H h)
        (canonicalRole H h) (canonicalCenters H h) B hD) :
    originalCentralSum G (canonicalCenters H h) =
      originalCentralSum D (canonicalCenters H h) :=
  originalCentralSum_eq_of_sparseCode_vector_eq G D
    (canonicalExceptional G H h) (canonicalExceptional D H h)
    (canonicalRole H h) (canonicalCenters H h) B u hG hD hU hZ
    (canonicalRole_agreement G H h) (canonicalRole_agreement D H h) hcode hexp


end AntichainOfGivenSize.FaithfulLower
