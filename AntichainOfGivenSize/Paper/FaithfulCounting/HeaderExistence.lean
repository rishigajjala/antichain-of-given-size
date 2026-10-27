import AntichainOfGivenSize.LowerBound.ClusterEncoding
import Mathlib.Order.Partition.Finpartition
import AntichainOfGivenSize.Paper.FaithfulCounting.ConnectedSubset
open scoped BigOperators
open Finset
open AntichainOfGivenSize.ClusterCore
open AntichainOfGivenSize.ClusterLowerBound

namespace AntichainOfGivenSize.FaithfulLower

/-- Trim a finite packing without changing the number of clusters. -/
theorem trim_connected_packing {K h : ℕ} (hpos : 0 < h)
    {g : SimpleGraph (Fin K)} {P : Finset (Finset (Fin K))}
    (hP : IsConnectedPacking g univ h P) :
    ∃ Q : Finset (Finset (Fin K)), Q.card = P.card ∧
      IsConnectedPacking g univ h Q ∧ ∀ C ∈ Q, C.card = h := by
  classical
  choose D hD using fun C : P ↦ exists_connected_subset_card g
    (hP.1 C.1 C.2).2.2 hpos (hP.1 C.1 C.2).2.1
  have hdisjoint : ∀ a b : P, a ≠ b → Disjoint (D a) (D b) := by
    intro a b hab
    exact (hP.2 a.2 b.2 (fun h ↦ hab (Subtype.ext h))).mono
      (hD a).1 (hD b).1
  have hinj : Function.Injective D := by
    intro a b hab
    by_contra hne
    have he : D b = ∅ := (Finset.disjoint_self_iff_empty _).mp
      (by simpa only [hab] using hdisjoint a b hne)
    have hc := (hD b).2.1
    simp only [he, card_empty] at hc
    omega
  refine ⟨univ.image D, ?_, ?_, ?_⟩
  · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_coe]
  · constructor
    · intro C hC
      obtain ⟨a, _, rfl⟩ := mem_image.mp hC
      exact ⟨subset_univ _, (hD a).2.1.ge, (hD a).2.2⟩
    · intro C hC E hE hne
      obtain ⟨a, _, rfl⟩ := mem_image.mp hC
      obtain ⟨b, _, rfl⟩ := mem_image.mp hE
      exact hdisjoint a b (fun hab ↦ hne (congrArg D hab))
  · intro C hC
    obtain ⟨a, _, rfl⟩ := mem_image.mp hC
    exact (hD a).2.1

/-- The plateau argument works for any decreasing finite sequence of graphs.
It produces exact-size fine clusters and small coarse residual components. -/
theorem exists_stable_exact_packing {K h J : ℕ} (hpos : 0 < h)
    (hcover : K < (J + 1) * h)
    (graphs : Fin (J + 2) → SimpleGraph (Fin K)) (hanti : Antitone graphs) :
    ∃ j : Fin (J + 1), ∃ r : ℕ,
      ∃ P : PackedClusters (graphs j.succ) h r,
        r ≤ J ∧ (∀ a, (P.cluster a).card = h) ∧
        ∀ C : Finset (Fin K), C ⊆ P.residual →
          ConnectedOn (graphs j.castSucc) C → C.card < h := by
  classical
  obtain ⟨j, hj⟩ := exists_common_stable_gap J
    (fun s i ↦ HasConnectedPacking (graphs i) univ h (s.1 + 1))
    (by
      intro s i k hik hp
      exact hp.mono (hanti hik))
  let good : ℕ → Prop := fun r ↦ HasConnectedPacking (graphs j.succ) univ h r
  let r := Nat.findGreatest good J
  have hrJ : r ≤ J := Nat.findGreatest_le J
  have hrgood : good r := Nat.findGreatest_spec (Nat.zero_le J)
    (hasConnectedPacking_zero (graphs j.succ) univ h)
  have hmax : r < J → ¬ HasConnectedPacking (graphs j.castSucc) univ h (r + 1) := by
    intro hrlt hc
    have hf : good (r + 1) := (hj ⟨r, hrlt⟩).1 hc
    exact Nat.findGreatest_is_greatest (P := good)
      (Nat.lt_succ_self r) (Nat.succ_le_iff.mpr hrlt) hf
  obtain ⟨Q₀, hQ₀, hcard₀⟩ := hrgood
  obtain ⟨Q, hcardQ, hQ, hexact⟩ := trim_connected_packing hpos hQ₀
  have hcard : Q.card = r := hcardQ.trans hcard₀
  let P : PackedClusters (graphs j.succ) h r := PackedClusters.ofFinset Q hQ hcard
  have hsmall : ∀ C : Finset (Fin K),
      C ⊆ univ \ packingSupport Q → ConnectedOn (graphs j.castSucc) C → C.card < h := by
    intro C hres hconn
    by_cases hrlt : r < J
    · exact residual_connected_card_lt_of_no_succ_packing hpos
        (hanti j.castSucc_le_succ) hQ hcard (hmax hrlt) hres hconn
    · have hr : r = J := le_antisymm hrJ (Nat.le_of_not_gt hrlt)
      exact (card_mono hres).trans_lt
        (residual_card_lt_of_terminal_packing hcover hQ (hcard.trans hr))
  refine ⟨j, r, P, hrJ, ?_, ?_⟩
  · intro a
    exact hexact _ (Finset.equivFinOfCardEq hcard |>.symm a).2
  · intro C hres hconn
    apply hsmall C _ hconn
    simpa only [P, PackedClusters.ofFinset_residual] using hres

theorem packed_role_eq_inl_iff {K h r : ℕ} {g : SimpleGraph (Fin K)}
    (P : PackedClusters g h r) (i : Fin K) (a : Fin r) :
    P.role i = Sum.inl a ↔ i ∈ P.cluster a := by
  classical
  unfold PackedClusters.role
  split
  · rename_i hex
    constructor
    · intro heq
      have ha := Sum.inl.inj heq
      simpa [← ha] using Classical.choose_spec hex
    · intro hi
      congr 1
      by_contra hne
      exact Finset.disjoint_left.mp (P.pairwise_disjoint hne)
        (Classical.choose_spec hex) hi
  · rename_i hn
    constructor
    · exact fun heq ↦ False.elim (Sum.inr_ne_inl heq)
    · exact fun hi ↦ False.elim (hn ⟨a, hi⟩)

/-- Temporary labels used only to construct the unlabeled partition. -/
noncomputable def headerLabel {K h r : ℕ} {fine : SimpleGraph (Fin K)}
    (P : PackedClusters fine h r) (coarse : SimpleGraph (Fin K))
    (i : Fin K) : Fin r ⊕ Fin (K + 1) :=
  match P.role i with
  | Sum.inl a => Sum.inl a
  | Sum.inr _ => Sum.inr (P.componentLabel coarse i)

theorem headerLabel_eq_inl_iff {K h r : ℕ} {fine : SimpleGraph (Fin K)}
    (P : PackedClusters fine h r) (coarse : SimpleGraph (Fin K))
    (i : Fin K) (a : Fin r) :
    headerLabel P coarse i = Sum.inl a ↔ i ∈ P.cluster a := by
  rw [← packed_role_eq_inl_iff]
  cases heq : P.role i <;> simp [headerLabel, heq]

theorem headerLabel_eq_inr_iff {K h r : ℕ} {fine : SimpleGraph (Fin K)}
    (P : PackedClusters fine h r) (coarse : SimpleGraph (Fin K))
    (i : Fin K) (c : Fin (K + 1)) :
    headerLabel P coarse i = Sum.inr c ↔
      i ∈ P.residual ∧ P.componentLabel coarse i = c := by
  cases heq : P.role i with
  | inl a =>
    have hi := (packed_role_eq_inl_iff P i a).mp heq
    have hn : i ∉ P.residual := fun hr ↦ (P.mem_residual_iff i).mp hr a hi
    simp [headerLabel, heq, hn]
  | inr j =>
    have hi := (P.role_eq_inr_iff i j).mp heq
    simp [headerLabel, heq, hi.2]

/-- This is the actual set partition recorded in the header. -/
noncomputable def headerPartition {K h r : ℕ} {fine : SimpleGraph (Fin K)}
    (P : PackedClusters fine h r) (coarse : SimpleGraph (Fin K)) :
    Finpartition (univ : Finset (Fin K)) := by
  classical
  exact Finpartition.ofSetoid (Setoid.ker (headerLabel P coarse))

theorem mem_headerPartition_part_iff {K h r : ℕ} {fine : SimpleGraph (Fin K)}
    (P : PackedClusters fine h r) (coarse : SimpleGraph (Fin K)) (i j : Fin K) :
    j ∈ (headerPartition P coarse).part i ↔
      headerLabel P coarse i = headerLabel P coarse j := by
  classical
  exact Finpartition.mem_part_ofSetoid_iff_rel

theorem headerPartition_part_cluster {K h r : ℕ} {fine : SimpleGraph (Fin K)}
    (P : PackedClusters fine h r) (coarse : SimpleGraph (Fin K))
    {i : Fin K} {a : Fin r} (hi : i ∈ P.cluster a) :
    (headerPartition P coarse).part i = P.cluster a := by
  ext j
  rw [mem_headerPartition_part_iff, (headerLabel_eq_inl_iff P coarse i a).mpr hi]
  exact (eq_comm.trans (headerLabel_eq_inl_iff P coarse j a))

theorem headerPartition_part_residual {K h r : ℕ} {fine : SimpleGraph (Fin K)}
    (P : PackedClusters fine h r) (coarse : SimpleGraph (Fin K))
    {i : Fin K} (hi : i ∈ P.residual) :
    (headerPartition P coarse).part i = P.componentFiber coarse i := by
  ext j
  rw [mem_headerPartition_part_iff,
    (headerLabel_eq_inr_iff P coarse i (P.componentLabel coarse i)).mpr ⟨hi, rfl⟩]
  rw [eq_comm, headerLabel_eq_inr_iff, P.mem_componentFiber]

/-- Its parts are exactly the fine clusters and the coarse residual components.
The temporary labels, graphs, and trees are absent from the resulting partition. -/
theorem headerPartition_parts {K h r : ℕ} {fine : SimpleGraph (Fin K)}
    (P : PackedClusters fine h r) (coarse : SimpleGraph (Fin K)) (hpos : 0 < h) :
    (headerPartition P coarse).parts =
      univ.image P.cluster ∪ P.residual.image (P.componentFiber coarse) := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨i, hi⟩ := (headerPartition P coarse).nonempty_of_mem_parts hC
    have heq := (headerPartition P coarse).part_eq_of_mem hC hi
    by_cases hres : i ∈ P.residual
    · apply mem_union.mpr; right
      exact mem_image.mpr ⟨i, hres, (headerPartition_part_residual P coarse hres).symm.trans heq⟩
    · have hex : ∃ a, i ∈ P.cluster a := by
        simpa only [P.mem_residual_iff, not_forall, not_not] using hres
      obtain ⟨a, ha⟩ := hex
      apply mem_union.mpr; left
      exact mem_image.mpr ⟨a, mem_univ a, (headerPartition_part_cluster P coarse ha).symm.trans heq⟩
  · intro hC
    rcases mem_union.mp hC with hcluster | hres
    · obtain ⟨a, _, rfl⟩ := mem_image.mp hcluster
      obtain ⟨i, hi⟩ := card_pos.mp (hpos.trans_le (P.large a).2.1)
      rw [← headerPartition_part_cluster P coarse hi]
      exact (headerPartition P coarse).part_mem.mpr (mem_univ i)
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hres
      rw [← headerPartition_part_residual P coarse hi]
      exact (headerPartition P coarse).part_mem.mpr (mem_univ i)

/-- Every eligible graph sequence admits a header with exactly `h` vertices
per fine cluster and fewer than `h` vertices per coarse residual component. -/
theorem exists_header {K h J : ℕ} (hpos : 0 < h)
    (hcover : K < (J + 1) * h)
    (graphs : Fin (J + 2) → SimpleGraph (Fin K)) (hanti : Antitone graphs) :
    ∃ j : Fin (J + 1), ∃ r : ℕ,
      ∃ P : PackedClusters (graphs j.succ) h r,
      ∃ H : Finpartition (univ : Finset (Fin K)),
        r ≤ J ∧ (∀ a, (P.cluster a).card = h) ∧
        (∀ i ∈ P.residual, (P.componentFiber (graphs j.castSucc) i).card < h) ∧
        H.parts = univ.image P.cluster ∪
          P.residual.image (P.componentFiber (graphs j.castSucc)) := by
  obtain ⟨j, r, P, hr, hexact, hsmall⟩ := exists_stable_exact_packing hpos hcover graphs hanti
  exact ⟨j, r, P, headerPartition P (graphs j.castSucc), hr, hexact,
    P.componentFiber_card_lt (graphs j.castSucc) hsmall,
    headerPartition_parts P (graphs j.castSucc) hpos⟩


end AntichainOfGivenSize.FaithfulLower
