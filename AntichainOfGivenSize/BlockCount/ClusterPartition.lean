import AntichainOfGivenSize.LowerBound.ClusterCore
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Finite normalized cluster partitions

Connected-component fibers partition the large generators. A single finite
exceptional set controls all clusters; its quadratic bound is deliberately
coarse and is independent of the ambient cardinality normalization.
-/

open scoped BigOperators symmDiff
open Finset

namespace AntichainOfGivenSize.BlockCount

variable {V : Type*} [DecidableEq V]

/-- The original vertices belonging to one connected component on `active`. -/
noncomputable def componentFamily (active : Finset V) (g : SimpleGraph active)
    (c : g.ConnectedComponent) : Finset V := by
  classical
  exact c.supp.toFinset.image Subtype.val

@[simp] theorem mem_componentFamily (active : Finset V) (g : SimpleGraph active)
    (c : g.ConnectedComponent) (a : active) :
    a.1 ∈ componentFamily active g c ↔ g.connectedComponentMk a = c := by
  classical
  simp only [componentFamily, Finset.mem_image, Set.mem_toFinset,
    SimpleGraph.ConnectedComponent.mem_supp_iff]
  constructor
  · rintro ⟨b, hb, hba⟩
    have : b = a := Subtype.ext hba
    simpa [this] using hb
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem componentFamily_subset (active : Finset V) (g : SimpleGraph active)
    (c : g.ConnectedComponent) : componentFamily active g c ⊆ active := by
  classical
  intro a ha
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
  exact b.2

theorem componentFamily_nonempty (active : Finset V) (g : SimpleGraph active)
    (c : g.ConnectedComponent) : (componentFamily active g c).Nonempty := by
  classical
  obtain ⟨a, ha⟩ := c.nonempty_supp
  exact ⟨a.1, (mem_componentFamily active g c a).2 ha⟩

theorem componentFamily_disjoint (active : Finset V) (g : SimpleGraph active)
    {c d : g.ConnectedComponent} (hcd : c ≠ d) :
    Disjoint (componentFamily active g c) (componentFamily active g d) := by
  classical
  rw [Finset.disjoint_left]
  intro a hac had
  let aa : active := ⟨a, componentFamily_subset active g c hac⟩
  have hc := (mem_componentFamily active g c aa).1 hac
  have hd := (mem_componentFamily active g d aa).1 had
  exact hcd (hc.symm.trans hd)

theorem componentFamily_injective (active : Finset V) (g : SimpleGraph active) :
    Function.Injective (componentFamily active g) := by
  classical
  intro c d hcd
  by_contra hne
  obtain ⟨a, ha⟩ := componentFamily_nonempty active g c
  exact Finset.disjoint_left.mp (componentFamily_disjoint active g hne) ha (hcd ▸ ha)

/-- The finite family of connected-component fibers. -/
noncomputable def componentPartition (active : Finset V) (g : SimpleGraph active) :
    Finset (Finset V) := by
  classical
  exact Finset.univ.image (componentFamily active g)

theorem mem_componentPartition (active : Finset V) (g : SimpleGraph active)
    {C : Finset V} : C ∈ componentPartition active g ↔
      ∃ c : g.ConnectedComponent, componentFamily active g c = C := by
  classical
  simp [componentPartition]

theorem componentPartition_nonempty (active : Finset V) (g : SimpleGraph active)
    {C : Finset V} (hC : C ∈ componentPartition active g) : C.Nonempty := by
  obtain ⟨c, rfl⟩ := (mem_componentPartition active g).1 hC
  exact componentFamily_nonempty active g c

theorem componentPartition_subset (active : Finset V) (g : SimpleGraph active)
    {C : Finset V} (hC : C ∈ componentPartition active g) : C ⊆ active := by
  obtain ⟨c, rfl⟩ := (mem_componentPartition active g).1 hC
  exact componentFamily_subset active g c

theorem componentPartition_disjoint (active : Finset V) (g : SimpleGraph active) :
    (componentPartition active g : Set (Finset V)).PairwiseDisjoint id := by
  classical
  intro C hC D hD hCD
  obtain ⟨c, rfl⟩ := (mem_componentPartition active g).1 hC
  obtain ⟨d, rfl⟩ := (mem_componentPartition active g).1 hD
  apply componentFamily_disjoint active g
  intro h
  exact hCD (congrArg (componentFamily active g) h)

theorem componentPartition_biUnion (active : Finset V) (g : SimpleGraph active) :
    (componentPartition active g).biUnion id = active := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨C, hC, haC⟩ := Finset.mem_biUnion.mp ha
    exact componentPartition_subset active g hC haC
  · intro ha
    let aa : active := ⟨a, ha⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨componentFamily active g (g.connectedComponentMk aa), ?_, ?_⟩
    · exact (mem_componentPartition active g).2 ⟨_, rfl⟩
    · exact (mem_componentFamily active g _ aa).2 rfl

theorem componentPartition_sum_card (active : Finset V) (g : SimpleGraph active) :
    ∑ C ∈ componentPartition active g, C.card = active.card := by
  classical
  calc
    ∑ C ∈ componentPartition active g, C.card =
        ((componentPartition active g).biUnion id).card :=
      (Finset.card_biUnion (componentPartition_disjoint active g)).symm
    _ = active.card := congrArg Finset.card (componentPartition_biUnion active g)

/-- Vertices in different fibers cannot be adjacent. -/
theorem componentPartition_not_adj (active : Finset V) (g : SimpleGraph active)
    {C D : Finset V} (hC : C ∈ componentPartition active g)
    (hD : D ∈ componentPartition active g) (hCD : C ≠ D)
    {a b : active} (ha : a.1 ∈ C) (hb : b.1 ∈ D) : ¬g.Adj a b := by
  obtain ⟨c, rfl⟩ := (mem_componentPartition active g).1 hC
  obtain ⟨d, rfl⟩ := (mem_componentPartition active g).1 hD
  intro hab
  have hac := (mem_componentFamily active g c a).1 ha
  have hbd := (mem_componentFamily active g d b).1 hb
  have hcd : c = d := hac.symm.trans ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hab).trans hbd)
  exact hCD (congrArg (componentFamily active g) hcd)

/-- Two vertices in the same fiber have a walk in the original graph. -/
theorem componentPartition_reachable (active : Finset V) (g : SimpleGraph active)
    {C : Finset V} (hC : C ∈ componentPartition active g)
    {a b : active} (ha : a.1 ∈ C) (hb : b.1 ∈ C) : g.Reachable a b := by
  obtain ⟨c, rfl⟩ := (mem_componentPartition active g).1 hC
  apply SimpleGraph.ConnectedComponent.exact
  exact ((mem_componentFamily active g c a).1 ha).trans
    ((mem_componentFamily active g c b).1 hb).symm

/-- Large generators at one normalized integer threshold. -/
def largeGenerators (G : Finset (Finset ℕ)) (offset : ℤ) (H : ℕ) :
    Finset (Finset ℕ) :=
  G.filter fun A => -(H : ℤ) ≤ (A.card : ℤ) + offset

/-- Proximity on any finite active family, with normalized integer exponents. -/
def normalizedGraph (active : Finset (Finset ℕ)) (offset : ℤ) (H : ℕ) :
    SimpleGraph active where
  Adj A D := A ≠ D ∧ -(H : ℤ) ≤ ((A.1 ∩ D.1).card : ℤ) + offset
  symm := ⟨fun A D h => ⟨h.1.symm, by simpa [Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A uniform exceptional-set radius for a family with at most `k` members. -/
def clusterRadius (k B H : ℕ) : ℕ := H + k * k * (2 * (B + H))

theorem card_symmDiff_le_of_normalized_inter
    {A D : Finset ℕ} {offset : ℤ} {B H : ℕ}
    (hA : (A.card : ℤ) + offset ≤ B)
    (hD : (D.card : ℤ) + offset ≤ B)
    (hAD : -(H : ℤ) ≤ ((A ∩ D).card : ℤ) + offset) :
    (A ∆ D).card ≤ 2 * (B + H) := by
  have hdisj : Disjoint (A \ D) (D \ A) := by
    rw [Finset.disjoint_left]
    intro v hvAD hvDA
    exact (Finset.mem_sdiff.1 hvAD).2 (Finset.mem_sdiff.1 hvDA).1
  have hsplitA := Finset.card_sdiff_add_card_inter A D
  have hsplitD := Finset.card_sdiff_add_card_inter D A
  rw [Finset.inter_comm D A] at hsplitD
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdisj]
  omega

/-- Every query within a normalized cluster has a uniformly bounded-below
intersection exponent. The proof uses all proximity edges, avoiding any choice
of a spanning tree for individual clusters. -/
theorem normalized_cluster_intersection_lower
    (active : Finset (Finset ℕ)) (offset : ℤ) (B H : ℕ)
    (hupper : ∀ A ∈ active, (A.card : ℤ) + offset ≤ B)
    (hlower : ∀ A ∈ active, -(H : ℤ) ≤ (A.card : ℤ) + offset)
    {C : Finset (Finset ℕ)}
    (hC : C ∈ componentPartition active (normalizedGraph active offset H))
    {S : Finset (Finset ℕ)} (hSC : S ⊆ C) (hS : S.Nonempty) :
    -(clusterRadius active.card B H : ℤ) ≤
      ((S.inf' hS id).card : ℤ) + offset := by
  classical
  let g := normalizedGraph active offset H
  let F : active → Finset ℕ := Subtype.val
  let E := ClusterCore.spanningExceptionalSet g F
  have hE : E.card ≤ active.card * active.card * (2 * (B + H)) := by
    have he := ClusterCore.spanningExceptionalSet_card_le_square_mul
      (T := g) (G := F) (d := 2 * (B + H)) (by
        intro A D hAD
        exact card_symmDiff_le_of_normalized_inter
          (hupper A.1 A.2) (hupper D.1 D.2) hAD.2)
    simpa [E, Fintype.card_coe] using he
  let root := hS.choose
  have hrootS : root ∈ S := hS.choose_spec
  have hrootC : root ∈ C := hSC hrootS
  have hrootactive : root ∈ active := componentPartition_subset active g hC hrootC
  let root' : active := ⟨root, hrootactive⟩
  have hsubset : root \ E ⊆ S.inf' hS id := by
    intro v hv
    have hvroot := (Finset.mem_sdiff.mp hv).1
    have hvE := (Finset.mem_sdiff.mp hv).2
    rw [Finset.mem_inf' hS]
    intro A hAS
    have hAC := hSC hAS
    let A' : active := ⟨A, componentPartition_subset active g hC hAC⟩
    have hreach : g.Reachable root' A' :=
      componentPartition_reachable active g hC hrootC hAC
    let walk : g.Walk root' A' := Classical.choice hreach
    exact (ClusterCore.mem_iff_mem_of_walk_avoiding_exceptional
      (G := F) walk hvE).mp hvroot
  have hsubcard := Finset.card_le_card hsubset
  have hsplit := Finset.card_sdiff_add_card_inter root E
  have hinter : (root ∩ E).card ≤ E.card := Finset.card_le_card Finset.inter_subset_right
  have hrootlower := hlower root hrootactive
  unfold clusterRadius
  omega

/-- The clusters of the large generators in an original family. -/
noncomputable def normalizedClusterPartition (G : Finset (Finset ℕ))
    (offset : ℤ) (H : ℕ) : Finset (Finset (Finset ℕ)) :=
  componentPartition (largeGenerators G offset H)
    (normalizedGraph (largeGenerators G offset H) offset H)

theorem normalizedClusterPartition_intersection_lower
    (G : Finset (Finset ℕ)) (offset : ℤ) (B H : ℕ)
    (hupper : ∀ A ∈ G, (A.card : ℤ) + offset ≤ B)
    {C : Finset (Finset ℕ)} (hC : C ∈ normalizedClusterPartition G offset H)
    {S : Finset (Finset ℕ)} (hSC : S ⊆ C) (hS : S.Nonempty) :
    -(clusterRadius G.card B H : ℤ) ≤ ((S.inf' hS id).card : ℤ) + offset := by
  have h := normalized_cluster_intersection_lower (largeGenerators G offset H)
    offset B H (by
      intro A hA
      exact hupper A (Finset.mem_filter.mp hA).1) (by
      intro A hA
      exact (Finset.mem_filter.mp hA).2) hC hSC hS
  have hcard : (largeGenerators G offset H).card ≤ G.card := Finset.card_filter_le _ _
  have hrad : clusterRadius (largeGenerators G offset H).card B H ≤
      clusterRadius G.card B H := by
    unfold clusterRadius
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (Nat.mul_self_le_mul_self hcard)) _
  omega

theorem normalizedClusterPartition_cross_low
    (G : Finset (Finset ℕ)) (offset : ℤ) (H H' : ℕ)
    (hgap : ∀ A ∈ G, ∀ D ∈ G,
      -(H : ℤ) ≤ ((A ∩ D).card : ℤ) + offset ∨
        ((A ∩ D).card : ℤ) + offset < -(H' : ℤ))
    {C D : Finset (Finset ℕ)} (hC : C ∈ normalizedClusterPartition G offset H)
    (hD : D ∈ normalizedClusterPartition G offset H) (hCD : C ≠ D)
    {A E : Finset ℕ} (hA : A ∈ C) (hE : E ∈ D) :
    ((A ∩ E).card : ℤ) + offset < -(H' : ℤ) := by
  classical
  let active := largeGenerators G offset H
  let g := normalizedGraph active offset H
  have hAa : A ∈ active := componentPartition_subset active g hC hA
  have hEa : E ∈ active := componentPartition_subset active g hD hE
  let A' : active := ⟨A, hAa⟩
  let E' : active := ⟨E, hEa⟩
  have hne : A' ≠ E' := by
    intro heq
    have hv : A = E := congrArg Subtype.val heq
    have hdis := componentPartition_disjoint active g hC hD hCD
    exact Finset.disjoint_left.mp hdis hA (hv ▸ hE)
  have hnot := componentPartition_not_adj active g hC hD hCD
    (a := A') (b := E') hA hE
  rcases hgap A (Finset.mem_filter.mp hAa).1 E (Finset.mem_filter.mp hEa).1 with h | h
  · exact False.elim (hnot ⟨hne, h⟩)
  · exact h

/-- Every normalized cluster contains at least one generator. -/
theorem normalizedClusterPartition_nonempty
    (G : Finset (Finset ℕ)) (offset : ℤ) (H : ℕ)
    {C : Finset (Finset ℕ)} (hC : C ∈ normalizedClusterPartition G offset H) :
    C.Nonempty :=
  componentPartition_nonempty _ _ hC

/-- Every normalized cluster consists of large generators from the original family. -/
theorem normalizedClusterPartition_subset_large
    (G : Finset (Finset ℕ)) (offset : ℤ) (H : ℕ)
    {C : Finset (Finset ℕ)} (hC : C ∈ normalizedClusterPartition G offset H) :
    C ⊆ largeGenerators G offset H :=
  componentPartition_subset _ _ hC

theorem normalizedClusterPartition_subset
    (G : Finset (Finset ℕ)) (offset : ℤ) (H : ℕ)
    {C : Finset (Finset ℕ)} (hC : C ∈ normalizedClusterPartition G offset H) : C ⊆ G := by
  intro A hA
  exact (Finset.mem_filter.mp (normalizedClusterPartition_subset_large G offset H hC hA)).1

theorem normalizedClusterPartition_disjoint
    (G : Finset (Finset ℕ)) (offset : ℤ) (H : ℕ) :
    (normalizedClusterPartition G offset H : Set (Finset (Finset ℕ))).PairwiseDisjoint id :=
  componentPartition_disjoint _ _

theorem normalizedClusterPartition_biUnion
    (G : Finset (Finset ℕ)) (offset : ℤ) (H : ℕ) :
    (normalizedClusterPartition G offset H).biUnion id = largeGenerators G offset H :=
  componentPartition_biUnion _ _

theorem normalizedClusterPartition_sum_card
    (G : Finset (Finset ℕ)) (offset : ℤ) (H : ℕ) :
    ∑ C ∈ normalizedClusterPartition G offset H, C.card = (largeGenerators G offset H).card :=
  componentPartition_sum_card _ _

theorem normalizedClusterPartition_sum_card_le
    (G : Finset (Finset ℕ)) (offset : ℤ) (H : ℕ) :
    ∑ C ∈ normalizedClusterPartition G offset H, C.card ≤ G.card := by
  rw [normalizedClusterPartition_sum_card]
  exact Finset.card_filter_le _ _

/-- The pair gap assumption includes singleton exponents by taking equal generators. -/
theorem exponent_low_of_not_mem_largeGenerators
    (G : Finset (Finset ℕ)) (offset : ℤ) (H H' : ℕ)
    (hgap : ∀ A ∈ G, ∀ D ∈ G,
      -(H : ℤ) ≤ ((A ∩ D).card : ℤ) + offset ∨
        ((A ∩ D).card : ℤ) + offset < -(H' : ℤ))
    {A : Finset ℕ} (hA : A ∈ G) (hsmall : A ∉ largeGenerators G offset H) :
    (A.card : ℤ) + offset < -(H' : ℤ) := by
  have hnot : ¬ -(H : ℤ) ≤ (A.card : ℤ) + offset := by
    intro h
    exact hsmall (Finset.mem_filter.mpr ⟨hA, h⟩)
  have h := hgap A hA A hA
  simpa only [Finset.inter_self, or_iff_right hnot] using h

/-- A missing generator gives a strict saving in the total cluster cost. -/
theorem normalizedClusterPartition_sum_card_lt
    (G : Finset (Finset ℕ)) (offset : ℤ) (H : ℕ)
    (hsmall : ∃ A ∈ G, A ∉ largeGenerators G offset H) :
    ∑ C ∈ normalizedClusterPartition G offset H, C.card < G.card := by
  rw [normalizedClusterPartition_sum_card]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  obtain ⟨A, hA, hnot⟩ := hsmall
  exact hnot (heq.symm ▸ hA)

end AntichainOfGivenSize.BlockCount
