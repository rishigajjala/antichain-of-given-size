import AntichainOfGivenSize.Section6.Core
import AntichainOfGivenSize.LowerBound.VennProfiles
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.SymmDiff

/-!
# The finite cluster-compression core

This file isolates the exact, finite combinatorics used by the connected-cluster
argument.  There are no asymptotic hypotheses here.  In particular, the
inclusion--exclusion compression at the end is an equality in `ℤ`, so it keeps
all signs and carries.
-/

open scoped BigOperators symmDiff
open Finset

namespace AntichainOfGivenSize.ClusterCore

variable {ι V : Type*}

/-! ## Intersection proximity graphs -/

/-- Two distinct generators are close at loss scale `ρ` if their intersection
has more than `B - ρ` elements. -/
def intersectionProximityGraph [DecidableEq ι] [DecidableEq V]
    (G : ι → Finset V) (B ρ : ℕ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ B - ρ < #(G i ∩ G j)
  symm := ⟨fun i j h ↦ ⟨h.1.symm, by simpa [inter_comm] using h.2⟩⟩
  loopless := ⟨fun _i h ↦ h.1 rfl⟩

@[simp] theorem intersectionProximityGraph_adj [DecidableEq ι] [DecidableEq V]
    (G : ι → Finset V) (B ρ : ℕ) (i j : ι) :
    (intersectionProximityGraph G B ρ).Adj i j ↔
      i ≠ j ∧ B - ρ < #(G i ∩ G j) :=
  Iff.rfl

/-- Increasing the permitted loss only adds proximity edges. -/
theorem intersectionProximityGraph_mono [DecidableEq ι] [DecidableEq V]
    (G : ι → Finset V) (B : ℕ) {ρ ρ' : ℕ} (hρ : ρ ≤ ρ') :
    intersectionProximityGraph G B ρ ≤ intersectionProximityGraph G B ρ' := by
  intro i j hij
  rw [intersectionProximityGraph_adj] at hij ⊢
  exact ⟨hij.1, lt_of_le_of_lt (Nat.sub_le_sub_left hρ B) hij.2⟩

/-- A proximity edge has small symmetric difference.  This is the exact
finite version of the estimate `|Aᵢ △ Aⱼ| < 2ρ`. -/
theorem card_symmDiff_lt_two_mul_of_proximity
    [DecidableEq V] {A D : Finset V} {B ρ : ℕ}
    (hA : #A ≤ B) (hD : #D ≤ B) (hclose : B - ρ < #(A ∩ D)) :
    #(A ∆ D) < 2 * ρ := by
  have hdisj : Disjoint (A \ D) (D \ A) := by
    rw [Finset.disjoint_left]
    intro v hvAD hvDA
    exact (Finset.mem_sdiff.1 hvAD).2 (Finset.mem_sdiff.1 hvDA).1
  have hsplitA := card_sdiff_add_card_inter A D
  have hsplitD := card_sdiff_add_card_inter D A
  rw [inter_comm D A] at hsplitD
  rw [Finset.symmDiff_def, card_union_of_disjoint hdisj]
  omega

theorem card_symmDiff_lt_two_mul_of_adj
    [DecidableEq ι] [DecidableEq V] {G : ι → Finset V} {B ρ : ℕ}
    (hsize : ∀ i, #(G i) ≤ B) {i j : ι}
    (hij : (intersectionProximityGraph G B ρ).Adj i j) :
    #(G i ∆ G j) < 2 * ρ :=
  card_symmDiff_lt_two_mul_of_proximity (hsize i) (hsize j)
    (intersectionProximityGraph_adj G B ρ i j |>.1 hij).2

/-! ## Connected packings and a common stable gap -/

/-- Connectivity of the graph induced on a finite vertex set. -/
def ConnectedOn (g : SimpleGraph ι) (C : Finset ι) : Prop :=
  (g.induce (C : Set ι)).Connected

theorem connectedOn_mono {g g' : SimpleGraph ι} {C : Finset ι}
    (hgg' : g ≤ g') (hC : ConnectedOn g C) : ConnectedOn g' C := by
  apply hC.mono
  intro i j hij
  exact hgg' hij

/-- A connected subset of the active vertices with at least `h` vertices. -/
def IsLargeConnectedSet (g : SimpleGraph ι) (active : Finset ι)
    (h : ℕ) (C : Finset ι) : Prop :=
  C ⊆ active ∧ h ≤ #C ∧ ConnectedOn g C

/-- A labelled collection of pairwise disjoint large connected sets.  Using
`h ≤ |C|` instead of equality avoids an inessential tree-pruning lemma. -/
def IsConnectedPacking (g : SimpleGraph ι) (active : Finset ι)
    (h : ℕ) (P : Finset (Finset ι)) : Prop :=
  (∀ C ∈ P, IsLargeConnectedSet g active h C) ∧
    (P : Set (Finset ι)).PairwiseDisjoint id

/-- Existence of a packing with exactly `r` labelled cluster sets. -/
def HasConnectedPacking [DecidableEq ι] (g : SimpleGraph ι)
    (active : Finset ι) (h r : ℕ) : Prop :=
  ∃ P : Finset (Finset ι), IsConnectedPacking g active h P ∧ #P = r

theorem IsLargeConnectedSet.mono {g g' : SimpleGraph ι} {active : Finset ι}
    {h : ℕ} {C : Finset ι} (hgg' : g ≤ g')
    (hC : IsLargeConnectedSet g active h C) :
    IsLargeConnectedSet g' active h C :=
  ⟨hC.1, hC.2.1, connectedOn_mono hgg' hC.2.2⟩

theorem IsConnectedPacking.mono {g g' : SimpleGraph ι} {active : Finset ι}
    {h : ℕ} {P : Finset (Finset ι)} (hgg' : g ≤ g')
    (hP : IsConnectedPacking g active h P) :
    IsConnectedPacking g' active h P := by
  refine ⟨?_, hP.2⟩
  intro C hCP
  exact (hP.1 C hCP).mono hgg'

theorem HasConnectedPacking.mono [DecidableEq ι]
    {g g' : SimpleGraph ι} {active : Finset ι} {h r : ℕ}
    (hgg' : g ≤ g') (hP : HasConnectedPacking g active h r) :
    HasConnectedPacking g' active h r := by
  rcases hP with ⟨P, hpack, hcard⟩
  exact ⟨P, hpack.mono hgg', hcard⟩

/-- `J` monotone Boolean rows have a common unchanged adjacent gap among
`J+1` gaps.  This is the finite pigeonhole step behind the stable-scale
selection. -/
theorem exists_common_stable_gap (J : ℕ)
    (P : Fin J → Fin (J + 2) → Prop)
    (hanti : ∀ s i j, i ≤ j → P s j → P s i) :
    ∃ j : Fin (J + 1), ∀ s : Fin J,
      (P s j.castSucc ↔ P s j.succ) := by
  classical
  by_contra hstable
  push Not at hstable
  choose witness hwitness using hstable
  have hchange : ∀ j : Fin (J + 1),
      P (witness j) j.castSucc ∧ ¬ P (witness j) j.succ := by
    intro j
    have hstep : P (witness j) j.succ → P (witness j) j.castSucc :=
      hanti _ _ _ j.castSucc_le_succ
    rcases hwitness j with h | h
    · exact h
    · exact False.elim (h.1 (hstep h.2))
  have hinj : Function.Injective witness := by
    intro i j hij
    apply Fin.eq_of_val_eq
    by_contra hval
    rcases lt_or_gt_of_ne hval with hijval | hjival
    · have hle : i.succ ≤ j.castSucc := by
        change i.1 + 1 ≤ j.1
        omega
      have hp : P (witness j) i.succ :=
        hanti _ _ _ hle (hchange j).1
      rw [← hij] at hp
      exact (hchange i).2 hp
    · have hle : j.succ ≤ i.castSucc := by
        change j.1 + 1 ≤ i.1
        omega
      have hp : P (witness i) j.succ :=
        hanti _ _ _ hle (hchange i).1
      rw [hij] at hp
      exact (hchange j).2 hp
  have hcard := Fintype.card_le_of_injective witness hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- Stable-gap selection specialized to decreasing loss scales and connected
packings.  Row `s` asks for `s+1` disjoint clusters. -/
theorem exists_packing_stable_gap [DecidableEq ι] [DecidableEq V]
    (G : ι → Finset V) (active : Finset ι) (B h J : ℕ)
    (ρ : Fin (J + 2) → ℕ) (hρ : Antitone ρ) :
    ∃ j : Fin (J + 1), ∀ s : Fin J,
      (HasConnectedPacking
          (intersectionProximityGraph G B (ρ j.castSucc)) active h (s.1 + 1) ↔
       HasConnectedPacking
          (intersectionProximityGraph G B (ρ j.succ)) active h (s.1 + 1)) := by
  apply exists_common_stable_gap J
    (P := fun s i ↦ HasConnectedPacking
      (intersectionProximityGraph G B (ρ i)) active h (s.1 + 1))
  intro s i j hij hpack
  apply hpack.mono
  apply intersectionProximityGraph_mono
  exact hρ hij

/-! ## Exceptional sets and agreement outside them -/

/-- Symmetric differences along all directed edges of a finite graph.  When
the graph is a spanning tree, this is precisely the exceptional set needed
to propagate agreement through the cluster (each undirected edge is merely
listed twice). -/
noncomputable def spanningExceptionalSet [Fintype ι] [DecidableEq V]
    (T : SimpleGraph ι) (G : ι → Finset V) : Finset V :=
  by
    classical
    exact Finset.univ.biUnion fun i ↦
      (Finset.univ.filter fun j ↦ T.Adj i j).biUnion fun j ↦ G i ∆ G j

theorem symmDiff_subset_spanningExceptionalSet [Fintype ι] [DecidableEq V]
    {T : SimpleGraph ι} {G : ι → Finset V} {i j : ι} (hij : T.Adj i j) :
    G i ∆ G j ⊆ spanningExceptionalSet T G := by
  classical
  intro v hv
  simp only [spanningExceptionalSet, mem_biUnion, mem_univ, true_and,
    mem_filter]
  exact ⟨i, j, hij, hv⟩

theorem mem_iff_mem_of_not_mem_symmDiff [DecidableEq V]
    {A D : Finset V} {v : V} (hv : v ∉ A ∆ D) :
    (v ∈ A ↔ v ∈ D) := by
  simp only [mem_symmDiff, not_or, not_and] at hv
  tauto

theorem mem_iff_mem_of_walk_avoiding_exceptional
    [Fintype ι] [DecidableEq V] {T : SimpleGraph ι} {G : ι → Finset V}
    {i j : ι} (p : T.Walk i j) {v : V}
    (hv : v ∉ spanningExceptionalSet T G) :
    (v ∈ G i ↔ v ∈ G j) := by
  induction p with
  | nil => rfl
  | @cons u w z huw p ih =>
      have hnot : v ∉ G u ∆ G w := fun hvd ↦
        hv (symmDiff_subset_spanningExceptionalSet huw hvd)
      exact (mem_iff_mem_of_not_mem_symmDiff hnot).trans ih

/-- In a connected edge certificate, every generator agrees with the root
away from the union of the edge symmetric differences. -/
theorem cluster_agrees_off_spanningExceptionalSet
    [Fintype ι] [DecidableEq V] {T : SimpleGraph ι} (hT : T.Connected)
    (G : ι → Finset V) (root i : ι) {v : V}
    (hv : v ∉ spanningExceptionalSet T G) :
    (v ∈ G i ↔ v ∈ G root) := by
  let p : T.Walk i root := Classical.choice (hT i root)
  exact mem_iff_mem_of_walk_avoiding_exceptional p hv

/-- Every connected finite cluster admits a spanning-tree exceptional set;
outside it all cluster facets agree with the chosen root. -/
theorem exists_spanningTree_exceptional_agreement
    [DecidableEq ι] [DecidableEq V] {g : SimpleGraph ι}
    {C : Finset ι} (hC : ConnectedOn g C) (G : ι → Finset V) :
    ∃ T : SimpleGraph C, T ≤ g.induce (C : Set ι) ∧ T.IsTree ∧
      ∀ root i : C, ∀ v : V,
        v ∉ spanningExceptionalSet T (fun a : C ↦ G a.1) →
          (v ∈ G i.1 ↔ v ∈ G root.1) := by
  rcases hC.exists_isTree_le with ⟨T, hTle, hTtree⟩
  refine ⟨T, hTle, hTtree, ?_⟩
  intro root i v hv
  exact cluster_agrees_off_spanningExceptionalSet hTtree.connected
    (fun a : C ↦ G a.1) root i hv

/-- A deliberately coarse but robust cardinality bound for the exceptional
set.  It is useful both for a spanning tree and for the simplification in
which all close edges of a cluster are retained. -/
theorem spanningExceptionalSet_card_le_square_mul
    [Fintype ι] [DecidableEq V] {T : SimpleGraph ι} {G : ι → Finset V}
    {d : ℕ} (hedge : ∀ i j, T.Adj i j → #(G i ∆ G j) ≤ d) :
    #(spanningExceptionalSet T G) ≤
      Fintype.card ι * Fintype.card ι * d := by
  classical
  unfold spanningExceptionalSet
  calc
    #((Finset.univ : Finset ι).biUnion fun i ↦
        (Finset.univ.filter fun j ↦ T.Adj i j).biUnion fun j ↦ G i ∆ G j) ≤
        ∑ i : ι, #((Finset.univ.filter fun j ↦ T.Adj i j).biUnion
          fun j ↦ G i ∆ G j) := card_biUnion_le
    _ ≤ ∑ _i : ι, Fintype.card ι * d := by
      apply Finset.sum_le_sum
      intro i _hi
      calc
        #((Finset.univ.filter fun j ↦ T.Adj i j).biUnion
            fun j ↦ G i ∆ G j) ≤
            ∑ j ∈ Finset.univ.filter (fun j ↦ T.Adj i j), #(G i ∆ G j) :=
          card_biUnion_le
        _ ≤ ∑ _j ∈ Finset.univ.filter (fun j ↦ T.Adj i j), d := by
          apply Finset.sum_le_sum
          intro j hj
          exact hedge i j (Finset.mem_filter.1 hj).2
        _ ≤ Fintype.card ι * d := by
          calc
            ∑ _j ∈ Finset.univ.filter (fun j ↦ T.Adj i j), d =
                #(Finset.univ.filter fun j ↦ T.Adj i j) * d := by simp
            _ ≤ #(Finset.univ : Finset ι) * d :=
              Nat.mul_le_mul_right d (Finset.card_filter_le _ _)
            _ = Fintype.card ι * d := by simp
    _ = Fintype.card ι * Fintype.card ι * d := by
      simp [mul_assoc]

/-- In particular, a spanning subgraph of the proximity graph has an
exceptional set of size at most `|ι|²(2ρ)`. -/
theorem spanningExceptionalSet_card_le_of_proximity
    [Fintype ι] [DecidableEq ι] [DecidableEq V]
    {T : SimpleGraph ι} {G : ι → Finset V} {B ρ : ℕ}
    (hT : T ≤ intersectionProximityGraph G B ρ)
    (hsize : ∀ i, #(G i) ≤ B) :
    #(spanningExceptionalSet T G) ≤
      Fintype.card ι * Fintype.card ι * (2 * ρ) := by
  apply spanningExceptionalSet_card_le_square_mul
  intro i j hij
  exact (card_symmDiff_lt_two_mul_of_adj hsize (hT hij)).le

/-! ## Exact grouped inclusion--exclusion -/

/-- Nonempty generator queries occurring in inclusion--exclusion. -/
abbrev IEQuery [DecidableEq ι] (s : Finset ι) :=
  ↥(s.powerset.filter (fun t : Finset ι ↦ t.Nonempty))

/-- The part of a query intersection inside the exceptional set. -/
def exceptionalIntersectionSize [DecidableEq ι] [DecidableEq V]
    {s : Finset ι} (G : ι → Finset V) (U : Finset V) (t : IEQuery s) : ℕ :=
  #((AntichainOfGivenSize.Section6.generatorIntersection G t) ∩ U)

/-- The part of a query intersection outside the exceptional set. -/
def regularIntersectionSize [DecidableEq ι] [DecidableEq V]
    {s : Finset ι} (G : ι → Finset V) (U : Finset V) (t : IEQuery s) : ℕ :=
  #((AntichainOfGivenSize.Section6.generatorIntersection G t) \ U)

theorem regular_add_exceptional_eq_intersection_card
    [DecidableEq ι] [DecidableEq V] {s : Finset ι}
    (G : ι → Finset V) (U : Finset V) (t : IEQuery s) :
    regularIntersectionSize G U t + exceptionalIntersectionSize G U t =
      #(AntichainOfGivenSize.Section6.generatorIntersection G t) := by
  exact card_sdiff_add_card_inter _ _

/-- The compressed support of a query: indices with the same `role` are
identified.  Taking `role = Sum.inl ∘ clusterOwner` on clusters and
`role i = Sum.inr i` on the residual facets gives the `(S,Q)` key from the
paper. -/
def compressionKey [DecidableEq ι] [DecidableEq κ]
    {s : Finset ι} (role : ι → κ) (t : IEQuery s) : Finset κ :=
  t.1.image role

/-- The semantic condition needed for role compression: generators with the
same role have identical incidence outside the exceptional set. -/
def RoleAgreementOutside [DecidableEq V]
    (G : ι → Finset V) (U : Finset V) (role : ι → κ) : Prop :=
  ∀ ⦃i j : ι⦄, role i = role j → ∀ ⦃v : V⦄, v ∉ U →
    (v ∈ G i ↔ v ∈ G j)

/-- Equal compressed supports have exactly equal intersections outside `U`.
This is the formal content of replacing every cluster by one base facet. -/
theorem generatorIntersection_sdiff_eq_of_compressionKey_eq
    [DecidableEq ι] [DecidableEq V] [DecidableEq κ]
    {s : Finset ι} {G : ι → Finset V} {U : Finset V} {role : ι → κ}
    (hagree : RoleAgreementOutside G U role) (t u : IEQuery s)
    (hkey : compressionKey role t = compressionKey role u) :
    AntichainOfGivenSize.Section6.generatorIntersection G t \ U =
      AntichainOfGivenSize.Section6.generatorIntersection G u \ U := by
  ext v
  constructor
  · intro hv
    have hvU : v ∉ U := (Finset.mem_sdiff.1 hv).2
    have hvall : ∀ i ∈ t.1, v ∈ G i := by
      simpa [AntichainOfGivenSize.Section6.generatorIntersection] using
        (Finset.mem_sdiff.1 hv).1
    apply Finset.mem_sdiff.2
    refine ⟨?_, hvU⟩
    simp only [AntichainOfGivenSize.Section6.generatorIntersection,
      Finset.mem_inf' (Finset.mem_filter.1 u.2).2]
    intro j hju
    have hjimage : role j ∈ compressionKey role u := by
      exact Finset.mem_image.2 ⟨j, hju, rfl⟩
    rw [← hkey] at hjimage
    rcases Finset.mem_image.1 hjimage with ⟨i, hit, hi⟩
    exact (hagree hi hvU).1 (hvall i hit)
  · intro hv
    have hvU : v ∉ U := (Finset.mem_sdiff.1 hv).2
    have hvall : ∀ j ∈ u.1, v ∈ G j := by
      simpa [AntichainOfGivenSize.Section6.generatorIntersection] using
        (Finset.mem_sdiff.1 hv).1
    apply Finset.mem_sdiff.2
    refine ⟨?_, hvU⟩
    simp only [AntichainOfGivenSize.Section6.generatorIntersection,
      Finset.mem_inf' (Finset.mem_filter.1 t.2).2]
    intro i hit
    have hiimage : role i ∈ compressionKey role t := by
      exact Finset.mem_image.2 ⟨i, hit, rfl⟩
    rw [hkey] at hiimage
    rcases Finset.mem_image.1 hiimage with ⟨j, hju, hj⟩
    exact (hagree hj hvU).1 (hvall j hju)

theorem regularIntersectionSize_eq_of_compressionKey_eq
    [DecidableEq ι] [DecidableEq V] [DecidableEq κ]
    {s : Finset ι} {G : ι → Finset V} {U : Finset V} {role : ι → κ}
    (hagree : RoleAgreementOutside G U role) (t u : IEQuery s)
    (hkey : compressionKey role t = compressionKey role u) :
    regularIntersectionSize G U t = regularIntersectionSize G U u := by
  exact congrArg Finset.card
    (generatorIntersection_sdiff_eq_of_compressionKey_eq hagree t u hkey)

/-- The signed coefficient of one compressed query is the exact sum over its
fiber, retaining the intersections with the exceptional set. -/
def groupedCoefficient [DecidableEq ι] [DecidableEq V] [DecidableEq κ]
    {s : Finset ι} (G : ι → Finset V) (U : Finset V)
    (key : IEQuery s → κ) (k : κ) : ℤ :=
  ∑ t ∈ (Finset.univ : Finset (IEQuery s)).filter (fun t ↦ key t = k),
    (-1 : ℤ) ^ (t.1.card + 1) * (2 : ℤ) ^ exceptionalIntersectionSize G U t

/-- Exact cluster compression.  The only semantic premise is that the
outside-`U` intersection cardinality is constant on each fiber of `key`.
No term is discarded and no congruence is taken. -/
theorem generatedIdealIdx_card_grouped_compression
    [DecidableEq ι] [DecidableEq V] [DecidableEq κ]
    (s : Finset ι) (G : ι → Finset V) (U : Finset V)
    (key : IEQuery s → κ) (outsideExponent : κ → ℕ)
    (houtside : ∀ t : IEQuery s,
      regularIntersectionSize G U t = outsideExponent (key t)) :
    ((AntichainOfGivenSize.Section6.generatedIdealIdx s G).card : ℤ) =
      ∑ k ∈ (Finset.univ : Finset (IEQuery s)).image key,
        (2 : ℤ) ^ outsideExponent k * groupedCoefficient G U key k := by
  rw [AntichainOfGivenSize.Section6.generatedIdealIdx_card_inclusionExclusion]
  classical
  let Q : Finset (IEQuery s) := Finset.univ
  let term : IEQuery s → ℤ := fun t ↦
    (-1 : ℤ) ^ (t.1.card + 1) *
      (2 : ℤ) ^ (AntichainOfGivenSize.Section6.generatorIntersection G t).card
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s := Q) (t := Q.image key) (g := key)
    (fun t _ ↦ Finset.mem_image_of_mem key (Finset.mem_univ t))
    term
  change (∑ t ∈ Q, term t) = _
  rw [← hgroup]
  apply Finset.sum_congr rfl
  intro k hk
  unfold groupedCoefficient
  rw [Finset.mul_sum]
  change (∑ t ∈ Q with key t = k, term t) = _
  simp only [Q]
  apply Finset.sum_congr rfl
  intro t ht
  have hkey : key t = k := (Finset.mem_filter.1 ht).2
  change term t = (2 : ℤ) ^ outsideExponent k *
      ((-1 : ℤ) ^ (t.1.card + 1) *
        (2 : ℤ) ^ exceptionalIntersectionSize G U t)
  rw [← hkey, ← houtside t]
  simp only [term]
  rw [← regular_add_exceptional_eq_intersection_card G U t, pow_add]
  ring

end AntichainOfGivenSize.ClusterCore
