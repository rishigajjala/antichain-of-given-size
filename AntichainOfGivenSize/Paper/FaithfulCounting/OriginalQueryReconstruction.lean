import AntichainOfGivenSize.LowerBound.ClusterStateConstruction
import AntichainOfGivenSize.LowerBound.ClusterEncoding

open scoped BigOperators symmDiff
open Finset
open AntichainOfGivenSize.ClusterCore

namespace AntichainOfGivenSize.FaithfulLower

variable {ι V : Type*} [DecidableEq V]

def edgeDifference (G : ι → Finset V) : Sym2 ι → Finset V :=
  Sym2.lift ⟨fun i j ↦ G i ∆ G j, fun i j ↦ symmDiff_comm (G i) (G j)⟩

@[simp] theorem edgeDifference_pair (G : ι → Finset V) (i j : ι) :
    edgeDifference G s(i,j) = G i ∆ G j := rfl

noncomputable def edgeExceptional [Fintype ι] (T : SimpleGraph ι)
    [Fintype T.edgeSet] (G : ι → Finset V) : Finset V := by
  classical
  exact T.edgeFinset.biUnion (edgeDifference G)

theorem spanningExceptional_eq_edgeExceptional [Fintype ι]
    (T : SimpleGraph ι) [Fintype T.edgeSet] (G : ι → Finset V) :
    spanningExceptionalSet T G = edgeExceptional T G := by
  classical
  ext x
  simp only [spanningExceptionalSet, edgeExceptional, mem_biUnion,
    mem_univ, true_and, mem_filter]
  constructor
  · rintro ⟨i, j, hij, hx⟩
    exact ⟨s(i,j), by simpa using hij, hx⟩
  · rintro ⟨e, he, hx⟩
    induction e using Sym2.ind with
    | _ i j => exact ⟨i, j, by simpa using he, hx⟩

theorem edgeExceptional_card_le [Fintype ι]
    (T : SimpleGraph ι) [Fintype T.edgeSet] (G : ι → Finset V) {d : ℝ}
    (hedge : ∀ i j, T.Adj i j → (#(G i ∆ G j) : ℝ) ≤ d) :
    (#(edgeExceptional T G) : ℝ) ≤ (T.edgeFinset.card : ℝ) * d := by
  classical
  calc
    (#(edgeExceptional T G) : ℝ) ≤
        ∑ e ∈ T.edgeFinset, (#(edgeDifference G e) : ℝ) := by
      unfold edgeExceptional
      exact_mod_cast (Finset.card_biUnion_le :
        #(T.edgeFinset.biUnion (edgeDifference G)) ≤
          ∑ e ∈ T.edgeFinset, #(edgeDifference G e))
    _ ≤ ∑ _e ∈ T.edgeFinset, d := by
      apply Finset.sum_le_sum
      intro e he
      induction e using Sym2.ind with
      | _ i j => exact hedge i j (by simpa using he)
    _ = (T.edgeFinset.card : ℝ) * d := by simp

noncomputable def clusterVariation (G : ι → Finset V) (C : Finset ι) : Finset V := by
  classical
  exact C.biUnion fun i ↦ C.biUnion fun j ↦ G i ∆ G j

theorem mem_clusterVariation (G : ι → Finset V) (C : Finset ι) (x : V) :
    x ∈ clusterVariation G C ↔ ∃ i ∈ C, ∃ j ∈ C, x ∈ G i ∆ G j := by
  classical
  simp [clusterVariation]

theorem clusterVariation_subset_treeExceptional [DecidableEq ι]
    {C : Finset ι} {T : SimpleGraph C} [Fintype T.edgeSet] (hT : T.Connected)
    (G : ι → Finset V) :
    clusterVariation G C ⊆ edgeExceptional T (fun i : C ↦ G i) := by
  classical
  intro x hx
  by_contra hnot
  rw [← spanningExceptional_eq_edgeExceptional] at hnot
  rcases (mem_clusterVariation G C x).1 hx with ⟨i, hi, j, hj, hxij⟩
  have hagree := cluster_agrees_off_spanningExceptionalSet hT
    (fun i : C ↦ G i) (⟨j,hj⟩ : C) (⟨i,hi⟩ : C) hnot
  simp only [Finset.mem_symmDiff] at hxij
  exact hxij.elim (fun h ↦ h.2 (hagree.mp h.1))
    (fun h ↦ h.2 (hagree.mpr h.1))

/-- Intrinsic varying membership costs at most one edge bound per tree edge. -/
theorem clusterVariation_card_le [DecidableEq ι]
    {g : SimpleGraph ι} {C : Finset ι} (hC : ConnectedOn g C)
    (G : ι → Finset V) {d : ℝ}
    (hedge : ∀ i j, g.Adj i j → (#(G i ∆ G j) : ℝ) ≤ d) :
    (#(clusterVariation G C) : ℝ) ≤ ((C.card - 1 : ℕ) : ℝ) * d := by
  classical
  obtain ⟨T, hTle, hT⟩ := hC.exists_isTree_le
  calc
    (#(clusterVariation G C) : ℝ) ≤
        (#(edgeExceptional T (fun i : C ↦ G i)) : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (clusterVariation_subset_treeExceptional hT.connected G)
    _ ≤ (T.edgeFinset.card : ℝ) * d :=
      edgeExceptional_card_le T (fun i : C ↦ G i)
        (fun i j hij ↦ hedge i j (hTle hij))
    _ = ((C.card - 1 : ℕ) : ℝ) * d := by
      have hc := hT.card_edgeFinset
      have hcard : Fintype.card (C : Set ι) = C.card := Fintype.card_coe C
      rw [hcard] at hc
      have hc' : T.edgeFinset.card = C.card - 1 := by
        exact Nat.eq_sub_of_add_eq hc
      rw [hc']

/-- The union is defined using varying membership within each block, independently
of any tree selected for the size proof. -/
noncomputable def intrinsicExceptional (G : ι → Finset V)
    (P : Finset (Finset ι)) : Finset V := by
  classical
  exact P.biUnion (clusterVariation G)

/-- The exact tree-edge count; no equal-size or covering assumption is needed. -/
theorem intrinsicExceptional_card_le_sum [DecidableEq ι]
    {g : SimpleGraph ι} {P : Finset (Finset ι)}
    (hconn : ∀ C ∈ P, ConnectedOn g C) (G : ι → Finset V) {d : ℝ}
    (hedge : ∀ i j, g.Adj i j → (#(G i ∆ G j) : ℝ) ≤ d) :
    (#(intrinsicExceptional G P) : ℝ) ≤
      (∑ C ∈ P, ((C.card - 1 : ℕ) : ℝ)) * d := by
  classical
  calc
    (#(intrinsicExceptional G P) : ℝ) ≤
        ∑ C ∈ P, (#(clusterVariation G C) : ℝ) := by
      unfold intrinsicExceptional
      exact_mod_cast (Finset.card_biUnion_le :
        #(P.biUnion (clusterVariation G)) ≤ ∑ C ∈ P, #(clusterVariation G C))
    _ ≤ ∑ C ∈ P, ((C.card - 1 : ℕ) : ℝ) * d := by
      exact Finset.sum_le_sum (fun C hC ↦ clusterVariation_card_le (hconn C hC) G hedge)
    _ = (∑ C ∈ P, ((C.card - 1 : ℕ) : ℝ)) * d := by rw [Finset.sum_mul]

/-- Pairwise disjoint clusters use at most the ambient number of vertices. -/
theorem intrinsicExceptional_card_le [Fintype ι] [DecidableEq ι]
    {g : SimpleGraph ι} {P : Finset (Finset ι)}
    (hconn : ∀ C ∈ P, ConnectedOn g C)
    (hdisj : (P : Set (Finset ι)).PairwiseDisjoint id)
    (G : ι → Finset V) {d : ℝ} (hd : 0 ≤ d)
    (hedge : ∀ i j, g.Adj i j → (#(G i ∆ G j) : ℝ) ≤ d) :
    (#(intrinsicExceptional G P) : ℝ) ≤ (Fintype.card ι : ℝ) * d := by
  classical
  have hcards : ∑ C ∈ P, C.card ≤ Fintype.card ι := by
    calc
      ∑ C ∈ P, C.card = #(P.biUnion id) := by
        simpa only [id_eq] using (Finset.card_biUnion hdisj).symm
      _ ≤ Fintype.card ι := Finset.card_le_univ (P.biUnion id)
  have hsum : (∑ C ∈ P, ((C.card - 1 : ℕ) : ℝ)) ≤ (Fintype.card ι : ℝ) := by
    have hnat : ∑ C ∈ P, (C.card - 1) ≤ Fintype.card ι :=
      (Finset.sum_le_sum (fun C _hC ↦ Nat.sub_le C.card 1)).trans hcards
    exact_mod_cast hnat
  exact (intrinsicExceptional_card_le_sum hconn G hedge).trans
    (mul_le_mul_of_nonneg_right hsum hd)

/-- The paper's real-scale edge estimate, with no floor of the threshold. -/
theorem symmDiff_card_lt_real_proximity {A D : Finset V} {B : ℕ} {ρ : ℝ}
    (hA : A.card ≤ B) (hD : D.card ≤ B)
    (hclose : (B : ℝ) - ρ < (#(A ∩ D) : ℝ)) :
    (#(A ∆ D) : ℝ) < 2 * ρ := by
  have hdisj : Disjoint (A \ D) (D \ A) := by
    rw [Finset.disjoint_left]
    intro v hvAD hvDA
    exact (Finset.mem_sdiff.1 hvAD).2 (Finset.mem_sdiff.1 hvDA).1
  have hsplitA : (#(A \ D) : ℝ) + #(A ∩ D) = #A := by
    exact_mod_cast card_sdiff_add_card_inter A D
  have hsplitD : (#(D \ A) : ℝ) + #(A ∩ D) = #D := by
    simpa only [inter_comm] using
      (show (#(D \ A) : ℝ) + #(D ∩ A) = #D by
        exact_mod_cast card_sdiff_add_card_inter D A)
  rw [Finset.symmDiff_def, card_union_of_disjoint hdisj, Nat.cast_add]
  have hA' : (#A : ℝ) ≤ B := by exact_mod_cast hA
  have hD' : (#D : ℝ) ≤ B := by exact_mod_cast hD
  linarith

def realProximityGraph [DecidableEq ι] (G : ι → Finset V)
    (B : ℕ) (ρ : ℝ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (B : ℝ) - ρ < (#(G i ∩ G j) : ℝ)
  symm := ⟨fun i j h ↦ ⟨h.1.symm, by simpa [inter_comm] using h.2⟩⟩
  loopless := ⟨fun _i h ↦ h.1 rfl⟩

/-- The literal paper bound |U| ≤ 2Kρ', for intrinsic U and real ρ'. -/
theorem intrinsicExceptional_card_le_two_mul {K B : ℕ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (G : Fin K → Finset V)
    (hsize : ∀ i, #(G i) ≤ B) {P : Finset (Finset (Fin K))}
    (hconn : ∀ C ∈ P, ConnectedOn (realProximityGraph G B ρ) C)
    (hdisj : (P : Set (Finset (Fin K))).PairwiseDisjoint id) :
    (#(intrinsicExceptional G P) : ℝ) ≤ 2 * K * ρ := by
  have hedge : ∀ i j, (realProximityGraph G B ρ).Adj i j →
      (#(G i ∆ G j) : ℝ) ≤ 2 * ρ := by
    intro i j hij
    exact (symmDiff_card_lt_real_proximity (hsize i) (hsize j) hij.2).le
  have h := intrinsicExceptional_card_le hconn hdisj G (by positivity : 0 ≤ 2 * ρ) hedge
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

theorem mem_intrinsicExceptional (G : ι → Finset V)
    (P : Finset (Finset ι)) (x : V) :
    x ∈ intrinsicExceptional G P ↔
      ∃ C ∈ P, ∃ i ∈ C, ∃ j ∈ C, ¬ (x ∈ G i ↔ x ∈ G j) := by
  classical
  simp only [intrinsicExceptional, clusterVariation, mem_biUnion, mem_symmDiff]
  constructor
  · rintro ⟨C, hC, i, hi, j, hj, h⟩
    exact ⟨C, hC, i, hi, j, hj, by tauto⟩
  · rintro ⟨C, hC, i, hi, j, hj, h⟩
    exact ⟨C, hC, i, hi, j, hj, by tauto⟩

/-- This is the paper's agreement on W, stated pointwise. -/
theorem cluster_agrees_off_intrinsicExceptional
    (G : ι → Finset V) {P : Finset (Finset ι)} {C : Finset ι}
    (hC : C ∈ P) {i j : ι} (hi : i ∈ C) (hj : j ∈ C) {x : V}
    (hx : x ∉ intrinsicExceptional G P) : (x ∈ G i ↔ x ∈ G j) := by
  by_contra h
  exact hx ((mem_intrinsicExceptional G P x).2 ⟨C, hC, i, hi, j, hj, h⟩)

theorem cluster_sdiff_intrinsicExceptional_eq
    (G : ι → Finset V) {P : Finset (Finset ι)} {C : Finset ι}
    (hC : C ∈ P) {i j : ι} (hi : i ∈ C) (hj : j ∈ C) :
    G i \ intrinsicExceptional G P = G j \ intrinsicExceptional G P := by
  ext x
  simp only [mem_sdiff]
  constructor
  · rintro ⟨hxi, hx⟩
    exact ⟨(cluster_agrees_off_intrinsicExceptional G hC hi hj hx).mp hxi, hx⟩
  · rintro ⟨hxj, hx⟩
    exact ⟨(cluster_agrees_off_intrinsicExceptional G hC hi hj hx).mpr hxj, hx⟩

/-- Exact intermediate bound for r disjoint or overlapping h-vertex clusters.
Disjointness is used only to simplify this to the final 2Kρ bound. -/
theorem intrinsicExceptional_card_le_uniform {K B r h : ℕ} {ρ : ℝ}
    (G : Fin K → Finset V) (hsize : ∀ i, #(G i) ≤ B)
    {P : Finset (Finset (Fin K))}
    (hconn : ∀ C ∈ P, ConnectedOn (realProximityGraph G B ρ) C)
    (hcard : ∀ C ∈ P, C.card = h) (hP : P.card = r) :
    (#(intrinsicExceptional G P) : ℝ) ≤ 2 * r * ((h - 1 : ℕ) : ℝ) * ρ := by
  have hedge : ∀ i j, (realProximityGraph G B ρ).Adj i j →
      (#(G i ∆ G j) : ℝ) ≤ 2 * ρ := by
    intro i j hij
    exact (symmDiff_card_lt_real_proximity (hsize i) (hsize j) hij.2).le
  have hs := intrinsicExceptional_card_le_sum hconn G hedge
  have heq : (∑ C ∈ P, ((C.card - 1 : ℕ) : ℝ)) = r * ((h - 1 : ℕ) : ℝ) := by
    calc
      (∑ C ∈ P, ((C.card - 1 : ℕ) : ℝ)) = ∑ _C ∈ P, ((h - 1 : ℕ) : ℝ) := by
        exact Finset.sum_congr rfl (fun C hC ↦ by rw [hcard C hC])
      _ = r * ((h - 1 : ℕ) : ℝ) := by simp [hP]
  rw [heq] at hs
  convert hs using 1
  ring


end AntichainOfGivenSize.FaithfulLower

open AntichainOfGivenSize.ClusterCore
open AntichainOfGivenSize.ClusterLowerBound
open AntichainOfGivenSize.Section6
open AntichainOfGivenSize.VennProfile

namespace AntichainOfGivenSize.FaithfulLower

variable {I V W κ : Type*} [Fintype I] [DecidableEq I]
  [DecidableEq V] [DecidableEq W] [DecidableEq κ]

/-- Multiplicities of the membership words of the points in the chosen U. -/
noncomputable def incidenceCount (G : I → Finset V) (U : Finset V)
    (A : Finset I) : ℕ :=
  (U.filter fun v ↦ membershipPattern G v = A).card

theorem sum_incidenceCount (G : I → Finset V) (U : Finset V) :
    ∑ A : Finset I, incidenceCount G U A = U.card := by
  classical
  unfold incidenceCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp

/-- The existing multiplicity code, now parameterized by the chosen U. -/
noncomputable def incidenceSparseCode
    (G : I → Finset V) (U : Finset V) (u : ℕ) (hU : U.card ≤ u) :
    SparseCode (Finset I) u :=
  SparseCode.ofNat u (incidenceCount G U) (by
    rw [sum_incidenceCount]
    exact hU)

theorem incidenceCount_eq_of_sparseCode_eq
    (G : I → Finset V) (H : I → Finset W) (U : Finset V) (Z : Finset W)
    (u : ℕ) (hU : U.card ≤ u) (hZ : Z.card ≤ u)
    (hcode : incidenceSparseCode G U u hU = incidenceSparseCode H Z u hZ) :
    incidenceCount G U = incidenceCount H Z := by
  funext A
  exact congrArg (fun c : SparseCode (Finset I) u ↦ (c.count A : ℕ)) hcode

/-- The exceptional exponent of any original index set is obtained from its
incidence words. This works for arbitrary finite U, not just global graph edges. -/
theorem exceptionalIntersectionSize_eq_incidence_sum
    (G : I → Finset V) (U : Finset V)
    (t : IEQuery (Finset.univ : Finset I)) :
    exceptionalIntersectionSize G U t =
      ∑ A ∈ Finset.univ.powerset.filter (t.1 ⊆ ·), incidenceCount G U A := by
  classical
  unfold exceptionalIntersectionSize incidenceCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  apply congrArg Finset.card
  ext v
  simp only [mem_filter, mem_inter]
  constructor
  · rintro ⟨hvI, hvU⟩
    refine ⟨hvU, mem_powerset.2 (subset_univ _), ?_⟩
    have hvAll : ∀ i ∈ t.1, v ∈ G i := by
      simpa [generatorIntersection] using hvI
    intro i hi
    exact (mem_membershipPattern G v i).2 (hvAll i hi)
  · rintro ⟨hvU, _hvPow, hvSub⟩
    refine ⟨?_, hvU⟩
    simp only [generatorIntersection, Finset.mem_inf' (Finset.mem_filter.1 t.2).2]
    intro i hi
    exact (mem_membershipPattern G v i).1 (hvSub hi)

/-- The central keys are fixed by the header alone. -/
noncomputable def centralKeys (role : I → κ)
    (centers : Finset (IEQuery (Finset.univ : Finset I))) : Finset (Finset κ) :=
  centers.image (compressionKey role)

noncomputable def centralRepresentative (role : I → κ)
    (centers : Finset (IEQuery (Finset.univ : Finset I)))
    (k : centralKeys role centers) : IEQuery (Finset.univ : Finset I) :=
  Classical.choose (Finset.mem_image.1 k.2)

theorem centralRepresentative_key (role : I → κ)
    (centers : Finset (IEQuery (Finset.univ : Finset I)))
    (k : centralKeys role centers) :
    compressionKey role (centralRepresentative role centers k) = k.1 :=
  (Classical.choose_spec (Finset.mem_image.1 k.2)).2

theorem regularIntersectionSize_le_generator_bound
    (G : I → Finset V) (U : Finset V) {B : ℕ}
    (hsize : ∀ i, #(G i) ≤ B) (t : IEQuery (Finset.univ : Finset I)) :
    regularIntersectionSize G U t ≤ B := by
  obtain ⟨i, hi⟩ := (Finset.mem_filter.1 t.2).2
  apply (Finset.card_le_card ?_).trans (hsize i)
  intro v hv
  have hvAll : ∀ j ∈ t.1, v ∈ G j := by
    simpa [generatorIntersection] using (Finset.mem_sdiff.1 hv).1
  exact hvAll i hi

/-- One bounded regular exponent for every central key, in fixed header order. -/
noncomputable def centralExponentVector
    (G : I → Finset V) (U : Finset V) (role : I → κ)
    (centers : Finset (IEQuery (Finset.univ : Finset I)))
    (B : ℕ) (hsize : ∀ i, #(G i) ≤ B) :
    centralKeys role centers → Fin (B + 1) := fun k ↦
  ⟨regularIntersectionSize G U (centralRepresentative role centers k),
    Nat.lt_succ_of_le (regularIntersectionSize_le_generator_bound
      G U hsize (centralRepresentative role centers k))⟩

/-- Number of possible vectors, with no cost for transmitting the keys. -/
theorem card_centralExponentVectors (role : I → κ)
    (centers : Finset (IEQuery (Finset.univ : Finset I))) (B : ℕ) :
    Fintype.card (centralKeys role centers → Fin (B + 1)) =
      (B + 1) ^ (centralKeys role centers).card := by
  classical
  simp

theorem centralExponentVector_recovers
    (G : I → Finset V) (U : Finset V) (role : I → κ)
    (centers : Finset (IEQuery (Finset.univ : Finset I)))
    (B : ℕ) (hsize : ∀ i, #(G i) ≤ B)
    (hagree : RoleAgreementOutside G U role)
    (t : IEQuery (Finset.univ : Finset I)) (ht : t ∈ centers) :
    regularIntersectionSize G U t =
      (centralExponentVector G U role centers B hsize
        ⟨compressionKey role t, Finset.mem_image_of_mem _ ht⟩ : ℕ) := by
  apply regularIntersectionSize_eq_of_compressionKey_eq hagree
  exact (centralRepresentative_key role centers
    ⟨compressionKey role t, Finset.mem_image_of_mem _ ht⟩).symm

/-- Equal records give equal FULL exponents in every original central IE term. -/
theorem central_intersection_card_eq_of_records_eq
    (G : I → Finset V) (H : I → Finset W) (U : Finset V) (Z : Finset W)
    (role : I → κ) (centers : Finset (IEQuery (Finset.univ : Finset I)))
    (B : ℕ) (hG : ∀ i, #(G i) ≤ B) (hH : ∀ i, #(H i) ≤ B)
    (hagreeG : RoleAgreementOutside G U role)
    (hagreeH : RoleAgreementOutside H Z role)
    (hinc : incidenceCount G U = incidenceCount H Z)
    (hexp : centralExponentVector G U role centers B hG =
      centralExponentVector H Z role centers B hH)
    (t : IEQuery (Finset.univ : Finset I)) (ht : t ∈ centers) :
    #(generatorIntersection G t) = #(generatorIntersection H t) := by
  have hregG := centralExponentVector_recovers G U role centers B hG hagreeG t ht
  have hregH := centralExponentVector_recovers H Z role centers B hH hagreeH t ht
  have hreg : regularIntersectionSize G U t = regularIntersectionSize H Z t := by
    rw [hregG, hregH, hexp]
  have hexc : exceptionalIntersectionSize G U t = exceptionalIntersectionSize H Z t := by
    rw [exceptionalIntersectionSize_eq_incidence_sum,
      exceptionalIntersectionSize_eq_incidence_sum, hinc]
  rw [← regular_add_exceptional_eq_intersection_card G U t,
    ← regular_add_exceptional_eq_intersection_card H Z t, hreg, hexc]

noncomputable def originalCentralSum (G : I → Finset V)
    (centers : Finset (IEQuery (Finset.univ : Finset I))) : ℤ :=
  ∑ t ∈ centers, (-1 : ℤ) ^ (t.1.card + 1) * (2 : ℤ) ^ #(generatorIntersection G t)

/-- The central sum keeps the original index sets and their original signs. -/
theorem originalCentralSum_eq_of_records_eq
    (G : I → Finset V) (H : I → Finset W) (U : Finset V) (Z : Finset W)
    (role : I → κ) (centers : Finset (IEQuery (Finset.univ : Finset I)))
    (B : ℕ) (hG : ∀ i, #(G i) ≤ B) (hH : ∀ i, #(H i) ≤ B)
    (hagreeG : RoleAgreementOutside G U role)
    (hagreeH : RoleAgreementOutside H Z role)
    (hinc : incidenceCount G U = incidenceCount H Z)
    (hexp : centralExponentVector G U role centers B hG =
      centralExponentVector H Z role centers B hH) :
    originalCentralSum G centers = originalCentralSum H centers := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [central_intersection_card_eq_of_records_eq G H U Z role centers B
    hG hH hagreeG hagreeH hinc hexp t ht]

theorem originalCentralSum_eq_of_sparseCode_vector_eq
    (G : I → Finset V) (H : I → Finset W) (U : Finset V) (Z : Finset W)
    (role : I → κ) (centers : Finset (IEQuery (Finset.univ : Finset I)))
    (B u : ℕ) (hG : ∀ i, #(G i) ≤ B) (hH : ∀ i, #(H i) ≤ B)
    (hU : U.card ≤ u) (hZ : Z.card ≤ u)
    (hagreeG : RoleAgreementOutside G U role)
    (hagreeH : RoleAgreementOutside H Z role)
    (hcode : incidenceSparseCode G U u hU = incidenceSparseCode H Z u hZ)
    (hexp : centralExponentVector G U role centers B hG =
      centralExponentVector H Z role centers B hH) :
    originalCentralSum G centers = originalCentralSum H centers :=
  originalCentralSum_eq_of_records_eq G H U Z role centers B hG hH hagreeG hagreeH
    (incidenceCount_eq_of_sparseCode_eq G H U Z u hU hZ hcode) hexp

/-- The existing packed role construction needs only agreement within blocks. -/
theorem packedRoleAgreementOutside_of_cluster_agreement
    {K h r : ℕ} {g : SimpleGraph (Fin K)} (P : PackedClusters g h r)
    (G : Fin K → Finset V) (U : Finset V)
    (hcluster : ∀ a i j, i ∈ P.cluster a → j ∈ P.cluster a →
      ∀ v, v ∉ U → (v ∈ G i ↔ v ∈ G j)) :
    RoleAgreementOutside G U P.role := by
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
      exact hcluster (Classical.choose hi) i j himem hjmem v hv
    next hj => exact False.elim (Sum.inl_ne_inr hrole)
  next hi =>
    split at hrole
    next hj => exact False.elim (Sum.inr_ne_inl hrole)
    next hj =>
      have hij : i = j := Sum.inr.inj hrole
      subst j
      rfl

noncomputable def packedClusterFamily {K h r : ℕ} {g : SimpleGraph (Fin K)}
    (P : PackedClusters g h r) : Finset (Finset (Fin K)) := by
  classical
  exact Finset.univ.image P.cluster

theorem packedRoleAgreementOutside_intrinsic
    {K h r : ℕ} {g : SimpleGraph (Fin K)} (P : PackedClusters g h r)
    (G : Fin K → Finset V) :
    RoleAgreementOutside G (intrinsicExceptional G (packedClusterFamily P)) P.role := by
  apply packedRoleAgreementOutside_of_cluster_agreement P
  intro a i j hi hj v hv
  exact cluster_agrees_off_intrinsicExceptional G
    (Finset.mem_image_of_mem P.cluster (Finset.mem_univ a)) hi hj hv

noncomputable def packedCenters {K h r : ℕ} {gFine : SimpleGraph (Fin K)}
    (P : PackedClusters gFine h r) (g : SimpleGraph (Fin K)) :
    Finset (IEQuery (Finset.univ : Finset (Fin K))) := by
  classical
  exact Finset.univ.filter (IsCenterQuery g P)

theorem packedKey_toRight {K h r : ℕ} {gFine : SimpleGraph (Fin K)}
    (P : PackedClusters gFine h r)
    (t : IEQuery (Finset.univ : Finset (Fin K))) :
    (compressionKey P.role t).toRight = P.residualPart t := by
  classical
  ext i
  simp only [Finset.mem_toRight, compressionKey, Finset.mem_image,
    PackedClusters.residualPart, Finset.mem_inter]
  constructor
  · rintro ⟨j, hjt, hrole⟩
    obtain ⟨rfl, hjR⟩ := (P.role_eq_inr_iff j i).1 hrole
    exact ⟨hjt, hjR⟩
  · rintro ⟨hit, hiR⟩
    exact ⟨i, hit, (P.role_eq_inr_iff i i).2 ⟨rfl, hiR⟩⟩

theorem packedKey_toRight_mem_centerRightKeys {K h r : ℕ}
    {gFine : SimpleGraph (Fin K)} (P : PackedClusters gFine h r)
    (g : SimpleGraph (Fin K)) (t : IEQuery (Finset.univ : Finset (Fin K)))
    (ht : IsCenterQuery g P t) :
    (compressionKey P.role t).toRight ∈ P.centerRightKeys g := by
  classical
  rw [packedKey_toRight]
  by_cases hQ : P.residualPart t = ∅
  · simp [hQ, PackedClusters.centerRightKeys]
  · obtain ⟨i, hiQ⟩ := Finset.nonempty_iff_ne_empty.2 hQ
    apply Finset.mem_insert.2
    right
    apply Finset.mem_biUnion.2
    refine ⟨i, (Finset.mem_inter.1 hiQ).2, Finset.mem_powerset.2 ?_⟩
    intro j hjQ
    have hiR : i ∈ P.residual := (Finset.mem_inter.1 hiQ).2
    have hjR : j ∈ P.residual := (Finset.mem_inter.1 hjQ).2
    apply (PackedClusters.mem_componentFiber g P i j).2
    refine ⟨hjR, ?_⟩
    exact (P.componentLabel_eq_iff g hjR hiR).2 (ht j hjQ i hiQ)

/-- The paper's central-key count, independent of U and the exponents. -/
theorem packedCentralKeys_card_le {K h r : ℕ}
    {gFine : SimpleGraph (Fin K)} (P : PackedClusters gFine h r)
    (g : SimpleGraph (Fin K))
    (hsmall : ∀ i ∈ P.residual, #(P.componentFiber g i) < h) :
    #(centralKeys P.role (packedCenters P g)) ≤ 2 ^ r * (1 + K * 2 ^ h) := by
  classical
  let target : Finset (Finset (Fin r) × Finset (Fin K)) :=
    (Finset.univ : Finset (Fin r)).powerset.product (P.centerRightKeys g)
  calc
    #(centralKeys P.role (packedCenters P g)) ≤ #target := by
      apply Finset.card_le_card_of_injOn (fun k ↦ Finset.sumEquiv k)
      · intro k hk
        rcases Finset.mem_image.1 hk with ⟨t, ht, rfl⟩
        apply Finset.mem_product.2
        refine ⟨Finset.mem_powerset.2 (Finset.subset_univ _), ?_⟩
        exact packedKey_toRight_mem_centerRightKeys P g t (Finset.mem_filter.1 ht).2
      · intro k _hk l _hl hkl
        exact Finset.sumEquiv.injective hkl
    _ = 2 ^ r * #(P.centerRightKeys g) := by simp [target]
    _ ≤ 2 ^ r * (1 + K * 2 ^ h) := by
      exact Nat.mul_le_mul_left _ (P.card_centerRightKeys_le g hsmall)

theorem packedCentralKeys_card_le_of_le {K h r J : ℕ}
    {gFine : SimpleGraph (Fin K)} (P : PackedClusters gFine h r)
    (g : SimpleGraph (Fin K)) (hr : r ≤ J)
    (hsmall : ∀ i ∈ P.residual, #(P.componentFiber g i) < h) :
    #(centralKeys P.role (packedCenters P g)) ≤ 2 ^ J * (1 + K * 2 ^ h) :=
  (packedCentralKeys_card_le P g hsmall).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega : 0 < 2) hr))



end AntichainOfGivenSize.FaithfulLower
