import AntichainOfGivenSize.Paper.FaithfulCounting.CompleteCounting
import AntichainOfGivenSize.Paper.Representation

/-! Complete interfaces for the compound mathematical claims in the counting
argument. Padding repeats generator zero; repeating any existing generator,
including the final generator used in the manuscript, preserves the same ideal.
The normalization below uses a genuine bijection from the active ground set. -/

open scoped BigOperators
open Finset
open AntichainOfGivenSize
open AntichainOfGivenSize.Section6
open AntichainOfGivenSize.ClusterCore
open AntichainOfGivenSize.ClusterLowerBound
open AntichainOfGivenSize.FaithfulLower.Numerical

namespace AntichainOfGivenSize.FaithfulLower

/-- Repeating a generator preserves the entire ideal, before relabelling. -/
theorem generatedIdealIdx_padded {s K : ℕ} {V : Type*} [DecidableEq V]
    (hs : 0 < s) (hsK : s ≤ K) (G : Fin s → Finset V) :
    generatedIdealIdx univ (fun i : Fin K ↦ G (paddedIndex hsK hs i)) =
      generatedIdealIdx univ G := by
  classical
  ext A
  simp only [generatedIdealIdx, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨paddedIndex hsK hs i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨Fin.castLE hsK i, by simpa using hi⟩

/-- Relabelling preserves the cardinality of an indexed generated ideal. -/
theorem generatedIdealIdx_card_map {I V W : Type*} [Fintype I]
    [DecidableEq I] [DecidableEq V] [DecidableEq W]
    (G : I → Finset V) (f : V ↪ W) :
    (generatedIdealIdx univ (fun i ↦ (G i).map f)).card =
      (generatedIdealIdx univ G).card := by
  have himage : univ.image (fun i ↦ (G i).map f) = mapFamily f (univ.image G) := by
    simp only [mapFamily, Finset.map_eq_image, Finset.image_image,
      finsetMapEmbedding, Function.comp_def, Function.Embedding.coeFn_mk]
  rw [generatedIdealIdx_eq_generatedIdeal_image, himage,
    generatedIdeal_mapFamily, Finset.card_map, ← generatedIdealIdx_eq_generatedIdeal_image]

/-- Pad to exactly K generators, delete unused points, and relabel the active
points by Fin N. The output has N<=KB and exactly the original ideal size. -/
theorem normalized_family {s K B : ℕ} {V : Type*} [DecidableEq V]
    (hs : 0 < s) (hsK : s ≤ K) (G : Fin s → Finset V)
    (hsize : ∀ i, (G i).card ≤ B) :
    ∃ N : ℕ, N = (univ.biUnion G).card ∧ N ≤ K * B ∧
      ∃ D : Fin K → Finset (Fin N),
      (∀ i, (D i).card ≤ B) ∧
      univ.biUnion D = univ ∧
      (generatedIdealIdx univ D).card = (generatedIdealIdx univ G).card := by
  classical
  let S : Finset V := univ.biUnion G
  let R : Fin s → Finset S := fun i ↦ univ.filter (fun v ↦ v.1 ∈ G i)
  let f : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hR (i : Fin s) : (R i).map f = G i := by
    ext v
    constructor
    · intro hv
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hv
      exact (mem_filter.mp ha).2
    · intro hv
      have hvS : v ∈ S := mem_biUnion.mpr ⟨i, mem_univ i, hv⟩
      exact mem_map.mpr ⟨⟨v, hvS⟩, by simp [R, hv], rfl⟩
  have hRcard (i : Fin s) : (R i).card = (G i).card := by
    rw [← hR i, Finset.card_map]
  let e : S ≃ Fin S.card := S.equivFin
  let P : Fin K → Finset S := fun i ↦ R (paddedIndex hsK hs i)
  let D : Fin K → Finset (Fin S.card) := fun i ↦ (P i).map e.toEmbedding
  have hS : S.card ≤ K * B := by
    calc
      S.card ≤ (univ : Finset (Fin s)).card * B :=
        card_biUnion_le_card_mul _ _ _ (fun i _ ↦ hsize i)
      _ = s * B := by simp
      _ ≤ K * B := Nat.mul_le_mul_right B hsK
  refine ⟨S.card, rfl, hS, D, ?_, ?_, ?_⟩
  · intro i
    change ((P i).map e.toEmbedding).card ≤ B
    rw [Finset.card_map]
    exact (hRcard (paddedIndex hsK hs i)).le.trans (hsize _)
  · ext v
    simp only [mem_univ, iff_true]
    let a : S := e.symm v
    obtain ⟨i, _hi, hai⟩ := mem_biUnion.mp a.2
    apply mem_biUnion.mpr
    refine ⟨Fin.castLE hsK i, mem_univ _, ?_⟩
    change v ∈ (R (paddedIndex hsK hs (Fin.castLE hsK i))).map e.toEmbedding
    rw [paddedIndex_castLE]
    apply mem_map.mpr
    refine ⟨a, ?_, ?_⟩
    · exact mem_filter.mpr ⟨mem_univ a, hai⟩
    · exact e.apply_symm_apply v
  · calc
      (generatedIdealIdx univ D).card = (generatedIdealIdx univ P).card :=
        generatedIdealIdx_card_map P e.toEmbedding
      _ = (generatedIdealIdx univ R).card := by
        rw [show P = (fun i : Fin K ↦ R (paddedIndex hsK hs i)) from rfl,
          generatedIdealIdx_padded hs hsK R]
      _ = (generatedIdealIdx univ G).card := by
        have hc := generatedIdealIdx_card_map R f
        have heq : (fun i ↦ (R i).map f) = G := funext hR
        rw [heq] at hc
        exact hc.symm

/-- Complete row 5: existence and the exact count concern the same header type. -/
theorem paper_headers {B K : ℕ} {L : ℝ} (hL : 20 ≤ L)
    (hK : Admissible L K) (hBL : (2 : ℝ)^L = B) (x : BoundedProfile K B) :
    (∃ H : Fin (packingBound L K + 1) × Partition K,
      ValidHeader x (clusterSize L) (packingBound L K) (literalScales B L K) H) ∧
    Fintype.card (Fin (packingBound L K + 1) × Partition K) ≤
      (packingBound L K + 1) * K ^ K := by
  obtain ⟨hpos, hcover, hanti, _⟩ := literal_scale_conditions hL hK hBL
  exact ⟨exists_validHeader x _ _ hpos hcover _ hanti, card_headers_le _ _⟩

/-- Complete row 6: the intrinsic exceptional-set estimate and agreement on
its complement, using exactly the paper's adjacent scales. -/
theorem paper_exceptional_bound_and_agreement {B K : ℕ} {L : ℝ}
    (hL : 20 ≤ L) (x : BoundedProfile K B)
    (H : Fin (packingBound L K + 1) × Partition K)
    (hH : ValidHeader x (clusterSize L) (packingBound L K) (literalScales B L K) H) :
    (canonicalExceptional x.generators H.2 (clusterSize L)).card ≤ K * B ∧
    (#(canonicalExceptional x.generators H.2 (clusterSize L)) : ℝ) ≤
      2 * K * literalScale B L H.1.val / L^6 ∧
    ∀ C ∈ canonicalClusterFamily H.2 (clusterSize L),
      ∀ i ∈ C, ∀ j ∈ C,
        x.generators i \ canonicalExceptional x.generators H.2 (clusterSize L) =
        x.generators j \ canonicalExceptional x.generators H.2 (clusterSize L) := by
  have hρ : 0 ≤ literalScales B L K H.1.succ :=
    literalScale_nonneg (by positivity) (by linarith) _
  have hb := validHeader_exceptional_bound hH (clusterSize_pos hL) hρ
  refine ⟨hb.1, ?_, ?_⟩
  · simpa only [literalScales, Fin.val_succ, literalScale_succ, mul_div_assoc] using hb.2
  · intro C hC i hi j hj
    exact cluster_sdiff_intrinsicExceptional_eq x.generators hC hi hj

/-- Complete row 8: one uniform incidence-code budget for every family with
this header, and both exact record-count factors. -/
theorem paper_record_counts {B K : ℕ} {L : ℝ} (hL : 20 ≤ L)
    (x : BoundedProfile K B) (H : Fin (packingBound L K + 1) × Partition K)
    (hH : ValidHeader x (clusterSize L) (packingBound L K) (literalScales B L K) H) :
    ∃ u : ℕ,
      (∀ y : BoundedProfile K B,
        ValidHeader y (clusterSize L) (packingBound L K) (literalScales B L K) H →
        (canonicalExceptional y.generators H.2 (clusterSize L)).card ≤ u) ∧
      (Fintype.card (SparseCode (Finset (Fin K)) u) : ℝ) ≤
        ((K * B + 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ (2 * (K : ℝ)^2 * literalScale B L H.1.val / L^6) ∧
      Fintype.card (centralKeys (canonicalRole H.2 (clusterSize L))
        (canonicalCenters H.2 (clusterSize L)) → Fin (B + 1)) ≤
        (B + 1) ^ (2 ^ packingBound L K * (1 + K * 2 ^ clusterSize L)) := by
  classical
  let ρ' : ℝ := literalScales B L K H.1.succ
  let u : ℕ := min (K * B) ⌊2 * (K : ℝ) * ρ'⌋₊
  have hρ : 0 ≤ ρ' := literalScale_nonneg (by positivity) (by linarith) _
  have hn : 0 ≤ 2 * (K : ℝ) * ρ' := by positivity
  have huB : u ≤ K * B := min_le_left _ _
  have huρ : (u : ℝ) ≤ 2 * (K : ℝ) * ρ' := by
    have hf : (u : ℝ) ≤ (⌊2 * (K : ℝ) * ρ'⌋₊ : ℝ) := by
      dsimp [u]
      exact_mod_cast min_le_right (K * B) ⌊2 * (K : ℝ) * ρ'⌋₊
    exact hf.trans (Nat.floor_le hn)
  refine ⟨u, ?_, ?_, ?_⟩
  · intro y hy
    have hb := validHeader_exceptional_bound hy (clusterSize_pos hL) hρ
    exact le_min hb.1 ((Nat.le_floor_iff hn).2 hb.2)
  · have hc := card_incidence_records_real_le huB huρ
    simpa only [ρ', literalScales, Fin.val_succ, literalScale_succ, mul_div_assoc] using hc
  · rw [card_centralExponentVectors]
    exact Nat.pow_le_pow_right (by omega)
      (validHeader_key_bound hH (clusterSize_pos hL))

/-- Complete row 9: full noncentral exponents, actual signed-tail containment,
and the cardinality of that same integer interval. -/
theorem paper_tail_bounds {B K : ℕ} {L : ℝ} (hL : 20 ≤ L)
    (x : BoundedProfile K B) (H : Fin (packingBound L K + 1) × Partition K)
    (hH : ValidHeader x (clusterSize L) (packingBound L K) (literalScales B L K) H) :
    let ρ : ℝ := literalScale B L H.1.val
    let centers := canonicalCenters H.2 (clusterSize L)
    let R : ℕ := 2 ^ K * 2 ^ (B - ⌈ρ⌉₊)
    (∀ t : IEQuery (univ : Finset (Fin K)), t ∉ centers →
      (#(generatorIntersection x.generators t) : ℝ) ≤ B - ρ) ∧
    |(originalTailSum x.generators centers : ℝ)| ≤
      (2 : ℝ) ^ ((B : ℝ) - ρ + K) ∧
    originalTailSum x.generators centers ∈ Finset.Icc (-(R : ℤ)) (R : ℤ) ∧
    (#(Finset.Icc (-(R : ℤ)) (R : ℤ)) : ℝ) ≤
      (2 : ℝ) ^ ((B : ℝ) - ρ + K + 2) := by
  classical
  dsimp only
  let ρ : ℝ := literalScale B L H.1.val
  let centers := canonicalCenters H.2 (clusterSize L)
  let R : ℕ := 2 ^ K * 2 ^ (B - ⌈ρ⌉₊)
  have hρ : 0 ≤ ρ := literalScale_nonneg (by positivity) (by linarith) _
  have hρB : ρ ≤ B := literalScale_le (by positivity) (by linarith) _
  have hexp (t : IEQuery (univ : Finset (Fin K))) (ht : t ∉ centers) :
      #(generatorIntersection x.generators t) ≤ B - ⌈ρ⌉₊ :=
    validHeader_noncentral_bound hH hρ hρB t ht
  have hqB : ⌈ρ⌉₊ ≤ B := Nat.ceil_le.2 hρB
  have htail := originalTailSum_natAbs_le x.generators centers hexp
  have htailcast : ((originalTailSum x.generators centers).natAbs : ℤ) ≤ R := by
    exact_mod_cast htail
  have habs : |originalTailSum x.generators centers| ≤ (R : ℤ) := by
    simpa only [Int.natCast_natAbs] using htailcast
  have hreal : |(originalTailSum x.generators centers : ℝ)| ≤
      (2 : ℝ) ^ ((B : ℝ) - ρ + K) := by
    obtain ⟨r, P, _hr, hexact, hsmall, heq⟩ := hH
    change |(originalTailSum x.generators
      (canonicalCenters H.2 (clusterSize L)) : ℝ)| ≤ _
    rw [heq, canonicalCenters_eq P _ hexact hsmall]
    exact originalTailSum_abs_le_real P x.generators hρ hρB
  refine ⟨?_, hreal, Finset.mem_Icc.mpr (abs_le.mp habs), ?_⟩
  · intro t ht
    have he : (#(generatorIntersection x.generators t) : ℝ) ≤
        ((B - ⌈ρ⌉₊ : ℕ) : ℝ) := by exact_mod_cast hexp t ht
    rw [Nat.cast_sub hqB] at he
    have hceil := Nat.le_ceil ρ
    linarith
  · simpa only [zero_sub, zero_add] using
      integer_tail_interval_card (K := K) (B := B) (ρ := ρ) 0 hρB

/-- Complete row 11: the same absolute threshold simultaneously exposes every
numerical inequality and the actual stronger attainable-value count. -/
theorem paper_numerics_and_strong_count : ∃ B₀ : ℕ, 1 ≤ B₀ ∧
    ∀ B : ℕ, B₀ ≤ B → ∀ K : ℕ,
      1 ≤ K → (K : ℝ) ≤ (Real.logb 2 B)^2 / (100 * Real.logb 2 (Real.logb 2 B)) →
      let L := Real.logb 2 B
      (2 : ℝ) ^ (7 * L / 10) ≤ gamma L K ∧
      fineCost L K ≤ 1/4 ∧
      recordCost L K ≤ gamma L K / 2 ∧
      Real.sqrt B ≤ gamma L K / 4 ∧
      (#(AntichainOfGivenSize.Paper.attainableValues B K) : ℝ) ≤
        (2 : ℝ)^((B : ℝ) - gamma L K / 4) := by
  obtain ⟨L₀, hL₀, hthreshold⟩ := exists_uniform_threshold
  refine ⟨2^L₀, one_le_pow₀ (by norm_num), ?_⟩
  intro B hB K hKpos hKbound
  have hBpos : (0 : ℝ) < B := by
    exact_mod_cast lt_of_lt_of_le (pow_pos (by norm_num : 0 < (2 : ℕ)) L₀) hB
  have hlog : (L₀ : ℝ) ≤ Real.logb 2 B := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (2 : ℝ)^L₀) (show (2 : ℝ)^L₀ ≤ B by exact_mod_cast hB)
    simpa [Real.logb_pow] using hh
  have hL₀real : (20 : ℝ) ≤ L₀ := by exact_mod_cast hL₀
  have h20 : 20 ≤ Real.logb 2 B := hL₀real.trans hlog
  have hK : Admissible (Real.logb 2 B) K := ⟨hKpos, hKbound⟩
  have hnum := hthreshold (Real.logb 2 B) hlog K hK
  have hBL : (2 : ℝ)^(Real.logb 2 B) = B :=
    Real.rpow_logb (by norm_num) (by norm_num) hBpos
  exact ⟨gamma_lower h20 hK, hnum.1, hnum.2.1,
    by simpa only [hBL] using hnum.2.2,
    (paper_counting_at_parameters h20 hK hBL hnum.2.1).1⟩

end AntichainOfGivenSize.FaithfulLower
