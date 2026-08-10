import ZhangClaim65Blocks
import ZhangClaim65Survivors
import ZhangStageBridge
import ZhangAddress
import ZhangStageArithmetic
import ZhangIndexedBounds
import ZhangConstructionNatParams
import ZhangMatchingParameters

open scoped BigOperators

namespace ZhangStageIntegration

open Finset
open ZhangSection6
open ZhangClaim65

/-! A dependent finite-history version, convenient for the actual induction. -/

def snocFun {h : ℕ} {A : Type*} (f : Fin h → A) (x : A) : Fin (h + 1) → A :=
  Fin.lastCases x f

noncomputable def finiteHistoryGenerator {r q h : ℕ} (w : Fin r → ℕ)
    (T : Fin h → Finset (Fin r)) (D : Fin h → ℕ) :
    BlockIndex r q → Finset (AtomVertex r q h w) :=
  oldGenerator w T D

noncomputable def finiteHistoryCard {r q h : ℕ} (w : Fin r → ℕ)
    (T : Fin h → Finset (Fin r)) (D : Fin h → ℕ) : ℕ :=
  (generatedIdealIdx (Finset.univ : Finset (BlockIndex r q))
    (finiteHistoryGenerator w T D)).card

@[simp] theorem snocFun_castSucc {h : ℕ} {A : Type*} (f : Fin h → A) (x : A)
    (i : Fin h) : snocFun f x i.castSucc = f i := by
  simp [snocFun]

@[simp] theorem snocFun_last {h : ℕ} {A : Type*} (f : Fin h → A) (x : A) :
    snocFun f x (Fin.last h) = x := by
  simp [snocFun]

theorem blockCommonCount_snoc {r q h : ℕ} (w : Fin r → ℕ)
    (T : Fin h → Finset (Fin r)) (D : Fin h → ℕ)
    (Tnew : Finset (Fin r)) (dnew : ℕ) (J : Finset (BlockIndex r q)) :
    blockCommonCount w (snocFun T Tnew) (snocFun D dnew) J =
      blockCommonCount w T D J +
        if J ⊆ selected Tnew dnew then 1 else 0 := by
  rw [blockCommonCount_expand, blockCommonCount_expand]
  simp only [Fin.sum_univ_castSucc, snocFun_castSucc, snocFun_last]
  omega

theorem generatorIntersection_finite_snoc {r q h : ℕ} (w : Fin r → ℕ)
    (T : Fin h → Finset (Fin r)) (D : Fin h → ℕ)
    (Tnew : Finset (Fin r)) (dnew : ℕ)
    (t : (Finset.univ : Finset (BlockIndex r q)).powerset.filter
      (fun u : Finset (BlockIndex r q) ↦ u.Nonempty)) :
    (generatorIntersection (finiteHistoryGenerator w (snocFun T Tnew)
      (snocFun D dnew)) t).card =
      (generatorIntersection (finiteHistoryGenerator w T D) t).card +
        if t.1 ⊆ selected Tnew dnew then 1 else 0 := by
  unfold finiteHistoryGenerator
  rw [generatorIntersection_oldGenerator_card,
    generatorIntersection_oldGenerator_card]
  exact blockCommonCount_snoc w T D Tnew dnew t.1

theorem finiteHistoryCard_snoc {r q h : ℕ} (w : Fin r → ℕ)
    (T : Fin h → Finset (Fin r)) (D : Fin h → ℕ)
    (Tnew : Finset (Fin r)) (dnew : ℕ) :
    finiteHistoryCard (q := q) w (snocFun T Tnew) (snocFun D dnew) =
      finiteHistoryCard (q := q) w T D +
        (generatedIdealIdx (selected (q := q) Tnew dnew)
          (finiteHistoryGenerator w T D)).card := by
  apply generatedIdealIdx_card_stage_of_intersection_cards
  · exact fun _ hi ↦ Finset.mem_univ _
  · exact generatorIntersection_finite_snoc w T D Tnew dnew

/-! Choosing and lifting the signed block digit. -/

noncomputable def chooseDigit (q r c : ℕ) : ℕ :=
  Classical.choose (Zhang.exists_remainderZ_cast q
    ((-1 : ZMod (2 ^ q)) ^ r * (c : ZMod (2 ^ q))))

theorem chooseDigit_lt (q r c : ℕ) : chooseDigit q r c < 2 ^ q :=
  (Classical.choose_spec (Zhang.exists_remainderZ_cast q
    ((-1 : ZMod (2 ^ q)) ^ r * (c : ZMod (2 ^ q))))).1

theorem chooseDigit_cast (q r c : ℕ) :
    (Zhang.remainderZ q (chooseDigit q r c) : ZMod (2 ^ q)) =
      (-1 : ZMod (2 ^ q)) ^ r * (c : ZMod (2 ^ q)) :=
  (Classical.choose_spec (Zhang.exists_remainderZ_cast q
    ((-1 : ZMod (2 ^ q)) ^ r * (c : ZMod (2 ^ q))))).2

theorem signed_mul_lift {a b r z c : ℕ}
    (hz : (z : ZMod b) = (-1 : ZMod b) ^ r * (c : ZMod b)) :
    (-1 : ZMod (a * b)) ^ r * (z : ZMod (a * b)) * (a : ZMod (a * b)) =
      ((a * c : ℕ) : ZMod (a * b)) := by
  rcases Nat.even_or_odd r with hr | hr
  · rw [hr.neg_one_pow] at hz ⊢
    simp only [one_mul]
    simp only [one_mul] at hz
    have hmod : z ≡ c [MOD b] :=
      (ZMod.natCast_eq_natCast_iff z c b).mp hz
    have hscaled : a * z ≡ a * c [MOD a * b] :=
      Nat.ModEq.mul_left' a hmod
    have hcast := (ZMod.natCast_eq_natCast_iff (a * z) (a * c) (a * b)).2 hscaled
    simpa [Nat.cast_mul, mul_comm] using hcast
  · rw [hr.neg_one_pow] at hz ⊢
    have hzero : ((z + c : ℕ) : ZMod b) = 0 := by
      push_cast
      rw [hz]
      ring
    have hmodzero : z + c ≡ 0 [MOD b] :=
      (ZMod.natCast_eq_natCast_iff (z + c) 0 b).mp (by simpa using hzero)
    have hdiv : b ∣ z + c := Nat.modEq_zero_iff_dvd.mp hmodzero
    have hscaledDiv : a * b ∣ a * (z + c) := Nat.mul_dvd_mul_left a hdiv
    have hscaledZeroMod : a * (z + c) ≡ 0 [MOD a * b] :=
      Nat.modEq_zero_iff_dvd.mpr hscaledDiv
    have hscaledZero :
        ((a * (z + c) : ℕ) : ZMod (a * b)) = 0 :=
      by simpa using
        (ZMod.natCast_eq_natCast_iff (a * (z + c)) 0 (a * b)).2 hscaledZeroMod
    push_cast at hscaledZero ⊢
    ring_nf at hscaledZero ⊢
    exact neg_eq_of_add_eq_zero_left (by simpa [add_comm] using hscaledZero)

theorem chosenDigit_signed_block {h q r c : ℕ} :
    (-1 : ZMod (2 ^ ((h + 1) * q))) ^ r *
        (Zhang.remainderZ q (chooseDigit q r c) : ZMod (2 ^ ((h + 1) * q))) *
        (2 : ZMod (2 ^ ((h + 1) * q))) ^ (h * q) =
      ((2 ^ (h * q) * c : ℕ) : ZMod (2 ^ ((h + 1) * q))) := by
  rw [Zhang.pow_block_succ]
  simpa [Nat.cast_pow, mul_comm, mul_left_comm, mul_assoc] using
    (signed_mul_lift (a := 2 ^ (h * q)) (b := 2 ^ q) (r := r)
      (z := Zhang.remainderZ q (chooseDigit q r c)) (c := c)
      (chooseDigit_cast q r c))

theorem selectedIdeal_eq_stageIdeal {r q h : ℕ} (w : Fin r → ℕ)
    (T : Fin h → Finset (Fin r)) (D : Fin h → ℕ)
    (Tnew : Finset (Fin r)) (dnew : ℕ) :
    generatedIdealIdx (selected Tnew dnew) (oldGenerator w T D) =
      generatedIdealIdx (Finset.univ : Finset (StageIndex r q))
        (stageOldGenerator w T D Tnew dnew) := by
  rw [← stageEmbedding_univ Tnew dnew]
  ext A
  simp only [generatedIdealIdx, Finset.mem_biUnion, Finset.mem_map,
    Finset.mem_univ, true_and, Finset.mem_powerset]
  constructor
  · rintro ⟨i, ⟨j, rfl⟩, hA⟩
    exact ⟨j, by simpa [stageOldGenerator] using hA⟩
  · rintro ⟨j, hA⟩
    exact ⟨stageEmbedding Tnew dnew j, ⟨j, rfl⟩,
      by simpa [stageOldGenerator] using hA⟩

/-- Exact Claim 6.5 in the form consumed by the stage recursion. -/
def ExactStageIncrement : Prop :=
  ∀ {r q h : ℕ}, 0 < q → (w : Fin r → ℕ) →
    (T : Fin h → Finset (Fin r)) → (D : Fin h → ℕ) →
    (Tnew : Finset (Fin r)) → (dnew : ℕ) →
    (∀ g, T g ≠ Tnew) → (∑ j ∈ Tnew, w j = h) →
    ((h + 1) * q ≤ (∑ j : Fin r, q * w j) + ∑ _j : Fin r, q) →
    (((generatedIdealIdx (selected (q := q) Tnew dnew)
      (finiteHistoryGenerator w T D)).card : ℕ) :
        ZMod (2 ^ ((h + 1) * q))) =
      (-1 : ZMod (2 ^ ((h + 1) * q))) ^ r *
        (Zhang.remainderZ q dnew : ZMod (2 ^ ((h + 1) * q))) *
        (2 : ZMod (2 ^ ((h + 1) * q))) ^ (h * q)

theorem exists_matching_finiteHistory
    {H q y h : ℕ} (hH : 1 < H) (hq : 0 < q) (hh : h ≤ H)
    (hexact : ExactStageIncrement)
    (hsize : ∀ (k : ℕ), k ≤ H →
      ∀ (T : Fin k → Finset (Fin (Zhang.addressBits H + 1))) (D : Fin k → ℕ),
        finiteHistoryCard (q := q) (Zhang.canonicalWeight H) T D ≤ y) :
    ∃ (T : Fin h → Finset (Fin (Zhang.addressBits H + 1))) (D : Fin h → ℕ),
      (∀ g, ∑ j ∈ T g, Zhang.canonicalWeight H j = g.val) ∧
      finiteHistoryCard (q := q) (Zhang.canonicalWeight H) T D ≡ y
        [MOD 2 ^ (h * q)] := by
  induction h with
  | zero =>
      refine ⟨Fin.elim0, Fin.elim0, ?_, ?_⟩
      · intro g
        exact Fin.elim0 g
      · simpa using (Nat.modEq_one :
          finiteHistoryCard (q := q) (Zhang.canonicalWeight H) Fin.elim0 Fin.elim0
            ≡ y [MOD 1])
  | succ h ih =>
      have hh' : h ≤ H := by omega
      obtain ⟨T, D, hweights, hmod⟩ := ih hh'
      let m : ℕ := finiteHistoryCard (q := q) (Zhang.canonicalWeight H) T D
      let a : ℕ := 2 ^ (h * q)
      let c : ℕ := (y - m) / a
      let d : ℕ := chooseDigit q (Zhang.addressBits H + 1) c
      have hhlt : h < H := by omega
      let Tnew : Finset (Fin (Zhang.addressBits H + 1)) :=
        Zhang.canonicalAddress H ⟨h, hhlt⟩
      let T' := snocFun T Tnew
      let D' := snocFun D d
      have hweightNew :
          ∑ j ∈ Tnew, Zhang.canonicalWeight H j = h := by
        simpa [Tnew] using
          (Zhang.sum_canonicalAddress_weight hH ⟨h, hhlt⟩)
      have hU :
          (h + 1) * q ≤
            (∑ j : Fin (Zhang.addressBits H + 1),
              q * Zhang.canonicalWeight H j) +
              ∑ _j : Fin (Zhang.addressBits H + 1), q := by
        rw [← Finset.mul_sum, Zhang.sum_canonicalWeight hH]
        have hrankPos : 0 < Zhang.addressBits H + 1 := by omega
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        have hhsub : h ≤ H - 1 := by omega
        have hqpart : h * q ≤ (H - 1) * q :=
          Nat.mul_le_mul_right q hhsub
        have hrankOne : 1 ≤ Zhang.addressBits H + 1 := by omega
        have hqrank : q ≤ (Zhang.addressBits H + 1) * q := by
          simpa using Nat.mul_le_mul_right q hrankOne
        calc
          (h + 1) * q = h * q + q := by rw [Nat.add_mul, one_mul]
          _ ≤ (H - 1) * q + (Zhang.addressBits H + 1) * q :=
            Nat.add_le_add hqpart hqrank
          _ = q * (H - 1) + (Zhang.addressBits H + 1) * q := by
            rw [Nat.mul_comm q (H - 1)]
      have hpast : ∀ g, T g ≠ Tnew := by
        intro g heq
        have hg := hweights g
        rw [heq, hweightNew] at hg
        omega
      let delta : ℕ :=
        (generatedIdealIdx (selected (q := q) Tnew d)
          (finiteHistoryGenerator (q := q) (Zhang.canonicalWeight H) T D)).card
      have hdeltaCast :
          (delta : ZMod (2 ^ ((h + 1) * q))) =
            (-1 : ZMod (2 ^ ((h + 1) * q))) ^ (Zhang.addressBits H + 1) *
              (Zhang.remainderZ q d : ZMod (2 ^ ((h + 1) * q))) *
              (2 : ZMod (2 ^ ((h + 1) * q))) ^ (h * q) := by
        exact hexact hq (Zhang.canonicalWeight H) T D Tnew d hpast hweightNew hU
      have hchosen :
          (-1 : ZMod (2 ^ ((h + 1) * q))) ^ (Zhang.addressBits H + 1) *
              (Zhang.remainderZ q d : ZMod (2 ^ ((h + 1) * q))) *
              (2 : ZMod (2 ^ ((h + 1) * q))) ^ (h * q) =
            ((2 ^ (h * q) * c : ℕ) : ZMod (2 ^ ((h + 1) * q))) := by
        simpa [d] using
          (chosenDigit_signed_block (h := h) (q := q)
            (r := Zhang.addressBits H + 1) (c := c))
      have hdelta : delta ≡ 2 ^ (h * q) * c [MOD 2 ^ ((h + 1) * q)] := by
        apply (ZMod.natCast_eq_natCast_iff delta
          (2 ^ (h * q) * c) (2 ^ ((h + 1) * q))).mp
        exact hdeltaCast.trans hchosen
      have hmle : m ≤ y := hsize h hh' T D
      have hc : c ≡ (y - m) / 2 ^ (h * q) [MOD 2 ^ q] := by
        rfl
      have hnext : m + delta ≡ y [MOD 2 ^ ((h + 1) * q)] := by
        exact Zhang.extend_pow_modEq_digit hmle hmod hc hdelta
      refine ⟨T', D', ?_, ?_⟩
      · intro g
        refine Fin.lastCases ?_ (fun i ↦ ?_) g
        · simpa [T'] using hweightNew
        · simpa [T'] using hweights i
      · rw [finiteHistoryCard_snoc]
        exact hnext

theorem card_blockIndex (r q : ℕ) :
    Fintype.card (BlockIndex r q) = 2 * r + 2 * q := by
  simp [BlockIndex]
  ring

theorem card_atomVertex (r q h : ℕ) (w : Fin r → ℕ) :
    Fintype.card (AtomVertex r q h w) =
      q * (∑ j : Fin r, w j) + r * q + q ^ 2 + h := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  change (∑ s : AtomSpecies r q h, speciesCount w s) =
    q * (∑ j : Fin r, w j) + r * q + q ^ 2 + h
  simp only [AtomSpecies, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool, speciesCount, Bool.false_eq_true, if_false, if_true,
    Nat.add_zero]
  rw [sum_remainder_pair_sizes]
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, pow_two,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem finiteHistoryCard_lt_of_bounds
    {H q h N n : ℕ} (hH : 1 < H) (hh : h ≤ H)
    (hHpow : H ≤ 2 ^ q) (hq4 : 4 ≤ q)
    (hexponents : H * q + 2 * q ^ 2 + H + q < N)
    (hn : 2 ^ N ≤ n)
    (T : Fin h → Finset (Fin (Zhang.addressBits H + 1))) (D : Fin h → ℕ) :
    finiteHistoryCard (q := q) (Zhang.canonicalWeight H) T D < n := by
  let r := Zhang.addressBits H + 1
  have hr : r ≤ q := by
    exact Zhang.addressRank_le_of_le_two_pow hH hHpow
  unfold finiteHistoryCard finiteHistoryGenerator
  apply ZhangImprovedBound.generatedIdealIdx_card_lt_of_exponent_bounds
      (generatorExponent := q)
      (universeExponent := H * q + 2 * q ^ 2 + H)
      (N := N)
  · rw [Finset.card_univ, card_blockIndex]
    exact Zhang.generatorCount_le_two_pow hr hq4
  · rw [card_atomVertex, Zhang.sum_canonicalWeight hH]
    calc
      q * (H - 1) + r * q + q ^ 2 + h ≤
          q * (H - 1) + q * r + q ^ 2 + H := by
        rw [Nat.mul_comm r q]
        omega
      _ ≤ H * q + 2 * q ^ 2 + H := Zhang.universeSize_le hr
  · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hexponents
  · exact hn

theorem exists_concrete_nat_matching
    {H q N n : ℕ} (hH : 1 < H) (hq4 : 4 ≤ q)
    (hHpow : H ≤ 2 ^ q)
    (hexponents : H * q + 2 * q ^ 2 + H + q < N)
    (hn : 2 ^ N ≤ n) (hexact : ExactStageIncrement) :
    ∃ m : ℕ,
      0 < m ∧ m < n ∧ m ≡ n + 1 [MOD 2 ^ (H * q)] ∧
        ZhangImprovedBound.alpha m ≤
          2 * (Zhang.addressBits H + 1) + 2 * q := by
  have hq : 0 < q := by omega
  have hsize : ∀ (k : ℕ), k ≤ H →
      ∀ (T : Fin k → Finset (Fin (Zhang.addressBits H + 1))) (D : Fin k → ℕ),
        finiteHistoryCard (q := q) (Zhang.canonicalWeight H) T D ≤ n + 1 := by
    intro k hk T D
    have hlt := finiteHistoryCard_lt_of_bounds hH hk hHpow hq4
      hexponents hn T D
    omega
  obtain ⟨T, D, _hweights, hmod⟩ :=
    exists_matching_finiteHistory hH hq (le_refl H) hexact hsize
  let m := finiteHistoryCard (q := q) (Zhang.canonicalWeight H) T D
  refine ⟨m, ?_, ?_, ?_, ?_⟩
  · unfold m finiteHistoryCard
    apply ZhangImprovedBound.generatedIdealIdx_card_pos
    exact ⟨Sum.inr (⟨0, hq⟩, false), Finset.mem_univ _⟩
  · exact finiteHistoryCard_lt_of_bounds hH (le_refl H) hHpow hq4
      hexponents hn T D
  · exact hmod
  · unfold m finiteHistoryCard finiteHistoryGenerator
    simpa [card_blockIndex, Nat.mul_comm] using
      (ZhangImprovedBound.alpha_generatedIdealIdx_univ_card_le
        (oldGenerator (q := q) (Zhang.canonicalWeight H) T D))

theorem constructionMatching_of_exact (hexact : ExactStageIncrement) :
    ZhangImprovedBound.MatchingSuccessorAtBits 10 8 16
      ZhangImprovedBound.constructionBits := by
  intro x hx n hrange
  let N : ℕ := ZhangImprovedBound.binaryLog n
  let q : ℕ := ⌈x⌉₊
  let H : ℕ := Zhang.stageCount N q
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hxq : x ≤ (q : ℝ) := by
    simpa [q] using Nat.le_ceil x
  have hqx : (q : ℝ) < x + 1 := by
    simpa [q] using Nat.ceil_lt_add_one hx0
  have hq16 : 16 ≤ q := by
    have : (16 : ℝ) ≤ (q : ℝ) := hx.trans hxq
    exact_mod_cast this
  have hlogN : Real.logb 2 (n : ℝ) < (N : ℝ) + 1 := by
    have hfloor := Nat.lt_floor_add_one (Real.logb 2 (n : ℝ))
    have heq : ⌊Real.logb 2 (n : ℝ)⌋₊ = N := by
      simpa [N, ZhangImprovedBound.binaryLog] using
        Real.natFloor_logb_natCast 2 n
    rw [heq] at hfloor
    exact hfloor
  have hpredx : ((q - 1 : ℕ) : ℝ) < x := by
    rw [Nat.cast_sub (by omega)]
    norm_num
    linarith
  have hrpowPred := Real.rpow_lt_rpow_of_exponent_lt one_lt_two hpredx
  have hpowPredReal : ((2 ^ (q - 1) : ℕ) : ℝ) < (2 : ℝ) ^ x := by
    calc
      ((2 ^ (q - 1) : ℕ) : ℝ) =
          (2 : ℝ) ^ ((q - 1 : ℕ) : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ < (2 : ℝ) ^ x := hrpowPred
  have hpowPredN : 2 ^ (q - 1) ≤ N := by
    have hreal : ((2 ^ (q - 1) : ℕ) : ℝ) < (N : ℝ) + 1 :=
      (hpowPredReal.trans_le hrange.1).trans hlogN
    have hnat : 2 ^ (q - 1) < N + 1 := by exact_mod_cast hreal
    omega
  have hHtwo : 2 ≤ H := by
    simpa [H, Zhang.stageCount] using
      (Zhang.two_le_stageCount_of_pow_pred_le (by omega) hpowPredN)
  have hH : 1 < H := by omega
  have hsmall : 4 * q ^ 2 ≤ N :=
    (Zhang.four_sq_le_two_pow_pred (by omega)).trans hpowPredN
  have hHlNat : H * q ≤ N := by
    calc
      H * q ≤ H * (q + 2) := by gcongr; omega
      _ ≤ N - 4 * q ^ 2 := by
        simpa [H] using Zhang.stageCount_mul_le N q
      _ ≤ N := Nat.sub_le _ _
  have hHx : (H : ℝ) * x ≤ (N : ℝ) := by
    calc
      (H : ℝ) * x ≤ (H : ℝ) * (q : ℝ) := by gcongr
      _ ≤ (N : ℝ) := by exact_mod_cast hHlNat
  have hHle : (H : ℝ) ≤ (N : ℝ) / x :=
    (le_div_iff₀ hxpos).2 hHx
  have hNlog : (N : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    simpa [N] using
      ZhangImprovedBound.binaryLog_le_logb_of_wideRange 10 x n hrange
  have hNupper : (N : ℝ) < (2 : ℝ) ^ x * x / 1024 := by
    calc
      (N : ℝ) ≤ Real.logb 2 (n : ℝ) := hNlog
      _ < (2 : ℝ) ^ (x + Real.logb 2 x - 10) := hrange.2
      _ = (2 : ℝ) ^ x * x / (2 : ℝ) ^ (10 : ℝ) :=
        ZhangImprovedBound.wideRange_upper_endpoint 10 x hxpos
      _ = (2 : ℝ) ^ x * x / 1024 := by
        norm_num [Real.rpow_natCast]
  have hNdiv : (N : ℝ) / x < (2 : ℝ) ^ x / 1024 := by
    calc
      (N : ℝ) / x < ((2 : ℝ) ^ x * x / 1024) / x :=
        div_lt_div_of_pos_right hNupper hxpos
      _ = (2 : ℝ) ^ x / 1024 := by field_simp
  have hHlt : (H : ℝ) < (2 : ℝ) ^ x / 1024 := hHle.trans_lt hNdiv
  have hP : 0 < (2 : ℝ) ^ x := Real.rpow_pos_of_pos zero_lt_two x
  have hHltPowX : (H : ℝ) < (2 : ℝ) ^ x := by nlinarith
  have hPowXleQ : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ (q : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two hxq
  have hHpowReal : (H : ℝ) < ((2 ^ q : ℕ) : ℝ) := by
    calc
      (H : ℝ) < (2 : ℝ) ^ x := hHltPowX
      _ ≤ (2 : ℝ) ^ (q : ℝ) := hPowXleQ
      _ = ((2 ^ q : ℕ) : ℝ) := by norm_num [Real.rpow_natCast]
  have hHpow : H ≤ 2 ^ q := by
    have : H < 2 ^ q := by exact_mod_cast hHpowReal
    omega
  have hexponents : H * q + 2 * q ^ 2 + H + q < N := by
    simpa [H] using Zhang.constructionExponent_lt (by omega) hsmall
  have hn0 : n ≠ 0 := by
    intro hnzero
    subst n
    have hlower := hrange.1
    have hpos := Real.rpow_pos_of_pos zero_lt_two x
    simp [Real.logb] at hlower
    linarith
  have hnPow : 2 ^ N ≤ n := by
    simpa [N, ZhangImprovedBound.binaryLog] using Nat.pow_log_le_self 2 hn0
  obtain ⟨m, hmpos, hmn, hmod, halpha⟩ :=
    exists_concrete_nat_matching hH (by omega) hHpow hexponents hnPow hexact
  refine ⟨m, hmpos, hmn, ?_, ?_⟩
  · simpa [ZhangImprovedBound.constructionBits, Zhang.matchingBits, N, q, H]
      using hmod
  · have hrank : Zhang.addressBits H + 1 ≤ q :=
      Zhang.addressRank_le_of_le_two_pow hH hHpow
    have hcount : 2 * (Zhang.addressBits H + 1) + 2 * q ≤ 4 * q := by
      omega
    have hcountReal :
        ((2 * (Zhang.addressBits H + 1) + 2 * q : ℕ) : ℝ) ≤ 4 * (q : ℝ) := by
      exact_mod_cast hcount
    have hqBound : 4 * (q : ℝ) ≤ 8 * x := by
      have : (q : ℝ) < x + 1 := hqx
      nlinarith
    calc
      (ZhangImprovedBound.alpha m : ℝ) ≤
          ((2 * (Zhang.addressBits H + 1) + 2 * q : ℕ) : ℝ) := by
        exact_mod_cast halpha
      _ ≤ 4 * (q : ℝ) := hcountReal
      _ ≤ 8 * x := hqBound

end ZhangStageIntegration
