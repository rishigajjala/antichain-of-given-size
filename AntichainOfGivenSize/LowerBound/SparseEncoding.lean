import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic

/-!
# Sparse finite encodings

The cluster obstruction repeatedly records a nonnegative function whose total
mass is small, even though its alphabet is large.  `SparseCode α U` is that
finite type.  The stars-and-bars encoding below gives a convenient uniform
cardinality bound without choosing an ordering of `α`.
-/

open scoped BigOperators
open Finset Fintype

namespace AntichainOfGivenSize.ClusterLowerBound

/-- A nonnegative function on `α` with total mass at most `U`. -/
structure SparseCode (α : Type*) [Fintype α] (U : ℕ) where
  count : α → Fin (U + 1)
  mass_le : ∑ a, (count a : ℕ) ≤ U

noncomputable instance { α : Type* } [Fintype α] [DecidableEq α] (U : ℕ) :
    Fintype (SparseCode α U) :=
  Fintype.ofInjective SparseCode.count (by
    intro x y h
    cases x
    cases y
    simp_all)

noncomputable instance { α : Type* } [Fintype α] (U : ℕ) :
    DecidableEq (SparseCode α U) :=
  Classical.decEq _

/-- Package a natural-valued function of total mass at most `U`. -/
noncomputable def SparseCode.ofNat { α : Type* } [Fintype α]
    (U : ℕ) (f : α → ℕ) (h : ∑ a, f a ≤ U) : SparseCode α U where
  count := fun a ↦ ⟨f a, Nat.lt_succ_of_le <|
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)).trans h⟩
  mass_le := by simpa using h

@[simp] theorem SparseCode.coe_ofNat { α : Type* } [Fintype α]
    (U : ℕ) (f : α → ℕ) (h : ∑ a, f a ≤ U) (a : α) :
    ((SparseCode.ofNat U f h).count a : ℕ) = f a :=
  rfl

/-- Multiset containing `count a` copies of `some a`. -/
noncomputable def SparseCode.multiset { α : Type* } [Fintype α]
    {U : ℕ} (c : SparseCode α U) : Multiset (Option α) :=
  ∑ a : α, Multiset.replicate (c.count a) (some a)

@[simp] theorem SparseCode.card_multiset { α : Type* } [Fintype α]
    {U : ℕ} (c : SparseCode α U) :
    c.multiset.card = ∑ a, (c.count a : ℕ) := by
  classical
  simp [SparseCode.multiset]

@[simp] theorem SparseCode.count_some_multiset { α : Type* }
    [Fintype α] [DecidableEq α] {U : ℕ} (c : SparseCode α U)
    (a : α) : c.multiset.count (some a) = c.count a := by
  classical
  unfold SparseCode.multiset
  have hmain : ∀ (s : Finset α),
      Multiset.count (some a)
          (∑ b ∈ s, Multiset.replicate (c.count b) (some b)) =
        if a ∈ s then c.count a else 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert b s hb ih =>
      rw [Finset.sum_insert hb, Multiset.count_add, ih]
      by_cases hba : b = a
      · subst b
        simp [hb]
      · have hab : a ≠ b := Ne.symm hba
        simp [Multiset.count_replicate, hba, hab]
  simpa using hmain Finset.univ

/-- Pad the multiset by `none` to obtain exactly `U` symbols. -/
noncomputable def SparseCode.toSym { α : Type* } [Fintype α]
    (U : ℕ) (c : SparseCode α U) : Sym (Option α) U :=
  Sym.mk (c.multiset + Multiset.replicate (U - c.multiset.card) none) (by
    rw [Multiset.card_add, Multiset.card_replicate]
    exact Nat.add_sub_of_le (by simpa using c.mass_le))

theorem SparseCode.toSym_injective { α : Type* }
    [Fintype α] [DecidableEq α] (U : ℕ) :
    Function.Injective (SparseCode.toSym ( α := α) U) := by
  intro c d h
  have hcount : c.count = d.count := by
    funext a
    apply Fin.ext
    have hm : (c.toSym U : Multiset (Option α)) = d.toSym U :=
      congrArg Sym.toMultiset h
    have hc := congrArg (Multiset.count (some a)) hm
    have hnone : (none : Option α) ≠ some a :=
      (Option.some_ne_none a).symm
    simpa only [SparseCode.toSym, Sym.coe_mk, Multiset.count_add,
      SparseCode.count_some_multiset, Multiset.count_replicate,
      Option.some.injEq, Option.some_ne_none, hnone,
      if_false, add_zero] using hc
  cases c with
  | mk cc hc =>
      cases d with
      | mk dc hd =>
          simp only at hcount
          subst dc
          rfl

/-- Stars-and-bars upper bound for sparse codes. -/
theorem card_sparseCode_le { α : Type* } [Fintype α]
    [DecidableEq α] (U : ℕ) :
    Fintype.card (SparseCode α U) ≤
      (Fintype.card (Option α) + U) ^ U := by
  calc
    Fintype.card (SparseCode α U) ≤
        Fintype.card (Sym (Option α) U) :=
      Fintype.card_le_of_injective _ (SparseCode.toSym_injective U)
    _ = (Fintype.card (Option α) + U - 1).choose U :=
      Sym.card_sym_eq_choose U
    _ ≤ (Fintype.card (Option α) + U - 1) ^ U :=
      Nat.choose_le_pow _ _
    _ ≤ (Fintype.card (Option α) + U) ^ U := by
      gcongr
      omega

end AntichainOfGivenSize.ClusterLowerBound
