import Mathlib.Data.Nat.Bits
import Mathlib.Tactic

namespace AntichainOfGivenSize

/-!
# Binary block count

The lower bound uses the number of maximal runs of `1`s in the canonical
binary expansion of a natural number.  In the recursion below, `b` is the
current low bit and `n.bodd` is the next bit.  Thus
`b && !n.bodd` marks exactly the high end of a block of `1`s.
-/

/-- The number of maximal blocks of `1`s in the binary expansion of `n`.
In particular, `binaryBlockCount 0 = 0`. -/
def binaryBlockCount : ℕ → ℕ :=
  Nat.binaryRec 0 fun b n count ↦
    count + if b && !n.bodd then 1 else 0

/-- Direct list semantics: count starts of maximal `true` runs, where
`previous` is the bit immediately below the list. -/
def oneBlockCountAux : Bool → List Bool → ℕ
  | _, [] => 0
  | previous, bit :: bits =>
      (if !previous && bit then 1 else 0) + oneBlockCountAux bit bits

/-- The same block count, visibly defined from the canonical bit list. -/
def binaryBlockCountFromBits (n : ℕ) : ℕ :=
  oneBlockCountAux false n.bits

@[simp] theorem binaryBlockCount_zero : binaryBlockCount 0 = 0 := rfl

theorem binaryBlockCount_bit (b : Bool) (n : ℕ) :
    binaryBlockCount (Nat.bit b n) =
      binaryBlockCount n + if b && !n.bodd then 1 else 0 := by
  unfold binaryBlockCount
  rw [Nat.binaryRec_eq b n (Or.inl rfl)]

@[simp] theorem binaryBlockCount_bit_false (n : ℕ) :
    binaryBlockCount (Nat.bit false n) = binaryBlockCount n := by
  unfold binaryBlockCount
  rw [Nat.binaryRec_eq false n (Or.inl rfl)]
  simp

@[simp] theorem binaryBlockCount_bit_true (n : ℕ) :
    binaryBlockCount (Nat.bit true n) =
      binaryBlockCount n + if !n.bodd then 1 else 0 := by
  rw [binaryBlockCount_bit true n]
  simp

lemma one_add_oneBlockCountAux_true (bits : List Bool) :
    1 + oneBlockCountAux true bits =
      oneBlockCountAux false bits + if !bits.headD false then 1 else 0 := by
  cases bits with
  | nil => simp [oneBlockCountAux]
  | cons b bits => cases b <;> simp [oneBlockCountAux, Nat.add_comm]

theorem bits_headD_false_eq_bodd (n : ℕ) :
    n.bits.headD false = n.bodd := by
  rw [Nat.bodd_eq_bits_head]
  cases n.bits <;> rfl

/-- The executable recursion computes exactly the number of maximal `1`-runs
in `Nat.bits`. -/
theorem binaryBlockCount_eq_fromBits (n : ℕ) :
    binaryBlockCount n = binaryBlockCountFromBits n := by
  induction n using Nat.binaryRec' with
  | zero => simp [binaryBlockCount, binaryBlockCountFromBits, oneBlockCountAux]
  | bit b n h ih =>
      rw [binaryBlockCount_bit b n]
      change _ = oneBlockCountAux false (Nat.bit b n).bits
      rw [Nat.bits_append_bit n b h]
      cases b with
      | false =>
          simp [binaryBlockCountFromBits, oneBlockCountAux, ih]
      | true =>
          simp only [oneBlockCountAux, Bool.not_false, Bool.true_and, if_pos]
          change binaryBlockCount n = oneBlockCountAux false n.bits at ih
          rw [one_add_oneBlockCountAux_true, bits_headD_false_eq_bodd, ← ih]

/-- Adding one cannot create more than one new `1`-block.  If the low bit
was already `1`, carrying cannot create a new block. -/
theorem binaryBlockCount_succ (n : ℕ) :
    if n.bodd then binaryBlockCount (n + 1) ≤ binaryBlockCount n
    else binaryBlockCount (n + 1) ≤ binaryBlockCount n + 1 := by
  induction n using Nat.binaryRec' with
  | zero => norm_num [binaryBlockCount, Nat.binaryRec]
  | bit b n h ih =>
      cases b with
      | false =>
          have hn : n ≠ 0 := by
            intro hn
            exact Bool.false_ne_true (h hn)
          simp only [Nat.bodd_bit, Bool.false_eq_true, ↓reduceIte]
          rw [show Nat.bit false n + 1 = Nat.bit true n by simp [Nat.bit_val]]
          rw [binaryBlockCount_bit_true, binaryBlockCount_bit_false n]
          split <;> omega
      | true =>
          simp only [Nat.bodd_bit, ↓reduceIte]
          rw [show Nat.bit true n + 1 = Nat.bit false (n + 1) by
            norm_num [Nat.bit_val]
            omega]
          rw [binaryBlockCount_bit_false (n + 1), binaryBlockCount_bit_true]
          cases hnodd : n.bodd <;> simp [hnodd] at ih ⊢ <;> omega

theorem binaryBlockCount_add_one_le (n : ℕ) :
    binaryBlockCount (n + 1) ≤ binaryBlockCount n + 1 := by
  have h := binaryBlockCount_succ n
  split at h <;> omega

/-- Adding one power of two creates at most one new `1`-block. -/
theorem binaryBlockCount_add_pow (n y : ℕ) :
    binaryBlockCount (n + 2 ^ y) ≤ binaryBlockCount n + 1 := by
  induction y generalizing n with
  | zero => simpa using binaryBlockCount_add_one_le n
  | succ y ih =>
      refine Nat.bitCasesOn
        (motive := fun n ↦
          binaryBlockCount (n + 2 ^ (y + 1)) ≤ binaryBlockCount n + 1)
        n fun b q ↦ ?_
      have hadd : Nat.bit b q + 2 ^ (y + 1) = Nat.bit b (q + 2 ^ y) := by
        cases b <;> norm_num [Nat.bit_val, pow_succ] <;> omega
      rw [hadd]
      cases b with
      | false =>
          change binaryBlockCount (Nat.bit false (q + 2 ^ y)) ≤
            binaryBlockCount (Nat.bit false q) + 1
          simpa only [binaryBlockCount_bit_false] using ih q
      | true =>
          change binaryBlockCount (Nat.bit true (q + 2 ^ y)) ≤
            binaryBlockCount (Nat.bit true q) + 1
          rw [binaryBlockCount_bit_true, binaryBlockCount_bit_true]
          cases y with
          | zero =>
              norm_num at ih ⊢
              have hs := binaryBlockCount_succ q
              cases hq : q.bodd <;> simp [hq] at hs ⊢ <;> omega
          | succ y =>
              have heven : (2 ^ (y + 1)).bodd = false := by
                simp [pow_succ]
              rw [Nat.bodd_add, heven]
              simp only [Bool.xor_false]
              have hi := ih q
              omega

/-- Removing one changes the number of `1`-blocks by at most one.  If the
low bit is `1`, removing it cannot increase the count. -/
theorem binaryBlockCount_pred (n : ℕ) :
    if n.bodd then binaryBlockCount (n - 1) ≤ binaryBlockCount n
    else binaryBlockCount (n - 1) ≤ binaryBlockCount n + 1 := by
  induction n using Nat.binaryRec' with
  | zero => simp [binaryBlockCount_zero]
  | bit b n h ih =>
      cases b with
      | false =>
          have hn : n ≠ 0 := fun hn ↦ Bool.false_ne_true (h hn)
          simp only [Nat.bodd_bit, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
          rw [show Nat.bit false (q + 1) - 1 = Nat.bit true q by
            norm_num [Nat.bit_val]
            omega]
          change binaryBlockCount (Nat.bit true q) ≤
            binaryBlockCount (Nat.bit false (q + 1)) + 1
          rw [binaryBlockCount_bit_true, binaryBlockCount_bit_false]
          have hi := ih
          cases hq : q.bodd <;> simp [Nat.bodd_succ, hq] at hi ⊢ <;> omega
      | true =>
          simp only [Nat.bodd_bit, ↓reduceIte]
          rw [show Nat.bit true n - 1 = Nat.bit false n by
            norm_num [Nat.bit_val]]
          rw [binaryBlockCount_bit_false, binaryBlockCount_bit_true]
          omega

theorem binaryBlockCount_sub_one_le (n : ℕ) :
    binaryBlockCount (n - 1) ≤ binaryBlockCount n + 1 := by
  have h := binaryBlockCount_pred n
  split at h <;> omega

/-- Subtracting one power of two, without underflow, creates at most one new
`1`-block. -/
theorem binaryBlockCount_sub_pow (n y : ℕ) (h : 2 ^ y ≤ n) :
    binaryBlockCount (n - 2 ^ y) ≤ binaryBlockCount n + 1 := by
  induction y generalizing n with
  | zero => simpa using binaryBlockCount_sub_one_le n
  | succ y ih =>
      refine Nat.bitCasesOn
        (motive := fun n ↦ 2 ^ (y + 1) ≤ n →
          binaryBlockCount (n - 2 ^ (y + 1)) ≤ binaryBlockCount n + 1)
        n (fun b q h ↦ ?_) h
      have hq : 2 ^ y ≤ q := by
        cases b <;> norm_num [Nat.bit_val, pow_succ] at h ⊢ <;> omega
      have hsub : Nat.bit b q - 2 ^ (y + 1) = Nat.bit b (q - 2 ^ y) := by
        cases b <;> norm_num [Nat.bit_val, pow_succ] <;> omega
      rw [hsub]
      cases b with
      | false =>
          change binaryBlockCount (Nat.bit false (q - 2 ^ y)) ≤
            binaryBlockCount (Nat.bit false q) + 1
          simpa only [binaryBlockCount_bit_false] using ih q hq
      | true =>
          change binaryBlockCount (Nat.bit true (q - 2 ^ y)) ≤
            binaryBlockCount (Nat.bit true q) + 1
          rw [binaryBlockCount_bit_true, binaryBlockCount_bit_true]
          cases y with
          | zero =>
              norm_num at ih hq ⊢
              have hp := binaryBlockCount_pred q
              obtain ⟨r, rfl⟩ :=
                Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
              cases hr : r.bodd <;>
                simp [Nat.bodd_succ, hr] at hp ⊢ <;> omega
          | succ y =>
              have heven : (2 ^ (y + 1)).bodd = false := by
                simp [pow_succ]
              have hparity : (q - 2 ^ (y + 1)).bodd = q.bodd := by
                have heq := congrArg Nat.bodd (Nat.sub_add_cancel hq)
                simpa only [Nat.bodd_add, heven, Bool.xor_false] using heq
              rw [hparity]
              have hi := ih q hq
              omega

end AntichainOfGivenSize
