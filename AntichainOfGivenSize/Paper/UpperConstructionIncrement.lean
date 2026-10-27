import AntichainOfGivenSize.Paper.UpperConstructionSteps

namespace AntichainOfGivenSize.Paper.UpperConstruction

theorem paper_block_increment
    {r ell d : ℕ} (hr : 0 < r) (hd : d < 2 ^ ell)
    (active : Finset (BitMatching.Stage r))
    (hist : BitMatching.Stage r →
      Finset (PatternGadget.Index ell))
    (i : BitMatching.Stage r) (hi : i ∉ active) :
    ((idealCard (ell := ell)
        (insert i active)
        (Function.update hist i (digitSelection ell d))
        PatternGadget.generator
      - idealCard (ell := ell) active hist
        PatternGadget.generator : ℕ) :
        ZMod (2 ^ ((i.val + 1) * ell))) =
      (-1 : ZMod (2 ^ ((i.val + 1) * ell))) ^ r *
        (d : ZMod (2 ^ ((i.val + 1) * ell))) *
        (2 : ZMod (2 ^ ((i.val + 1) * ell))) ^
          (i.val * ell) := by
  classical
  have hz :
      (2 : ZMod (2 ^ ((i.val + 1) * ell))) ^ ell *
        (2 : ZMod (2 ^ ((i.val + 1) * ell))) ^
          (i.val * ell) = 0 := by
    rw [← pow_add,
      show ell + i.val * ell = (i.val + 1) * ell by ring]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (ZMod.natCast_self (2 ^ ((i.val + 1) * ell)))
  rw [idealCard_update active hist PatternGadget.generator
        i hi (digitSelection ell d),
      Nat.add_sub_cancel_left,
      block_increment hr hd active hist i hi]
  push_cast
  linear_combination
    (-1 : ZMod (2 ^ ((i.val + 1) * ell))) ^ r * hz

end AntichainOfGivenSize.Paper.UpperConstruction
