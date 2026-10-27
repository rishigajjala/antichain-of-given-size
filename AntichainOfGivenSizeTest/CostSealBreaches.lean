import AntichainOfGivenSize.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

/-!
# The seal, made to fail

These tests exercise the generated compiler checks and `#programSeal`. Each
`#guard_msgs` block requires the stated diagnostic: it fails if a prohibited
operation starts passing or if a different error prevents the intended check.

The installed generator's tests used separate namespaces, but its checker now
requires `AntichainOfGivenSize.Program`. The helper below elaborates each test
in that canonical namespace, calls the production checker, and then restores
the preceding environment. Thus each rejection concerns exactly one test
without retaining its deliberately invalid program for later tests. The
helper does not change the checker or filter its diagnostics.

## What is covered

* §1 — the cheats the *compiler* rejects, so that a change making one of them
  compile is caught before either seal is reached.
* §2 — `#programSeal`: the routes past the compiler, inside the algorithm —
  including the one that only a *transitive* scan catches, which is the property
  `reaches` exists for and the first test to run if it is ever touched.
The namespace and nonempty checks are tested separately, and a permitted
computation provides a positive control.
-/

namespace AntichainOfGivenSizeTest

open Arlib.Computation

open Lean Elab Command in
/-- Run the production seal on one temporary declaration in its canonical namespace. -/
elab "#checkProgramSealOn " decl:command : command => do
  withoutModifyingEnv do
    elabCommand decl
    let programNamespace := mkIdent `AntichainOfGivenSize.Program
    elabCommand (← `(command| #programSeal $programNamespace))

/-! The checker must reject an unrelated namespace and an empty canonical
namespace before any test program is added. -/
/--
error: Program seal must target the canonical namespace AntichainOfGivenSize.Program, not AntichainOfGivenSizeTest.Unrelated.
-/
#guard_msgs (whitespace := lax) in
#programSeal AntichainOfGivenSizeTest.Unrelated

/--
error: Program seal checked zero declarations under AntichainOfGivenSize.Program. Put the executable declarations from Model/Program.lean in this exact namespace; a vacuous seal is not a seal.
-/
#guard_msgs (whitespace := lax) in
#programSeal AntichainOfGivenSize.Program

/-! A computation using only `pure` passes; its informational report is ignored,
but any warning or error still fails the test. -/
#guard_msgs (drop info) in
#checkProgramSealOn
def _root_.AntichainOfGivenSize.Program.permitted : Charged StdOp Cell Nat := pure 0

/-! ## 1. What the compiler rejects on its own -/

/-! Copying a computation's result to drop its charges.  This is the cheat that
would make every bound in the development vacuous, and it does not compile,
because `Charged.val` is `noncomputable`. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Charged.val', which is 'noncomputable'
-/
#guard_msgs in
def dropTally (p : Charged StdOp Cell Nat) : Charged StdOp Cell Nat := pure p.val

/-! Reading a dictionary's size without asking it.  `Roster.card` is the
specification's view and is `noncomputable`, so a program that wants the number
must call `Roster.size` and pay. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Roster.card', which is 'noncomputable'
-/
#guard_msgs in
def freeSize (d : Roster Nat) : Nat := d.card

/-! Forging a tally.  There is no syntax for asserting what something cost. -/
/--
error: Invalid `⟨...⟩` notation: Constructor for `Arlib.Computation.Charged` is marked as private
-/
#guard_msgs in
example : Charged StdOp Cell Nat := ⟨0, 0, 1⟩

/-! ## 2. `#programSeal` — the routes past the compiler -/

/-! **Laundering a tally through a change of currency.**  `exchange` is
computable and takes a `Charged` to a `Charged`, so nothing the compiler checks
stands in the way; at a rate of zero it re-prices any computation at nothing. -/
/--
error: Seal breach in AntichainOfGivenSize.Program: [(AntichainOfGivenSize.Program.exchange, Arlib.Computation.Charged.exchange)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#checkProgramSealOn
def _root_.AntichainOfGivenSize.Program.exchange (p : Charged StdOp Cell Nat) : Charged StdOp Cell Nat :=
  Charged.exchange (fun _ => (0 : CostVec StdOp)) p

/-! **Silencing the compiler.**  Writing `noncomputable def` turns off the half
of the seal §1 relies on.  Nothing else about this declaration is wrong, which is
the point: the marker alone is the breach. -/
/--
error: Seal breach in AntichainOfGivenSize.Program: [(AntichainOfGivenSize.Program.noncomputable, noncomputableProgram)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#checkProgramSealOn
noncomputable def _root_.AntichainOfGivenSize.Program.noncomputable : Real := 0

/-! **Projecting a dictionary's contents through the eliminator.**  `casesOn` is
generated public even though the constructor is private, and it is compiled, so
this is the one route the compiler genuinely leaves open. -/
/--
error: Seal breach in AntichainOfGivenSize.Program: [(AntichainOfGivenSize.Program.casesOn, Arlib.Computation.Roster.casesOn)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#checkProgramSealOn
def _root_.AntichainOfGivenSize.Program.casesOn (d : Roster Nat) : Nat :=
  Roster.casesOn (motive := fun _ => Nat) d (fun elems _ => elems.length)

/-! **Pricing a line by hand.**  `Charged.op o a` is arlib's escape hatch — one
operation of the currency, returning a value the algorithm computed for itself —
and a program may not call it inline. Standard operations come from arlib;
project-local operations come from `Model/Operations.lean`.

The cheat below is exactly what the algorithm used to do, and it is the shape to
watch for: the charge says "one coin" and the argument is an `O(level)` scan of a
bare bit block, read at a level nobody paid for.  The seal cannot see that the
argument is expensive — nothing can — so it forbids the escape hatch directly in
`Program.lean`. The honest fix for a line that genuinely needs one is to expose
the primitive in the operation model. -/
/--
error: Seal breach in AntichainOfGivenSize.Program: [(AntichainOfGivenSize.Program.handPriced, Arlib.Computation.Charged.op)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#checkProgramSealOn
-- The original wrote this against the development's own `BitBlock` and
-- `acceptsAt`, which is the shape the algorithm actually had. Here it is a
-- bare function on `Nat`, so that the breach library builds with nothing but
-- arlib and can be a default target from the first commit of a project. The
-- property under test is unchanged: the charge says one coin, and the seal
-- cannot see what the argument cost.
def _root_.AntichainOfGivenSize.Program.handPriced (level : Nat) (bits : Nat → Bool) : Charged StdOp Cell Bool :=
  Charged.op (StdOp.rand .accept) (bits level)

/-! **Reading the sampling level.**  The level is inside a `Sampler` and
`Sampler.levelOf` is noncomputable, so the compiler rejects this before the seal
gets to it — which is the stronger of the two rejections.  With `level : ℕ` a
bare field, `|X| * 2 ^ level` was the driver's arithmetic on a number nobody
asked for. -/
namespace Breach.PeekLevel.Program
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Sampler.levelOf', which is 'noncomputable'
-/
#guard_msgs in
def cheat (s : Sampler) (n : Nat) : Nat := n * 2 ^ s.levelOf
end Breach.PeekLevel.Program

/-! **Observing a computation's own tally.**  `Charged.cost` is computable and
"produces no value" — until `decide` is applied to it.  `Roster.cost_filterErase`
equates a thinning pass's tally to `d.card`, so a program that may read `cost`
has a free cardinality and therefore a free `cardEq`. -/
/--
error: Seal breach in AntichainOfGivenSize.Program: [(AntichainOfGivenSize.Program.cost, Arlib.Computation.Charged.cost)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#checkProgramSealOn
def _root_.AntichainOfGivenSize.Program.cost (p : Charged StdOp Cell Nat) : CostVec StdOp := p.cost

/-! **The same read, one hop away.**  `Charged.steps` is deliberately absent from
`forbiddenInProgram`: it is `CostVec.steps C p.cost`, so a blacklist of *direct*
mentions would miss it entirely.  This test is what makes the transitive walk a
checked fact rather than an intention, and it is the one to run first if
`reaches` is ever changed.

Note which constant the message names — the intermediary the program actually
called, not the forbidden constant behind it.  That is the name whose call site
has to change. -/
/--
error: Seal breach in AntichainOfGivenSize.Program: [(AntichainOfGivenSize.Program.transitive, Arlib.Computation.Charged.steps)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#checkProgramSealOn
def _root_.AntichainOfGivenSize.Program.transitive (p : Charged StdOp Cell Nat) : Nat := Charged.steps (Rate.unit StdOp) p

/-! **Reading what a computation holds.**  This one the compiler rejects on its
own, and for a stronger reason than it rejects `Charged.cost`: a tally tells a
program which branch it took, which it already knew, while a profile tells it how
much data it holds — which is exactly what the data seal hides.  `decide
(p.space.net k = 1)` after an insertion is a free membership test. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Charged.space', which is 'noncomputable'
-/
#guard_msgs in
def readProfile (p : Charged StdOp Cell Nat) : Profile Cell := p.space

/-! **Measuring a dictionary directly.**  `Residency.at'` is the space analogue
of `Roster.card`, and noncomputable for the same reason. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Residency.at'', which is 'noncomputable'
-/
#guard_msgs in
def readResidency (r : Residency Cell) : Nat := r.at' Cell.roster

/-! **Supplying your own measure.**  `opUpdate` is computable and takes the
measure as an argument, so nothing the compiler checks objects to a measure that
reports nothing — this is `Charged.exchange (fun _ => 0)` for space.  A program
calls `Roster.insert`, which passes a measure private to `Roster`. -/
/--
error: Seal breach in AntichainOfGivenSize.Program: [(AntichainOfGivenSize.Program.measure, Arlib.Computation.Charged.opUpdate), (AntichainOfGivenSize.Program.measure, Arlib.Computation.Residency.ofFun)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#checkProgramSealOn
def _root_.AntichainOfGivenSize.Program.measure (d : Roster Nat) : Charged StdOp Cell (Roster Nat) :=
  Charged.opUpdate (StdOp.roster .insert) (fun _ => Residency.ofFun fun _ => 0) id d

/-! **Reading the measured peak.**  `Charged.peakAt` is computable on purpose —
`#guard` has to read it for the protocol's execution tests — so the compiler does
not object, and the seal is what stops an algorithm from using it as a free size
query.  Same standing as `Charged.cost`. -/
/--
error: Seal breach in AntichainOfGivenSize.Program: [(AntichainOfGivenSize.Program.peakAt, Arlib.Computation.Charged.peakAt)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#checkProgramSealOn
def _root_.AntichainOfGivenSize.Program.peakAt (p : Charged StdOp Cell Nat) : Int := p.peakAt Cell.roster

/-! None of the temporary programs, including the positive control, may escape
the helper's restored environment. -/
/--
error: Program seal checked zero declarations under AntichainOfGivenSize.Program. Put the executable declarations from Model/Program.lean in this exact namespace; a vacuous seal is not a seal.
-/
#guard_msgs (whitespace := lax) in
#programSeal AntichainOfGivenSize.Program

end AntichainOfGivenSizeTest
