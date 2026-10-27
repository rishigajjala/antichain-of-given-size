import AntichainOfGivenSize.Meta.ModelClosure
import Mathlib.Data.Finset.Card

/-!
# Controls for the statement-closure checker

These checks exercise the generated `#modelClosureOfType` and `#modelClosure`
commands without changing either checker. The mathematical claims are true;
the rejected cases differ only in where their defining vocabulary lives.
`#guard_msgs` requires the intended diagnostic, so a different elaboration
error cannot masquerade as a successful rejection.
-/

namespace AntichainOfGivenSize.ClosureTest

/-- Test-only vocabulary deliberately defined outside `Model/`. -/
def externalNumber : ℕ := 3

/-- A second layer tests traversal through definition bodies. -/
def externalAlias : ℕ := externalNumber

theorem externalStatement : externalNumber = 3 := rfl

theorem transitiveStatement : externalAlias = 3 := rfl

theorem proofFact : (3 : ℕ) = 3 := rfl

/-- Proof-side dependencies are allowed outside the statement surface. -/
theorem proofOnly : (3 : ℕ) = 3 := proofFact

/-- Private names must be classified by their underlying project namespace. -/
private def privateNumber : ℕ := 3

theorem privateStatement : privateNumber = 3 := rfl

/-- The external dependency occurs only in a structure field's type. -/
structure FieldContainer where
  value : Fin externalNumber

theorem fieldStatement (x : FieldContainer) : x = x := rfl

end AntichainOfGivenSize.ClosureTest

namespace AntichainOfGivenSizeTest.ModelClosure

/-! The ordinary Mathlib statement has no project vocabulary. -/
theorem mathlibStatement (s : Finset ℕ) : s.card ≤ s.card := le_rfl

/-- info: OK — the STATEMENT is under Model/ or an admitted module (0) -/
#guard_msgs in
#modelClosureOfType mathlibStatement

/-! The checker reads the statement, allowing an external proof lemma. -/
/-- info: OK — the STATEMENT is under Model/ or an admitted module (0) -/
#guard_msgs in
#modelClosureOfType AntichainOfGivenSize.ClosureTest.proofOnly

/-! A true statement still fails when it depends on vocabulary outside Model. -/
/--
error: OUTSIDE Model/ in the statement: [(AntichainOfGivenSize.ClosureTest.externalNumber, AntichainOfGivenSizeTest.ModelClosure)]
-/
#guard_msgs (whitespace := lax) in
#modelClosureOfType AntichainOfGivenSize.ClosureTest.externalStatement

/-! The alias must not hide the vocabulary it unfolds to. -/
/--
error: OUTSIDE Model/ in the statement: [(AntichainOfGivenSize.ClosureTest.externalNumber, AntichainOfGivenSizeTest.ModelClosure), (AntichainOfGivenSize.ClosureTest.externalAlias, AntichainOfGivenSizeTest.ModelClosure)]
-/
#guard_msgs (whitespace := lax) in
#modelClosureOfType AntichainOfGivenSize.ClosureTest.transitiveStatement

/-! The definition-body variant also follows an external dependency. -/
/--
error: OUTSIDE Model/ in closure of AntichainOfGivenSize.ClosureTest.externalAlias: [(AntichainOfGivenSize.ClosureTest.externalNumber, AntichainOfGivenSizeTest.ModelClosure)]
-/
#guard_msgs (whitespace := lax) in
#modelClosure AntichainOfGivenSize.ClosureTest.externalAlias

/-! A private declaration must not evade the project-namespace check. -/
/--
error: OUTSIDE Model/ in the statement: [(_private.AntichainOfGivenSizeTest.ModelClosure.0.AntichainOfGivenSize.ClosureTest.privateNumber, AntichainOfGivenSizeTest.ModelClosure)]
-/
#guard_msgs (whitespace := lax) in
#modelClosureOfType AntichainOfGivenSize.ClosureTest.privateStatement

/-! Checking the structure's universe alone misses this field dependency.
The required diagnostic must name `externalNumber`, as well as the structure. -/
/--
error: OUTSIDE Model/ in the statement: [(AntichainOfGivenSize.ClosureTest.FieldContainer.mk, AntichainOfGivenSizeTest.ModelClosure), (AntichainOfGivenSize.ClosureTest.externalNumber, AntichainOfGivenSizeTest.ModelClosure), (AntichainOfGivenSize.ClosureTest.FieldContainer, AntichainOfGivenSizeTest.ModelClosure)]
-/
#guard_msgs (whitespace := lax) in
#modelClosureOfType AntichainOfGivenSize.ClosureTest.fieldStatement

end AntichainOfGivenSizeTest.ModelClosure
