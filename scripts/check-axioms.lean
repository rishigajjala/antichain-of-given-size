import AntichainOfGivenSize
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Check the assumptions used by the project's proofs

Run from the repository root after `lake build --wfail`:
`lake env lean scripts/check-axioms.lean`.

This checks the axioms used by every theorem in the project library,
including private and generated theorems. It does not verify that a
mathematical definition expresses the intended problem; see
`docs/statement-audit.md` for that review.

The module list is explicit so a change in the imported library requires
review. Keep it in sync with the library's Lean source files.
-/

open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000

run_cmd do
  let env ← getEnv
  let expected : Array Name := #[
    `AntichainOfGivenSize,
    `AntichainOfGivenSize.AntichainReduction,
    `AntichainOfGivenSize.AsymptoticBridge,
    `AntichainOfGivenSize.BasicLemmas,
    `AntichainOfGivenSize.BlockCount.AssembleClusters,
    `AntichainOfGivenSize.BlockCount.AssembledError,
    `AntichainOfGivenSize.BlockCount.AssembledGrid,
    `AntichainOfGivenSize.BlockCount.Binary,
    `AntichainOfGivenSize.BlockCount.ClusterGrid,
    `AntichainOfGivenSize.BlockCount.ClusterPartition,
    `AntichainOfGivenSize.BlockCount.ErrorArithmetic,
    `AntichainOfGivenSize.BlockCount.ErrorToGrid,
    `AntichainOfGivenSize.BlockCount.ExplicitWitness,
    `AntichainOfGivenSize.BlockCount.ExtremalRecursion,
    `AntichainOfGivenSize.BlockCount.FiniteExponents,
    `AntichainOfGivenSize.BlockCount.FiniteIncrement,
    `AntichainOfGivenSize.BlockCount.FiniteScales,
    `AntichainOfGivenSize.BlockCount.GapArithmetic,
    `AntichainOfGivenSize.BlockCount.ReductionCertificate,
    `AntichainOfGivenSize.BlockCount.ScaledIdeals,
    `AntichainOfGivenSize.BlockCount.SingletonBound,
    `AntichainOfGivenSize.BlockCount.TermGap,
    `AntichainOfGivenSize.BlockCount.Tight,
    `AntichainOfGivenSize.BlockCount.Upper,
    `AntichainOfGivenSize.BlockCount.ValuationBounds,
    `AntichainOfGivenSize.Definitions,
    `AntichainOfGivenSize.LowerBound.BinaryBlocks,
    `AntichainOfGivenSize.LowerBound.BoundedProfiles,
    `AntichainOfGivenSize.LowerBound.CarrySensitive,
    `AntichainOfGivenSize.LowerBound.ClusterCore,
    `AntichainOfGivenSize.LowerBound.ClusterEncoding,
    `AntichainOfGivenSize.LowerBound.ClusterFiber,
    `AntichainOfGivenSize.LowerBound.ClusterImageBound,
    `AntichainOfGivenSize.LowerBound.ClusterParameters,
    `AntichainOfGivenSize.LowerBound.ClusterProfileCodes,
    `AntichainOfGivenSize.LowerBound.ClusterSparsityAssembly,
    `AntichainOfGivenSize.LowerBound.ClusterState,
    `AntichainOfGivenSize.LowerBound.ClusterStateConstruction,
    `AntichainOfGivenSize.LowerBound.Conductor,
    `AntichainOfGivenSize.LowerBound.FiniteFiberBound,
    `AntichainOfGivenSize.LowerBound.IdealBlockCount,
    `AntichainOfGivenSize.LowerBound.InfinitelyOften,
    `AntichainOfGivenSize.LowerBound.Matching,
    `AntichainOfGivenSize.LowerBound.ProfilePadding,
    `AntichainOfGivenSize.LowerBound.QuadraticLogEndpoint,
    `AntichainOfGivenSize.LowerBound.SignedPowers,
    `AntichainOfGivenSize.LowerBound.SparseEncoding,
    `AntichainOfGivenSize.LowerBound.ThresholdFiltration,
    `AntichainOfGivenSize.LowerBound.VennProfiles,
    `AntichainOfGivenSize.MainStatement,
    `AntichainOfGivenSize.MainTheorems,
    `AntichainOfGivenSize.MatchingParameters,
    `AntichainOfGivenSize.RangeArithmetic,
    `AntichainOfGivenSize.RangeReduction,
    `AntichainOfGivenSize.Section6.Address,
    `AntichainOfGivenSize.Section6.Blocks,
    `AntichainOfGivenSize.Section6.Construction,
    `AntichainOfGivenSize.Section6.Core,
    `AntichainOfGivenSize.Section6.IndexedBounds,
    `AntichainOfGivenSize.Section6.ModularIncrement,
    `AntichainOfGivenSize.Section6.NatParameters,
    `AntichainOfGivenSize.Section6.Remainder,
    `AntichainOfGivenSize.Section6.StageArithmetic,
    `AntichainOfGivenSize.Section6.StageBridge,
    `AntichainOfGivenSize.Section6.Survivors,
    `AntichainOfGivenSize.Theorem
  ]
  let actual := env.header.moduleNames.filter (Name.isPrefixOf `AntichainOfGivenSize ·)
  for mod in expected do
    unless actual.contains mod do
      throwError "Project source module was not imported: {mod}"
  for mod in actual do
    unless expected.contains mod do
      throwError "Imported project module has no tracked source: {mod}"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked := 0
  let mut allProjectConstants := 0
  let mut observed : Array Name := #[]
  let mut perModule : NameMap Nat := {}
  let mut noAxioms := 0
  for mod in expected do
    let some idx := env.getModuleIdx? mod
      | throwError "Missing project module: {mod}"
    let data := env.header.moduleData[idx.toNat]!
    for info in data.constants do
      let name := info.name
      allProjectConstants := allProjectConstants + 1
      if info matches .axiomInfo _ then
        throwError "Project declares a custom axiom: {name}"
      if info matches .thmInfo _ then
        checked := checked + 1
        perModule := perModule.insert mod (perModule.getD mod 0 + 1)
        let axs ← collectAxioms name
        if axs.isEmpty then
          noAxioms := noAxioms + 1
        for ax in axs do
          unless allowed.contains ax do
            throwError "Unexpected transitive axiom: {name} uses {ax}"
          unless observed.contains ax do
            observed := observed.push ax
  unless checked > 0 do
    throwError "The audit found no project theorem declarations"
  logInfo m!"PASS: {checked} theorem declarations checked across {actual.size} project library modules; {allProjectConstants} total project declarations; {noAxioms} theorem declarations require no axioms."
  logInfo m!"Observed axiom union: {observed.qsort Name.lt}"
  for mod in expected do
    logInfo m!"MODULE {mod}: {perModule.getD mod 0} theorem declarations"

#print axioms AntichainOfGivenSize.mainAlphaHasAntichainWitness
#print axioms AntichainOfGivenSize.mainUpperBound
#print axioms AntichainOfGivenSize.mainLowerBound
#print axioms AntichainOfGivenSize.mainLowerBound_explicit
#print axioms AntichainOfGivenSize.mainBlockCountLowerBound
#print axioms AntichainOfGivenSize.mainBlockCountUpperBound
#print axioms AntichainOfGivenSize.mainBlockCountBounds
#print axioms AntichainOfGivenSize.mainBlockCountTightBound
#print axioms AntichainOfGivenSize.mainExplicitBlockWitness
