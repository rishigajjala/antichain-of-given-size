import AntichainOfGivenSize
import AntichainOfGivenSize.Model.Theorem
import AntichainOfGivenSize.Meta.Audit
import AntichainOfGivenSize.Meta.CostSeal
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Check the assumptions used by the project's proofs

Run from the repository root after `lake build --wfail`:
`lake env lean -DwarningAsError=true scripts/CheckAxioms.lean`.

This checks the axioms used by every declaration in the project library,
including private declarations and proof-bearing definitions or instances.
It does not verify that a
mathematical definition expresses the intended problem; see
`docs/statement-audit.md` for that review.

The module list is explicit so a change in the imported library requires
review. It is checked against both the source files and imported modules,
so an unimported source file cannot silently escape the audit.

At an opening proof frontier, ordinary elaboration reports every transitive
`sorryAx` dependency as an `OPEN` warning so proof scheduling can inspect the
development. Such a run never reports `PASS`. The strict command above rejects
these warnings; custom axioms and all other audit violations remain errors
in both modes.
-/

open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000

run_cmd do
  let env ← getEnv
  let expected : Array Name := #[
    `AntichainOfGivenSize,
    `AntichainOfGivenSize.Analysis.AlphaEventualUpperProof,
    `AntichainOfGivenSize.Analysis.AlphaLowerDensityOneProof,
    `AntichainOfGivenSize.Analysis.AlphaMaximumOrderProof,
    `AntichainOfGivenSize.Analysis.AlphaSimultaneousDensityOneProof,
    `AntichainOfGivenSize.Analysis.AttainableCountProof,
    `AntichainOfGivenSize.Analysis.AttainableValuesMembershipProof,
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
    `AntichainOfGivenSize.Meta.Audit,
    `AntichainOfGivenSize.Meta.CostSeal,
    `AntichainOfGivenSize.Meta.ModelClosure,
    `AntichainOfGivenSize.Model.CountingVocabulary,
    `AntichainOfGivenSize.Model.MainVocabulary,
    `AntichainOfGivenSize.Model.Prelude,
    `AntichainOfGivenSize.Model.Prior,
    `AntichainOfGivenSize.Model.Theorem,
    `AntichainOfGivenSize.Paper.AlmostAll,
    `AntichainOfGivenSize.Paper.BasicResults,
    `AntichainOfGivenSize.Paper.BitMatching,
    `AntichainOfGivenSize.Paper.CountingEstimates,
    `AntichainOfGivenSize.Paper.CountingParameters,
    `AntichainOfGivenSize.Paper.Density,
    `AntichainOfGivenSize.Paper.DirectReduction,
    `AntichainOfGivenSize.Paper.Extremal,
    `AntichainOfGivenSize.Paper.FaithfulCounting.ActualCounting,
    `AntichainOfGivenSize.Paper.FaithfulCounting.CanonicalHeader,
    `AntichainOfGivenSize.Paper.FaithfulCounting.CompleteCounting,
    `AntichainOfGivenSize.Paper.FaithfulCounting.ConnectedSubset,
    `AntichainOfGivenSize.Paper.FaithfulCounting.HeaderExistence,
    `AntichainOfGivenSize.Paper.FaithfulCounting.IncidenceCount,
    `AntichainOfGivenSize.Paper.FaithfulCounting.LiteralScales,
    `AntichainOfGivenSize.Paper.FaithfulCounting.NumericalParameters,
    `AntichainOfGivenSize.Paper.FaithfulCounting.OriginalQueryReconstruction,
    `AntichainOfGivenSize.Paper.FaithfulCounting.PartitionHeader,
    `AntichainOfGivenSize.Paper.FaithfulCounting.RealTailFiberCore,
    `AntichainOfGivenSize.Paper.FaithfulCounting.ScalarNormalization,
    `AntichainOfGivenSize.Paper.FirstUpper,
    `AntichainOfGivenSize.Paper.GeneralCounting,
    `AntichainOfGivenSize.Paper.PatternGadget,
    `AntichainOfGivenSize.Paper.RealDensity,
    `AntichainOfGivenSize.Paper.Representation,
    `AntichainOfGivenSize.Paper.FaithfulCounting.ClaimBundles,
    `AntichainOfGivenSize.Paper.LiteralBlockMatching,
    `AntichainOfGivenSize.Paper.LiteralUpperParameters,
    `AntichainOfGivenSize.Paper.MainSemantics,
    `AntichainOfGivenSize.Paper.UpperConstructionIncrement,
    `AntichainOfGivenSize.Paper.Results,
    `AntichainOfGivenSize.Paper.Scale,
    `AntichainOfGivenSize.Paper.Statements,
    `AntichainOfGivenSize.Paper.Typical,
    `AntichainOfGivenSize.Paper.UpperConstructionBounds,
    `AntichainOfGivenSize.Paper.UpperConstructionCore,
    `AntichainOfGivenSize.Paper.UpperConstructionGeometry,
    `AntichainOfGivenSize.Paper.UpperConstructionSteps,
    `AntichainOfGivenSize.Paper.UpperParameters,
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
  let sourceDir : System.FilePath := "AntichainOfGivenSize"
  let umbrella : System.FilePath := "AntichainOfGivenSize.lean"
  unless (← sourceDir.isDir) && (← umbrella.pathExists) do
    throwError "Run this audit from the repository root (library sources not found)"
  let sourcePaths := ((← sourceDir.walkDir).filter (·.extension == some "lean")).push umbrella
  let sourceModules := sourcePaths.map fun path ↦
    (path.withExtension "").components.foldl Name.str Name.anonymous
  unless expected.toList.eraseDups.length == expected.size do
    throwError "The tracked module list contains a duplicate"
  for mod in sourceModules do
    unless expected.contains mod do
      throwError "Library source module is not tracked by the audit: {mod}"
  for mod in expected do
    unless sourceModules.contains mod do
      throwError "Tracked module has no library source file: {mod}"
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
  let mut openDeclarations : Array Name := #[]
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
      let axs ← collectAxioms name
      for ax in axs do
        if ax == ``sorryAx then
          openDeclarations := openDeclarations.push name
          logWarning m!"OPEN: {name} depends on sorryAx"
        else unless allowed.contains ax do
          throwError "Unexpected transitive axiom: {name} uses {ax}"
        unless observed.contains ax do
          observed := observed.push ax
      if info matches .thmInfo _ then
        checked := checked + 1
        perModule := perModule.insert mod (perModule.getD mod 0 + 1)
        if axs.isEmpty then
          noAxioms := noAxioms + 1
  unless checked > 0 do
    throwError "The audit found no project theorem declarations"
  if openDeclarations.isEmpty then
    logInfo m!"PASS: {allProjectConstants} declarations checked across {actual.size} project library modules and matching source files; {checked} theorem declarations; {noAxioms} theorem declarations require no axioms."
  else
    logInfo m!"OPEN: {allProjectConstants} declarations inspected across {actual.size} project library modules and matching source files; {openDeclarations.size} declarations depend on unfinished proofs. The strict warnings-as-errors audit rejects these dependencies."
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

-- Current-manuscript certificates: all hypotheses are discharged here.
#print axioms AntichainOfGivenSize.Paper.bitMatching
#print axioms AntichainOfGivenSize.Paper.bitMatchingInt
#print axioms AntichainOfGivenSize.Paper.quadraticUpper
#print axioms AntichainOfGivenSize.Paper.blockMatching
#print axioms AntichainOfGivenSize.Paper.firstUpper
#print axioms AntichainOfGivenSize.Paper.directReduction
#print axioms AntichainOfGivenSize.Paper.countingBound
#print axioms AntichainOfGivenSize.Paper.faithfulCountingBound
#print axioms AntichainOfGivenSize.FaithfulLower.paper_counting_at_parameters
#print axioms AntichainOfGivenSize.FaithfulLower.exists_paper_counting_threshold_strong
#print axioms AntichainOfGivenSize.FaithfulLower.exists_paper_counting_threshold
#print axioms AntichainOfGivenSize.attainable_count
#print axioms AntichainOfGivenSize.Model.attainableValues_membership
#print axioms AntichainOfGivenSize.alpha_asymptotic_order
#print axioms AntichainOfGivenSize.Paper.typicalLowerBound
#print axioms AntichainOfGivenSize.Paper.almostAllLowerBound
#print axioms AntichainOfGivenSize.Paper.almostAllOrder
#print axioms AntichainOfGivenSize.Paper.almostAllGoodProportion
#print axioms AntichainOfGivenSize.Paper.realAlmostAllGoodProportion
#print axioms AntichainOfGivenSize.Paper.extremalOrder
#print axioms AntichainOfGivenSize.Paper.mainTheorem

#print axioms AntichainOfGivenSize.Paper.LiteralUpperParameters.blockMatching
#print axioms AntichainOfGivenSize.Paper.UpperConstruction.paper_block_increment
#print axioms AntichainOfGivenSize.FaithfulLower.normalized_family
#print axioms AntichainOfGivenSize.FaithfulLower.paper_headers
#print axioms AntichainOfGivenSize.FaithfulLower.paper_exceptional_bound_and_agreement
#print axioms AntichainOfGivenSize.FaithfulLower.paper_record_counts
#print axioms AntichainOfGivenSize.FaithfulLower.paper_tail_bounds
#print axioms AntichainOfGivenSize.FaithfulLower.paper_numerics_and_strong_count
#print axioms AntichainOfGivenSize.Paper.density_representations
#print axioms AntichainOfGivenSize.Paper.maximumBelow_spec
