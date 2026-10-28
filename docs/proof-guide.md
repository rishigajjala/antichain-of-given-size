# Reading and checking the Lean proofs

Start with the [README](../README.md) for the current manuscript and
[`Model/Theorem.lean`](../AntichainOfGivenSize/Model/Theorem.lean) for its public
statements. Review the definitions in
[`Model/ProblemSetting.lean`](../AntichainOfGivenSize/Model/ProblemSetting.lean),
the representation equivalence in
[`Model/Prelude.lean`](../AntichainOfGivenSize/Model/Prelude.lean), and the field-free
[`Model/Prior.lean`](../AntichainOfGivenSize/Model/Prior.lean) alongside the paper.
The [manuscript correspondence](current-paper.md#numbered-results) maps all
18 numbered proof targets to their Lean declarations.

## Current manuscript proofs

[`Analysis/TheoremProof.lean`](../AntichainOfGivenSize/Analysis/TheoremProof.lean)
assembles the main asymptotic theorem. Its components have these proof entry points:

| Result | Files to read |
| --- | --- |
| Universal sharp upper bound | [`Analysis/AlphaEventualUpperProof.lean`](../AntichainOfGivenSize/Analysis/AlphaEventualUpperProof.lean), then [`Analysis/Paper/Extremal.lean`](../AntichainOfGivenSize/Analysis/Paper/Extremal.lean) |
| Uniform counting bound | [`Analysis/AttainableCountProof.lean`](../AntichainOfGivenSize/Analysis/AttainableCountProof.lean), then [`Analysis/Paper/FaithfulCounting/CompleteCounting.lean`](../AntichainOfGivenSize/Analysis/Paper/FaithfulCounting/CompleteCounting.lean) |
| Density-one lower bound and simultaneous bounds | [`Analysis/AlphaLowerDensityOneProof.lean`](../AntichainOfGivenSize/Analysis/AlphaLowerDensityOneProof.lean), [`Analysis/AlphaSimultaneousDensityOneProof.lean`](../AntichainOfGivenSize/Analysis/AlphaSimultaneousDensityOneProof.lean), and [`Analysis/Paper/RealDensity.lean`](../AntichainOfGivenSize/Analysis/Paper/RealDensity.lean) |
| Exact dyadic probability statement | [`Analysis/Paper/TypicalProbability.lean`](../AntichainOfGivenSize/Analysis/Paper/TypicalProbability.lean) |
| Paper's literal block-matching construction | [`Analysis/Paper/LiteralBlockMatching.lean`](../AntichainOfGivenSize/Analysis/Paper/LiteralBlockMatching.lean) |

The sharp upper endpoint reuses the earlier complete construction and proves
finite-prefix absorption. The literal block-matching result is also proved;
the correspondence document explains where the formal routes differ from the
paper's proof. Moving their files under `Analysis/` retains the original proofs
and dependencies. Mathematical namespaces such as `AntichainOfGivenSize.Paper`
and `AntichainOfGivenSize.BlockCount` have not changed.

Import the [umbrella module](../AntichainOfGivenSize.lean) with
`import AntichainOfGivenSize` to make all results available.

## Related statements and certificates

The [related-results overview](related-results.md) retains the binary-block
results and the earlier infinitely-often bounds.
[`Analysis/Supporting/MainStatement.lean`](../AntichainOfGivenSize/Analysis/Supporting/MainStatement.lean)
collects their propositions, and
[`Analysis/Supporting/MainTheorems.lean`](../AntichainOfGivenSize/Analysis/Supporting/MainTheorems.lean)
supplies the corresponding proofs. Their names retain the namespace
`AntichainOfGivenSize`; for example, `AntichainOfGivenSize.mainBlockCountBounds`.
The explicit witness is
`AntichainOfGivenSize.BlockCount.explicitBlockWitness`.

The following sections give the supporting routes for these related results.

## The sharp block-count bound

| Part of the argument | Files to read |
| --- | --- |
| Removing redundant generators to obtain an antichain | [`Analysis/Supporting/AntichainReduction.lean`](../AntichainOfGivenSize/Analysis/Supporting/AntichainReduction.lean) |
| Combining ideals and multiplying their sizes by powers of two | [`Analysis/Supporting/BasicLemmas.lean`](../AntichainOfGivenSize/Analysis/Supporting/BasicLemmas.lean) |
| Counting binary runs and proving the upper bound | [`Analysis/BlockCount/Binary.lean`](../AntichainOfGivenSize/Analysis/BlockCount/Binary.lean), [`Analysis/BlockCount/Upper.lean`](../AntichainOfGivenSize/Analysis/BlockCount/Upper.lean) |
| Expressing an ideal size by adding and subtracting powers of two, then proving the logarithmic lower bound | [`Analysis/LowerBound/SignedPowers.lean`](../AntichainOfGivenSize/Analysis/LowerBound/SignedPowers.lean), [`Analysis/LowerBound/BinaryBlocks.lean`](../AntichainOfGivenSize/Analysis/LowerBound/BinaryBlocks.lean), [`Analysis/LowerBound/IdealBlockCount.lean`](../AntichainOfGivenSize/Analysis/LowerBound/IdealBlockCount.lean) |
| Defining sums of ideal sizes multiplied by integer powers of two, with cost equal to their total generator count | [`Analysis/BlockCount/ScaledIdeals.lean`](../AntichainOfGivenSize/Analysis/BlockCount/ScaledIdeals.lean) |
| Choosing a finite list of scales and finding a gap among the relevant exponents | [`Analysis/BlockCount/FiniteExponents.lean`](../AntichainOfGivenSize/Analysis/BlockCount/FiniteExponents.lean), [`Analysis/BlockCount/FiniteScales.lean`](../AntichainOfGivenSize/Analysis/BlockCount/FiniteScales.lean) |
| Grouping terms, controlling the error, and proving that the grouped sum lies on a discrete grid | [`Analysis/BlockCount/AssembleClusters.lean`](../AntichainOfGivenSize/Analysis/BlockCount/AssembleClusters.lean), [`Analysis/BlockCount/AssembledError.lean`](../AntichainOfGivenSize/Analysis/BlockCount/AssembledError.lean), [`Analysis/BlockCount/AssembledGrid.lean`](../AntichainOfGivenSize/Analysis/BlockCount/AssembledGrid.lean) |
| Converting those estimates into a reduction of the generator cost | [`Analysis/BlockCount/ReductionCertificate.lean`](../AntichainOfGivenSize/Analysis/BlockCount/ReductionCertificate.lean), [`Analysis/BlockCount/FiniteIncrement.lean`](../AntichainOfGivenSize/Analysis/BlockCount/FiniteIncrement.lean) |
| Proving attainment for every positive block count and verifying the explicit recursion | [`Analysis/BlockCount/Tight.lean`](../AntichainOfGivenSize/Analysis/BlockCount/Tight.lean), [`Analysis/BlockCount/ExplicitWitness.lean`](../AntichainOfGivenSize/Analysis/BlockCount/ExplicitWitness.lean) |

For the central reduction theorem, look for
`finiteThreshold_costReduction_proved` in `Analysis/BlockCount/Tight.lean`. It has the
full namespace `AntichainOfGivenSize.BlockCount` and supplies the estimate
used to prove both attainment and the explicit witness theorem. The imports
at the top of each file point to its supporting lemmas.

## Bounds in terms of the integer's size

The upper bound is assembled in
[`Analysis/Supporting/Theorem.lean`](../AntichainOfGivenSize/Analysis/Supporting/Theorem.lean). Its finite construction
is in [`Analysis/Section6/Construction.lean`](../AntichainOfGivenSize/Analysis/Section6/Construction.lean),
and the exact change in ideal size at one construction step is proved in
[`Analysis/Section6/ModularIncrement.lean`](../AntichainOfGivenSize/Analysis/Section6/ModularIncrement.lean).
[`Analysis/Supporting/RangeReduction.lean`](../AntichainOfGivenSize/Analysis/Supporting/RangeReduction.lean) and
[`Analysis/Supporting/AsymptoticBridge.lean`](../AntichainOfGivenSize/Analysis/Supporting/AsymptoticBridge.lean) turn
the finite construction into an upper bound for all sufficiently large inputs.

The matching lower bound is exposed in
[`Analysis/LowerBound/Matching.lean`](../AntichainOfGivenSize/Analysis/LowerBound/Matching.lean).
The proof records how many universe elements belong to each exact
pattern of generator membership in
[`Analysis/LowerBound/VennProfiles.lean`](../AntichainOfGivenSize/Analysis/LowerBound/VennProfiles.lean),
counts the possible records in
[`Analysis/LowerBound/ClusterSparsityAssembly.lean`](../AntichainOfGivenSize/Analysis/LowerBound/ClusterSparsityAssembly.lean),
and converts this count into the stated lower bound using
[`Analysis/LowerBound/QuadraticLogEndpoint.lean`](../AntichainOfGivenSize/Analysis/LowerBound/QuadraticLogEndpoint.lean).
This lower bound holds at arbitrarily large inputs.

## Other lower-bound results

[`Analysis/LowerBound/InfinitelyOften.lean`](../AntichainOfGivenSize/Analysis/LowerBound/InfinitelyOften.lean)
uses alternating binary words to obtain a simpler logarithm-of-a-logarithm
lower bound. [`Analysis/LowerBound/CarrySensitive.lean`](../AntichainOfGivenSize/Analysis/LowerBound/CarrySensitive.lean)
improves this explicit family by accounting for carries in binary addition.

[`Analysis/LowerBound/Conductor.lean`](../AntichainOfGivenSize/Analysis/LowerBound/Conductor.lean)
studies the first integer whose ideal needs more than a specified number of
generators. [`Analysis/LowerBound/ThresholdFiltration.lean`](../AntichainOfGivenSize/Analysis/LowerBound/ThresholdFiltration.lean)
studies nested collections of intersections obtained by varying a size
threshold. These additional results are exported by the umbrella module.

## Build

From the repository root, with Lean installed, run:

```bash
lake exe cache get
lake build --wfail
```

The toolchain and dependency versions are pinned by
[`lean-toolchain`](../lean-toolchain), [`lakefile.toml`](../lakefile.toml), and
[`lake-manifest.json`](../lake-manifest.json). The
[CI workflow](../.github/workflows/ci.yml) also runs the build with warnings
treated as failures.

## Checking the axioms

The [statement audit](statement-audit.md) explains how the definitions,
quantifiers, and proof assumptions were checked against the intended
mathematics. The automated check below addresses a different question:
which assumed principles do the formal proofs depend on?

After building, run the repository-wide dependency check:

```bash
lake env lean -DwarningAsError=true scripts/CheckAxioms.lean
```

It checks every declaration originating in the project library modules,
including definitions, instances, private declarations, and automatically
generated declarations. It also checks that the source files, explicit
module registry, and imports agree. The
[verification report](../.blueprint/verification/checks.json) identifies the exact
source snapshot, while [the manuscript correspondence](current-paper.md) describes
the expanded statement checks. The strict command
rejects omitted-proof dependencies and unexpected axioms. These checks support
the semantic audit; they do not decide whether a definition expresses the
intended problem.

To inspect the nine original public certificates, save the following as
`/tmp/AntichainAxioms.lean`:

```lean
import AntichainOfGivenSize

#print axioms AntichainOfGivenSize.mainAlphaHasAntichainWitness
#print axioms AntichainOfGivenSize.mainUpperBound
#print axioms AntichainOfGivenSize.mainLowerBound
#print axioms AntichainOfGivenSize.mainLowerBound_explicit
#print axioms AntichainOfGivenSize.mainBlockCountLowerBound
#print axioms AntichainOfGivenSize.mainBlockCountUpperBound
#print axioms AntichainOfGivenSize.mainBlockCountBounds
#print axioms AntichainOfGivenSize.mainBlockCountTightBound
#print axioms AntichainOfGivenSize.mainExplicitBlockWitness
```

Then, from the repository root, run:

```bash
lake env lean /tmp/AntichainAxioms.lean
```

The reported dependencies are drawn only from Lean's standard principles
`propext` (equivalent propositions are equal), `Classical.choice` (choosing
an element whose existence is known), and `Quot.sound` (equivalent elements
give equal quotient classes). No certificate depends on `sorryAx`, the
placeholder used for an omitted proof, or on an additional custom axiom.
