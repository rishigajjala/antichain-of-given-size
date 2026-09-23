# Reading and checking the Lean proofs

Start with the [README](../README.md) for the problem and results, and the
[block-count explanation](block-count.md) for the explicit extremal integers.
This guide maps those statements to their proof files.

## Public definitions and certificates

All main definitions and theorem claims are collected in
[`MainStatement.lean`](../AntichainOfGivenSize/MainStatement.lean). This file
imports mathematical libraries but does not import the proofs of the claims.
[`MainTheorems.lean`](../AntichainOfGivenSize/MainTheorems.lean) supplies a short
proof, called a certificate here, of each named claim.

The public definitions and certificates have the namespace
`AntichainOfGivenSize`. For example, the full name of `mainBlockCountBounds`
is `AntichainOfGivenSize.mainBlockCountBounds`. Definitions for the explicit
block witness are in its `BlockCount` subnamespace, so the full witness name
is `AntichainOfGivenSize.BlockCount.explicitBlockWitness`.

Import the [umbrella module](../AntichainOfGivenSize.lean) with
`import AntichainOfGivenSize` to make all results available. Import
`AntichainOfGivenSize.MainStatement` when only the definitions and claims
are needed.

## The sharp block-count bound

| Part of the argument | Files to read |
| --- | --- |
| Removing redundant generators to obtain an antichain | [`AntichainReduction.lean`](../AntichainOfGivenSize/AntichainReduction.lean) |
| Combining ideals and multiplying their sizes by powers of two | [`BasicLemmas.lean`](../AntichainOfGivenSize/BasicLemmas.lean) |
| Counting binary runs and proving the upper bound | [`BlockCount/Binary.lean`](../AntichainOfGivenSize/BlockCount/Binary.lean), [`BlockCount/Upper.lean`](../AntichainOfGivenSize/BlockCount/Upper.lean) |
| Expressing an ideal size by adding and subtracting powers of two, then proving the logarithmic lower bound | [`LowerBound/SignedPowers.lean`](../AntichainOfGivenSize/LowerBound/SignedPowers.lean), [`LowerBound/BinaryBlocks.lean`](../AntichainOfGivenSize/LowerBound/BinaryBlocks.lean), [`LowerBound/IdealBlockCount.lean`](../AntichainOfGivenSize/LowerBound/IdealBlockCount.lean) |
| Defining sums of ideal sizes multiplied by integer powers of two, with cost equal to their total generator count | [`BlockCount/ScaledIdeals.lean`](../AntichainOfGivenSize/BlockCount/ScaledIdeals.lean) |
| Choosing a finite list of scales and finding a gap among the relevant exponents | [`BlockCount/FiniteExponents.lean`](../AntichainOfGivenSize/BlockCount/FiniteExponents.lean), [`BlockCount/FiniteScales.lean`](../AntichainOfGivenSize/BlockCount/FiniteScales.lean) |
| Grouping terms, controlling the error, and proving that the grouped sum lies on a discrete grid | [`BlockCount/AssembleClusters.lean`](../AntichainOfGivenSize/BlockCount/AssembleClusters.lean), [`BlockCount/AssembledError.lean`](../AntichainOfGivenSize/BlockCount/AssembledError.lean), [`BlockCount/AssembledGrid.lean`](../AntichainOfGivenSize/BlockCount/AssembledGrid.lean) |
| Converting those estimates into a reduction of the generator cost | [`BlockCount/ReductionCertificate.lean`](../AntichainOfGivenSize/BlockCount/ReductionCertificate.lean), [`BlockCount/FiniteIncrement.lean`](../AntichainOfGivenSize/BlockCount/FiniteIncrement.lean) |
| Proving attainment for every positive block count and verifying the explicit recursion | [`BlockCount/Tight.lean`](../AntichainOfGivenSize/BlockCount/Tight.lean), [`BlockCount/ExplicitWitness.lean`](../AntichainOfGivenSize/BlockCount/ExplicitWitness.lean) |

For the central reduction theorem, look for
`finiteThreshold_costReduction_proved` in `BlockCount/Tight.lean`. It has the
full namespace `AntichainOfGivenSize.BlockCount` and supplies the estimate
used to prove both attainment and the explicit witness theorem. The imports
at the top of each file point to its supporting lemmas.

## Bounds in terms of the integer's size

The upper bound is assembled in
[`Theorem.lean`](../AntichainOfGivenSize/Theorem.lean). Its finite construction
is in [`Section6/Construction.lean`](../AntichainOfGivenSize/Section6/Construction.lean),
and the exact change in ideal size at one construction step is proved in
[`Section6/ModularIncrement.lean`](../AntichainOfGivenSize/Section6/ModularIncrement.lean).
[`RangeReduction.lean`](../AntichainOfGivenSize/RangeReduction.lean) and
[`AsymptoticBridge.lean`](../AntichainOfGivenSize/AsymptoticBridge.lean) turn
the finite construction into an upper bound for all sufficiently large inputs.

The matching lower bound is exposed in
[`LowerBound/Matching.lean`](../AntichainOfGivenSize/LowerBound/Matching.lean).
The proof records how many universe elements belong to each exact
pattern of generator membership in
[`LowerBound/VennProfiles.lean`](../AntichainOfGivenSize/LowerBound/VennProfiles.lean),
counts the possible records in
[`LowerBound/ClusterSparsityAssembly.lean`](../AntichainOfGivenSize/LowerBound/ClusterSparsityAssembly.lean),
and converts this count into the stated lower bound using
[`LowerBound/QuadraticLogEndpoint.lean`](../AntichainOfGivenSize/LowerBound/QuadraticLogEndpoint.lean).
This lower bound holds at arbitrarily large inputs.

## Other lower-bound results

[`LowerBound/InfinitelyOften.lean`](../AntichainOfGivenSize/LowerBound/InfinitelyOften.lean)
uses alternating binary words to obtain a simpler logarithm-of-a-logarithm
lower bound. [`LowerBound/CarrySensitive.lean`](../AntichainOfGivenSize/LowerBound/CarrySensitive.lean)
improves this explicit family by accounting for carries in binary addition.

[`LowerBound/Conductor.lean`](../AntichainOfGivenSize/LowerBound/Conductor.lean)
studies the first integer whose ideal needs more than a specified number of
generators. [`LowerBound/ThresholdFiltration.lean`](../AntichainOfGivenSize/LowerBound/ThresholdFiltration.lean)
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
lake env lean scripts/check-axioms.lean
```

It checks every theorem declaration originating in the project library
modules, including private and automatically generated declarations.
It rejects unexpected axioms and also prints the dependencies of the nine
public certificates. This check supports the semantic audit; it cannot
itself decide whether a definition expresses the intended problem.

To inspect all nine public certificates, save the following as
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
