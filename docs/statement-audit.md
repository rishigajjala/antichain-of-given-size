# Audit of the Lean statements

This is the historical audit of the original public certificates. The
current manuscript's stronger counting and density-one statements, and
their independent statement audit, are documented in
[the manuscript correspondence](current-paper.md). Historical counts below
refer to the audited revision; the final section also describes current checks.
Source links point to the present locations of the preserved declarations under
`Analysis/`. The original README exposition is retained in
[Related results](related-results.md).

Audit date: 23 September 2026. The starting revision was
[`6075c1c`](https://github.com/rishigajjala/antichain-of-given-size/tree/6075c1cbd35b568e37721257b39c82d61428acae).
The accompanying changes correct two comments and add this audit; they do
not change any mathematical definition, theorem type, or proof.

**Result:** no substantive mismatch was found between the nine public
statements and the mathematics then advertised in the README (now in [Related results](related-results.md)). This conclusion
comes from reading the definitions and proof connections, as well as
checking Lean's proof dependencies. A successful build alone would not
establish that the intended problem had been formalized.

## What the main statements actually say

All names below have prefix `AntichainOfGivenSize`. Their propositions
are defined in [MainStatement.lean](../AntichainOfGivenSize/Analysis/Supporting/MainStatement.lean)
and their proofs are in [MainTheorems.lean](../AntichainOfGivenSize/Analysis/Supporting/MainTheorems.lean).
Here `bl(n)` counts maximal runs of ones in the binary expansion of `n`,
and `alpha(n)` is the minimum number of generators of an ideal of size `n`.

| Certificate | Content checked |
| --- | --- |
| `mainAlphaHasAntichainWitness` | For every `n`, an actual inclusion antichain with exactly `alpha(n)` generators produces an ideal of exactly size `n`. |
| `mainUpperBound` | One constant bounds `alpha(n)` by a multiple of `g(n)` for all sufficiently large `n`. |
| `mainLowerBound` | One positive constant gives a lower bound by a multiple of `g(n)` at arbitrarily large inputs. |
| `mainLowerBound_explicit` | The preceding lower bound holds with the fixed real constant `1/4096`. |
| `mainBlockCountLowerBound` | For every `n`, `log₂(bl(n)+1) ≤ alpha(n)`. |
| `mainBlockCountUpperBound` | For every `n`, `alpha(n) ≤ bl(n)+1`. |
| `mainBlockCountBounds` | Both preceding inequalities hold together. |
| `mainBlockCountTightBound` | For each positive `b`, every `n` with `b` blocks has `alpha(n) ≤ b+1`, and some positive `n` attains equality. |
| `mainExplicitBlockWitness` | The specified recursive integer `n_b` is positive, has exactly `b` blocks, and has `alpha(n_b)=b+1`, for every positive `b`. |

The scale in both size bounds is

$$
g(n)=\frac{(\log_2\log_2 n)^2}{\log_2\log_2\log_2 n}.
$$

The lower bound is **not** claimed for every sufficiently large input.
Likewise, the block theorem gives an attained maximum at each block
count; it does **not** say that every such integer needs `b+1` generators.

## Checks against possible changes of meaning

1. **The ideal is the intended union of powersets.**
   `generatedIdeal` collects precisely the subsets of the generators.
   `HasGeneratorCount` quantifies over every finite universe `Fin m` and
   every finite generator family on it. These agree with
   [Definitions 2.2–2.3 of the paper](https://arxiv.org/html/2506.07268v1#S2.SS2).
   Allowing the universe size to vary is essential and is present.

2. **The minimum is attained.**
   Lean assigns a value even to an infimum of an empty set of natural
   numbers. That convention does not create a loophole here:
   [BasicLemmas.lean](../AntichainOfGivenSize/Analysis/Supporting/BasicLemmas.lean) proves that
   every input has a representation (`hasGeneratorCount_nonempty`), that
   `alpha` is attained (`alpha_hasGeneratorCount`), and that it is at most
   every feasible generator count (`alpha_le_of_hasGeneratorCount`).
   The empty ideal gives the explicitly documented extension `alpha(0)=0`.

3. **Redundant generators do not change the minimum.**
   [AntichainReduction.lean](../AntichainOfGivenSize/Analysis/Supporting/AntichainReduction.lean)
   removes generators contained in other generators, proves that the
   ideal is unchanged, and obtains an antichain with exactly `alpha(n)`
   members. The implementation is not minimizing a different quantity.

4. **The binary recursion really counts runs.**
   [BinaryBlocks.lean](../AntichainOfGivenSize/Analysis/LowerBound/BinaryBlocks.lean)
   defines a run count on lists of bits and proves that `binaryBlockCount`
   agrees with it on `Nat.bits`. It therefore matches the paper's
   [Definition 1.2](https://arxiv.org/html/2506.07268v1#S1), rather than
   counting one-bits, run lengths, or the construction's unrelated blocks.

5. **The stronger auxiliary representation gives a valid lower bound.**
   The block proof allows finite sums of ideal sizes multiplied by
   integer powers of two, with cost equal to the total generator count.
   For every positive input `n`, `hasDyadicIdealSum_alpha` gives a
   representation in this larger class of value `n` and cost at most
   `alpha(n)`, in
   [ScaledIdeals.lean](../AntichainOfGivenSize/Analysis/BlockCount/ScaledIdeals.lean).
   Excluding low-cost representations in the larger class therefore
   excludes them in the original problem. The explicit recurrence and
   induction indices agree with the [block-count guide](block-count.md).

6. **The internal assumptions are discharged.**
   Some helper theorems state implications whose hypotheses package a
   construction or estimate. The final proofs supply those hypotheses:
   `ExactStageIncrement` in [Theorem.lean](../AntichainOfGivenSize/Analysis/Supporting/Theorem.lean),
   `EventuallySparseDyadicProfiles` in
   [ClusterSparsityAssembly.lean](../AntichainOfGivenSize/Analysis/LowerBound/ClusterSparsityAssembly.lean),
   and `FiniteGeometricBound` and `DyadicCostReduction` in
   [Tight.lean](../AntichainOfGivenSize/Analysis/BlockCount/Tight.lean).
   None remains as an assumption of a public certificate.

7. **The counting lower bound covers all relevant ideals.**
   [BoundedProfiles.lean](../AntichainOfGivenSize/Analysis/LowerBound/BoundedProfiles.lean)
   converts every minimum-generator representation of an integer below
   the size cutoff into a counted record of generator membership.
   [ProfilePadding.lean](../AntichainOfGivenSize/Analysis/LowerBound/ProfilePadding.lean)
   permits repeated generators when extending a shorter indexed family.
   Thus the counting proof does not silently restrict the set systems.

8. **Endpoint conventions do not make the asymptotic bounds vacuous.**
   Lean's real logarithm and division are defined at every input.
   Nevertheless, `g(n)>0` for `n≥5`. The upper bound eventually concerns
   only these inputs, and the lower theorem supplies unbounded inputs.
   The related-results overview's requirement `n≥max(N,5)` follows by applying the formal
   lower statement with cutoff `max N 5`. Its constant uses real division.

## Auxiliary statements and corrections

The auxiliary results concerning alternating binary words, intersection
thresholds, and the first integer requiring more than a prescribed number
of generators were also checked for their stated scope. Nonempty-index
and positive-parameter assumptions appear where needed. The first-missing
integer is proved to exist before its minimum is used.

The power-bound propositions in
[VennProfiles.lean](../AntichainOfGivenSize/Analysis/LowerBound/VennProfiles.lean)
and [Conductor.lean](../AntichainOfGivenSize/Analysis/LowerBound/Conductor.lean)
include target definitions and equivalences. Defining a proposition does
not prove it. These files distinguish these targets from the unconditional
matching lower bound, and the main proofs do not assume those targets.

Two comments were corrected:

- In `Conductor.lean`, the improved alternating word is shorter by **four**
  binary positions, comprising two isolated one-bits, rather than two
  binary positions.
- In `ClusterParameters.lean`, `q_pow_le_two_pow_h` bounds the powers
  `q^d` for `d≤32`. Its old comment incorrectly described a bound for
  arbitrary polynomials, which could have additional coefficients and terms.

Neither correction changes a theorem or its proof.

## Reproducing the mechanical checks

At the historical revision audited here, all 66 project library modules were
reachable from the umbrella import `AntichainOfGivenSize`. The latest
[verification report](../.blueprint/verification/checks.json) identifies the current
source snapshot and complete module coverage; [the manuscript correspondence](current-paper.md)
describes the expanded checks.
To check the current checkout, run from the repository root:

```bash
lake build --wfail
lake env lean -DwarningAsError=true scripts/CheckAxioms.lean
```

The current [dependency checker](../scripts/CheckAxioms.lean) checks all
project declarations by their source module, including definitions, instances,
private declarations, and generated theorems. It also checks agreement between
the source files, explicit module registry, and imports. It follows dependencies
and permits only
`propext`, `Classical.choice`, and `Quot.sound`, the standard principles
explained in the [proof guide](proof-guide.md#checking-the-axioms).
It also rejects project declarations that introduce a new axiom, and
prints the assumptions used by each public certificate. In particular,
`sorryAx`, which marks an omitted proof, is not permitted.

[CI](../.github/workflows/ci.yml) runs the full build with warnings treated
as errors, followed by this dependency check. The source scan also found
no `sorry`, `admit`, custom axiom declarations, or `native_decide` uses in
the project library. Resource-limit options increase time available to
the elaborator; they do not disable proof checking.

These mechanical checks complement the reading of the statements above.
They do not establish semantic fidelity by themselves, and they do not
independently verify the implementation of Lean or its underlying logic.

## Scope of the conclusion

The conclusions concern ideal generators and `alpha`. Boolean formula
semantics and the paper's unrestricted parameter `beta` are not defined
in this Lean development. Their relationship in the related-results overview is cited
background, not a formally verified equivalence in this repository.
The block theorem does not resolve the paper's conjecture about `beta`.

The source contains no executable optimizer for arbitrary input `n`, and
no theorem about the time needed to compute `alpha(n)`. The explicit
extremal-number recurrence does not supply such an optimizer.

The finite-universe formulation is sufficient for finite families of
finite sets: one can restrict any larger ambient universe to the union of
the generators. The development proves relabeling for finite ambient
types; this preliminary restriction from an arbitrary ambient type is not
packaged as a separate Lean theorem.

The public arXiv paper was used to check the definitions and its elementary
block bounds. The separate four-author manuscript cited for Section 6
was not available for a version-specific comparison in this audit.
The upper bound was checked against the full displayed formula and its
unconditional Lean proof; the audit does not certify the correspondence
of every internal lemma number with that separate manuscript.
