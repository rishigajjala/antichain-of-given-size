# Generating antichains of a prescribed size

[![CI](https://github.com/rishigajjala/antichain-of-given-size/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/rishigajjala/antichain-of-given-size/actions/workflows/ci.yml)

Lean 4 formalization of *Generating Antichains for Ideals of Prescribed Size:
Universal Upper Bounds and Almost-All Lower Bounds*, by L. Sunil Chandran,
Rishikesh Gajjala, Kuldeep S. Meel, and Daniel J. Zhang.
The [saved manuscript](paper/Generating_Antichains_Simplified.tex) is linked to
Lean statements in the [complete numbered-result table](docs/current-paper.md#numbered-results).

For a finite family of sets $S$, let
$\mathrm{ID}(S)=\bigcup_{A\in S}2^A$ and
$\alpha(n)=\min\{|S|:|\mathrm{ID}(S)|=n\}$, allowing the finite universe to vary.
Write

$$
g(n)=\frac{(\log_2\log_2 n)^2}{\log_2\log_2\log_2 n}.
$$

There are constants $c,C>0$ such that $\alpha(n)\le Cg(n)$ for every integer
$n\ge5$, and the integers satisfying $cg(n)\le\alpha(n)\le Cg(n)$ have natural
density one. The development also proves
$\max_{1\le n<X}\alpha(n)=\Theta(g(X))$ for real cutoffs $X$.
All 18 numbered proof targets have Lean endpoints. The
[correspondence document](docs/current-paper.md) records their exact scope and
differences between the formal proofs and the paper.

## Read the statements, then the proofs

Start with `Model/` while reading the paper. These files determine what is proved.

| File | What to review |
| --- | --- |
| [Model/ProblemSetting.lean](AntichainOfGivenSize/Model/ProblemSetting.lean) | Generated ideals, `alpha`, bounded families, density sets, probability distribution, and real cutoffs |
| [Model/Prelude.lean](AntichainOfGivenSize/Model/Prelude.lean) | The equivalence between finite profiles and arbitrary bounded generating families |
| [Model/Prior.lean](AntichainOfGivenSize/Model/Prior.lean) | The field-free `Prior` structure; it introduces no additional unproved hypothesis |
| [Model/Theorem.lean](AntichainOfGivenSize/Model/Theorem.lean) | The main asymptotic theorem, counting theorem, and splitting lemma |

Follow the main proof into
[Analysis/TheoremProof.lean](AntichainOfGivenSize/Analysis/TheoremProof.lean).
The sharp upper-bound entry point is
[Analysis/AlphaEventualUpperProof.lean](AntichainOfGivenSize/Analysis/AlphaEventualUpperProof.lean),
which reaches [Paper/Extremal.lean](AntichainOfGivenSize/Analysis/Paper/Extremal.lean)
and the earlier complete construction. The counting entry point is
[Analysis/AttainableCountProof.lean](AntichainOfGivenSize/Analysis/AttainableCountProof.lean),
backed by [FaithfulCounting/CompleteCounting.lean](AntichainOfGivenSize/Analysis/Paper/FaithfulCounting/CompleteCounting.lean).
The [proof guide](docs/proof-guide.md) gives the remaining routes.

```text
AntichainOfGivenSize/
  Model/       ProblemSetting, Prelude, Prior, Theorem
  Analysis/    Proofs and theorem assembly
    Paper/     Current manuscript results and constructions
    Supporting/, Section6/, LowerBound/, BlockCount/
  Meta/        ModelClosure, CostSeal, Audit checks
```

The proof modules and their dependencies are retained under `Analysis/`; their
mathematical declaration names are unchanged. The separate sharp binary-block
theorem and earlier results are explained in [Related results](docs/related-results.md).

## Build and check

The project pins Lean and Mathlib to `v4.32.0`. From the repository root:

```sh
lake exe cache get
lake build --wfail
lake env lean -DwarningAsError=true scripts/CheckAxioms.lean
lake env lean -DwarningAsError=true scripts/CheckPaperStatements.lean
shasum -a 256 --check paper/SHA256SUMS
```

The checks cover every library declaration, the explicit module registry, and
independently written statement contracts. They reject omitted proofs and
unexpected axioms. [Verification records](.blueprint/verification/checks.json)
identify the checked files and command results. Comparing the Model definitions
and statements with the paper remains a separate review task.

## Tex2Lean evidence

The [preserved Tex2Lean records](docs/verification/native/README.md) cover three
selected workflows—main theorem, counting theorem, and splitting lemma—using the
existing Lean development. They are **records from before the file reorganization**,
preserved for [revision `684d670`](https://github.com/rishigajjala/antichain-of-given-size/tree/684d670720ebd84433189c6dc0ad4ffb3a1b17cd).
They do not provide a new native certification of the moved source paths. The current layout is
checked by the Lean build and audits above. The other 15 numbered results have
no separate native plans.

Those records retain two native `/check` heuristic failures, the main handoff's
two verification limitations, and counting's two metadata exclusions. The
[compatibility build](scripts/tex2lean-compat/README.md), assistant review, and
proof reuse are documented; no human review signature is asserted.

[MIT license](LICENSE).
