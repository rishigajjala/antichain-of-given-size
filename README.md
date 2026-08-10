# Antichain of a Given Size

[![CI](https://github.com/rishigajjala/antichain-of-given-size/actions/workflows/ci.yml/badge.svg)](https://github.com/rishigajjala/antichain-of-given-size/actions/workflows/ci.yml)

This repository contains an unconditional Lean 4 formalization of Theorem
6.10 from *Exponentially Smaller Generating Antichains for an Ideal of
Prescribed Size* by L. Sunil Chandran, Rishikesh Gajjala, Kuldeep S. Meel,
and Daniel J. Zhang.

For the paper's function `α`, the theorem is

$$
  \alpha(n) = O\left(
    \frac{(\log_2 \log_2 n)^2}{\log_2 \log_2 \log_2 n}
  \right).
$$

The public entry point is `AntichainOfGivenSize.theorem6_10` in
[`AntichainOfGivenSize/Theorem.lean`](AntichainOfGivenSize/Theorem.lean):

```lean
theorem theorem6_10 :
    (fun n : ℕ ↦ (alpha n : ℝ)) =O[atTop]
      (fun n : ℕ ↦
        (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 2 /
          Real.logb 2 (Real.logb 2 (Real.logb 2 (n : ℝ))))
```

It has no hypotheses.

## Mathematical model

For a finite family of finite sets `S`, the generated ideal is defined as

$$
  \mathrm{ID}(S) = \bigcup_{A \in S} 2^A.
$$

`alpha n` is the minimum cardinality of a generating family whose generated
ideal has exactly `n` members. The ambient universe is represented by a
finite type `Fin m`, which canonically represents a finite ambient universe.

The asymptotic statement uses `IsBigO` along `Filter.atTop`. Thus it has the
standard meaning “for all sufficiently large natural numbers,” and the
totalized values of iterated logarithms at the finitely many small inputs do
not affect the theorem. All logarithms are base 2, as in the paper.

## Proof organization

| Modules | Role |
| --- | --- |
| `AntichainOfGivenSize.Definitions`, `AntichainOfGivenSize.BasicLemmas` | Definitions of `ID`, `alpha`, the comparison scale, attainment of the minimum, and the Splitting and Lifting Lemmas |
| `AntichainOfGivenSize.AsymptoticBridge`, `AntichainOfGivenSize.RangeArithmetic` | Iteration of the range reduction, an explicit cofinal ladder, the ladder-sum estimate, and the final analytic Big-O argument |
| `AntichainOfGivenSize.RangeReduction`, `AntichainOfGivenSize.MatchingParameters` | Lemma 6.8 and the explicit numerical parameters needed by the matching construction |
| `AntichainOfGivenSize.Section6.Core`, `.Remainder`, `.Blocks`, `.Survivors`, `.ModularIncrement` | The Section 6 block construction and its exact modular increment calculation |
| `AntichainOfGivenSize.Section6.Address`, `.StageArithmetic`, `.IndexedBounds`, `.NatParameters`, `.StageBridge`, `.Construction` | Stage addresses, recursion, cardinality bounds, and the concrete matching theorem |
| `AntichainOfGivenSize.Theorem`, `AntichainOfGivenSize` | Assembly of the hypothesis-free theorem and the package's umbrella module |

The formalization targets Theorem 6.10 rather than reproducing every stronger
intermediate statement verbatim. In particular, it makes the paper's
real-parameter rounding explicit by using `B = H * ceil(q)`, proves only the
successor residue required by Lemma 6.8, bounds the final construction
directly, and uses the explicit ladder
`qᵢ = (T + i) * log₂(T + i)`. Every replacement estimate is proved in Lean.

## Build and verification

The project pins Lean and mathlib to version `v4.32.0`. With
[Lean](https://lean-lang.org/install/) installed, run:

```bash
git clone https://github.com/rishigajjala/antichain-of-given-size.git
cd antichain-of-given-size
lake exe cache get
lake build --wfail
```

The source contains no `sorry`, `admit`, or custom axioms. Running
`#print axioms AntichainOfGivenSize.theorem6_10` reports only Lean/mathlib's
standard foundational principles:

```text
propext
Classical.choice
Quot.sound
```

GitHub Actions runs the warning-free build on every push and pull request.

## License

This formalization is released under the [MIT License](LICENSE).
