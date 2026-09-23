# Antichain of a Given Size

[![CI](https://github.com/rishigajjala/antichain-of-given-size/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/rishigajjala/antichain-of-given-size/actions/workflows/ci.yml)

Lean 4 proofs about the minimum number of sets needed to generate an ideal
with a prescribed number of members. The sharp result in terms of binary
blocks is

$$
\boxed{\max_{\mathrm{bl}(n)=b}\alpha(n)=b+1
\qquad\text{for every }b\geq1.}
$$

Here $\alpha(n)$ is the minimum generator count and $\mathrm{bl}(n)$
counts runs of ones in the binary expansion of $n$. Both are defined below.
The repository also proves an upper bound in terms of $n$ and a matching
lower bound at arbitrarily large inputs.

| Start here | What it contains |
| --- | --- |
| [MainStatement.lean](AntichainOfGivenSize/MainStatement.lean) | All main definitions and theorem claims, without their proofs |
| [MainTheorems.lean](AntichainOfGivenSize/MainTheorems.lean) | Short proofs connecting those claims to the implementation |
| [Block-count proof guide](docs/block-count.md) | The inequalities, proof outline, and complete explicit witness recurrence |
| [Repository guide](docs/proof-guide.md) | Source navigation, supporting results, and axiom checks |
| [Statement audit](docs/statement-audit.md) | Checks that the Lean statements express the intended problem, with scope and limitations |

## The problem

For a finite family $S$ of finite sets, define its **generated ideal** by

$$
\mathrm{ID}(S)=\bigcup_{A\in S}2^A.
$$

Here $2^A$ is the collection of all subsets of $A$, and $|X|$ denotes the
number of members of a finite set $X$. The members of $S$ are its
**generators**. We define

$$
\alpha(n)=\min\{|S|:|\mathrm{ID}(S)|=n\}.
$$

The underlying finite universe may vary with $S$. Removing a generator
contained in another generator leaves the ideal unchanged, so a minimum
family is an **inclusion antichain**: no distinct members contain one
another. The theorem `mainAlphaHasAntichainWitness` proves this formally.

The empty family generates the empty ideal, giving $\alpha(0)=0$.
The family consisting of the empty set generates $\{\varnothing\}$,
giving $\alpha(1)=1$. For $n\geq2$, take $n-1$ distinct singleton
generators: their ideal consists of those singletons and the empty set.
Thus the minimum is defined for every natural number $n$.

## The sharp bound from binary blocks

A **binary block** is a maximal consecutive run of `1` bits.
For example, $49=110001_2$ has the two blocks `11` and `1`, so
$\mathrm{bl}(49)=2$. Set $\mathrm{bl}(0)=0$.
All logarithms below have base two.

For every natural number $n$,

$$
\log_2\!\bigl(\mathrm{bl}(n)+1\bigr)
\leq\alpha(n)\leq\mathrm{bl}(n)+1.
$$

These pointwise bounds appear in *CNFs and DNFs with Exactly k Solutions*:
the lower bound is [Corollary 3.6](https://arxiv.org/html/2506.07268v1#S3)
and the upper bound is [Lemma 4.4](https://arxiv.org/html/2506.07268v1#S4.SS3).

The sharpness theorem in this repository supplies, for every $b\geq1$,
an explicit integer $n_b$ such that

$$
\mathrm{bl}(n_b)=b,\qquad \alpha(n_b)=b+1.
$$

Thus $b+1$ is the exact largest value at a fixed positive block count.
Individual integers can have smaller generator counts: both $2=10_2$
and $3=11_2$ have one block, but $\alpha(2)=1$ and $\alpha(3)=2$.
One singleton generator produces two subsets; two distinct singleton
generators produce three. A single generator always produces a power of
two subsets, so it cannot produce three.

The witness starts at $n_1=3$ and uses

$$
n_{b+1}=2^{t_b}n_b+1,
$$

where $t_b\geq2$ is a specified function of $n_b$ and $b$.
The [proof guide](docs/block-count.md#the-explicit-integers) gives that
function in full and explains why every step forces one more generator.
The resulting witnesses can be very large; they are not claimed to be
the smallest integers attaining the bound.

Since $b+1$ eventually exceeds $C(\log_2(b+1))^2$ for every fixed $C>0$,
there is no uniform upper bound of that form for $\alpha$.

The paper also studies $\beta(n)$, the minimum number of terms or clauses
in a Boolean formula with **exactly $n$ satisfying assignments**, using
DNF (an OR of AND terms) or CNF (an AND of OR clauses). These formulas may
use negated variables. It proves $\beta(n)\leq\alpha(n)$ and
[conjectures a bound polynomial in $\log\mathrm{bl}(n)$ for $\beta$](https://arxiv.org/html/2506.07268v1#S1).
The result above concerns $\alpha$, which corresponds to ideals and
monotone DNF formulas (using only positive variables). It does not settle
the conjecture for $\beta$.

## Bounds in terms of n

For natural numbers $n\geq5$, write

$$
g(n)=\frac{(\log_2\log_2 n)^2}{\log_2\log_2\log_2 n}.
$$

There are constants $C>0$ and $N_0\geq5$ such that
$\alpha(n)\leq Cg(n)$ for every $n\geq N_0$. This is the meaning of
$\alpha(n)=O(g(n))$ here. The upper bound is formalized as `theorem6_10`,
corresponding to the Section 6 construction in
*Exponentially Smaller Generating Antichains for an Ideal of Prescribed Size*
by L. Sunil Chandran, Rishikesh Gajjala, Kuldeep S. Meel, and Daniel J. Zhang.
That construction is separate from the earlier arXiv paper linked above.

The repository also proves that, for every $N$, some
$n\geq\max\{N,5\}$ satisfies

$$
\frac{1}{4096}\,g(n)\leq\alpha(n).
$$

This lower bound holds at arbitrarily large inputs. It does not hold at
every input: a power of two needs only one generator. The very large
integers $n_b$ used for block-count attainment are compatible with these
bounds in terms of $n$.

## Use and verify

The project pins Lean and mathlib to `v4.32.0`.
With [Lean installed](https://lean-lang.org/install/), run:

```bash
git clone https://github.com/rishigajjala/antichain-of-given-size.git
cd antichain-of-given-size
lake exe cache get
lake build --wfail
```

The build treats warnings as errors. GitHub Actions runs it on pushes and
pull requests. To inspect the main statements from a Lean file:

```lean
import AntichainOfGivenSize

#check AntichainOfGivenSize.mainBlockCountBounds
#check AntichainOfGivenSize.mainBlockCountTightBound
#check AntichainOfGivenSize.mainExplicitBlockWitness
#check AntichainOfGivenSize.mainUpperBound
#check AntichainOfGivenSize.mainLowerBound_explicit
```

The source contains no `sorry`, `admit`, or custom axioms.
The [repository guide](docs/proof-guide.md#checking-the-axioms) explains how
to inspect the foundational axioms used by the public certificates.

The Lean definition of `alpha` specifies a mathematical minimum. This
repository proves existence and bounds and defines the explicit witnesses
$n_b$. It does not provide an executable optimizer or a theorem about
the time needed to compute $\alpha(n)$ from an arbitrary input $n$.

## License

[MIT](LICENSE).
