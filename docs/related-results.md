# Related results and binary-block bounds

This page retains the mathematical exposition previously on the repository's
front page. The [current manuscript](current-paper.md) concerns the sharp
size-dependent upper bound and the almost-all lower bound. The binary-block
results and the earlier infinitely-often bounds below remain part of the library.
Their proof files now live under `Analysis/BlockCount`, `Analysis/LowerBound`,
and `Analysis/Supporting`; declaration names are unchanged.

See the [block-count proof](block-count.md) for the explicit recurrence and the
[proof guide](proof-guide.md) for the supporting source files. The original
statement and certificate collections are
[`Analysis/Supporting/MainStatement.lean`](../AntichainOfGivenSize/Analysis/Supporting/MainStatement.lean)
and [`Analysis/Supporting/MainTheorems.lean`](../AntichainOfGivenSize/Analysis/Supporting/MainTheorems.lean).

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
The [proof guide](block-count.md#the-explicit-integers) gives that
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

There is a constant $C>0$ such that $\alpha(n)\leq Cg(n)$ for every
integer $n\geq5$. For some $c>0$, the proportion of integers $5\leq n\leq X$
satisfying $cg(n)\leq\alpha(n)\leq Cg(n)$ tends to one as $X\to\infty$.
Also, $\max_{1\leq n<X}\alpha(n)=\Theta(g(X))$ for real cutoffs $X$.
These are the unconditional certificates `Paper.mainTheorem` and
`Paper.almostAllGoodProportion`, for the manuscript
*Generating Antichains for Ideals of Prescribed Size: Universal Upper Bounds
and Almost-All Lower Bounds*
by L. Sunil Chandran, Rishikesh Gajjala, Kuldeep S. Meel, and Daniel J. Zhang.
This manuscript is separate from the earlier arXiv paper linked above.

The counting theorem `Paper.faithfulCountingBound` keeps the manuscript's constant
100: for every sufficiently large integer $B$ and
$1\leq K\leq (\log_2 B)^2/(100\log_2\log_2 B)$,

$$
|\mathcal V(B,K)|\leq 2^{B-\sqrt B}.
$$

[`Representation.lean`](../AntichainOfGivenSize/Analysis/Paper/Representation.lean)
verifies that this finite set counts exactly the
ideal sizes generated by nonempty families of at most $K$ sets, each of
size at most $B$, with no additional ambient-universe restriction. The
[manuscript correspondence](current-paper.md) distinguishes exact
statement coverage from differences in the formal proofs.

The repository also proves that, for every $N$, some
$n\geq\max\{N,5\}$ satisfies

$$
\frac{1}{4096}\,g(n)\leq\alpha(n).
$$

This lower bound holds at arbitrarily large inputs. It does not hold at
every input: a power of two needs only one generator. The very large
integers $n_b$ used for block-count attainment are compatible with these
bounds in terms of $n$.

The Lean definition of `alpha` specifies a mathematical minimum. The library
proves existence and bounds and defines the explicit witnesses above. It does
not provide an executable optimizer for arbitrary inputs or a theorem about
its running time. The discussion of unrestricted Boolean formulas is cited
background, not a formalized equivalence for `beta`.
