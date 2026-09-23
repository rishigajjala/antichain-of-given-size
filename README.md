# Antichain of a Given Size

[![CI](https://github.com/rishigajjala/antichain-of-given-size/actions/workflows/ci.yml/badge.svg)](https://github.com/rishigajjala/antichain-of-given-size/actions/workflows/ci.yml)

This repository formalizes bounds on the smallest number of sets needed to
generate an ideal of a prescribed size. Its sharp block-count result says that
**for every $b\geq1$, among integers with exactly $b$ binary blocks,
the largest possible minimum generator count is $b+1$**. The repository also proves matching worst-case
asymptotic bounds in terms of the size of the integer.

## The problem and the meaning of a block

For a finite family of sets S, its **generated ideal** is the collection of all
subsets of members of S:

$$
\operatorname{ID}(S)=\bigcup_{A\in S}2^A.
$$

Here $2^A$ is the set of all subsets of $A$. Let $\alpha(n)$ be the smallest
possible number of generators in a family $S$ for which
$|\operatorname{ID}(S)|=n$. Generators contained in another generator can be
removed without changing the ideal. Thus a smallest family can be chosen as
an **inclusion antichain**: no two distinct members contain one another.

Write $\operatorname{bl}(n)$ for the number of maximal runs of `1` bits in the
binary expansion of $n$. For example, $49=110001_2$ has two runs, `11` and
`1`, so $\operatorname{bl}(49)=2$. We set $\operatorname{bl}(0)=0$. These binary
runs are different from the sets called blocks in the Section 6
upper-bound construction in this repository. All logarithms below have base two.

## Sharp bounds from binary blocks

The pointwise inequalities, valid for every natural number $n$, are

$$
\boxed{\quad
\log_2\!\bigl(\operatorname{bl}(n)+1\bigr)
\;\leq\; \alpha(n)
\;\leq\; \operatorname{bl}(n)+1.
\quad}
$$

The lower inequality comes from
[*CNFs and DNFs with Exactly k Solutions*](https://arxiv.org/html/2506.07268v1).
The upper inequality is its simple block-count construction. The
sharpness result proved in this repository is

$$
\boxed{\quad
\text{for every }b\geq 1,\qquad
\max_{\operatorname{bl}(n)=b}\alpha(n)=b+1.
\quad}
$$

In particular, there is an explicit integer $n_b$ with
$\operatorname{bl}(n_b)=b$ and $\alpha(n_b)=b+1$. Equality is a **worst-case**
statement at fixed $b$, not a claim about every integer with $b$ blocks:
$2=10_2$ has one block and $\alpha(2)=1$, while $3=11_2$ has one block and
$\alpha(3)=2$. For $2$, one singleton generator suffices; for $3$, two
distinct singleton generators suffice, and one generator cannot work because
it always produces a power of two subsets. The hypothesis $b\geq1$
matters: $0$ is the only integer with no `1`-blocks and $\alpha(0)=0$.

Consequently, for every fixed constant $C$, some $n$ has
$\alpha(n)>C(\log_2(\operatorname{bl}(n)+1))^2$. Thus a uniform
quadratic-in-logarithm upper bound in the block count is impossible for
$\alpha$. More generally, a function growing strictly slower than $b$
cannot be a uniform upper bound in terms of $b=\operatorname{bl}(n)$.

The cited paper also defines $\beta(n)$ for the minimum number of terms or
clauses in an **unrestricted** Boolean formula in DNF (an OR of AND terms)
or CNF (an AND of OR clauses). Unrestricted formulas may use negated
variables; monotone formulas use only positive variables. The paper proves
$\beta(n)\leq\alpha(n)$ and conjectures an upper bound polynomial in
$\log\operatorname{bl}(n)$ for $\beta$. The sharpness theorem here concerns
$\alpha$, equivalently the ideal or monotone-DNF problem; it does not settle
that conjecture about $\beta$.

### Why the bounds hold

If an ideal has $q$ generators, inclusion-exclusion (counting a union by
adding the sizes of its parts and correcting for overlaps) expresses its
size as a signed sum of at most $2^q-1$ powers of two. A positive
signed sum of $r$ powers of two has at most $r$ runs of `1` bits. Hence
$\operatorname{bl}(n)+1\leq 2^q$, which gives the logarithmic lower bound.

For the upper bound, a power of two needs one generator and a nonempty run
of `1` bits needs at most two. **Lifting** appends zero bits by multiplying the
ideal size by a power of two without increasing its generator count.
**Splitting** combines two ideals whose only common member is the empty
set. Applying these operations to successive binary runs adds at most one
generator for each new run. The Lean proof is in
[`BlockCount/Upper.lean`](AntichainOfGivenSize/BlockCount/Upper.lean).

### Which integer attains the upper bound?

The formalization defines an explicit sequence, starting with $n_1=3$:

$$
n_{b+1}=2^{t_b}n_b+1,\qquad
t_b=\max\{2,\ \operatorname{finiteThreshold}(n_b,b+1)\}
\quad(b\geq1).
$$

The natural-number function `finiteThreshold` is defined by a finite
recursion in [`MainStatement.lean`](AntichainOfGivenSize/MainStatement.lean).
Because $t_b\geq2$, the new final `1` follows a zero gap, so each step adds
exactly one binary run. The chosen gap also forces the minimum generator
count to rise by one.

The hard part is a cost-reduction lemma for **scaled ideal sums**. Such a sum
adds ideal cardinalities multiplied by integer powers of two; its cost is the
total number of generators in its components. An ordinary representation
of a positive-sized ideal is a special case. When $t$ is at least `finiteThreshold(p,k)`,
the lemma turns any scaled representation of $2^t p+1$ with cost at most $k$
into one of $p$ with cost at most $k-1$. The base value $3$ has no scaled
representation of cost one. Induction therefore rules out fewer than $b+1$
generators for $n_b$, while the pointwise upper bound supplies $b+1$.

The shift is deliberately generous and the resulting integers can be very
large. The theorem identifies the exact worst case for each block count; it
does not claim these are the smallest extremal integers.

The public Lean certificates can be inspected with:

```lean
import AntichainOfGivenSize

#check AntichainOfGivenSize.mainBlockCountBounds
#check AntichainOfGivenSize.mainBlockCountTightBound
#check AntichainOfGivenSize.mainExplicitBlockWitness
```

All three statement definitions, the binary block count, and the witness
recursion are in [`MainStatement.lean`](AntichainOfGivenSize/MainStatement.lean).
The short certificates are in
[`MainTheorems.lean`](AntichainOfGivenSize/MainTheorems.lean). The proof of
attainment is in [`BlockCount/Tight.lean`](AntichainOfGivenSize/BlockCount/Tight.lean)
and the recursive witness proof is in
[`BlockCount/ExplicitWitness.lean`](AntichainOfGivenSize/BlockCount/ExplicitWitness.lean).

## Bounds in terms of the integer's size

The repository also formalizes Theorem 6.10 of
*Exponentially Smaller Generating Antichains for an Ideal of Prescribed Size*
by L. Sunil Chandran, Rishikesh Gajjala, Kuldeep S. Meel, and Daniel J.
Zhang. Here $f(n)=O(g(n))$ means that $f(n)\leq Cg(n)$ for some
constant $C$ and all sufficiently large $n$. The theorem states

$$
\alpha(n)=O\!\left(
\frac{(\log_2\log_2 n)^2}{\log_2\log_2\log_2 n}
\right).
$$

A matching lower bound holds at arbitrarily large inputs: there is a fixed
$c>0$ such that, for every $N$, some $n\geq N$ satisfies

$$
c\,\frac{(\log_2\log_2 n)^2}{\log_2\log_2\log_2 n}
\leq\alpha(n).
$$

The formalization gives $c=1/4096$. This is an infinitely-often lower bound,
not a lower bound for every $n$. The canonical certificates are
`mainUpperBound`, `mainLowerBound`, and `mainLowerBound_explicit`. The
unfolded earlier entry points are in
[`Theorem.lean`](AntichainOfGivenSize/Theorem.lean) and
[`LowerBound/Matching.lean`](AntichainOfGivenSize/LowerBound/Matching.lean).

These size-based bounds are compatible with the sharp block-count result:
the extremal $n_b$ above can grow very quickly as $b$ grows.

Alternating binary words `1`, `101`, `10101`, and so on combine the
block-count lower bound with the size of the word to yield
$\alpha(n)\geq\frac12\log_2\log_2 n$ at arbitrarily large inputs. A separate
carry-sensitive argument uses the shorter family

$$
a_q=1+4+\cdots+4^{\,2^q-2}\qquad(q\geq2)
$$

and proves $q+1\leq\alpha(a_q)$, as well as an infinitely-often
$\log_2\log_2 n\leq\alpha(n)$ consequence. This improves a witness for the
log-log lower bound; it is distinct from the $n_b$ attaining $b+1$.

## Where to read and check the formalization

[`MainStatement.lean`](AntichainOfGivenSize/MainStatement.lean) collects
the problem definitions, explicit block witness, common asymptotic scale,
and all main theorem claims without importing their proofs.
[`MainTheorems.lean`](AntichainOfGivenSize/MainTheorems.lean) connects those
claims to the implementation. The main theorem claims include attainment
of $\alpha(n)$ by an antichain, both size-based bounds, the pointwise
block-count bounds, and exact block-count attainment.

To check the axioms of the public theorems, put this in a Lean file in the
repository and run `lake env lean FileName.lean`:

```lean
import AntichainOfGivenSize

#print axioms AntichainOfGivenSize.mainAlphaHasAntichainWitness
#print axioms AntichainOfGivenSize.mainBlockCountBounds
#print axioms AntichainOfGivenSize.mainBlockCountTightBound
#print axioms AntichainOfGivenSize.mainExplicitBlockWitness
#print axioms AntichainOfGivenSize.mainUpperBound
#print axioms AntichainOfGivenSize.mainLowerBound
#print axioms AntichainOfGivenSize.mainLowerBound_explicit
```

The reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The source uses no `sorry`, `admit`, or custom axioms.

| Module group | Contents |
| --- | --- |
| `MainStatement`, `MainTheorems` | Central definitions and theorem claims, then short unconditional certificates |
| `Definitions`, `BasicLemmas`, `AntichainReduction` | Generator representations, splitting and lifting, and antichain attainment |
| `BlockCount/Upper`, `BlockCount/Binary` | Pointwise upper bound and binary-run arithmetic |
| `BlockCount/ScaledIdeals` through `BlockCount/Tight` | Finite scale and cost-reduction argument for worst-case attainment |
| `BlockCount/ExplicitWitness` | Concrete recursive extremal integer for each positive block count |
| `LowerBound/BinaryBlocks`, `SignedPowers`, `IdealBlockCount` | Signed-power arithmetic and pointwise logarithmic lower bound |
| `LowerBound/InfinitelyOften`, `CarrySensitive` | Explicit log-log lower-bound families |
| `LowerBound/VennProfiles` through `Matching` | Counting argument for the matching size-based lower bound |
| `Section6/*`, `RangeReduction`, `AsymptoticBridge`, `RangeArithmetic` | Section 6 construction and size-based asymptotic upper bound |
| `Theorem`, `LowerBound/Matching` | Fully unfolded compatibility theorem names |

The Lean definition of `alpha` is noncomputable: the repository proves
existence, bounds, and an explicit extremal number $n_b$, but does not
implement an algorithm or establish a time complexity for finding a minimum
generator family from an arbitrary input $n$.

## Build

The project pins Lean and mathlib to `v4.32.0`. With
[Lean](https://lean-lang.org/install/) installed, run:

```bash
git clone https://github.com/rishigajjala/antichain-of-given-size.git
cd antichain-of-given-size
lake exe cache get
lake build --wfail
```

GitHub Actions runs the warning-free build on every push and pull request.

## License

This formalization is released under the [MIT License](LICENSE).
