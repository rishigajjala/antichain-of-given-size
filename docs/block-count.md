# The sharp bound from binary blocks

[Back to the README](../README.md) · [Source and verification guide](proof-guide.md)

This note explains the theorem

$$
\max_{\operatorname{bl}(n)=b}\alpha(n)=b+1\qquad(b\geq1).
$$

It gives the complete numerical definition of an integer attaining the
maximum and an outline of its proof. The finite reduction lemma used in
the sharpness argument is proved in the linked Lean files.

## Definitions and statement

A **generator family** $S$ is a finite collection of finite sets.
Its generated ideal is $\operatorname{ID}(S)=\bigcup_{A\in S}2^A$,
where $2^A$ denotes all subsets of $A$.
The number $\alpha(n)$ is the minimum number of generators in a family
whose ideal has $n$ members. The finite universe containing the generators
is allowed to vary.

The **block count** $\operatorname{bl}(n)$ is the number of maximal runs
of ones in the binary expansion of $n$. For example,
$110001_2=49$ has two blocks. Zero has block count zero.
These runs are unrelated to the sets called blocks in the repository's
Section 6 construction.

For every $n\geq0$,

$$
\log_2(\operatorname{bl}(n)+1)\leq\alpha(n)
\leq\operatorname{bl}(n)+1.
$$

For every $b\geq1$, the upper bound is attained at an explicitly defined
$n_b$ with $\operatorname{bl}(n_b)=b$.
The case $b=0$ has only $n=0$, with $\alpha(0)=0$.

The formal definitions and all main theorem claims are in
[MainStatement.lean](../AntichainOfGivenSize/MainStatement.lean).
The certificates are in
[MainTheorems.lean](../AntichainOfGivenSize/MainTheorems.lean).

## The logarithmic lower bound

Suppose an ideal of size $n$ has $q$ generators. Inclusion-exclusion counts
their union of powersets by adding the sizes of single powersets,
subtracting pairwise overlaps, adding triple overlaps, and continuing.
Every nonempty subfamily contributes one signed power of two, because

$$
\bigcap_{A\in T}2^A=2^{\,\bigcap_{A\in T}A}.
$$

Here $T$ is a nonempty subfamily of the generators, and a signed power
means a term $+2^e$ or $-2^e$ with a nonnegative integer exponent $e$.
There are $2^q-1$ nonempty subfamilies.

A nonnegative signed sum of $r$ powers of two has at most $r$ binary
blocks. This follows by tracking binary carries and borrows; the precise
arithmetic lemma is in
[SignedPowers.lean](../AntichainOfGivenSize/LowerBound/SignedPowers.lean).
Consequently,

$$
\operatorname{bl}(n)+1\leq 2^q.
$$

Taking the base-two logarithm and minimizing $q$ gives the lower bound.
Since $\alpha(n)$ is an integer, the proof also yields

$$
\left\lceil\log_2(\operatorname{bl}(n)+1)\right\rceil\leq\alpha(n),
$$

where $\lceil x\rceil$ is the least integer at least $x$.
The Lean theorem `clog_binaryBlockCount_le_alpha` proves this integer
version in [IdealBlockCount.lean](../AntichainOfGivenSize/LowerBound/IdealBlockCount.lean).

## The upper bound: one extra generator per new run

Two operations suffice.

**Lifting.** Add the same $s$ new elements to every generator. Each old
ideal member can now be combined with any subset of the new elements, so
the size is multiplied by $2^s$ while the generator count stays the same:

$$
\alpha(2^s m)\leq\alpha(m).
$$

**Splitting.** For $m\geq1$ and $k\geq0$, take ideals of sizes $m$ and $k+1$
on disjoint universes. Their only common member is the empty set.
Their union therefore has size $m+(k+1)-1=m+k$, and

$$
\alpha(m+k)\leq\alpha(m)+\alpha(k+1).
$$

A power of two needs one generator. For $r\geq1$, splitting the number
$2^r-1$ as $2^{r-1}+(2^{r-1}-1)$ gives a representation with at most two
generators. This handles the first run of ones; lifting handles zero bits.

For any positive prefix $p$, appending $r\geq1$ ones gives
$2^r p+(2^r-1)$. Splitting and lifting yield

$$
\alpha(2^r p+2^r-1)
\leq\alpha(2^r p)+\alpha(2^r)
\leq\alpha(p)+1.
$$

When $p$ ends in zero, this creates a new run. Each later run therefore
adds at most one generator. Starting from at most two generators for the
first run gives $b+1$ for $b$ runs.

See [BasicLemmas.lean](../AntichainOfGivenSize/BasicLemmas.lean) for the
two operations and [Upper.lean](../AntichainOfGivenSize/BlockCount/Upper.lean)
for the complete induction.

## The explicit integers

The following recurrence is exactly the numerical construction in
[MainStatement.lean](../AntichainOfGivenSize/MainStatement.lean).

For nonnegative integers $p,k$, define

$$
E(k)=k(k+k^2),\qquad
H_0(p,k)=1,
$$

$$
H_{j+1}(p,k)
=H_j(p,k)+2k^2\bigl(p+1+H_j(p,k)\bigr)+E(k)+2,
$$

and stop after $E(k)+1$ steps:

$$
T(p,k)=H_{E(k)+1}(p,k).
$$

These symbols correspond to the Lean names:

| Mathematical symbol | Lean definition in `BlockCount` |
| --- | --- |
| $E(k)$ | `exponentBudget k` |
| $H_j(p,k)$ | `finiteScale p k j` |
| $T(p,k)$ | `finiteThreshold p k` |

Now set

$$
n_1=3,\qquad
t_b=\max\{2,T(n_b,b+1)\},\qquad
n_{b+1}=2^{t_b}n_b+1\quad(b\geq1).
$$

The Lean names are `explicitBlockWitness b` and `explicitWitnessShift b`.
Lean also defines $n_0=0$ to give the function a value at every natural
number; the attainment theorem assumes $b\geq1$.

Multiplication by $2^{t_b}$ appends $t_b$ zero bits. Adding one changes the
last of those bits to one, leaving $t_b-1$ separating zeroes:

```text
binary(n_b)   00...00   1
             t_b - 1
               zeroes
```

Since $t_b\geq2$, this creates exactly one new block. Thus
$\operatorname{bl}(n_b)=b$ by induction from $n_1=11_2$.

For example, $E(2)=12$ and $H_{j+1}(3,2)=9H_j(3,2)+46$, so

$$
t_1=T(3,2)=17\,157\,594\,341\,215,\qquad
n_2=3\cdot2^{17\,157\,594\,341\,215}+1.
$$

This integer has two binary blocks and needs exactly three generators.
The size illustrates how generous the sufficient threshold is; no claim
of minimality for $n_b$ is made. The shift can be checked without expanding
$n_2$:

```lean
import AntichainOfGivenSize.MainStatement

-- Expected output: 17157594341215
#eval AntichainOfGivenSize.BlockCount.finiteThreshold 3 2
```

## Why the recurrence forces one more generator

The proof uses a larger class of representations to make induction work.
A **scaled ideal sum** is a finite sum

$$
\sum_i 2^{e_i}\,|\operatorname{ID}(S_i)|,
$$

where each $e_i$ is an integer (possibly negative) and each $S_i$ is a
nonempty finite generator family. Its **cost** is $\sum_i|S_i|$.
The empty sum has value and cost zero. The sum can be rational.
An ordinary positive ideal cardinality is a
one-component sum with exponent zero and the same generator count.

The key finite reduction lemma states: for $p\geq0$, $k\geq1$, and
$t\geq T(p,k)$, a scaled ideal sum representing $2^t p+1$ at cost at most
$k$ yields a scaled ideal sum representing $p$ at cost at most $k-1$.
Its Lean name is
`BlockCount.finiteThreshold_costReduction_proved` in
[Tight.lean](../AntichainOfGivenSize/BlockCount/Tight.lean).
The proof constructs finitely many thresholds and uses an interval with
no relevant exponents to separate the leading integer from the small
remainder. The [repository guide](proof-guide.md) maps the proof files.

A cost-one scaled ideal sum is a single power $2^e$ with integer $e$.
Neither cost zero nor cost one can therefore represent $3$. We prove
inductively that $n_b$ has no scaled
representation of cost at most $b$.

For the induction step, suppose $n_{b+1}=2^{t_b}n_b+1$ had cost at most
$b+1$. The reduction lemma, with $p=n_b$ and $k=b+1$, would give a
representation of $n_b$ with cost at most $b$, contradicting the
induction assumption. Every ordinary generator family is included among
these scaled representations, so $\alpha(n_b)\geq b+1$.
The upper bound and $\operatorname{bl}(n_b)=b$ give the reverse inequality.

This proves both $\alpha(n_b)=b+1$ and the claimed exact maximum.
The induction is formalized in
[ExplicitWitness.lean](../AntichainOfGivenSize/BlockCount/ExplicitWitness.lean).
