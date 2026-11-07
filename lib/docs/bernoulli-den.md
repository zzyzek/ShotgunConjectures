# Denominators of Bernoulli numbers (von Staudt–Clausen)

Module: `BernoulliDen.lean`.

## 1. The method

The denominator of a Bernoulli number is known exactly: for $k \ge 1$ it is the product of the
primes $p$ with $p - 1 \mid 2k$. Questions about these denominators (their residues, their
values along a subsequence of indices, which primes divide them) reduce to questions about
which $p - 1$ divide $2k$. The module derives the product formula and its standard corollaries
from Mathlib's von Staudt–Clausen theorem.

**Notation.** $B_n$ are the Bernoulli numbers with Mathlib's convention $B_1 = -\tfrac12$
(`bernoulli n`; denominators do not depend on the sign of $B_1$). $\operatorname{den}(x)$ is the
denominator of $x \in \mathbb Q$ in lowest terms. For $k \in \mathbb N$,

$$S(k) = \lbrace p \text{ prime} : p < 2k+2,\ (p-1) \mid 2k \rbrace \qquad (\texttt{vscSet k}).$$

For $k \ge 1$ the bound $p < 2k + 2$ is automatic; for $k = 0$ it makes $S(0) = \emptyset$.

**Theorem** (`BernoulliDen.lean`).

1. $\operatorname{den}(B_{2k}) \mid \prod_{p \in S(k)} p$ for every $k$ (`bernoulli_den_dvd_prod`).
2. $\operatorname{den}(B_{2k}) = \prod_{p \in S(k)} p$ for $k \ge 1$ (`bernoulli_den_eq_prod`).
3. A prime $p$ with $(p-1) \nmid 2k$ does not divide $\operatorname{den}(B_{2k})$
   (`bernoulli_den_not_dvd`).
4. $\operatorname{den}(B_{2k}) \equiv 2 \pmod 4$ for $k \ge 1$ (`bernoulli_den_mod4`).
5. For every $j$, $\operatorname{den}(B_j) = 1$ or $\operatorname{den}(B_j) \equiv 2 \pmod 4$
   (`bernoulli_den_cases`).

## 2. When to reach for it

- The entry is about A027642 (denominators of $B_n$), A002445 (denominators of $B_{2n}$),
  A090801 (distinct denominators), or a subsequence of them.
- The claim is a congruence for those denominators (mod 4, mod 9, mod 36, ...), or their value
  along indices such as $2^m$, primes, or $p - 1$.
- A $p$-adic valuation of an expression containing $B_{2k}$: item 3 says $B_{2k}$ is
  $p$-integral unless $(p-1) \mid 2k$, and item 2 says $v_p(B_{2k}) = -1$ otherwise.
- Coefficients of $\tan x$, $\log\cos x$, $x/(e^x - 1)$, power sums $\sum i^k$: they are
  built from Bernoulli numbers.

## 3. Paper proof

The input is the theorem of K. G. C. von Staudt and T. Clausen (both 1840), proved in Mathlib
(`Bernoulli.vonStaudt_clausen`, `Bernoulli.dvd_den_bernoulli`,
`Bernoulli.not_sq_dvd_den_bernoulli`); a textbook proof is in Ireland and Rosen, *A Classical
Introduction to Modern Number Theory*, Chapter 15. It is taken as given here:

$$B_{2k} + \sum_{p \in S(k)} \frac1p \in \mathbb Z \qquad (k \ge 0).$$

The corollaries below are classical; their arrangement and Lean proofs are this repository's.

**1.** Let $P = \prod_{p \in S(k)} p$ and $B_{2k} = N - \sum_{p \in S(k)} 1/p$ with
$N \in \mathbb Z$. Then $P\,B_{2k} = PN - \sum_{p \in S(k)} P/p \in \mathbb Z$, so
$\operatorname{den}(B_{2k}) \mid P$.

**2.** Let $k \ge 1$ and $p \in S(k)$. Write $B_{2k} = N - \frac1p - \sum_{q \in S(k),\ q \ne p}\frac1q$.
The last sum has denominator prime to $p$. If $p \nmid \operatorname{den}(B_{2k})$, then
$\frac1p = N - B_{2k} - \sum_{q \ne p}\frac1q$ would have denominator prime to $p$, which is
false. So every $p \in S(k)$ divides $\operatorname{den}(B_{2k})$; they are distinct primes, so
$P \mid \operatorname{den}(B_{2k})$, and item 1 gives equality.

**3.** If $p \mid \operatorname{den}(B_{2k})$ then $p \mid P$ by item 1, so $p \in S(k)$, so
$(p-1) \mid 2k$.

**4.** For $k \ge 1$, $2 \in S(k)$ since $1 \mid 2k$, and $P$ is squarefree, so
$\operatorname{den}(B_{2k}) = P$ is divisible by $2$ and not by $4$.

**5.** $B_0 = 1$; $B_1 = -\tfrac12$ has denominator $2$; $B_j = 0$ for odd $j \ge 3$; even
$j = 2k \ge 2$ is item 4.

## 4. Worked example: A219196

**Claim** ([A219196](https://oeis.org/A219196)). $a(n) = \operatorname{den}(B_{A131577(n)})$,
where $A131577(0) = 0$ and $A131577(n) = 2^{n-1}$ for $n \ge 1$. The entry conjectures
$a(15) = a(16) = 131070$ and $a(17) = \cdots = a(32) = 8589934590$.

**Reduction.** For $n \ge 2$ the index is $2^{n-1} = 2k$ with $k = 2^{n-2} \ge 1$, so by item 2
$a(n) = \prod p$ over primes with $(p-1) \mid 2^{n-1}$. Such $p$ has $p - 1 = 2^j$ with
$j \le n-1$. For $j \le 31$, $2^j + 1$ is prime exactly for $j = 0, 1, 2, 4, 8, 16$, giving
$p = 2, 3, 5, 17, 257, 65537$ (for $j$ not a power of 2, $2^j + 1$ has the factor
$2^{j/d} + 1$ for an odd divisor $d > 1$ of $j$; the Lean checks the 32 cases directly). Hence

$$a(n) = \prod_{\substack{j \in \lbrace 0,1,2,4,8,16 \rbrace \\ j \le n-1}} (2^j + 1), \qquad 2 \le n \le 32,$$

so $a(15) = a(16) = 2\cdot3\cdot5\cdot17\cdot257 = 131070$ ($n - 1 = 14, 15 < 16$) and
$a(n) = 131070\cdot 65537 = 8589934590$ for $17 \le n \le 32$.

**Small case.** $n = 5$: $B_{16} = -3617/510$, $S(8) = \lbrace 2, 3, 5, 17 \rbrace$ (the primes
$p < 18$ with $(p-1) \mid 16$), and $2\cdot 3\cdot 5\cdot 17 = 510$. The first terms are
$a(0), \dots, a(7) = 1, 2, 6, 30, 30, 510, 510, 510$, and $\operatorname{den}(B_{2^{14}}) =
131070$ (PARI `bernfrac`).

**Lean.** In [`OEIS/A219196/A219196_mathlib.lean`](../../OEIS/A219196/A219196_mathlib.lean):
`A219196_15 : A219196 15 = 131070`, `A219196_16 : A219196 16 = 131070`,
`A219196_17_32 (n : ℕ) (h1 : 17 ≤ n) (h2 : n ≤ 32) : A219196 n = 8589934590`, with
`A219196 n = (bernoulli (A131577 n)).den`. Route: `fermat_like` (primes with
$(p-1) \mid 2^m$, $m \le 31$), `vscSet_pow` (computes $S(2^{m-1})$), `A219196_eq`, and
`bernoulli_den_eq_prod`.

A shorter use of the same module: A219543 and A218755 (Bernoulli denominators $\equiv 3$,
resp. $6 \pmod 9$) have all first differences divisible by $36$, because by item 5 every such
denominator is $\equiv 2 \pmod 4$, hence $\equiv 30$, resp. $6 \pmod{36}$.

## 5. In Lean

`import OpenProblemsLib.BernoulliDen`; namespace `OpenProblemsLib.BernoulliDen`.

| declaration | meaning |
|---|---|
| `vscSet k` | $S(k)$, as a filter of `range (2 * k + 2)` |
| `bernoulli_den_dvd_prod` | item 1 |
| `bernoulli_den_eq_prod` | item 2 ($k \ge 1$) |
| `bernoulli_den_not_dvd` | item 3 (needs `[Fact p.Prime]`) |
| `bernoulli_den_mod4` | item 4 ($k \ge 1$) |
| `bernoulli_den_cases` | item 5 |

**Problems using it:**
[A219196](../../OEIS/A219196/) (`bernoulli_den_eq_prod`),
[A219543 / A218755](../../OEIS/A219543/) (`bernoulli_den_mod4`, `bernoulli_den_cases`),
[A131262](../../OEIS/A131262/) (`bernoulli_den_mod4`: $v_2(B_{2k}) = -1$),
[A141459 / A211163](../../OEIS/A141459/) (`bernoulli_den_not_dvd`).
The module `ShevelevFactorial.lean` uses Mathlib's von Staudt–Clausen directly
(`bernoulli_even_mem`), not this module.
