# q-series: Gaussian binomials, the Jacobi triple product, a q-Gauss sum

Module: `QSeries.lean`.

## 1. The method

Theta-type sums $\sum_{j \in \mathbb Z} \pm q^{(\text{quadratic in } j)}$ and $q$-hypergeometric
sums are proved equal to products by finite identities among Gaussian binomials (q-Pascal
induction), followed by truncation: two power series are equal when they agree modulo $q^N$ for
every $N$. Everything is algebraic and holds over any commutative ring. The module provides the
Gaussian binomials, the finite and infinite Jacobi triple product, and one $q$-Gauss sum (a
conjugate Bailey pair) proved by Gosper/Zeilberger telescoping.

**Notation.** $R$ is a commutative ring, $Q \in R$.
$(a;Q)_n = (1-a)(1-aQ)\cdots(1-aQ^{n-1})$.

- The **Gaussian binomial** $[N,k]_Q$ ($N \in \mathbb N$, $k \in \mathbb Z$) is defined by
  $[0,k] = [k = 0]$ and q-Pascal

  $$[N+1,k] = [N,k-1] + Q^k\,[N,k],$$

  with $[N,k] = 0$ for $k < 0$ or $k > N$ (`gauss Q N k`).
- For $a, b \ge 1$, $m = a+b$, in $R[[q]]$:

  $$\mathrm{jtpFactor}_i = (1 - q^{m(i+1)})(1 - q^{mi+a})(1 - q^{mi+b}), \qquad
  \mathrm{jtpSeries} = \sum_{j \in \mathbb Z} (-1)^j q^{a\,j(j+1)/2 + b\,j(j-1)/2}.$$

**Theorem 1** (Gaussian binomials). For $0 \le K \le N$:

- second q-Pascal rule $[N+1,k] = Q^{N+1-k}[N,k-1] + [N,k]$ (`gauss_rule2`);
- $[N+2,k] = Q^{N+2-k}[N,k-2] + (1+Q^{N+1})[N,k-1] + Q^k[N,k]$ (`gauss_two_step`);
- $[N,K]\,(Q;Q)_K = \prod_{i<K}\bigl(1 - Q^{N-K+1+i}\bigr)$ (`gauss_mul_poch`).

**Theorem 2** (finite Jacobi triple product, `jtp_finite`). For $x, y \in R$ and $Q = xy$,

$$\prod_{i<n} (1 - xQ^i)(1 - yQ^i) = \sum_{j=-n}^{n} (-1)^j x^{j(j+1)/2} y^{j(j-1)/2}\,[2n, n+j]_Q .$$

**Theorem 3** (Jacobi triple product, `jacobi_triple_product`). For $a, b \ge 1$, $m = a+b$,

$$\prod_{i \ge 0} (1 - q^{m(i+1)})(1 - q^{mi+a})(1 - q^{mi+b})
= \sum_{j \in \mathbb Z} (-1)^j q^{a\,j(j+1)/2 + b\,j(j-1)/2}$$

in $R[[q]]$, as a product converging coefficientwise (`HasProd` in the pi topology). For
$k < n$ the coefficient of $q^k$ in the first $n$ factors already equals that of the sum
(`jtp_coeff`). $a = 2$, $b = 1$ is Euler's pentagonal number theorem.

**Theorem 4** ($q$-Gauss sum for a conjugate Bailey pair, `qGaussSum_mul`). In $\mathbb Z[[q]]$,
for every $r \ge 0$,

$$(-q;q)_{r+1} \sum_{k \ge 0} s_{r,k} = 1, \qquad
s_{r,k} = \frac{(-q^r;q)_k\,(-q)^k\,(q;q)_{k+r}}{(q;q)_k\,(q;q)_{2r+k+1}} .$$

This is the instance of Bailey's lemma with $a = q$, $\rho_1 = q$, $\rho_2 = -1$; the Lean
statement is this single family, not the general $q$-Gauss sum.

## 2. When to reach for it

- A generating function $1/\sum_{j\in\mathbb Z} (-1)^j q^{(Aj^2 + Bj)/2}$ (generalized polygonal
  numbers), or $\sum_j (-1)^j q^{\ldots}$ times something: Theorem 3 turns it into a product, so the
  coefficients count partitions with parts in residue classes.
- A claimed parity or sign pattern of a $q$-series coefficient sitting on quadratic exponents
  $3n(n+1)$, $n(3n\pm1)/2$, ...: look for a finite Gaussian-binomial identity (Theorem 2 style),
  a Bailey pair, and a summation like Theorem 4.
- Sums $\sum_k (\text{q-Pochhammer ratios})\,z^k$ with $z = c/(ab)$: a $q$-Gauss sum; prove it by
  a telescoping certificate checked in the fraction field.

## 3. Paper proof

Sources: C. F. Gauss (q-binomials), C. G. J. Jacobi (1829, triple product), E. Heine (1847,
$q$-Gauss sum), W. N. Bailey (1947–49, Bailey's lemma), R. W. Gosper and D. Zeilberger
(telescoping certificates). Finite forms of the triple product in Gaussian binomials are classical;
the induction below is the standard q-Pascal one. The telescoping certificates of Theorem 4 and
all Lean proofs are this repository's.

**Theorem 1.** By the recursion, $[N,k]$ is $g_{N,k}(Q)$ for a polynomial
$g_{N,k} \in \mathbb Z[Q]$, so it suffices to prove the identities in
$\mathbb Z[Q] \subset \mathbb Q(Q)$ and evaluate. There $g_{N,k} = (Q;Q)_N/\bigl((Q;Q)_k(Q;Q)_{N-k}\bigr)$
for $0 \le k \le N$ (both satisfy the recursion and the initial values), and the second rule is
the identity $1 - Q^{N+1} = (1 - Q^{N+1-k}) + Q^{N+1-k}(1 - Q^{k})$ multiplied by
$(Q;Q)_N/\bigl((Q;Q)_k(Q;Q)_{N+1-k}\bigr)$. Subtracting
the two rules gives $[N,k-1](1 - Q^{N+1-k}) = [N,k](1-Q^k)$ (`gauss_ratio`), and
`gauss_mul_poch` follows by induction on $K$. For the two-step rule apply rule 1 to $[N+2,k]$ and
rule 2 to both resulting terms:

$$[N+2,k] = \bigl(Q^{N+2-k}[N,k-2] + [N,k-1]\bigr) + Q^k\bigl(Q^{N+1-k}[N,k-1] + [N,k]\bigr).$$

**Theorem 2**, by induction on $n$ ($n = 0$: both sides are $1$). Put
$c_j = (-1)^j x^{j(j+1)/2} y^{j(j-1)/2}$, so $c_{j+1} = -xQ^j c_j$ and $c_{j-1} = -yQ^{-j}c_j$
(as Laurent monomials). Expand $[2n+2, n+1+j]$ by the two-step rule with $N = 2n$,
$k = n+1+j$, and collect the coefficient of $[2n, n+i]$:

$$c_{i+1}Q^{n-i} + c_i\,(1 + Q^{2n+1}) + c_{i-1}Q^{n+i}
= c_i\bigl(1 + Q^{2n+1} - xQ^n - yQ^n\bigr) = c_i\,(1 - xQ^n)(1 - yQ^n).$$

So the right side for $n+1$ is $(1-xQ^n)(1-yQ^n)$ times the right side for $n$. (Terms with
$|i| > n$ vanish because $[2n, n+i] = 0$, so negative powers of $Q$ never occur.)

**Theorem 3.** Take $x = q^a$, $y = q^b$, $Q = q^m$ in $R[[q]]$; since $a, b \ge 1$ every factor
$\mathrm{jtpFactor}_i$ with $i \ge N$ is $\equiv 1 \pmod{q^N}$, and so is $1 - Q^{i+1}$ for
$i+1 \ge N$. Fix $N$ and apply Theorem 2 with $n = 2N$, multiplied by $U = (Q;Q)_{2N}$:

$$\prod_{i<N}\mathrm{jtpFactor}_i \equiv U \prod_{i < 2N}(1-xQ^i)(1-yQ^i)
= \sum_{|j| \le 2N} c_j \cdot U\,[4N, 2N+j]_Q \pmod{q^N}.$$

If $|j| \ge N$, the exponent of $c_j$ is $\ge |j| \ge N$, so the term vanishes mod $q^N$. If
$|j| < N$, put $K = 2N + j$; then $U \equiv (Q;Q)_K \pmod{q^N}$ (they differ only in factors
$1 - Q^{i}$ with $i \ge N$), and by Theorem 1

$$[4N, K]_Q\,(Q;Q)_K = \prod_{i<K}\bigl(1 - Q^{4N-K+1+i}\bigr) \equiv 1 \pmod{q^N}$$

since $4N - K + 1 > N$. Hence $\prod_{i<N}\mathrm{jtpFactor}_i \equiv \sum_{|j|<N} c_j \equiv
\mathrm{jtpSeries} \pmod{q^N}$ (`jtp_mod`), and the factors $\equiv 1 \bmod q^{i+1}$ make the
partial products converge coefficientwise to $\mathrm{jtpSeries}$ (`hasProd_of_modX`).

**Theorem 4.** Let $G_r = \sum_k s_{r,k}$; $s_{r,k}$ has $q$-order $\ge k$ (the factor $(-q)^k$
times units), so the sum converges. Two telescoping identities of rational functions, checked by
clearing denominators in $\mathbb Q(q)$ (`gosper_field`, `zeil_field`, then transported into
$\mathbb Z[[q]]$ through its fraction field):

- (Gosper, $r = 0$) $s_{0,K} = R_K - R_{K+1}$ with $R_K = s_{0,K}\,\dfrac{1 - q^{K+1}}{1+q}$.
  Summing, $G_0 = R_0 = \dfrac{1}{1+q}$, since $R_K \to 0$.
- (Zeilberger, $r \to r+1$) $(1 + q^{r+2})\,s_{r+1,K} - s_{r,K} = c_{r,K+1} - c_{r,K}$ with

  $$c_{r,K} = s_{r,K}\cdot\frac{-q^r\,\bigl(q^{K+2r+2} + q^{K+r+1} + q - 1\bigr)(1 - q^K)}{(1+q^r)(1 - q^{K+2r+2})}.$$

  The factor $1 + q^r$ in the denominator cancels against the first factor of $(-q^r;q)_K$
  ($K \ge 1$), so $c_{r,K} \in \mathbb Z[[q]]$; $c_{r,0} = 0$ and $c_{r,K} \to 0$, so summing
  over $K$ gives $(1+q^{r+2})G_{r+1} = G_r$.

By induction $G_r = 1/\prod_{i=1}^{r+1}(1+q^i) = 1/(-q;q)_{r+1}$.

Cross-check with the classical sum: $s_{r,k} = \frac{(q;q)_r}{(q;q)_{2r+1}}\cdot
\frac{(-q^r;q)_k\,(q^{r+1};q)_k}{(q;q)_k\,(q^{2r+2};q)_k}(-q)^k$, which is Heine's
${}_2\phi_1(a, b; c; q, c/ab)$ with $a = -q^r$, $b = q^{r+1}$, $c = q^{2r+2}$, $c/ab = -q$;
Heine's product $\frac{(c/a;q)_\infty (c/b;q)_\infty}{(c;q)_\infty (c/ab;q)_\infty}$ times
$\frac{(q;q)_r}{(q;q)_{2r+1}}$ simplifies to $\frac{(-q^{r+2};q)_\infty}{(-q;q)_\infty} = \frac{1}{(-q;q)_{r+1}}$.

## 4. Worked example: A195825

**Claim** ([A195825](https://oeis.org/A195825), O. E. Pol, conjecture of Jun 21 2012). Column $k$
of the array has g.f. $1/\sum_{j\in\mathbb Z}(-1)^j q^{(mj^2 - (m-2)j)/2}$, $m = k+2$. If $k$ is
odd it has $(k+1)/2$ plateaus (maximal runs of $\ge 2$ equal terms) of lengths
$k+1, k-1, \dots, 2$; if $k$ is even, $k/2$ plateaus of lengths $k+1, k-1, \dots, 3$; the
plateau levels are the first terms of A210843 (1, 4, 13, 35, 86, ...).

**Reduction to Theorem 3.** $\frac{mj^2 - (m-2)j}{2} = 1\cdot\frac{j(j+1)}{2} + (m-1)\frac{j(j-1)}{2}$,
so the entry's sum is $\mathrm{jtpSeries}$ with $a = 1$, $b = m-1$ (`thetaEntry_eq`), and
Theorem 3 gives

$$\sum_{j\in\mathbb Z}(-1)^j q^{(mj^2-(m-2)j)/2} = \prod_{i \ge 0}(1 - q^{m(i+1)})(1 - q^{mi+1})(1 - q^{mi+m-1}).$$

Its reciprocal is the generating function of partitions into parts $\equiv 0, \pm1 \pmod m$
(Mathlib's restricted-partition product). The plateau structure is then combinatorics outside
this module: $T(n+1) - T(n)$ counts such partitions of $n+1$ without a part $1$, and these exist
iff $A(m-1) \le n+1 \le A(m+1)$ for some $A \ge 1$.

**Small case** $k = 3$, $m = 5$. The sum has exponents ($j = 0, 1, -1, 2, -2, 3, -3, 4$)
$0, 1, 4, 7, 13, 18, 27, 34$ with signs $+,-,-,+,+,-,-,+$:

$$1 - q - q^4 + q^7 + q^{13} - q^{18} - q^{27} + q^{34} - \cdots
= \prod_{i\ge0}(1-q^{5i+5})(1-q^{5i+1})(1-q^{5i+4})$$

(checked to $q^{39}$). Its reciprocal begins

$$T(n,3) = 1, 1, 1, 1, 2, 3, 4, 4, 5, 7, 10, 12, 14, 16, 21, 27, \dots \quad (n = 0, 1, \dots),$$

equal to the number of partitions of $n$ into parts $\equiv 0, 1, 4 \pmod 5$ (checked to $n = 19$).
The plateaus are $n \in [0, 3]$ (length $4 = k+1$, level 1) and $n \in [6, 7]$ (length
$2 = k-1$, level 4), matching A210843 $= 1, 4, \dots$.

**Lean.** In [`OEIS/A195825/A195825_mathlib.lean`](../../OEIS/A195825/A195825_mathlib.lean)
(namespace `OEIS_A195825`): `column_gf c : thetaEntry (c + 3) * PowerSeries.mk (fun n => (T (c + 3) n : ℤ)) = 1`
(the module enters here through `jacobi_triple_product` and `jtp_coeff` in `hasProd_goodFactor`),
and the main theorems `flat_iff` (exact set of $n$ with $T(n+1) = T(n)$) and `level_const` (the
level of plateau $A$ does not depend on $k \ge 2A+1$).

## 5. In Lean

`import OpenProblemsLib.QSeries`; namespace `OpenProblemsLib.QSeries`.

| declaration | meaning |
|---|---|
| `gauss Q N k`, `gauss_succ`, `gauss_eq_zero`, `gauss_zero_right` | $[N,k]_Q$ by q-Pascal, integer $k$ |
| `gauss_rule2`, `gauss_two_step`, `gauss_ratio`, `gauss_mul_poch` | Theorem 1 |
| `tri`, `tri'`, `jc x y j`, `jc_succ`, `jc_pred`, `jc_swap` | $j(j\pm1)/2$ and the terms $c_j$ |
| `jtp_finite` | Theorem 2 |
| `modX N`, `coeff_eq_of_modX`, `eq_of_modX`, `prod_modX_stable` | working modulo $q^N$ in $R[[q]]$ |
| `jtpFactor`, `jtpPartial`, `jtpSeries`, `coeff_jtpSeries` | the product factors and the theta sum |
| `jtp_mod`, `jtp_coeff`, `hasProd_of_modX`, `jacobi_triple_product` | Theorem 3 |
| `osum`, `modX_osum` | order-convergent sums $\sum_k f_k$ |
| `qpF`, `ppF`, `sF`, `cF`, `gosper_field`, `zeil_field` | Theorem 4's certificates in any field |
| `qpS`, `ppS`, `sS`, `cS`, `gS`, `inv1`, `sum_sS_zero`, `sum_sS_succ` | the same in $\mathbb Z[[q]]$ (`cS r K` is $c_{r,K+1}$, `gS K` is $R_K$) |
| `qGaussSum r`, `qGaussSum_mul` | Theorem 4 |

**Problems using it:**
[A195825](../../OEIS/A195825/) (Jacobi triple product) and
[A202150 / A202146](../../OEIS/A202150/) (parity of the $q$-analog of $\pi/2$: finite
Gaussian-binomial identities, a Bailey pair, and `qGaussSum_mul` for Bailey's lemma with
$a = q$, $\rho_1 = q$, $\rho_2 = -1$).
