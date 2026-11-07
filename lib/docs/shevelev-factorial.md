# Shevelev's generalized factorials: the first row divisible by $p$

Module: `ShevelevFactorial.lean`.

## 1. The method

Iterated power sums $Q_{m+1}(n) = \sum_{i=1}^n i^t Q_m(i)$ are polynomials in $n$ with rational
coefficients. Newton's identity writes $m\,Q_m$ through the power-sum polynomials
$S_{t}, S_{2t}, \dots, S_{mt}$, and von Staudt–Clausen says exactly which $S_k$ have a
coefficient with $p$ in the denominator. Together they locate the first $m$ at which $p$ divides
a denominator of $Q_m$, and so the first row of Shevelev's generalized binomial triangle whose
inner entries are divisible by $p$.

**Definitions.** Fix $t \ge 1$ and a prime $p$. $\mathbb Z_{(p)}$ is the ring of rationals whose
denominator is prime to $p$ (`Zp p`), and $\mathbb Z_{(p)}[x]$ the polynomials with coefficients
in it (`ZpX p`).

- $S_k(x)$ is the Faulhaber polynomial with $S_k(n) = \sum_{i=1}^n i^k$ for $n \in \mathbb N$
  (`Spoly k`).
- $Q_0 = 1$ and $Q_{m+1}$ is the polynomial with $Q_{m+1}(n) = \sum_{i=1}^n i^t Q_m(i)$ for all
  $n \in \mathbb N$ (`shevQ t m`; `shevQ_unique`: any family with these two properties is it).
- $n!^{(t)}$ is the lcm of the denominators of the coefficients of $Q_n$ (`shevFact t n`), and
  $C^{(t)}(n,m) = n!^{(t)} / \bigl(m!^{(t)}\,(n-m)!^{(t)}\bigr) \in \mathbb Q$ (`shevBinom t n m`).

**Theorem 1** (power sums). $S_k \in \mathbb Z_{(p)}[x]$ for $1 \le k \le 2p-3$, $k \ne p-1$
(`Spoly_mem`), and $S_k \notin \mathbb Z_{(p)}[x]$ for $k \in \lbrace p-1,\ 2p-2,\ 2p-1 \rbrace$
(`Spoly_not_mem`).

**Theorem 2** (Newton's identity, `newton`). For $m \ge 0$,

$$m\,Q_m = \sum_{b=1}^{m} Q_{m-b}\,S_{tb}.$$

**Theorem 3** (threshold, `shevelev_threshold`, `shevFact_threshold`). Let $r < p$ with

- $ts \le 2p-3$ and $ts \ne p-1$ for $1 \le s < r$, and
- $tr \in \lbrace p-1,\ 2p-2,\ 2p-1 \rbrace$.

Then $Q_m \in \mathbb Z_{(p)}[x]$ (so $p \nmid m!^{(t)}$) for $m < r$, and
$Q_r \notin \mathbb Z_{(p)}[x]$ (so $p \mid r!^{(t)}$).

**Theorem 4** (the row, `shevelev_row`). Under the same hypotheses: $C^{(t)}(r,0) =
C^{(t)}(r,r) = 1$; for $0 < m < r$, $v_p\bigl(C^{(t)}(r,m)\bigr) \ge 1$ (in particular
$C^{(t)}(r,m) \ne 1$); and every integer $N$ equal to $\sum_{m=0}^r C^{(t)}(r,m)$ satisfies
$N \equiv 2 \pmod p$.

The last clause is conditional: the library does not prove that the row sum is an integer; it
proves the congruence for any integer equal to it.

## 2. When to reach for it

- A sequence defined by iterated sums $\sum_{i \le n} i^t(\cdots)$, or by complete homogeneous
  symmetric polynomials $h_m(1^t, 2^t, \dots, n^t)$, and a claim about the primes in the
  denominators of its coefficients.
- Claims of the form "the $((p-1)/t)$-th row contains two 1's and the other entries are multiples
  of $p$" or "the row sum at $(p-1)/t$ is $\equiv 2 \pmod p$".
- More generally, any question about the first index where $p$ enters a denominator, when the
  object is built from power sums $S_k$ with $k$ below $2p$.

## 3. Paper proof

Sources: von Staudt and Clausen (1840) for Bernoulli denominators; Faulhaber's formula
$S_k(x) = \frac{1}{k+1}\sum_{j=0}^{k} \binom{k+1}{j} B_j^{+} x^{k+1-j}$ ($B_j^{+}$ the
Bernoulli numbers with $B_1^{+} = +\tfrac12$); Newton's identity for complete homogeneous
symmetric polynomials. The definitions are V. Shevelev's (OEIS A202367–A202369, 2011). The
threshold argument and the Lean proofs were written for this repository.

*von Staudt–Clausen.* For $j \ge 2$ even, $B_j + \sum_{q \text{ prime},\ (q-1) \mid j} 1/q \in
\mathbb Z$. So $B_j \in \mathbb Z_{(p)}$ if $(p-1) \nmid j$, and $pB_j \in \mathbb Z_{(p)}$
always (`bernoulli_even_mem`). Odd $j \ge 3$ have $B_j = 0$.

**Theorem 1, $1 \le k \le 2p-3$, $k \ne p-1$.** Then $2 \le k+1 \le 2p-2$ and $k+1 \ne p$, so
$p \nmid k+1$, and it suffices that each $\binom{k+1}{j} B_j^{+}$ ($j \le k$) is in
$\mathbb Z_{(p)}$. The range is empty for $p = 2$, so $p$ is odd and $B_1^{+} = \tfrac12$ is fine.
For even $j \le k \le 2p-3 < 2(p-1)$, $(p-1) \mid j$ forces $j = p-1$; then $k \ge p$, so
$p \le k+1 < 2p$ and $k+2-p \le p-1$, and $\binom{k+1}{p-1} = \frac{(k+1)!}{(p-1)!\,(k+2-p)!}$
has exactly one factor $p$ in the numerator and none in the denominator. Hence
$\binom{k+1}{p-1}B_{p-1} = \frac{1}{p}\binom{k+1}{p-1}\cdot pB_{p-1} \in \mathbb Z_{(p)}$. All
other even $j$ have $B_j \in \mathbb Z_{(p)}$.

**Theorem 1, $k \in \lbrace p-1, 2p-2 \rbrace$.** By Fermat, $i^k \equiv 1 \pmod p$ for $p \nmid i$,
so $S_k(p) = \sum_{i=1}^p i^k \equiv p - 1 \equiv -1 \pmod p$. If $P \in \mathbb Z_{(p)}[x]$ then
$P(a) - P(b) = (a-b)z$ with $z \in \mathbb Z_{(p)}$ for integers $a, b$ (`eval_sub_eq_mul`);
with $P = S_k$, $a = p$, $b = 0$ and $S_k(0) = 0$ this would give $p \mid S_k(p)$.
**$k = 2p-1$:** the leading coefficient of $S_k$ is $1/(k+1) = 1/(2p)$.

**Theorem 2.** $Q_m(n)$ is the complete homogeneous symmetric polynomial $h_m$ evaluated at
$1^t, 2^t, \dots, n^t$, since $h_{m+1}(x_1, \dots, x_n) = \sum_{i \le n} x_i\,h_m(x_1, \dots, x_i)$
has the same recursion. Hence for each $n \in \mathbb N$

$$H_n(z) = \sum_{m \ge 0} Q_m(n) z^m = \prod_{i=1}^n \frac{1}{1 - i^t z}, \qquad
\frac{z H_n'(z)}{H_n(z)} = \sum_{i=1}^n \frac{i^t z}{1 - i^t z} = \sum_{b \ge 1} S_{tb}(n) z^b.$$

Comparing coefficients of $z^m$ in $zH_n' = H_n \cdot \sum_b S_{tb}(n) z^b$ gives the identity
at every natural $n$; two polynomials agreeing on $\mathbb N$ are equal.

**Theorem 3.** For $1 \le s < r$, $S_{ts} \in \mathbb Z_{(p)}[x]$ by Theorem 1. Induction on
$m < r$: by Theorem 2, $m\,Q_m = \sum_{b=1}^m Q_{m-b}S_{tb}$ has all factors in
$\mathbb Z_{(p)}[x]$, and $m < r < p$ is a unit. At $m = r$,

$$r\,Q_r = S_{tr} + \sum_{b=1}^{r-1} Q_{r-b}\,S_{tb},$$

where the sum is in $\mathbb Z_{(p)}[x]$ and $S_{tr}$ is not (Theorem 1); $r$ is a unit, so
$Q_r \notin \mathbb Z_{(p)}[x]$. Finally $p \nmid n!^{(t)}$ iff all coefficients of $Q_n$ are
$p$-integral (`not_dvd_lcm_den_iff`).

**Theorem 4.** $0!^{(t)} = 1$, so the outer entries are $r!^{(t)}/r!^{(t)} = 1$. For $0 < m < r$,
both $m$ and $r - m$ are $< r$, so $v_p\bigl(C^{(t)}(r,m)\bigr) = v_p(r!^{(t)}) \ge 1$. The row
sum is $2 + (\text{element of } p\mathbb Z_{(p)})$; an integer $N$ equal to it has
$N - 2 \in p\mathbb Z_{(p)} \cap \mathbb Z = p\mathbb Z$.

## 4. Worked example: A203509

**Claim** ([A203509](https://oeis.org/A203509), V. Shevelev). $a(n) = \sum_{m=0}^n C^{(4)}(n,m)$
(row sums of A178473) satisfies $a((p-1)/4) \equiv 2 \pmod p$ for primes $p \equiv 1 \pmod 4$
and $a((p-1)/2) \equiv 2 \pmod p$ for primes $p \equiv 3 \pmod 4$.

**Reduction to Theorem 4** ($t = 4$; the row-index arithmetic is `omega` in the problem file).

- $p = 4k+1$, $r = k$: $tr = 4k = p-1$; for $s < r$, $4s \le p - 5 \le 2p-3$ and $4s \ne p-1$.
- $p = 4k+3$, $r = 2k+1$: $tr = 8k+4 = 2p-2$; for $s < r$, $4s \le 8k = 2p-6$, and $4s \ne p-1$
  because $p - 1 \equiv 2 \pmod 4$.

In both cases $r < p$.

**Small case.** $r = 3$ is the row for both $p = 7$ ($= 4\cdot1+3$, $tr = 12 = 2p-2$) and
$p = 13$ ($= 4\cdot3+1$, $tr = 12 = p-1$). The polynomials:

$$Q_1 = S_4 = \frac{n^5}{5} + \frac{n^4}{2} + \frac{n^3}{3} - \frac{n}{30}, \qquad
S_{12} = \frac{n^{13}}{13} + \frac{n^{12}}{2} + n^{11} - \frac{11 n^9}{6} + \frac{22 n^7}{7}
- \frac{33 n^5}{10} + \frac{5n^3}{3} - \frac{691\,n}{2730},$$

with $2730 = 2\cdot3\cdot5\cdot7\cdot13$. $Q_2$ has denominators dividing $1800$, and $Q_3$ has the
coefficient $-691/8190$ of $n$ ($8190 = 2\cdot 3^2\cdot 5\cdot 7\cdot 13$), inherited from
$S_{12}/3$. So

$$0!^{(4)} = 1,\quad 1!^{(4)} = 30,\quad 2!^{(4)} = 1800 = 2^3 3^2 5^2,\quad
3!^{(4)} = 14742000 = 2^4\, 3^4\, 5^3\cdot 7\cdot 13,$$

row 3 is $1,\ 273,\ 273,\ 1$ with $273 = 3\cdot 7\cdot 13$, and $a(3) = 548 = 2 + 7\cdot 78 =
2 + 13\cdot 42$. Newton's identity $3Q_3 = Q_2 S_4 + Q_1 S_8 + S_{12}$ checks as a polynomial
identity, and $\sum_{i \le 7} i^{6} \equiv \sum_{i \le 7} i^{12} \equiv -1 \pmod 7$.

**Lean.** `A203509.A203509_main (p : ℕ) (hp : p.Prime) (r : ℕ) (hr : (p % 4 = 1 ∧ r = (p - 1) / 4)
∨ (p % 4 = 3 ∧ r = (p - 1) / 2)) (N : ℤ) (hN : (N : ℚ) = a r) : (p : ℤ) ∣ N - 2` in
[`OEIS/A203509/A203509_mathlib.lean`](../../OEIS/A203509/A203509_mathlib.lean), one application
of `shevelev_row`. Reading of the entry outside Lean: "$\equiv 2 \pmod p$" for the row sum as
"every integer equal to it is $2 \bmod p$".

## 5. In Lean

`import OpenProblemsLib.ShevelevFactorial`; namespace `OpenProblemsLib.ShevelevFactorial`.

| declaration | meaning |
|---|---|
| `Zp p`, `ZpX p`, `mem_Zp`, `mem_ZpX` | $\mathbb Z_{(p)}$ and $\mathbb Z_{(p)}[x]$ as subrings |
| `eval_sub_eq_mul` | $P \in \mathbb Z_{(p)}[x]$ ⇒ $P(a) - P(b) = (a-b)z$, $z \in \mathbb Z_{(p)}$ |
| `not_dvd_lcm_den_iff` | $p \nmid$ lcm of coefficient denominators ⇔ $P \in \mathbb Z_{(p)}[x]$ |
| `Spoly k`, `Spoly_eval`, `Spoly_coeff_top` | Faulhaber polynomial, its values, leading coefficient $1/(k+1)$ |
| `bernoulli_even_mem` | $pB_{2i} \in \mathbb Z_{(p)}$; $B_{2i} \in \mathbb Z_{(p)}$ if $(p-1) \nmid 2i$ |
| `Spoly_mem`, `Spoly_not_mem`, `sum_pow_not_dvd` | Theorem 1 |
| `sumOp`, `sumOp_eval` | the summation operator $P \mapsto \sum_{i \le n} P(i)$ |
| `shevQ`, `shevQ_succ_eval`, `shevQ_unique` | $Q_m$ |
| `shevFact`, `shevBinom`, `shevFact_zero` | $n!^{(t)}$, $C^{(t)}(n,m)$ |
| `Hser`, `Pser`, `newton_series`, `newton` | Theorem 2 |
| `shevelev_threshold`, `shevFact_threshold` | Theorem 3 |
| `shevelev_row` | Theorem 4 |

**Problems using it** (all import the module; argument in
[OEIS/A202941/README.md](../../OEIS/A202941/README.md)):
[A202941](../../OEIS/A202941/) ($t = 2$, row $(p-1)/2$),
[A203278](../../OEIS/A203278/) (its row sums),
[A203484](../../OEIS/A203484/) ($t = 3$),
[A203498](../../OEIS/A203498/) (its row sums),
[A178473](../../OEIS/A178473/) ($t = 4$),
[A203509](../../OEIS/A203509/) (its row sums).
