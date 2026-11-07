# Short-interval primes: a prime in $(x, 1.21x]$ for $x \ge 25$ (Chebyshev 1852)

Module: `ShortIntervalPrimes.lean`.

## 1. The method

Bertrand's postulate (Mathlib `Nat.exists_prime_lt_and_le_two_mul`) gives a prime in $(x, 2x]$.
Many induction arguments on primes need a shorter interval with an explicit start. Chebyshev's
1852 weights give explicit upper and lower bounds on $\psi(x) = \sum_{n \le x} \Lambda(n)$ whose
constants differ by the factor $6/5$, so a prime lies in $(x, rx]$ for every fixed $r > 6/5$ once $x$
is large; a chain of certified primes covers the small $x$. The module does this for $r = 1.21$ and
all real $x \ge 25$. No zeta-function input is used.

**Notation.** $\psi$ and $\theta$ are Mathlib's `Chebyshev.psi`, `Chebyshev.theta`
($\theta(x) = \sum_{p \le x} \log p$). The Chebyshev constant is

$$a = \tfrac{7}{15}\log 2 + \tfrac{3}{10}\log 3 + \tfrac16 \log 5 = 0.92129\ldots \qquad (\texttt{a},\ \texttt{a\_bound}).$$

**Theorem** (`ShortIntervalPrimes.lean`).

1. $\psi(x) \ge a x - 5\log x + 5$ for $x \ge 30$ (`psi_lower`).
2. $\psi(x) \le \tfrac65 a x + \tfrac{\log x}{\log 6}(5\log x - 5) + 170$ for $x \ge 30$ (`psi_upper`).
3. If $\theta(x) < \theta(y)$ then some prime $p$ has $x < p \le y$ (`exists_prime_of_theta_lt`).
4. For real $x \ge 10^8$ there is a prime in $(x, 1.21x]$ (`exists_prime_Ioc_large`).
5. For real $x \ge 25$ there is a prime in $(x, 1.21x]$ (`exists_prime_Ioc_mul`); for natural
   $n \ge 25$ a prime $p$ with $n < p$ and $100p \le 121n$ (`exists_prime_Ioc_mul_nat`).

## 2. When to reach for it

- An induction adds one prime at a time and needs the next prime within a fixed ratio $r < 2$ of
  the previous one: sums of $k$ distinct primes (A102237), Richert-type "every large integer is a sum
  of distinct primes from a set" arguments.
- Ratios of consecutive primes: $p_{n+1} < r\,p_n$ for any $r \ge 1.21$ and $p_n \ge 25$, for
  example $p_{n+1} < \tfrac32(p_n + 1)$ (A207480) and $p_{n+1} < \tfrac43(p_n + 2)$ (A208548).
- Not for intervals of relative length $o(1)$ such as $(x, x + x/\log x]$ (A077510) or $(x, \tfrac{57}{56}x]$
  (A188672): those need Rosser–Schoenfeld or Dusart, whose proofs use zeros of $\zeta$.
- Not for counting primes ($\pi(x)$ bounds with constant close to 1): items 1–2 bound $\theta$, and
  turning them into a sharp $\pi(x)$ upper bound needs partial summation, which the module does not
  contain.

## 3. Paper proof

Source: P. L. Chebyshev, *Mémoire sur les nombres premiers* (1852); the presentation follows
H. G. Diamond as formalised in PrimeNumberTheoremAnd (`IEANTN/Chebyshev.lean`, Apache 2.0); that
file's lemmas through `psi_diff_upper` are inlined in the module with attribution.

**Weighted sums.** Let $T(x) = \sum_{n \le x}\log n = \sum_{n \le x}\Lambda(n)\lfloor x/n\rfloor$.
Comparison with $\int \log t\,dt$ gives $|T(x) - (x\log x - x + 1)| \le \log x$ for $x \ge 1$. Put
$U(x) = T(x) - T(x/2) - T(x/3) - T(x/5) + T(x/30) = \sum_{n \le x}\Lambda(n)E(x/n)$ with
$E(y) = \lfloor y\rfloor - \lfloor y/2\rfloor - \lfloor y/3\rfloor - \lfloor y/5\rfloor + \lfloor y/30\rfloor$.
$E$ has period 30, takes values in $\{0, 1\}$, and equals 1 on $[1, 6)$. Hence
$\psi(x) - \psi(x/6) \le U(x) \le \psi(x)$. The main terms of $U$ cancel to $a x$ (the weights sum
to $0$ against $1/m$), and the error terms give $|U(x) - ax| \le 5\log x - 5$ for $x \ge 30$.
This yields item 1 and $\psi(x) - \psi(x/6) \le a x + 5\log x - 5$.

**Item 2.** Telescope over $x, x/6, x/6^2, \ldots$ until $x/6^n < 30$: $n \le \log x/\log 6$, the main
terms sum to at most $a x \sum 6^{-i} \le \tfrac65 a x$, each error term is at most $5\log x - 5$, and
$\psi(x/6^n) \le (\log 4 + 4)\cdot 30 \le 170$ (Mathlib `psi_le_const_mul_self`).

**Item 4.** $\theta(1.21x) \ge \psi(1.21x) - 2\sqrt{1.21x}\log(1.21x)$ (Mathlib `psi_sub_theta_le`)
and $\theta(x) \le \psi(x)$. With items 1 and 2,

$$\theta(1.21x) - \theta(x) \ge 0.01\,a\,x - 2.2\sqrt x\,L - 2.8L^2 - 5L - 165,\qquad L = \log(1.21x).$$

Write $\sqrt x = 10^4u$ with $u \ge 1$; $\log u \le u - 1$ gives $L \le 16.64 + 2u$, and the right
side is at least $875000u^2 - 367000u - 1100 > 0$. Item 3 gives the prime.

**Item 5.** For $25 \le x < 10^8$ use the 85 primes $29, 31, 37, 43, \ldots, 118074017$, each at most
$1.21$ times the previous (greedy: the largest prime $\le 1.21p$). If $p_i \le x < p_{i+1}$ then
$p_{i+1} \le 1.21p_i \le 1.21x$; for $25 \le x < 29$, $29 \le 1.21 \cdot 25$. Primality is by Pratt
certificates (`Pratt.lean`), the chain condition by `decide +kernel`.

## 4. Worked example: A102237

**Claim** ([A102237](https://oeis.org/A102237)). $a(n) = 2^n$ for $n > 5$, where $a(n)$ is the least
number that is a product of $n$ primes and a sum of $n$ distinct primes. Equivalently $2^n$ is a sum
of $n$ distinct primes.

**Induction.** $W(k, L, U, M)$: every $N \equiv k \pmod 2$ in $[L, U]$ is a sum of $k$ distinct odd
primes $\le M$. If $W(k, L, U, M)$, $M \ge 25$ and $0.42M \le 1.21(U - L)$, then for
$N \equiv k + 1$ in $[L + 1.21M,\ U + 2M/1.21]$ take a prime $q \in (b, 1.21b]$ with
$b = \max(N - U, M)$ (item 5). Then $M < q \le 2M$ and $N - q \in [L, U]$, so
$W(k+1, L + 1.21M, U + 2M/1.21, 2M)$. From the bases $W(6, 62, 152, 39)$ and $W(6, 62, 374, 78)$
(kernel tables) the windows contain $2^n$ for even $n$ and $2^n - 2$ for odd $n$; add the prime 2
in the odd case.

**Lean.** `OEIS/A102237/A102237_mathlib.lean`: `win_step`, `win_chain`, `sum_distinct_primes`,
`A102237_main` (`a102237 n = 2 ^ n` for `n ≥ 6`).

## 5. Lean names

| name | statement |
|---|---|
| `T`, `E`, `ν`, `U`, `a` | Chebyshev's sums and constant (adapted from PrimeNumberTheoremAnd) |
| `a_bound` | `a ∈ [0.92129, 0.92130]` |
| `U_bound` | `|U x - a x| ≤ 5 log x - 5` for `x ≥ 30` |
| `psi_lower` | `ψ x ≥ a x - 5 log x + 5` for `x ≥ 30` |
| `psi_diff_upper` | `ψ x - ψ (x/6) ≤ a x + 5 log x - 5` for `x ≥ 30` |
| `psi_upper` | `ψ x ≤ 6/5 a x + (log x / log 6)(5 log x - 5) + 170` for `x ≥ 30` |
| `exists_prime_of_theta_lt` | `θ x < θ y → ∃ p prime, x < p ≤ y` |
| `exists_prime_Ioc_large` | prime in `(x, 1.21 x]` for real `x ≥ 10^8` |
| `primeChain`, `primeChain_prime`, `chainOK_cover` | the 85-prime chain and its use |
| `exists_prime_Ioc_mul` | prime in `(x, 1.21 x]` for real `x ≥ 25` |
| `exists_prime_Ioc_mul_nat` | `25 ≤ n → ∃ p prime, n < p ∧ 100 p ≤ 121 n` |

All in namespace `OpenProblemsLib.ShortIntervalPrimes`; axioms propext, Classical.choice,
Quot.sound (`lib/test/ShortIntervalPrimesAxioms.lean`). Used by OEIS A102237.
