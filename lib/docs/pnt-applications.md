# Prime-density applications: divergent $\sum 1/p$ over a residue class, sieve density zero, primes in every block, semiprime counts

Module: `PNTApps.lean` (namespace `OpenProblemsLib.PNTApps`). Inputs: Mathlib's Dirichlet
L-series bound, Mathlib's Chebyshev bound, and the vendored PNT+ (`prime_between`, see
[../PNTPlus/README.md](../PNTPlus/README.md)).

## 1. The method

Many OEIS conjectures reduce to one qualitative prime-density fact plus elementary arithmetic.
The module packages four such facts so that an instance file only supplies the arithmetic.

1. **Dirichlet in reciprocal form.** For $\gcd(a, q) = 1$,
   $\sum_{p \equiv a\ (q)} 1/p = \infty$ (`not_summable_one_div_prime_mod`).
2. **Sieve density zero.** Let $P$ be a set of primes with $\sum_{p \in P} 1/p = \infty$. For each
   $p \in P$ let $G_p(n)$ depend only on $n \bmod p^2$ and hold for at least $p - 1$ residues mod
   $p^2$. Then $E = \{n : G_p(n) \text{ fails for every } p \in P\}$ has natural density 0
   (`density_zero_of_sieve`). Typical $G_p$: "$p \mid n$", "$p \,\|\, n$", "$p \,\|\, (un + v)$" with
   $p \nmid u$.
3. **Primes in every block.** For every $K$ there is $X$ such that $(km, (k+1)m)$ contains a prime
   whenever $k < K$ and $km \ge X$ (`exists_prime_block`). This is the prime number theorem in the
   form "a prime in $(x, (1+\varepsilon)x)$ for $x \ge x_0(\varepsilon)$", with $\varepsilon = 1/K$.
4. **Semiprime counts.** $\pi(y) \le (2\log 4 + 2)\,y/\log y$ for $y \ge 2$ (`pi_le_div_log`),
   $\sum_{p \le 2^J} 1/p \le \frac{2(2\log 4 + 2)}{\log 2}(1 + \log J)$ (`sum_inv_primes_le`), and the
   number of semiprimes up to $x$ is at most $C\,x\,(1 + \log(\log_2 x + 1))/\log x$ for $x \ge 16$
   (`semiprime_count_bound`).

Bookkeeping: densities are stated as `Tendsto (fun N => (Nat.count p N : ℝ) / N) atTop (𝓝 d)`.
`density_zero_or` (union), `tendsto_density_of_eq_off` (change a set on a density-zero set),
`tendsto_count_div_of_periodic` (a set periodic mod $M$ has density `count p M / M`) and
`tendsto_nth_div_of_density` (density $d > 0$ gives `nth p k / k → 1/d`) finish most instances.

## 2. When to reach for it

- "Almost all $n$ have property X" or "the terms have density zero", where X fails only when some
  prime of a residue class divides $n$ in a prescribed way (exactly once, at all, ...).
- "$b(k)/k \to c$" for the $k$-th element of a set that agrees with a periodic set off a
  density-zero set.
- A walk on primes (digit-sharing successors, nearest primes with a property) that needs a prime in
  every short block of fixed relative width: item 3.
- Average orders of counts of representations involving semiprimes: item 4.

Not for: explicit constants (Rosser–Schoenfeld, Dusart; see core
`core-explicit-prime-bounds-lean`), asymptotic constants with error terms (Mertens' constant,
Landau's $C x/\sqrt{\log x}$), or anything needing zero-free regions beyond PNT+.

## 3. Paper proof

**Item 1.** Mathlib (`LSeries_residueClass_lower_bound`) gives $C$ with
$\sum_{n \equiv a} \Lambda(n) n^{-x} \ge \frac{1}{\varphi(q)(x-1)} - C$ for $x \in (1, 2]$; the non-prime
part is bounded (`summable_residueClass_non_primes_div`). If $\sum_{p \equiv a} 1/p$ converged, choose
$N$ with tail $T = \sum_{p \ge N,\ p \equiv a} 1/p < \frac{1}{2\varphi(q)}$. Since
$\log p \le p^{x-1}/(x-1)$, the primes $p \ge N$ contribute at most $T/(x-1)$ and the primes $p < N$ a
constant $B$. So $\frac{1}{\varphi(q)(x-1)} - C \le A + B + \frac{T}{x-1}$, i.e.
$\frac{1}{2\varphi(q)} \le (A + B + C)(x - 1)$ for all $x \in (1, 2]$, false as $x \to 1$.

**Item 2.** For a finite $T \subseteq P$ put $M = \prod_{p \in T} p^2$. The condition "$G_p$ fails for all
$p \in T$" depends on $n \bmod M$; by the Chinese remainder theorem (`count_forall_prod`) it holds
for $\prod_{p\in T} c_p$ residues mod $M$, with $c_p \le p^2 - p + 1$. Hence its density is
$\prod_{p \in T} c_p/p^2 \le \prod_{p\in T}(1 - \tfrac{1}{2p}) \le \exp(-\tfrac12 \sum_{p \in T} 1/p)$, which
is below any $\varepsilon$ for $T$ large because $\sum_{p\in P} 1/p = \infty$. $E$ is contained in this
set for every $T$.

**Item 3.** PNT+'s `prime_between` with $\varepsilon = 1/K$ gives $x_0$; for $km \ge x_0$ there is a prime
in $(km, (1 + 1/K)km) \subseteq (km, (k+1)m)$ as $k < K$.

**Item 4.** Mathlib: $\pi(y) \le \log 4 \cdot y/\log\sqrt y + \sqrt y$, and $\sqrt y \le 2y/\log y$. Dyadic
blocks: $\sum_{2^j < p \le 2^{j+1}} 1/p \le \pi(2^{j+1})/2^j \le \frac{2C_0}{(j+1)\log 2}$, summed with
$H_J \le 1 + \log J$. A semiprime $m = pq \le x$, $p = \operatorname{minFac} m \le q$, has $p \le \sqrt x$,
$q \le x/p$, so the count is at most $\sum_{p \le \sqrt x} \pi(x/p)$, and $\log(x/p) \ge \log\sqrt x$ up to
a factor 2.

## 4. Worked example: A065255

B = $\{n \ge 1 : \sigma(n) \equiv n \pmod{10}\}$, conjecture $b(k)/k \to 10$. If a prime $p \equiv 9
\pmod{10}$ divides $n$ exactly once then $10 \mid \sigma(n)$, so $n \in B \iff 10 \mid n$
(`A065255_iff`, elementary). Item 1 with $q = 10$, $a = 9$ and item 2 with $G_p(n) = (p \,\|\, n)$
(true for the $p - 1$ residues $p, 2p, \ldots, (p-1)p$ mod $p^2$) make the exceptional set density 0
(`A065255_exceptional_density_zero`). `tendsto_density_of_eq_off` with the multiples of 10 gives
density 1/10 (`A065255_density`) and `tendsto_nth_div_of_density` gives $b(k)/k \to 10$
(`A065255_main`). File: `OEIS/A065255/A065255_mathlib.lean`, 116 lines.

## 5. Lean names

| name | statement |
|---|---|
| `not_summable_one_div_prime_residue` | `IsUnit a → ¬ Summable (fun n => if n.Prime ∧ (n : ZMod q) = a then 1/n else 0)` |
| `not_summable_one_div_prime_mod` | the same with `n % q = a % q`, `a.Coprime q`, `0 < q` |
| `count_mul_of_periodic`, `count_le_of_periodic`, `le_count_of_periodic` | counting a predicate of `n % M` |
| `tendsto_count_div_of_periodic` | its density is `count p M / M` |
| `count_dvd_mul`, `count_not_dvd_mul` | `#{n < q m : q ∣ n} = m`, `#{n < q m : q ∤ n} = m (q - 1)` |
| `count_and_of_coprime`, `count_forall_prod` | Chinese remainder counting |
| `density_zero_of_sieve` | item 2 |
| `exists_prime_block` | item 3 |
| `pi_le_div_log`, `primeCounting_eq_card`, `sum_inv_primes_le` | Chebyshev and dyadic Mertens bounds |
| `IsSemiprime`, `semiprime_structure`, `semiprime_count_le`, `semiprime_count_bound` | semiprime counts |
| `density_zero_or`, `count_le_count_add`, `tendsto_density_of_eq_off`, `tendsto_nth_div_of_density` | bookkeeping |

Axioms propext, Classical.choice, Quot.sound (`lib/test/PNTAppsAxioms.lean`). Used by OEIS A065255,
A200982, A204770 (items 1–2; A204770 with $G_q(n) = (q \,\|\, 24n + 10)$ and Mathlib's
`Nat.eq_sq_add_sq_iff`), A131194 and A133835 (item 3), A181674 (item 4).
