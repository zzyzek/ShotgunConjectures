# OEIS A139043: sum of composites ≤ 10^n versus 10^n(10^n+1)/2 - 1 - (10^n)^2/(2 log 10^n - 1)

**Source.** OEIS [A139043](https://oeis.org/A139043): a(n) = sum of the composite numbers ≤ 10^n.
Conjecture (Cino Hilliard, 2008): "10^n(10^n+1)/2 - 1 -(10^n)^2/(2*log(10^n)-1) -> a(n) as n ->
infinity. Here (10^n)^2/(2*log(10^n)-1) is also conjectured to -> sum of primes < 10^n ..."
(OEIS text, CC BY-SA 4.0.)

**Reading.** "→" can mean asymptotic equivalence (ratio → 1) or difference → 0. With x = 10^n and
S(x) = sum of primes ≤ x, a(n) = x(x+1)/2 - 1 - S(x), so the left side minus a(n) equals
S(x) - x^2/(2 log x - 1).

**Result.**
- Ratio reading: true. For the main statement it is immediate (both sides are ~ x^2/2, since
  S(x) ≤ x π(x) = o(x^2)); for the parenthetical statement S(x) ~ x^2/(2 log x - 1) it is the
  prime number theorem.
- Difference reading: false for both. S(x) - x^2/(2 log x - 1) ~ x^2/(8 log^3 x) → ∞.

**Argument.** By the PNT with the de la Vallée Poussin error term and partial summation,
S(x) = li(x^2) + O(x^2 exp(-c √(log x))). With L = log x, li(x^2) = x^2/(2L) + x^2/(4L^2) +
x^2/(4L^3) + O(x^2/L^4), while x^2/(2L - 1) = x^2/(2L) + x^2/(4L^2) + x^2/(8L^3) + O(x^2/L^4).
The difference is x^2/(8L^3)(1 + o(1)). (The scan argued failure of the difference reading from
oscillation of the error term; the third-order term gives it directly.)

**Evidence.**
- `certificate/a139043.py`: S(10^n) for n ≤ 8 by sieve; ratio S/approx = 1.0007 at 10^8 and the
  difference 2.03·10^11 against x^2/(8 log^3 x) = 2.0·10^11.
- Lean + Mathlib: [`A139043_mathlib.lean`](A139043_mathlib.lean), all four claims, with the prime number
  theorem from the vendored PrimeNumberTheoremAnd library (`lib/PNTPlus`, rev 127b50e3).
  - `A139043_ratio`: main statement, ratio reading (S(x) ≤ x·π(x) and Chebyshev's bound).
  - `A139043PNT.A139043_primes_ratio`: parenthetical statement, ratio reading, S(10^n)/(x²/(2 log x − 1)) → 1
    (θ ~ x, summation by parts for Σ p log p, then log p between (1 − η) log x and log x).
  - `A139043PNT.A139043Diff.A139043_primes_difference` and `A139043_main_difference`: S(10^n) − x²/(2 log x − 1)
    → +∞, and approx(n) − a(n) is the same quantity, so both differences tend to +∞ (θ(x) − x = O(x/log⁴ x)
    from `StrongPNT`, Abel summation against n/log n, and Σ_{n≤N} n/log n ≥ F(N) − F(3) with
    F(t) = t²/(2 log t) + t²/(4 log² t) + t²/(4 log³ t) by the mean value theorem).
  Axioms of every theorem: propext, Classical.choice, Quot.sound. Checked with tools/leancheck-mathlib.sh, no
  warnings.
- Outside Lean: that the Lean statements match the entry's text (S(x) is the sum of primes ≤ x, equal to the
  sum of primes < x for x = 10^n, n ≥ 1).

**Review level.** `lean-proof` (2026-11-07; previously `lean-witness` for the main ratio statement only).

**Depends on.** Prime number theorem (ratio) and PNT with error term O(x exp(-c√log x)) (difference), both
from the vendored PrimeNumberTheoremAnd (`lib/PNTPlus`), not from Mathlib.

**Prior art.** Verdict partly-known, immediate (OEIS status conjecture; searched 2026-11-04). The expansion is in the literature; the conclusion for this entry (ratio true, difference false) is not stated. Sources: [OEIS A139043 (fetched 2026-11-04)](https://oeis.org/A139043): still says Conjecture; [C. Axler, arXiv:1606.06874, eq. (1.4)](https://arxiv.org/abs/1606.06874): S(x) = x^2/(2L) + x^2/(4L^2) + x^2/(4L^3) + O(x^2/L^4), from which both readings follow in one line. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; Google/arXiv: sum of primes asymptotic expansion.
