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
- Lean (Mathlib, partial): [`A139043_mathlib.lean`](A139043_mathlib.lean), theorem `A139043_ratio`: the main
  statement in the ratio reading, a(n)/(x(x+1)/2 − 1 − x²/(2 log x − 1)) → 1 for x = 10^n (via S(x) ≤ x·π(x) and
  Chebyshev's bound). Outside Lean: the parenthetical S(x) ~ x²/(2 log x − 1) (prime number theorem) and the
  failure of the difference reading (PNT with error term).

**Review level.** `lean-witness`.

**Depends on (Mathlib).** Prime number theorem (ratio); PNT with error term O(x exp(-c√log x)) for
the difference statement.

**Prior art.** Verdict partly-known, immediate (OEIS status conjecture; searched 2026-11-04). The expansion is in the literature; the conclusion for this entry (ratio true, difference false) is not stated. Sources: [OEIS A139043 (fetched 2026-11-04)](https://oeis.org/A139043): still says Conjecture; [C. Axler, arXiv:1606.06874, eq. (1.4)](https://arxiv.org/abs/1606.06874): S(x) = x^2/(2L) + x^2/(4L^2) + x^2/(4L^3) + O(x^2/L^4), from which both readings follow in one line. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; Google/arXiv: sum of primes asymptotic expansion.
