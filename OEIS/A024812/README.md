# OEIS A024812: A024812(k) = (A024813(k) + k − 1)/2

**Source.** [A024812](https://oeis.org/A024812), comment by L. E. Jeffery (2013): "Conjecture (verified for
k <= 10^6 by M. F. Hasler): A024812(k) = (A024813(k)+k-1)/2, k=1,2,...." (OEIS text, CC BY-SA 4.0.)
A024812 = values n taken by f(m) = floor(cot(π/(2m))) for exactly one m; A024813 = the m with
f(m−1) < f(m) < f(m+1).

**Result.** True. Proved in the OEIS by H. Rungta (A024813, Oct 2026); re-derived here. (Barker's 2014
recurrence for A024812 is a separate claim, already marked false in the entry.)

**Argument.** g(x) = cot(π/(2x)) has g'(x) = (2/π)·((π/(2x))/sin(π/(2x)))^2, decreasing in x ≥ 2 with
2/π < g' ≤ π/4. By the mean value theorem g(m+1) − g(m) < 1 and g(m+2) − g(m) > 1 for m ≥ 2, and
f(1) = 0, f(2) = 1. So f is nondecreasing, hits every positive integer, each once or twice. If
n = A024812(k) is taken once, at m = A024813(k), then the positions 1..m hold f(1) = 0, the n − 1 values
1..n−1 (k − 1 of them once, n − k twice) and n itself: m = 1 + (k−1) + 2(n−k) + 1 = 2n − k + 1.

**Evidence.**
- `certificate/check.py` (mpmath, 40 digits): every value taken at most twice and the identity for all
  k with A024813(k) < 2·10^5.
- Lean (Mathlib): [`A024812_mathlib.lean`](A024812_mathlib.lean), theorem `A024812_conjecture`: with
  f(m) = ⌊cot(π/(2m))⌋, for every m ≥ 2 with f(m−1) < f(m) < f(m+1), the index k₁ of m among such positions
  equals the index k₂ of f(m) among the values taken exactly once (`onceVal_iff`), and 2f(m) = m + k₁ − 1. The
  analysis uses 1/θ − θ/2 ≤ cot θ < 1/θ on (0, π/2] (no mean value theorem needed). Nothing outside Lean.

**Review level.** `lean-proof`.
**Prior art.** Proof in OEIS A024813 (H. Rungta, Oct 04 2026), checked 2026-11-01; A024812 still says "Conjecture".
Resolved by others.
