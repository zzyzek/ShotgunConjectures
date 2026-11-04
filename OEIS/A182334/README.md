# OEIS A182334: the order-9 recurrence fails at n = 10, 11 (holds from n = 12)

**Source.** OEIS [A182334](https://oeis.org/A182334): triangular numbers that differ from a square
by 1 (0, 1, 3, 10, 15, 120, 325, 528, 4095, 11026, 17955, ...; offset 1). Formula (Greathouse,
2012, a conjecture when added, now printed without qualification): "a(n) = 35*a(n-3) -
35*a(n-6) + a(n-9)." (OEIS text, CC BY-SA 4.0.)

**Result.** False as printed: at n = 10, a(10) = 11026 but 35a(7) - 35a(4) + a(1) = 11025; at
n = 11, a(11) = 17955 but the right side is 17956. It holds for all n ≥ 12 (proof sketch below,
checked to 10^60).

**Argument.** Failure: direct computation. Corrected statement: T = k(k+1)/2 = s^2 ± 1 is
x^2 - 8s^2 = 9 or -7 with x = 2k + 1. Each solution class is x_j = c β^j + c̄ β^(-j),
β = 3 + √8, so T = (x^2 - 1)/8 restricted to a class is annihilated by (t - 1)(t^2 - 34t + 1).
Three classes interleave with period 3 once the β^(-j) terms are small, giving the annihilator
(t^3 - 1)(t^6 - 34 t^3 + 1) = t^9 - 35t^6 + 35t^3 - 1. The smallest terms (0, 1, 3) are where
classes collide or fail to interleave, which is why n = 10, 11 fail. Barker's g.f. in the entry
has numerator degree 11 over a degree-9 denominator, so it also only implies the recurrence for
n ≥ 12.

**Evidence.**
- [`A182334.lean`](A182334.lean): the triangular numbers T(k), k < 190, that are s^2 ± 1 are
  exactly the first 11 terms, and both failures (`decide +kernel`). Outside Lean: the corrected
  statement for n ≥ 12.
- [`A182334_mathlib.lean`](A182334_mathlib.lean) (Mathlib): `A182334_main` proves the full
  result for a(n) = `Nat.nth` of the set of triangular numbers equal to s^2 ± 1: the set is
  infinite, a(1..11) are the listed values, the recurrence fails at n = 10, 11 and holds for every
  n ≥ 12. Descent by 3 - √8 shows every solution of x^2 - 8s^2 = 9 or -7 lies on the orbit of
  (3, 0), (1, 1) or (5, 2) under (x, s) ↦ (3x + 8s, x + 3s); the orbits interleave with period 3
  from a(4) on, and T = x^2/8 obeys the order-3 recurrence on each orbit. Outside Lean: nothing.
- `certificate/a182334.py`: brute force over k < 10^6 (25 terms), the recurrence fails exactly at
  n = 10, 11 in that range. `certificate/pell_check_1e60.py` (scan): all terms below 10^60 from the
  Pell orbits; recurrence holds for every n ≥ 12 there.

**Review level.** `lean-proof` ([`A182334_mathlib.lean`](A182334_mathlib.lean): failure at
n = 10, 11 and the recurrence for all n ≥ 12, with the Pell-class descent and the period-3
interleaving proved in Lean). Previously `lean-witness` for the failure and `rechecked`
(numerically) for n ≥ 12.

**Prior art.** Partly known. [OEIS A182334](https://oeis.org/A182334) (fetched 2026-11-04) prints the recurrence without range; the entry's own g.f. (Barker, 2016) and Magma program are consistent with validity only from n = 12, but the failure at n = 10, 11 is not noted anywhere found. Searched: entry, OEIS cross-reference search (A001110, A072221, A006451), edit history. Worth an OEIS correction (add 'for n > 11'). (Prior-art review 2026-11-04.)
