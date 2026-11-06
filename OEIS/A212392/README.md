# OEIS A212392: n divides a(n) for A(x) = (x + A(A(x)))^2

**Source.** OEIS [A212392](https://oeis.org/A212392), "Conjecture: n divides a(n); see A212391." (P. D. Hanna,
2012).

**Result.** True. Proved together with A212425 and the general form for every exponent b ≥ 2 in
[`../A212425/`](../A212425/README.md); the b = 2 case is the Lean theorem `A212392_b2` in
[`../A212425/A212425_mathlib.lean`](../A212425/A212425_mathlib.lean).
