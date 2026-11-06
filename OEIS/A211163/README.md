# OEIS A211163: numerators of (-1/π^n) ∫_0^1 log(1-1/x)^n dx

The conjecture (the denominators are A141459) is proved, with a Lean proof (`A211163_conjecture`),
in [`../A141459`](../A141459/README.md): the integral equals 2^n B'_n (πi)^n, so (-1/π^n)·∫ = -2^n B'_n i^n,
whose denominator is A141459(n) for n ≥ 2.
