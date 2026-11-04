# OEIS A210826: multiplicative with Dirichlet g.f. ζ(3s)/ζ(s)

**Source.** OEIS [A210826](https://oeis.org/A210826): defined by sum_{n≥1} a(n) x^n/(1 - x^n) =
sum_{n≥1} x^(n^3). Conjecture (Mathar, 2012): "this is a multiplicative sequence with Dirichlet
g.f. zeta(3s)/zeta(s) and inverse Mobius transform in A010057." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Comparing coefficients of x^n, the Lambert series says sum_{d|n} a(d) = [n is a cube]
= A010057(n), i.e. the inverse Möbius transform of a is A010057, and a = μ * A010057 (Dirichlet
convolution). Both factors are multiplicative, so a is; its Dirichlet series is
ζ(3s) · (1/ζ(s)). At prime powers a(p^e) = [3 | e] - [3 | e - 1] = -1 + ((e + 2) mod 3) (the
formula now in the entry, Cloitre 2012).

**Evidence.**
- `certificate/a210826.py`: the Lambert coefficients (by recursion over divisors) equal the
  multiplicative formula for n ≤ 20000.
- Lean (Mathlib): [`A210826_mathlib.lean`](A210826_mathlib.lean), `A210826_main`: any a : N -> Z with sum_{d | n} a(d) = [n is a cube] (n >= 1) is multiplicative, equals mu * (cube indicator), has a(p^e) = -1 + ((e + 2) mod 3), and has L-series zeta(3s)/zeta(s) for Re s > 1.
- `A210826_main` takes the divisor-sum form as the definition; the coefficient extraction from the Lambert series is proved in `A210826_lambert_main` (next item).
- Lean (Mathlib), added: `A210826_lambert_main` in the same file takes the OEIS definition itself as hypothesis (the Lambert series identity in ℚ⟦X⟧ with the X-adic topology, as two `HasSum` families with the same sum) and derives the four conclusions; `A210826_divisor_sum` does the coefficient extraction. Nothing outside Lean.

**Review level.** `lean-proof` (Mathlib file above).

**Prior art.** Known. [OEIS A210826](https://oeis.org/A210826) (fetched 2026-11-04) states it as established (Cloitre, 2012: multiplicative formula, 'thus the Dirichlet g.f. is indeed zeta(3s)/zeta(s)'). Searched: entry, OEIS cross-reference search. (Prior-art review 2026-11-04.)
