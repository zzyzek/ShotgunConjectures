# OEIS A061002: denominator(H(p)/H(p−1)) / numerator(H(p−1)/p^2) = p^3

**Source.** [A061002](https://oeis.org/A061002), comment by G. Detlefs (2013): "Conjecture: If p is the n-th
prime and H(n) is the n-th harmonic number, then denominator(H(p)/H(p-1))/numerator(H(p-1)/p^2) = p^3.
A193758(p)/a(n) = p^3, p > 3." (OEIS text, CC BY-SA 4.0.)

**Result.** True for all primes p ≥ 5.

**Argument.** Write H(p−1) = a/b in lowest terms. Wolstenholme: p^2 | a; also p ∤ b. Then
H(p)/H(p−1) = 1 + b/(pa) = (pa + b)/(pa), and gcd(pa + b, p) = gcd(b, p) = 1, gcd(pa + b, a) = gcd(b, a) = 1,
so the denominator is pa. H(p−1)/p^2 = (a/p^2)/b in lowest terms, numerator a/p^2. Ratio pa/(a/p^2) = p^3.

**Evidence.**
- `certificate/check.py`: exact rationals, all primes 5 ≤ p < 1000.
- Lean (Mathlib): [`A061002_mathlib.lean`](A061002_mathlib.lean), theorem `A061002_conjecture`: for every prime
  p ≥ 5, den(H(p)/H(p−1)) = p^3 · num(H(p−1)/p^2) with that numerator positive, so the ratio is p^3 (H =
  Mathlib `harmonic`). Wolstenholme's theorem (`wolstenholme`: p^2 ∣ num H(p−1), p ∤ den H(p−1)) is proved in the
  file from Wilson's theorem and Σ_{x ∈ ZMod p} x^2 = 0. Nothing outside Lean.

**Review level.** `lean-proof`.
**Prior art.** New as a statement, but a direct corollary of Wolstenholme's theorem. [A061002](https://oeis.org/A061002) still has the conjecture. Searched OEIS entry, references and history. Checked 2026-11-04.
