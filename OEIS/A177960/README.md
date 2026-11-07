# OEIS A177960: the m-nomial form of the definition is correct

**Source.** [A177960](https://oeis.org/A177960): numbers A001317(t), excluding t = c*(2^k - 1) with c >= 0, k >= 2.
Rows of the 2^k-nomial triangles mod 2, read as binary numbers, give A001317 (k = 1), A177882, A177897, ...
Conjecture in the entry: "If for every m>=2, to consider triangle of m-nomial coefficients mod 2 converted to
decimal, then the sequence lists terms of A001317 which are not in the union of other sequences for m=3 (A038184),
4 (A177882), 5, 6,..." (OEIS text, checked 2026-11-07.)

**Reading.** Row n of the m-nomial triangle = coefficients of (1 + x + ... + x^(m-1))^n; reduce mod 2 and read the
coefficient of x^i as bit i. A001317(t) is the m = 2 row t.

**Result.** True: x is in A177960 iff x = A001317(t) for some t and x is not a row number of any m-nomial
triangle with m >= 3.

**Argument.** Work in GF(2)[x], P = x + 1, G_m = 1 + x + ... + x^(m-1), so G_m * P = x^m + 1. Bits to number is
injective, so the question is when G_m^n = P^t. Write m = 2^k r with r odd. By Frobenius,
x^m + 1 = (x^r + 1)^(2^k) = (G_r P)^(2^k), hence G_m = G_r^(2^k) P^(2^k - 1).
If G_m^n = P^t with n > 0: P^(t - (2^k-1)n) must be G_r^(2^k n) (the other order makes P a unit); evaluating at
x = 1 (G_r(1) = r = 1, P(1) = 0) gives exponent 0, so G_r is a unit, deg G_r = r - 1 = 0, r = 1, m = 2^k >= 3
forces k >= 2 and t = n(2^k - 1). If n = 0 then t = 0. Conversely G_(2^k)^c = P^(c(2^k-1)).

**Evidence.** [`A177960_mathlib.lean`](A177960_mathlib.lean), main theorem `A177960_conjecture`; `rowNum_eq` proves
that the ℕ-coefficient reading (sum of (coeff mod 2) * 2^i) equals the GF(2) one; `key` is the argument above.
Axioms: propext, Classical.choice, Quot.sound. Outside Lean: nothing beyond reading the definitions.
`certificate/check_data.py` reproduces the 23 data terms (m <= 40, n < 80).

**Review level.** lean-proof.

**Prior art.** No proof found: OEIS A177960, A001317, A177882, A177897 entries; V. Shevelev, arXiv:1011.6083 (Stephan's
conjectures, a different question); web search; google-deepmind/formal-conjectures (HEAD 2026-11-06) and
otoi-lab/oeis-lean-proofs: no entry. Checked 2026-11-07. The key step (G_m is a power of x + 1 over GF(2) only for
m a power of 2) is a standard fact; the write-up and Lean proof are new as far as found.
