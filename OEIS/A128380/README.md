# OEIS A128380: zeros of A097806^k * tau, all k for n <= 400

**Source.** [A128380](https://oeis.org/A128380), Gary W. Adamson, Feb 28 2007: A097806^24 * A000594. Comment:
among the sequences A097806^k * A000594 only k = 24 has a zero; with the partial-sum operator (A128378, A128379)
zeros occur only for k = 23 and k = 24. (OEIS text, CC BY-SA 4.0, cached entry read 2026-11-08.)

**Reading.** B_k(n) = sum_j C(k, j) tau(n - j) (A097806 = 1s on the diagonal and subdiagonal), g.f.
(1 + x)^k x prod(1 - x^m)^24; S_k(n) = sum_j C(k - 1 + j, j) tau(n - j), g.f. (1 - x)^(-k) x prod(1 - x^m)^24.

**Result (partial; the conjecture stays open).** For every n <= 400 and every integer k >= 0, B_k(n) = 0 only for
(k, n) = (24, 2), and S_k(n) = 0 only for (24, 2) and (23, 4). The three zeros come from vanishing low
coefficients: (1 + x)^24 prod(1 - x^m)^24 = (1 - x^2)^48 prod_{m>=3}(1 - x^m)^24 and (1 - x)^(-24) prod(1 - x^m)^24
= prod_{m>=2}(1 - x^m)^24 have no x^1 term; (1 - x) prod_{m>=2}(1 - x^m)^24 has x^3 coefficient -24 + 24 = 0.

**Argument.** For fixed n, B_k(n) and S_k(n) are polynomials in k of degree n - 1 with integer values; their
nonnegative integer roots are found exactly by PARI `nfroots` (rational roots over Q).

**Evidence.** `certificate/roots.gp` (PARI/GP 2.15+, about 5 min; output `roots.out`); `certificate/zeros.py`
(direct scan k <= 300, n <= 3000, same zeros). No Lean (degree-399 polynomials). Outside Lean: all of it
(PARI factorisation of the root polynomials).

**Open part and obstruction.** The k = 0 member is Lehmer's conjecture (tau(n) != 0); for k >= 1 the
sequences are coefficients of non-eigenform combinations (1 + q)^k Delta(q), with no multiplicativity.

**Review level.** rechecked (two independent computations agree on the overlap).

**Prior art.** Checked 2026-11-08: OEIS entries A128378-A128380, google-deepmind/formal-conjectures (no file).
No range beyond the listed terms found.
