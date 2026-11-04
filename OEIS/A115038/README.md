# OEIS A115038: every prime is y^k − x^2

**Source.** [A115038](https://oeis.org/A115038) (smallest x with x² + prime(n) a perfect power), comment:
"Conjecture: There will always be an x,y,n such that x^2 + p = y^n for all primes p. ..." (OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial (squares count as perfect powers, as the entry's data shows).

**Argument.** For odd p, ((p−1)/2)² + p = ((p+1)/2)²; for p = 2, 5² + 2 = 3³.

**Evidence.**
- Lean: [`A115038.lean`](A115038.lean): both cases. Nothing outside Lean.
- `certificate/check.py`: primes below 10^6.

**Review level.** `lean-proof`.
**Prior art.** Verdict known, immediate (OEIS status conjecture; searched 2026-11-04). Triviality; squares count as perfect powers per the entry's own data. Sources: [OEIS A115038 (fetched 2026-11-04)](https://oeis.org/A115038): conjecture text unchanged; Israel's 2026 formula restates the definition; [classical: every odd number is a difference of consecutive squares](https://en.wikipedia.org/wiki/Square_number): p = ((p+1)/2)^2 - ((p-1)/2)^2. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history.
