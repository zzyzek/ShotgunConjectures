# OEIS A133212: a(n) = 2*A038503(n+3) for n > 0

**Source.** OEIS [A133212](https://oeis.org/A133212): a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3)
for n > 3, a(0..3) = 1, 4, 12, 32. Conjecture (R. J. Mathar, 2007): "a(n)=2*A038503(n+3) if
n>0." (OEIS text, CC BY-SA 4.0.) A038503(m) = sum_k C(m, 4k).

**Result.** True.

**Argument.** Roots-of-unity filter: A038503(m) = (2^m + (1+i)^m + (1-i)^m + 0^m)/4. For
m ≥ 1 the 0^m term vanishes, so b(m) = A038503(m) satisfies the recurrence with
characteristic polynomial (x - 2)(x^2 - 2x + 2) = x^3 - 4x^2 + 6x - 4 for m ≥ 4. Hence
n ↦ 2b(n+3) and a(n) satisfy the same order-3 recurrence for n ≥ 4, and both equal 4, 12, 32 at
n = 1, 2, 3. (At n = 0 they differ: a(0) = 1, 2b(3) = 2, matching "if n > 0".)

**Evidence.**
- [`A133212.lean`](A133212.lean): `decide` check of a(n) = 2b(n+3) for 1 ≤ n ≤ 40 with b
  computed from binomial sums (n = 1, 2, 3 suffice). Outside Lean: the order-3 recurrence of
  A038503 (roots-of-unity filter), which turns the check into a proof (METHODS §6).
- `certificate/a133212.py`: agreement for n < 300.
- Lean (Mathlib): [`A133212_mathlib.lean`](A133212_mathlib.lean), `A133212_main`: for every n ≥ 1, a(n) = 2·A038503(n+3), both sequences defined from their OEIS definitions (the recurrence; Σ_k C(m,4k)). The order-3 recurrence of A038503 is proved there (Pascal's rule on the four residue sums); nothing outside Lean.

**Review level.** `lean-proof` (Mathlib file above).

**Prior art.** Verdict new, immediate (OEIS status conjecture; searched 2026-11-04). Both sides satisfy the same recurrence (stated in the two entries); matching initial terms is the whole proof, not written anywhere. Sources: [OEIS A133212 (fetched 2026-11-04)](https://oeis.org/A133212): Mathar's conjecture unchanged; Mathar/Fischer g.f. present; [OEIS A038503 (fetched 2026-11-04)](https://oeis.org/A038503): Barry 2004: same recurrence a(n)=4a(n-1)-6a(n-2)+4a(n-3). Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; OEIS A038503.
