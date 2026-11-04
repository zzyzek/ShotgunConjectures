# OEIS A112992: ceiling(2^r/3) is a Jacobsthal number or one more

**Source.** [A112992](https://oeis.org/A112992), comment: "Conjecture: the odd values of ceiling(2^(2^k mod k)/3) are
Jacobsthal numbers (and the even values are 1 plus a Jacobsthal number)." (OEIS text, CC BY-SA 4.0.)

**Result.** True, for every exponent r (the form r = 2^k mod k plays no role).

**Argument.** With J(n) = (2^n − (−1)^n)/3: for odd r, ceiling(2^r/3) = (2^r + 1)/3 = J(r), which is odd; for even
r ≥ 2, ceiling(2^r/3) = (2^r + 2)/3 = J(r) + 1, which is even; for r = 0 the value is 1 = J(1).

**Evidence.**
- Lean: [`A112992.lean`](A112992.lean) (J by its recurrence): the closed forms, J(n) odd for n ≥ 1, and the full
  statement for every r. Nothing outside Lean.
- `certificate/check.py`: r < 2000 and all k < 10^4.

**Review level.** `lean-proof`.
**Prior art.** Verdict known, immediate (OEIS status resolved-in-entry; searched 2026-11-04). The sister entry A005578 (cross-referenced from A112992) already gives ceiling(2^r/3) = Jacobsthal(r) + [r even]. Sources: [OEIS A112992 (fetched 2026-11-04)](https://oeis.org/A112992): conjecture text unchanged; cross-references A005578 and A001045; [OEIS A005578 (fetched 2026-11-04)](https://oeis.org/A005578): formulas a(n) = 1 + floor(2^n/3) and a(n) = A001045(n) + A000035(n+1), i.e. ceiling(2^r/3) = J(r) + [r even]. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; OEIS A005578, A001045.
