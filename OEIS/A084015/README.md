# OEIS A084015: no term is zero

**Source.** [A084015](https://oeis.org/A084015) (Amarnath Murthy and Meenakshi Srikanth, May 23 2003): largest n-digit
palindromic multiple of n; for n = 10k palindromic with leading zeros ignored; 0 if none exists. "Conjecture: no
entry is zero." (OEIS text, CC BY-SA 4.0, checked 2026-11-07.)

**Result.** True. A term is 0 only if no admissible n-digit multiple of n exists, and the companion entry
[A084013](../A084013/README.md) (smallest such number) proves that one always exists. Same reading as there; it
reproduces a(1..10) = 9, 88, ..., 9999999990.

**Evidence.** Lean (Mathlib): [`../A084013/A084013_mathlib.lean`](../A084013/A084013_mathlib.lean), theorem
`A084013.A084013_main`; check and certificate as in A084013 (`certificate/check.py` there also reproduces the
A084015 data for n <= 10). Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** As for A084013 (checked 2026-11-07): no proof found.
