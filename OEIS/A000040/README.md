# OEIS A000040: prime(n) = (6f + (-1)^f - 3)/2 with f = floor(prime(n)/3) + 1

**Source.** OEIS wiki Talk:Conjectures/List, entry for [A000040](https://oeis.org/A000040) (line 16):
"Conjecture: a(n) = (6*f(n)+(-1)^f(n)-3)/2, n>2, where f(n) = floor(ithprime(n)/3)+1. See A181709."
(OEIS text, CC BY-SA 4.0.) The current A000040 entry no longer carries this comment.

**Result.** True; trivial.

**Argument.** A prime p ≥ 5 is 6m+1 or 6m+5. For p = 6m+1, f = 2m+1 (odd) and
(6(2m+1) − 1 − 3)/2 = 6m+1. For p = 6m+5, f = 2m+2 (even) and (6(2m+2) + 1 − 3)/2 = 6m+5.

**Evidence.**
- Lean: [`A000040.lean`](A000040.lean) proves the formula for every p ≡ ±1 (mod 6) and that
  every prime p > 3 (divisor definition) is ≡ ±1 (mod 6). Axioms: propext, Quot.sound. Nothing outside Lean.
- `certificate/check.py`: all primes 5 ≤ p < 10^6.

**Review level.** `lean-proof`.
**Prior art.** New in the sense that no source states it, but trivial (primes > 3 are 6m +- 1). The comment is no longer in [A000040](https://oeis.org/A000040), so OEIS has nothing open here. Checked 2026-11-04.
