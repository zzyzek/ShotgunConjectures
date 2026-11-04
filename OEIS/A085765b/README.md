# OEIS A085765: a(n) mod 2 has period 7

**Source.** [A085765](https://oeis.org/A085765) (partial sums and bisection of A086450), comment:
"Conjecture: a(n) mod 2 repeats the 7-pattern 0,0,1,1,1,0,1." (OEIS text, CC BY-SA 4.0.) (The entry's
other conjecture, log a(n)/log n unbounded, is a separate item.)

**Result.** True. The entry already notes (L. Herrgesell, 2007) that it follows from the A086450 pattern
proved there; re-derived here.

**Argument.** A086450: b(0) = 1, b(2n+1) = b(n), b(2n) = b(0) + … + b(n). Claim b(n) ≡ P(n mod 7) (mod 2),
P = 1,1,0,1,0,0,1. By strong induction: for odd indices P((2r+1) mod 7) = P(r); for even indices P sums to 4
over a period, so b(0) + … + b(n) ≡ Q(n mod 7) with Q the prefix sums of P mod 2, and P(2r mod 7) = Q(r).
A085765(n) = b(2n) ≡ P(2n mod 7): 1, 0,0,1,1,1,0,1, 0,0,1,1,1,0,1, …

**Evidence.**
- Lean: [`A085765b.lean`](A085765b.lean) (`decide`): the four table facts used in the induction.
  Outside Lean: the strong induction itself and the identification A085765(n) = A086450(2n).
- `certificate/check.py`: both patterns for n < 2·10^4.

**Review level.** `lean-witness`.
**Prior art.** OEIS A086450 (L. Herrgesell, 2007) and the remark in A085765; checked 2026-11-01. Resolved by others.
