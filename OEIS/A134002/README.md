# OEIS A134002: n(n+5) = a(a+5) + b(b+5) is solvable iff n^2 + (n+5)^2 is composite

**Source.** OEIS [A134002](https://oeis.org/A134002): positive n such that
n(n+5) = a(a+5) + b(b+5) is solvable in positive integers. Conjecture (Layman, 2007): "If n a
positive integer not a term of this sequence, then n^2+(n+5)^2 is prime." (OEIS text,
CC BY-SA 4.0.)

**Result.** True, and the converse holds as well: with M = n^2 + (n+5)^2, the equation has a
solution in positive integers iff M is composite (see also OEIS-A134003).

**Argument.** Multiply by 4 and add 50: 2M = (2n+5)^2 + 5^2, and a solution is the same as
2M = X^2 + Y^2 with X = 2a+5, Y = 2b+5 odd and ≥ 7. M is odd (n and n+5 have opposite
parity). Representations 2M = X^2 + Y^2 with X ≥ Y ≥ 1 correspond to M = u^2 + v^2 with
u > v ≥ 0 via X = u+v, Y = u-v. The trivial one is (u, v) = (n+5, n), i.e. {2n+5, 5}.
- M prime: the representation of a prime as a sum of two squares is unique, so 2M has only
  {2n+5, 5}; Y = 5 means b = 0. No solution.
- 5 ∤ n, M composite: gcd(n, n+5) = 1, so every prime factor of M is ≡ 1 (mod 4) and
  r_2(M) = 4 d(M) ≥ 12. Counting (u, v) with u > v ≥ 0 gives at least 2 representations of M
  (d(M) ≥ 4 if M is not a square, d(M) ≥ 3 and the extra (√M, 0) if it is). The second one
  gives {X, Y} ≠ {2n+5, 5}; Y ≠ 5 (else X = 2n+5); Y = 1 or 3 would make (2n+5)^2 + 24 or
  (2n+5)^2 + 16 a square, impossible for n ≥ 1 (factor the difference of squares). So X, Y ≥ 7.
  (M = p^2 gives X = Y = p, i.e. a = b = (p-5)/2 ≥ 4.)
- n = 5m: 2M = 25((2m+1)^2 + 1) = (6m+7)^2 + (8m+1)^2, so a = 3m+1, b = 4m-2 ≥ 2; and
  M = 25(m^2 + (m+1)^2) is composite.

**Evidence.**
- `certificate/a134002.py`: brute-force solvability versus compositeness of M for n ≤ 3000, no
  mismatch. `certificate/scan_check.py`: the scan's check (to n = 6000).
- Lean (Mathlib): [`A134002_mathlib.lean`](A134002_mathlib.lean), theorem `A134002_iff`: for n ≥ 1 the equation has
  a positive solution iff n^2 + (n+5)^2 is not prime (`A134002_conjecture` is the stated direction). The two-squares
  facts below are covered by Mathlib (−1 a square mod M ⇒ every divisor is a sum of two squares) plus lemmas proved
  in the file (prime uniqueness, a second Brahmagupta representation). Nothing outside Lean.

**Review level.** `lean-proof` (argument re-derived independently, including the M = p^2 case the
scan's note flagged as the weak point; numerics to 3000).

**Depends on (Mathlib).** Uniqueness of the two-squares representation of a prime; r_2(M) = 4 d(M)
for M with all prime factors ≡ 1 (mod 4) (or: a composite such M has two representations,
via Gaussian integers).

**Prior art.** Verdict partly-known (OEIS status conjecture; searched 2026-11-04). Sierpinski proved the +1 analogue; the +5 version (and its converse) is not stated anywhere found, though the method is the same. Sources: [OEIS A134002 (fetched 2026-11-04)](https://oeis.org/A134002): still says Conjecture, unchanged since 2009; [W. Sierpinski (1963), via OEIS A012132 and Tsangaris (1998)](https://oeis.org/A012132): the analogue for x(x+1)+y(y+1) = z(z+1): solvable iff z^2+(z+1)^2 composite. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; OEIS A012132, A027861; Google: n(n+5)=a(a+5)+b(b+5).
