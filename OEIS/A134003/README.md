# OEIS A134003: n(n+5) = a(a+5) + b(b+5) has no positive solution when n^2 + (n+5)^2 is prime

**Source.** OEIS [A134003](https://oeis.org/A134003) (n with n^2 + (n+5)^2 prime). Conjecture
(Layman, 2007): "If n is in this sequence then n(n+5)=a(a+5)+b(b+5) is not solvable in
integers." (OEIS text, CC BY-SA 4.0.)

**Reading.** Literally ("in integers") it is false for every n: a = n, b = 0 is a solution (and
b = -5 as well). The intended reading, matching the definition of the complementary A134002, is
positive integers a, b.

**Result.** True for positive a, b; false as literally worded.

**Argument.** As in OEIS-A134002: 2M = (2n+5)^2 + 5^2 with M = n^2 + (n+5)^2, and a positive
solution is a representation 2M = X^2 + Y^2 with X, Y odd ≥ 7. For M prime the only
representation of 2M is {2n+5, 5} (uniqueness of the two-squares representation of the prime M,
transported by X = u+v, Y = u-v), so there is none.

**Evidence.** `certificate/a134002.py` (brute force n ≤ 3000, also covers this entry). Lean (Mathlib):
[`A134003_mathlib.lean`](A134003_mathlib.lean), theorem `A134003_positive`: if n^2 + (n+5)^2 is prime there are
no positive a, b with n(n+5) = a(a+5) + b(b+5) (uniqueness of the two-squares representation of a prime is proved
in the file, `sq_add_sq_unique`); `A134003_literal_false` is the identity n(n+5) = n(n+5) + 0(0+5). Nothing
outside Lean.

**Review level.** `lean-proof`.

**Depends on (Mathlib).** Uniqueness of the representation of a prime as a sum of two squares.

**Prior art.** Verdict partly-known (OEIS status conjecture; searched 2026-11-04). As A134002; the literal 'in integers' reading is false (b = 0), which nobody has noted. Sources: [OEIS A134003 (fetched 2026-11-04)](https://oeis.org/A134003): still says Conjecture ('in integers'), unchanged since 2013; [W. Sierpinski (1963), via OEIS A012132 and Tsangaris (1998)](https://oeis.org/A012132): the analogue for x(x+1)+y(y+1) = z(z+1): solvable iff z^2+(z+1)^2 composite. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; OEIS A012132, A027861; Google: n(n+5)=a(a+5)+b(b+5).
