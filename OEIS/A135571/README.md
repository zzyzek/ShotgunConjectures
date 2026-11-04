# OEIS A135571: differences of two positive triangular numbers in an odd number of ways

**Source.** OEIS [A135571](https://oeis.org/A135571): positive integers that are the difference of
two positive triangular numbers in an odd number of ways. Conjecture: "This sequence is just the
sequence of positive integers that are either square, twice a square, or triangular, but not both
square and triangular (A001110)." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** T(a) - T(b) = (a-b)(a+b+1)/2. Put d = a - b ≥ 1 and e = a + b + 1, so 2n = d e with d,
e of opposite parity and e > d. Conversely each such factorisation gives a, b ≥ 0. Factorisations
2n = d e with d < e of opposite parity correspond to the odd divisors of n (the odd one of d, e is
an odd divisor of n, and the pair is determined by it), so there are d_odd(n) of them. b = 0 means
e = d + 1, i.e. 2n = d(d+1), which happens (once) iff n is triangular. So the number of
representations with b ≥ 1 is r(n) = d_odd(n) - [n triangular].
d_odd(n) = d(odd part of n) is odd iff the odd part is a square iff n is a square or twice a
square. Hence r(n) is odd iff exactly one of "n is a square or twice a square" and "n is
triangular" holds. A twice-square is never triangular (k(k+1)/2 = 2m^2 means k(k+1) = (2m)^2, a
product of consecutive positive integers, which is never a square), and no n is both a square and
twice a square. So r(n) is odd iff n is a square, twice a square, or triangular, but not both a
square and triangular: the conjectured set.

**Evidence.**
- `certificate/a135571.py`: brute-force count for n ≤ 20000 equals the characterisation.
- Lean (Mathlib): [`A135571_mathlib.lean`](A135571_mathlib.lean), `A135571_main`: for every n ≥ 1, the number of pairs 1 ≤ b < a with T(a) - T(b) = n is odd iff n is a square, twice a square or triangular, but not both a square and triangular. Nothing outside Lean.

**Review level.** `lean-proof` (Mathlib file above).

**Prior art.** Verdict partly-known, immediate (OEIS status conjecture; searched 2026-11-04). The odd-divisor count is classical (Sylvester); the parity characterisation follows in a few lines but is not stated anywhere found. Sources: [OEIS A135571 (fetched 2026-11-04)](https://oeis.org/A135571): still says Conjecture; Verhoeff link covers the exactly-one-way case; [T. Verhoeff, Rectangular and Trapezoidal Arrangements, JIS 2 (1999) 99.1.6](https://cs.uwaterloo.ca/journals/JIS/trapzoid.html): classical count: representations as sums of consecutive integers = number of odd divisors. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; Google: difference of two triangular numbers number of ways.
