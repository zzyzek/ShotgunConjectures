# OEIS A197170: every n is gcd(k, y) for the fundamental unit of some Q(sqrt k)

**Source.** [A197170](https://oeis.org/A197170) (Artur Jasinski, 2011): smallest k such that the fundamental unit
(x + y w) or (x + y w)/2, w = sqrt(k), of Q(sqrt(k)) obeys gcd(k, y) = n. "Conjecture: For every n such a
quadratic field with minimum k exists." (OEIS text, CC BY-SA 4.0, fetched 2026-11-07.)

**Reading.** k runs over nonsquare integers, not only squarefree ones (k = 248 is a term). The entry's examples
(k = 6, 69, 248, 115, 511) write the field's fundamental unit in terms of w = sqrt(k), e.g. 63 + 8 sqrt(62) =
63 + 4 w for k = 248. When the coefficient of sqrt(k) is not integral the entry's data use another convention
(k = 54, 112 are treated differently from the order unit), and the printed minima depend on it. The conjecture
asks only for existence; the construction below has an integral coefficient of sqrt(k), so all readings agree on
it: (R1) fundamental solution of x^2 - k y^2 = +-4, and (R2) fundamental unit of the field Q(sqrt k) written
in w. The printed minima a(n) are not re-derived.

**Result.** True for every n >= 1. Take v >= 1 odd with gcd(v, n) = 1 and d0 = n^4 v^2 + 2 squarefree, and
k = n^2 d0. Then the fundamental unit of Q(sqrt k) = Q(sqrt d0) is (A^2 + 1) + A sqrt(d0) = (A^2 + 1) + n v w with
A = n^2 v, so y = n v and gcd(k, y) = n. Such v exists for every n (least v <= 5 for n <= 300).

**Argument.** For any nonsquare D = A^2 + 2 with A >= 2, sqrt(D) = [A; A, 2A] (period 2: 1/(sqrt D - A) =
(sqrt D + A)/2 has integer part A, and 2/(sqrt D - A) = sqrt D + A has integer part 2A), so the least solution
of x^2 - D y^2 = +-1 is the first convergent (A^2 + 1, A), of norm +1. For squarefree D = 2, 3 mod 4 (here
D = n^4 v^2 + 2 = 2 or 3 mod 4) the ring of integers is Z[sqrt D], so this is the fundamental unit of the field.
gcd(k, n v) = n gcd(n d0, v) = n, since gcd(v, n) = 1 and gcd(d0, v) = gcd(2, v) = 1.
Existence of v: F(v) = n^4 v^2 + 2 is irreducible and has no fixed square divisor on the progression v odd,
gcd(v, n) = 1 (p odd, p | n: F = 2 mod p; p = 2: F = 2 or 3 mod 4), so it takes squarefree values on that
progression for a positive proportion of v (Estermann 1931, Ricci 1933 for quadratic polynomials).
Under reading R1 alone the squarefree condition is unnecessary: k = n^4 + 2n (n odd), n^4/4 + n (n = 2 mod 4),
9n^4/4 + 3n (n = 0 mod 4), k = 2 (n = 1) have period-2 expansions [A; 2A/m, 2A] with m = 2n, n, 3n/4 and
give gcd(k, y) = n unconditionally (family.py).

**Evidence.** [`certificate/field.py`](certificate/field.py): least v for n <= 300 (max 5), the Pell identity and
gcd for each, and the unit's minimality by brute force for n <= 12. [`certificate/family.py`](certificate/family.py):
the R1 family against brute-force fundamental solutions for n <= 40. Lean: none. Outside Lean: the period-2
continued fraction argument, the identification of the ring of integers, and Estermann-Ricci (squarefree values
of quadratic polynomials) for general n.

**Review level.** `rechecked`.

**Prior art.** Checked 2026-11-07. The entry and A197127/A197169 give no proof. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones, 2026-11-06). The construction uses
only the classical Richaud-Degert unit for D = A^2 + 2.
