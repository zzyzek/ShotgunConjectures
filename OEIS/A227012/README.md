# OEIS A227012 (Kimberling floor-of-means conjectures): the case g(n) = n^3, f(k) = 1/k

**Source.** OEIS [A227012](https://oeis.org/A227012), a(n) = ⌊M(n)⌋ with M(n) the harmonic mean of
(n−1)^3 + 1, ..., n^3. Comment (C. Kimberling, 2013): "Conjecture: if f(k) = u/(v*k + w), where u,v,w are integers,
and g(n) is a polynomial, then the sequence with n-th term m(n) = floor(M(n)) is linearly recurrent", followed by
three refined cases; case (3) is g cubic with recurrence coefficients 3, −3, 1, 1, −3, 3, −1, e.g. A227012. The
entry's formulas (recurrence for n ≥ 10, g.f., closed forms) are marked "conjectured". (OEIS text, CC BY-SA 4.0,
checked 2026-11-06.) This directory also indexes the related records grouped with it in the scan: A219085
(settled, [`../A219085/`](../A219085/README.md)), A225919 (settled, [`../A225919/`](../A225919/README.md)),
A225920–A225922 (open).

**Result (partial).** For the entry's own sequence: a(n) = ((2n−1)^3 + 4) div 8 = ⌊(n − 1/2)^3 + 1/2⌋ for
n ≥ 3 (a(1) = 1, a(2) = 4). Hence the entry's recurrence a(n) = 3a(n−1) − 3a(n−2) + a(n−3) + a(n−4) − 3a(n−5) +
3a(n−6) − a(n−7) holds for n ≥ 10, and its g.f. and closed forms follow. The general conjecture (all u, v, w and
polynomials g) is not settled here.

**Argument.** Let A = (n−1)^3, B = n^3, L = B − A, s = H_B − H_A, M = L/s, T = (n − 1/2)^3 + 1/2.
1. Midpoint rule for the convex 1/x: 1/k ≤ ln((k+1/2)/(k−1/2)) ≤ 1/k + 1/(9k^3). Summing, V − 1/(18A^2) ≤ s ≤ V
   with V = ln((B+1/2)/(A+1/2)) = 2 artanh(z), z = L/(A+B+1), and 2z(1 + z^2/3) ≤ V ≤ 2z(1 + z^2/3 +
   z^4/(5(1−z^2))).
2. These give rational-function bounds L/V_up ≤ M ≤ L/(V_lo − 1/(18A^2)); both lie strictly within 1/8 of T for
   all n ≥ 12 (exact sign analysis of the numerator and denominator polynomials, sympy). For 3 ≤ n ≤ 11 interval
   arithmetic gives |M − T| < 1/8 directly. (M − T = −1/(80n) + O(n^(−2)).)
3. T = ((2n−1)^3 + 4)/8 has odd numerator, so its fractional part is 1/8, 3/8, 5/8 or 7/8; with |M − T| < 1/8,
   ⌊M⌋ = ⌊T⌋. ⌊T⌋ is a cubic polynomial plus a sequence of period 4, which satisfies the recurrence with
   characteristic polynomial (x−1)^3 (x^4 − 1).

**Evidence.**
- [`certificate/bounds.py`](certificate/bounds.py): sympy proof of the inequalities of step 2 for n ≥ 12; mpmath
  interval check for n ≤ 12 against the OEIS data and T.
- Outside Lean: everything (no Lean file).

**Review level.** `rechecked` (for the A227012 sequence). The general conjecture remains open here.

**Prior art.** Checked 2026-11-06: OEIS A227012 entry (formulas marked conjectured); C. Kimberling, "Unsolved
Problems and Rewards" (Problem 21 is the jump-point conjecture of A219085, solved by D. Moews; nothing on
harmonic means). Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
