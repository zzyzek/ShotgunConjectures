# OEIS A195538: denominators of Pythagorean approximations to √8 satisfy a(n) = 35a(n−2) − 35a(n−4) + a(n−6)

**Source.** OEIS [A195538](https://oeis.org/A195538) (offset 1): denominators a(n) of Pythagorean approximations
b(n)/a(n) to √8: 5, 12, 145, 420, 4901, 14280, ... Conjecture (R. J. Mathar, Sep 2011): "a(n) = 35*a(n-2)
-35*a(n-4) +a(n-6) with bisections A098602 and A076218." (OEIS text, CC BY-SA 4.0; still a conjecture on
2026-11-05, revision #15.)

**Reading.** P. J. C. Moses' program (A195500, A195538): s = r + √(1 + r²) = 3 + 2√2 for r = √8; for each n
take the n-term continued-fraction convergent p/q of s and reduce (p² − q²)/(2pq); a(n) is its
denominator. Offsets: A098602 (offset 0) = 0, 12, 420, ..., so the even bisection claim is
a(2k) = A098602(k), k ≥ 1; A076218 (offset 1) = 0, 1, 5, 145, ..., so the odd one is a(2k−1) = A076218(k+2).
The bisection sequences are taken from their own definitions: A098602(n) = A001652(n)·A046090(n), A001652 by
its recurrence, A046090 = X+1 over Pythagorean triples (X, X+1, Z), A076218 = numbers m with 2m² − 3m + 1 a
square.

**Result.** True (recurrence and both bisections).

**Argument.** s = 3 + 2√2 = [5; 1, 4, 1, 4, ...] (complete quotients (√2+1)/2 and 2 + 2√2 alternate).
Let (X_k, W_k) be the solutions of X² − 8W² = 1 ((1,0), (3,1), (17,6), ...; step (X, W) → (3X+8W, X+3W)),
U = X + 2W, V = X + 3W. The convergent recurrences give p_(2k) = U_(k+1) = U + 4V, q_(2k) = U, and
p_(2k+1) = V_(k+1) = U + 5V, q_(2k+1) = V (indices k on the right). From U² + 4UV − 4V² = 1:
- n = 2k+1: p, q odd and (p² − q²)/(2pq) = 4V(U+2V)/((U+4V)U) in lowest terms, so a = (U+4V)U;
- n = 2k+2: p − q odd and (p² − q²)/(2pq) = (U+4V)(U+6V)/(2(U+5V)V) in lowest terms, so a = 2(U+5V)V.
(Each coprimality has an explicit Bézout pair linear in U, V, e.g. (U+6V)(U+2V) − 4V(U+4V) = 1.) Both
bisections are quadratic forms in (X_k, W_k) under a matrix with eigenvalues λ^{±1}, λ = 3 + 2√2, so they
satisfy the recurrence with characteristic roots λ², 1, λ⁻², i.e. x³ − 35x² + 35x − 1 (a polynomial identity).
Bisections: a(2k+1) = (U+4V)U = 4W_(k+1)² + 1 (uses X² − 8W² = 1), and the m with 2m² − 3m + 1 = (2m−1)(m−1)
a square are 0 and, for m ≥ 1, m − 1 = u², 2m − 1 = v² (coprime factors), v² − 8(u/2)² = 1, so m = 4W_j² + 1.
a(2k+2) = 2(U+5V)V = x(x+1) with 2x + 1 = X_(k+1) + 4W_(k+1); A001652 satisfies 2x(k) + 1 = X_k + 4W_k, and
X² + (X+1)² = Z² ⇔ (2X+1)² − 2Z² = −1, which maps to X'² − 8W'² = 1 by X' = 2Z − (2X+1), W' = (2X+1−Z)/2,
so the Pythagorean X+1 values are x(k) + 1. Every solution of x² − 8w² = 1 in ℕ is some (X_k, W_k) by descent
(x, w) → (3x − 8w, 3w − x).

**Evidence.**
- Lean (Mathlib): [`A195538_mathlib.lean`](A195538_mathlib.lean), `A195538_main`: (1) a(1..16) are the printed
  terms; (2) ∀ n ≥ 7, a(n) = 35a(n−2) − 35a(n−4) + a(n−6); (3) ∀ k ≥ 1, a(2k) = A098602(k); (4) ∀ k ≥ 1,
  a(2k−1) = A076218(k+2). a(n) is `Rat.den` of (p² − q²)/(2pq) with p/q from the floor algorithm over ℝ on
  √8 + √(1 + √8²) and the standard convergent recurrences; A046090 and A076218 are `Nat.nth` of their defining
  sets. Lemmas: `A195538_c_val` (partial quotients), `A195538_PQ`, `A195538_a_odd`, `A195538_a_even`,
  `A195538_classify` (Pell descent), `A195538_S1_iff`, `A195538_S2_iff`, `A195538_A001652`.
  Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: exact continued fraction of 3 + 2√2 in Q(√2), the printed terms, the recurrence for
  n ≤ 60, the bisections against brute-force A046090 (8 terms), A076218 (6 terms) and A046176 (4 terms), and
  A195539's claims.
- Outside Lean: only the identification of Mathematica's FromContinuedFraction[ContinuedFraction[s, n]] with
  the recurrence convergent p_(n−1)/q_(n−1) (the classical convergent identity).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05: the entry and A195500 (Shiu's method) give no proof; a web search found none;
not in google-deepmind/formal-conjectures. The bisection sequences carry their own recurrences and closed
forms (A098602 by R. Knott, A076218 by A. G. Astudillo); those formulas are not used here.
