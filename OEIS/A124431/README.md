# OEIS A124431: Mathar's recurrence for Σ 2^k C(⌊(n+k)/2⌋, k) C(⌊(n+k+1)/2⌋, k)

**Source.** OEIS [A124431](https://oeis.org/A124431) (offset 0): a(n) = Sum_{k=0..n}
2^k*C([(n+k)/2],k)*C([(n+k+1)/2],k): 1, 3, 9, 29, 97, 331, 1145, ... Conjecture (R. J. Mathar, Aug 2012,
repeated Jun 2016): "(n+1)*a(n) -2*(2*n+1)*a(n-1) +2*(n-1)*a(n-2) +2*(5-2*n)*a(n-3) +(n-3)*a(n-4) =0."
(OEIS text, CC BY-SA 4.0; both copies still marked "Conjecture" on 2026-11-05, revision #41.)

**Result.** True for every n ≥ 4.

**Argument.** Group the summands k = n − 2i (n + k even) and k = n + 1 − 2i (n + k odd). With
C(p, n−2i) = C(p, i) this gives a(n) = Σ_{i=0}^{n+1} w(n, i),
w(n, i) = 2^(n−2i) (C(n−i, i)² + 2 C(n−i, i−1) C(n−i+1, i)), a hypergeometric term in (n, i) with no
floors. Let F(n, i) = Σ_{l=0}^{4} c_l(n) w(n−l, i) with Mathar's coefficients
c = (n+1, −2(2n+1), 2(n−1), 2(5−2n), n−3). Creative telescoping: with
G(n, i) = 2^(n−2i) [ (1+4i) X₀₀² − 6i X₀₀X₀₁ − 4i X₀₁² − (2+5i) X₀₀X₁₀ − ½ X₀₀X₂₀ + (½ − i/4) X₀₀X₃₀ + X₁₀²
+ (3i/4) X₁₀X₂₀ − (i/2) X₁₀X₃₀ + (¼ + 2i) X₂₀² − (5i/4) X₂₀X₃₀ + (i/4 − ¼) X₃₀² ], X_ab = C(n−i−a, i−b),
one has F(n, i) = G(n, i+1) − G(n, i). This is checked by writing every binomial as
C(n−i+1, i) times a rational function of (n, i) (contiguous relations) and verifying one rational-function
identity. Summing over 0 ≤ i ≤ n+1 gives Σ_l c_l(n) a(n−l) = G(n, n+2) − G(n, 0) = 0 (all binomials vanish
at i = n+2; at i = 0 the coefficients cancel). The identity needs (n−i+1)(n−i)…(n−i−3) ≠ 0; for n ≥ 8 the
other i have 2i ≥ n + 2, where every term is 0. n = 4..7 by direct computation.
G was found by fitting such binomial products with coefficients of degree ≤ 1 to the partial sums
Σ_{i'<i} F(n, i') (`certificate/find_certificate.py`).

**Evidence.**
- Lean (Mathlib): [`A124431_mathlib.lean`](A124431_mathlib.lean). `A124431_a n` is the OEIS sum over ℕ.
  `A124431_conjecture (n : ℕ) (hn : 4 ≤ n)`: ((n:ℤ)+1)·a n − 2(2n+1)·a (n−1) + 2(n−1)·a (n−2) +
  2(5−2n)·a (n−3) + (n−3)·a (n−4) = 0. Supporting: `A124431_a_eq_A` (reindexing), `A124431_core`
  (telescoping identity), `A124431_rat` (rational identity), `A124431_A_rec`, `A124431_small` (n = 4..7,
  `decide`), `A124431_data` (a(0..11) against the entry). Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: reindexed sum = OEIS sum (n < 300), first 60 terms = printed algebraic g.f.,
  recurrence for 4 ≤ n < 300, F = ΔG for 4 ≤ n < 80 and all i.
- `certificate/find_certificate.py` (finds G; run `1 4 0,1 50`), `certificate/gen_lean.py` (sympy check of the
  rational identity, then writes the definitions, `A124431_rat` and `A124431_core` used in the Lean file).
- Outside Lean: nothing for the theorem. The algebraic g.f. printed in the entry is not proved here.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05: the entry gives the algebraic g.f. (Voznyy 2009, Barry 2011) without a proof
that the sum has it; from that g.f. the recurrence would follow by differentiating. Web search found no proof
of the recurrence or of the g.f.; not in google-deepmind/formal-conjectures.
