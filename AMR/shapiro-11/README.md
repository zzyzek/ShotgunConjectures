# AMR shapiro-11/12/13: Forsgård–Shapiro real-zero bounds (Conjectures 8, 9, 10) fail

**Source.** B. Shapiro, *Problems around polynomials: the good, the bad and the ugly*,
Arnold Math. J. 1 (2015), arXiv 1503.05295, Section 7, Conjectures 8, 9, 10 (Forsgård–Shapiro),
listed at https://amathr.org/problems/. For f = Σ a_k x^k of degree n with all a_k > 0:
- Conj 8 (shapiro-11): the number of real zeros of f is at most the number of corners of
  t ↦ max_k (log a_k + kt + log C(n,k)).
- Conj 9 (shapiro-12): with c̃_k = (k+1)a_k² − k a_{k−1}a_{k+1} (a_{−1} = a_{n+1} = 0), and
  k_1 < … < k_m the indices with c̃_k > 0, the number of real zeros is at most the number of
  parity changes in (k_i mod 2).
- Conj 10 (shapiro-13): the same with c_k = a_k² − a_{k−1}a_{k+1} ≥ 0.

**Reading.** Real zeros are counted as distinct points (the counterexample below has simple
zeros, so the count with multiplicity gives the same answer).

**Result.** All three are false. One polynomial refutes all three:

P(x) = (19x² − 94x + 163) · ∏_{j=0}^{21} (2D x + 2D + 2j − 23),  D = 10^5.

P has degree 24, positive coefficients, and the 22 distinct rational zeros
x_j = −1 − (2j − 23)/(2D). Its corner count is 21, and both parity counts are 20.

- Conj 9 and 10: known. Katkova, Shapiro, Vishnyakova (arXiv 2403.12200, Section 5) refute
  them with Q_15(x) = (x+1)^13 (19/360360 x² − 89/720720 x + 83/720720) and its primitives
  Q_n(x) = ∫_{−1}^x Q_{n−1}, whose real zeros are a single zero at −1 of multiplicity n − 2.
- Conj 8: new here. Katkova–Shapiro–Vishnyakova list it as Conjecture 1 and do not refute it.
  Their own family refutes it: Q_21 has 18 corners against 19 real zeros (with multiplicity),
  and Q_n has n − 3 corners for 24 ≤ n ≤ 39 (checked). The polynomial P above splits the
  22-fold zero of Q_24 = (x+1)^22 · (19x² − 94x + 163)/K into distinct zeros. That makes the
  counterexample hold for distinct zeros too.

**Argument.** The zeros are explicit linear factors. 19x² − 94x + 163 has no real zeros
(94² < 4·19·163). Corners: f_trop is the maximum of the affine functions log w_k + kt with
w_k = a_k C(24,k). Its corners are the edges of the upper hull of the points (k, log w_k).
Index j is a strict hull vertex iff w_i^{l−j} w_l^{j−i} < w_j^{l−i} for all i < j < l. Exact
integer arithmetic finds the vertices 0..16, 20..24 (22 vertices, 21 corners). The indices
with c_k ≥ 0 and those with c̃_k > 0 are also 0..16, 20..24. That list has 16 + 4 = 20
parity changes. In all three cases 22 > the bound.

**Evidence.**
- Lean (core): [`shapiro_11.lean`](shapiro_11.lean). Main theorem
  `shapiro_conj_8_9_10_counterexample`: P (defined as the product) has 25 coefficients, all
  positive; homEval P (rootNum j) (2D) = 0 for j < 22 with distinct rootNum j; corners P = 21;
  vPar P true = 20; vPar P false = 20. Checked with tools/leancheck.sh (`decide +kernel`).
  Axioms: propext, Quot.sound.
- `certificate/check.py` (exact rational check of the same facts, output `check.out`).
- Outside Lean (definitional reading only): homEval a p q = q^24 · P(p/q), so it vanishes iff
  p/q is a zero; the corners of a maximum of affine functions are the upper-hull edges between
  consecutive strict vertices.

**Review level.** `lean-witness`.

**Prior art.** Checked 2026-11-06: O. Katkova, B. Shapiro, A. Vishnyakova, *In search of
Newton-type inequalities*, arXiv 2403.12200 (2024), Section 5 (refutes Conj 9 for large n
and Conj 10 in degree 15; Conj 8 is restated, not refuted). J. Forsgård, D. Novikov,
B. Shapiro, *A tropical analog of Descartes' rule of signs*, IMRN 2017 (a different
weighting). Web search; google-deepmind/formal-conjectures (HEAD 2026-11-05, no entry).
No refutation of Conj 8 found.
