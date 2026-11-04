# OEIS A114534: the Fibonacci matrix has rank 2

**Source.** [A114534](https://oeis.org/A114534) (permanent of the n × n matrix M filled row by row with Fibonacci
numbers), comment: "Conjecture: The rank of the matrix M is 2 for every n." (OEIS text, CC BY-SA 4.0.)

**Reading.** The entries are F(0), F(1), …, F(n² − 1) (this reproduces a(2) = 1 and a(3) = 132), and n ≥ 2 (the
offset).

**Result.** True.

**Argument.** M(r, c) = F(rn + c). The addition formula gives F(a + c) = F(a)·(F(c+1) − F(c)) + F(a+1)·F(c), so
every row is a combination of the two rows (F(c+1) − F(c))_c and (F(c))_c: rank ≤ 2. The minor on rows 0, 1 and
columns 0, 1 is F(0)F(n+1) − F(1)F(n) = −F(n) ≠ 0: rank ≥ 2.

**Evidence.**
- Lean: [`A114534.lean`](A114534.lean): the addition formula for all a, c, the factorization of M through Z²,
  the nonzero minor for n ≥ 1, and the n = 3 permanent 132. Outside Lean: the linear-algebra step from
  factorization / nonzero minor to rank.
- `certificate/check.py`: sympy ranks for n = 2..12.
- Lean (Mathlib): [`A114534_mathlib.lean`](A114534_mathlib.lean), `A114534_main`: for every n ≥ 2 the matrix M(r,c) = F(rn + c) over ℚ has `Matrix.rank` 2. Nothing outside Lean.

**Review level.** `lean-proof` (Mathlib file above).
**Prior art.** Verdict known, immediate (OEIS status resolved-in-entry; searched 2026-11-04). Resolved in the entry since Sep 2026 (our README's 2026-11-01 check missed the approved edit). Sources: [OEIS A114534 (fetched 2026-11-04)](https://oeis.org/A114534): comment 'True for n>= 2, see Weston paper' (J. S. Macias, Sep 2026); [J. D. Weston, Generalised Fibonacci matrices, Math. Gazette 82 (1998), p. 97](https://doi.org/10.2307/3620165): rank 2 for every n >= 2. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history.
