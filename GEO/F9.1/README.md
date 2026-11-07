# CFG F9: nine points with 19 unit circles through three of them, so f(9) ≥ 19

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991,
section F9. f(n) is the largest number of unit circles each passing through at least 3 points of an
n-point plane set. Known: f(3), ..., f(8) = 1, 4, 4, 8, 12, 16 (Harborth–Mengersen 1986; OEIS
A003829). The value f(9) is asked for.

**Result.** f(9) ≥ 19 (previous lower bound 16 = f(8)). Upper bound n(n−1)/3 = 24 (Harborth–Mengersen).
f(9) itself stays open.

**Construction.** Let ω = e^{2πi/3} and ρ = 5/6 + i√11/6 (|ρ| = 1; the rotation of the Moser spindle).
The 9 points, as a + bρ with a, b ∈ Z[ω]:
given exactly in `F9_1.lean` (`pts`); approximately
(−0.5620, 0.1320), (0.3954, 0.4207), (−0.0620, 0.9981), (0.8954, −0.4453), (1.3954, 0.4207),
(1, 0), (−1, 0), (0, 0), (0.4380, 0.1320).
There are 19 points (centres) at distance exactly 1 from at least 3 of them; the centre 0 is at
distance 1 from 4 points. Centres and incidences are listed in `F9_1.lean` (`circs`).

**Argument.** Exact arithmetic in Q(√3, √11): each listed centre has squared distance 1 to three
listed points, the centres are distinct, so the 19 unit circles are distinct.

**Evidence.**
- Lean (core): [`F9_1.lean`](F9_1.lean), `F9_1_main`: 9 distinct points, 19 distinct centres, each
  at squared distance 1 from 3 distinct listed points, computed in a 4-tuple model of Q(√3, √11)
  (`decide +kernel`). Axioms propext, Classical.choice, Quot.sound.
  Outside Lean: that the 4-tuple arithmetic is that of Q(√3, √11) ⊂ ℝ and that distinct tuples give
  distinct reals (linear independence of 1, √3, √11, √33 over Q).
- `certificate/search.py`, `search2.py`: local search over 9-subsets of {a + bρ : a, b ∈ Z[ω],
  coefficients in {−1, 0, 1}} (floating point); `certificate/exact.py`: exact recount (19);
  `certificate/genlean.py` emits the Lean data. The same search reaches only 15 for n = 8, so this
  pool is not optimal and f(9) may well exceed 19.

**Review level.** `lean-witness`.

**Prior art.** Not found. OEIS A003829 ends at n = 8; Erdős problem #104 (asymptotic) and its forum
(checked 2026-11-01) give nothing for n = 9; web search 2026-11-07 found nothing.
google-deepmind/formal-conjectures has Erdős 104 (asymptotic) only.
