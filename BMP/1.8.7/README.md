# BMP 1.8 Problem 7: congruent regular simplices packed in a cube of the same side

**Source.** P. Brass, W. Moser, J. Pach, *Research Problems in Discrete Geometry* (Springer 2005), §1.8,
Problem 7 (L. Moser, *Poorly formulated unsolved problems of combinatorial geometry*, mimeographed 1966,
reprinted in W. O. J. Moser, Discrete Appl. Math. 31 (1991) 201–225). Paraphrase: let f(d) be the largest number
of congruent copies of the regular d-simplex T^d of edge 1 that can be packed (pairwise disjoint interiors) into
a d-cube of side 1. Estimate f(d). Is lim log f(d)/d = ∞?

**Result.** Yes. For every d ≥ 1,

  ⌊√(d+1)/2⌋^d ≤ f(d) ≤ d! 2^{d/2} / √(d+1),

so ½ log d − O(1) ≤ log f(d)/d ≤ log d + O(1), and log f(d)/d → ∞.

**Argument.**
- *A small box holds one simplex.* Put n = d+1 and θ_jk = 2πjk/n. The vectors
  - c_j(k) = √(2/n) cos θ_jk and s_j(k) = √(2/n) sin θ_jk for 1 ≤ j < n/2,
  - and a(k) = (−1)^k/√n when n is even,

  together with the constant vector 1/√n, form an orthonormal basis of ℝ^n (the real discrete Fourier basis).
  Call the d non-constant ones b_1, …, b_d. The matrix with columns (1/√n, b_1, …, b_d) is orthogonal, so its
  rows are orthonormal. Hence the points v_k = (1/√2)(b_1(k), …, b_d(k)) ∈ ℝ^d, for k = 0, …, d, satisfy
  |v_k − v_l|² = ½(|e_k − e_l|² − 0) = 1 for k ≠ l: they are the vertices of a regular d-simplex of edge 1.
  Every coordinate satisfies |v_k(j)| ≤ (1/√2)·√(2/n) = 1/√n, so the simplex lies in a cube of side 2/√(d+1).
- *Lower bound.* Cut the unit cube into m^d cubes of side 1/m with m = ⌊√(d+1)/2⌋, so that 1/m ≥ 2/√(d+1).
  Put one translate of the simplex in each small cube. The interiors are disjoint because the open small
  cubes are, so f(d) ≥ m^d.
- *Upper bound.* vol T^d = √(d+1)/(d! 2^{d/2}), and the copies have disjoint interiors inside a cube of volume 1.

The containment step is a known theorem in sharper form, so the question is answered by the literature:
- Maehara, Ruzsa and Tokushige (2009) show the unit d-cube contains a regular d-simplex of edge c√d for every
  c < 1/2 and d large.
- Tamura (2011) shows c = (√336 − 4 − √2)/√664 ≈ 0.5012 works for every d. Scaling either down and
  translating gives the lower bound above.
- The Fourier construction gives edge √(d+1)/2 for every d. It is elementary and is included for a
  self-contained proof. I found no source that applies these results to Moser's question; Brass–Moser–Pach
  (2005) predates them.

**Evidence.**
- `certificate/check.py` (seconds): checks numerically, for d = 1..400, that the columns are orthonormal, that
  the v_k are pairwise at distance 1 (maximum error 5·10⁻¹⁴) and that every coordinate is at most 1/√(d+1).
  It also prints the two bounds on log f(d)/d (at d = 400 the window is [2.30, 5.34]).
- `BMP_1_8_7_mathlib.lean` (Lean 4 + Mathlib, namespace `BMP187`). It uses the Hartley basis
  cas(2πkt/n)/√n with cas x = cos x + sin x in place of the cos/sin pair; the bound is the same. Statements:
  - `regular_simplex_in_small_box`: an edge-1 regular simplex in ℝ^d with every coordinate in
    [−1/√(d+1), 1/√(d+1)] and nonempty interior (affine independence from the orthogonality of the Hartley
    matrix).
  - `moser_pack`: with m = Nat.sqrt((d+1)/4), there are m^d translates (indexed by Fin d → Fin m) with all
    vertices in [0,1]^d, each hull with nonempty interior (so the copies are genuine and distinct), and
    pairwise disjoint interiors.
  - `moser_tendsto` and `moser_log_tendsto`: m → ∞ and log(m^d)/d → ∞.
- Outside Lean: the definition of f(d) as a maximum over all packings is not formalised, so "f(d) ≥ m^d" is
  how `moser_pack` is read. The upper bound via volume is not in Lean. The literature theorems above are
  cited, not used.

**Review level.** `rechecked`. The argument was re-derived by hand and checked numerically.

**Prior art.** Checked 2026-11-05.
- H. Maehara, I. Z. Ruzsa, N. Tokushige, *Large regular simplices contained in a hypercube*, Period. Math.
  Hungar. 58 (2009) 121–126.
- H. Tamura, *Large regular simplices contained in a hypercube with a common barycenter*, arXiv:1101.2707
  (2011). Its abstract and introduction were read; it mentions neither Moser nor packing.
- Web searches for Moser's simplex-packing problem found no statement of its status.
- The problem is not in google-deepmind/formal-conjectures (no file found).
