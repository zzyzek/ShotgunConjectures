# Brass, Moser, Pach: Research Problems in Discrete Geometry

Problems from P. Brass, W. Moser, J. Pach, Research Problems in Discrete Geometry (Springer 2005), numbered by section and problem; statements paraphrased.

5 entries: 0 resolved by this project, 3 answered elsewhere, 2 disputed or partial.

Of the 0 resolutions: 0 proved in full in Lean, 0 with the finite facts (witnesses) checked in Lean and the remaining steps on paper, 0 on paper only (re-derived by a second reader; 0 of these need Mathlib to formalise).

Columns: **Lean** says how far Lean checks the result (`full proof`: the whole statement; `witness`: the finite facts, with the steps outside Lean named in the problem README; `needs Mathlib`: written proof only). **Prior art** (review 2026-11-04, sources in each problem README): `new` = no source found stating the answer, `partly-known`, `known`; "(immediate)" = follows in a few lines from a known theorem. **Verdict**: proved, disproved, or trivial/misstated. **Result**: one-line summary. **Method** links to [methods/](../methods/README.md). Each problem directory holds the README (source, reading, result, argument, evidence, review level, prior art), the Lean file and `certificate/` scripts.

## Answered in the literature; written up or confirmed here

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [1.5.4](1.5.4/) | known | a nonconvex plane body tiling by translates tiles by a lattice | — | known | [reading-the-statement](../methods/reading-the-statement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [1.8.7](1.8.7/) | proved | congruent regular simplices packed in a cube of the same side | [full proof](1.8.7/BMP_1_8_7_mathlib.lean) | known | [flat-orthogonal-basis](../methods/flat-orthogonal-basis/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [8.2.6](8.2.6/) | answered | an r-cap or an empty r-cup in every large point set (Valtr's conjecture) | — | known | [known-theorem](../methods/known-theorem/README.md) |

## Disputed or only partly answered (not counted as resolutions)

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [6.2.10](6.2.10/) | partial | BMP 6.2 Conjecture 10 (at least n-2 distinct angles) | — | known | [known-theorem](../methods/known-theorem/README.md) |
| [9.6.3](9.6.3/) | partial | k-cross-free families are linear in n; the O(kn) form is still open | — | known | [known-theorem](../methods/known-theorem/README.md) |

## Short proofs

Copied from each problem README (source paraphrase, result, argument).

### [1.5.4](1.5.4/): a nonconvex plane body tiling by translates tiles by a lattice

**Source.** P. Brass, W. Moser, J. Pach, *Research Problems in Discrete Geometry*, Springer 2005,
Section 1.5, Problem 4 (Grünbaum–Shephard): if a nonconvex plane body C tiles the plane by
translates, does it tile by a lattice? The authors add that even periodicity is not known.

**Reading.** BMP Chapter 0 defines a body as a set homeomorphic to a ball; in the plane, a closed
topological disk. Under that definition the problem is answered.

**Result.** Yes for bodies in BMP's sense. Girault-Beauquier and Nivat (1991, with boundary
conditions; Beauquier–Nivat for polyominoes, Discrete Comput. Geom. 6 (1991) 575–592) and
R. Kenyon, *Rigidity of planar tilings*, Invent. Math. 107 (1992) 637–651 (erratum 112 (1993) 223)
proved that a closed topological disk tiling the plane by translations has boundary split into 4
or 6 arcs matched in opposite pairs by translations (pseudo-square or pseudo-hexagon), which gives
a lattice tiling. For general compact tiles (disconnected or with holes) the periodic tiling
question in R^2 is open: R. Greenfeld, *Translational tilings: structured or wild?*,
arXiv:2509.25576 (2025), Section 7, Question 7.4.

Lean: —.

### [1.8.7](1.8.7/): congruent regular simplices packed in a cube of the same side

**Source.** P. Brass, W. Moser, J. Pach, *Research Problems in Discrete Geometry* (Springer 2005), §1.8,
Problem 7 (L. Moser, *Poorly formulated unsolved problems of combinatorial geometry*, mimeographed 1966,
reprinted in W. O. J. Moser, Discrete Appl. Math. 31 (1991) 201–225). Paraphrase: let f(d) be the largest number
of congruent copies of the regular d-simplex T^d of edge 1 that can be packed (pairwise disjoint interiors) into
a d-cube of side 1. Estimate f(d). Is lim log f(d)/d = ∞?

**Result.** Yes. For every d ≥ 1,

  ⌊√(d+1)/2⌋^d ≤ f(d) ≤ d! 2^{d/2} / √(d+1),

so ½ log d − O(1) ≤ log f(d)/d ≤ log d + O(1), and log f(d)/d → ∞.

**Argument.** - *A small box holds one simplex.* Put n = d+1 and θ_jk = 2πjk/n. The vectors
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

Lean: [full proof](1.8.7/BMP_1_8_7_mathlib.lean).

### [8.2.6](8.2.6/): an r-cap or an empty r-cup in every large point set (Valtr's conjecture)

**Source.** P. Brass, W. Moser, J. Pach, *Research Problems in Discrete Geometry* (2005), Section 8.2, Conjecture 6 (attributed to Valtr 2002). Paraphrase: for every r ≥ 3 there is f such that every set of at least f points in general position in the plane, no two on a vertical line, contains an r-cap or an empty r-cup (an r-cup whose convex hull contains no other point of the set).

**Result.** True.

**Argument.** P. Valtr (2007) calls a k-cap or k-cup p1, ..., pk *open* if no point p of the set with x(p1) < x(p) < x(pk) lies above the polygonal line p1 ... pk. The convex hull of a cup lies above the cup and inside that vertical strip, so an open cup is empty (Valtr states this in the proof of his Corollary 2). His Theorem 2 gives f(k, l) such that every configuration (general position, distinct x-coordinates) of size ≥ f(k, l) contains an open k-cap or an open l-cup; his Theorem 3(i) bounds f'(k, l), the threshold for "a k-cap or an open l-cup", between two double exponentials. With k = l = r this is the conjecture. Valtr also derives the consequence BMP state (a large set with no k-cap contains an empty l-gon, his Corollary 2) and notes he had asked this in the 2002 paper BMP cite.

Lean: —.

### [6.2.10](6.2.10/): BMP 6.2 Conjecture 10 (at least n-2 distinct angles)

Lean: —.

### [9.6.3](9.6.3/): k-cross-free families are linear in n; the O(kn) form is still open

**Source.** Brass-Moser-Pach, Research Problems in Discrete Geometry (2005), Section 9.6,
Conjecture 3 (paraphrased): a family of subsets of an n-set with no k pairwise crossing
members has at most Ckn members, C an absolute constant. Two sets cross when all four Venn
regions (A\B, B\A, A∩B, X\(A∪B)) are nonempty.

**Reading.** The conjecture has two strengths: linear in n for each fixed k (|F| <= c_k n), and
the stated form c_k = O(k).

**Result.** Partial, known. Linearity for each fixed k holds:
- E. Knill, Families of sets with locally bounded width, Graphs and Combinatorics 10 (1994)
  145-157, proves that k-wise laminar families (no antichain of k members with a common point)
  have size O_k(n); a k-cross-free family contains a k-wise laminar subfamily of at least half
  its size (Tomon, Lemma 2.1), so |F| <= c_k n.
- I. Tomon, Cross-free families have linear size, arXiv:2603.05443 (v3, Sep 2026), gives an
  independent proof (Theorem 1.1) and records that Knill's 1994 paper had been overlooked.
The constant in Tomon's proof is huge (an induction on k with trees of branching about
h/(2k)^{k^2}); neither paper gives c_k = O(k). The Ckn form stays open; known exact cases
are k = 2 (4n - 2, Edmonds-Giles) and k = 3 (8n - 20, Dress-Koolen-Moulton 2005).

**Argument.** Citation only.

Lean: —.

