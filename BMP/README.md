# Brass, Moser, Pach: Research Problems in Discrete Geometry

Problems from P. Brass, W. Moser, J. Pach, Research Problems in Discrete Geometry (Springer 2005), numbered by section and problem; statements paraphrased.

1 entries: 0 resolved by this project, 1 answered elsewhere, 0 disputed or partial.

Of the 0 resolutions: 0 proved in full in Lean, 0 with the finite facts (witnesses) checked in Lean and the remaining steps on paper, 0 on paper only (re-derived by a second reader; 0 of these need Mathlib to formalise).

Columns: **Lean** says how far Lean checks the result (`full proof`: the whole statement; `witness`: the finite facts, with the steps outside Lean named in the problem README; `needs Mathlib`: written proof only). **Prior art** (review 2026-11-04, sources in each problem README): `new` = no source found stating the answer, `partly-known`, `known`; "(immediate)" = follows in a few lines from a known theorem. **Verdict**: proved, disproved, or trivial/misstated. **Result**: one-line summary. **Method** links to [methods/](../methods/README.md). Each problem directory holds the README (source, reading, result, argument, evidence, review level, prior art), the Lean file and `certificate/` scripts.

## Answered in the literature; written up or confirmed here

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [1.8.7](1.8.7/) | proved | congruent regular simplices packed in a cube of the same side | [full proof](1.8.7/BMP_1_8_7_mathlib.lean) | known | [flat-orthogonal-basis](../methods/flat-orthogonal-basis/README.md), [known-theorem](../methods/known-theorem/README.md) |

## Short proofs

Copied from each problem README (source paraphrase, result, argument).

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

