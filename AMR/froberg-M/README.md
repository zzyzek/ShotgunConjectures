# AMR froberg-M: finiteness of B_{n,m} and B'_{n,m}

**Source.** R. Fröberg, S. Lundqvist, A. Oneto, B. Shapiro, *Algebraic stories from one and
from the other pockets*, Arnold Math. J. 4 (2018), §4.2, Problem M (listed at
https://amathr.org/problems/), going back to M.-D. Choi, T.-Y. Lam, B. Reznick, *Real zeros of
positive semidefinite forms I*, Math. Z. 171 (1980) 1–26. Paraphrase: for a real form p of even
degree m in n variables, let Z(p) be its set of real projective zeros. B_{n,m} (resp. B'_{n,m}) is
the supremum of |Z(p)| over non-negative forms (resp. sums of squares of forms) with
|Z(p)| < ∞. Are B_{n,m} and B'_{n,m} finite?

**Reading.** Only finiteness is asked. The exact values (Conjecture 4.2, Problem N of the same
paper) remain open and are not addressed here.

**Result.** Yes, known. Both are finite, with
B'_{n,m} ≤ B_{n,m} ≤ ((m−1)^n − 1)/(m − 2) (m ≥ 4; B_{n,2} = 1), and also
B_{n,m} ≤ m(2m−1)^(n−1)/2. The problem paper itself quotes the first (eigenvector) bound
from Cartwright–Sturmfels (2013); the second follows from Milnor (1964). So the question was
already answered when it was listed.

**Argument.**
1. *Milnor route.* Let p ≥ 0 with Z(p) finite, |Z(p)| = k. On the unit sphere S, the set
   V = {x ∈ R^n : p(x) = 0, |x|² − 1 = 0} consists of the 2k points ±x_i, so each is a
   connected component of V. Milnor's theorem (J. Milnor, *On the Betti numbers of real
   varieties*, Proc. AMS 15 (1964) 275–280) bounds the sum of Betti numbers of a real
   algebraic set in R^n cut out by polynomials of degree ≤ d by d(2d−1)^(n−1); here d = m.
   Hence 2k ≤ m(2m−1)^(n−1). Non-negativity is not even used: this bounds the number of real
   projective zeros of any form with finitely many such zeros.
2. *Eigenvector route (the bound quoted in the problem paper).* Each ±x_i is a strict local
   minimum of p on S (value 0, and p > 0 nearby on S). Take disjoint closed balls B_i around the
   2k points and let δ > 0 be the minimum of p over S ∩ ∂B_i. Forms whose symmetric tensor has
   exactly N = ((m−1)^n − 1)/(m − 2) complex eigenvector classes form a dense (Zariski-open,
   non-empty) set (D. Cartwright, B. Sturmfels, *The number of eigenvalues of a tensor*, Linear
   Algebra Appl. 438 (2013) 942–952, for generic symmetric tensors of order m in n
   variables). Pick such f with
   sup_S |f − p| < δ/2. Then f restricted to S ∩ B_i attains its minimum in the interior, at a
   critical point of f|_S, i.e. ∇f(x) = λx: an eigenvector. The k projective points give k
   distinct eigenvector classes, so k ≤ N.
3. B'_{n,m} ≤ B_{n,m} since sums of squares are non-negative.

**Evidence.** Hand argument above, re-derived here from the two cited theorems. No Lean:
Mathlib has neither Milnor's Betti bound nor the Cartwright–Sturmfels count. Outside Lean:
everything (Milnor 1964, Cartwright–Sturmfels 2013, the two short reductions above).

**Review level.** `rechecked` (two independent reductions to published theorems).

**Prior art.** Searched 2026-11-06: the problem paper (§4.2 itself states the
Cartwright–Sturmfels bound for B_{n,m} and remarks that finiteness should also follow from the
Petrovskii–Oleinik inequalities); M. Dressler, *Real zeros of SONC polynomials*, arXiv:1909.06707
(lists the known values from Choi–Lam–Reznick and calls the exact determination of B and B'
open, i.e. values, not finiteness); web search; google-deepmind/formal-conjectures (HEAD
2026-11-05, no entry). Verdict: known (finiteness follows from Milnor 1964 and from
Cartwright–Sturmfels 2013, the latter quoted in the problem paper).
