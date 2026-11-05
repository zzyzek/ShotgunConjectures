# OEIS A217876: adjacent transpositions in a random involution are asymptotically Poisson(1)

**Source.** [A217876](https://oeis.org/A217876), triangle T(n,k): the number of involutions of [n] whose
cycle form has exactly k adjacent transpositions (i i+1); row sums A000085 = I(n). Comment by David Callan
(2012): "Conjecture: The asymptotic distribution of adjacent transpositions in involutions is Poisson
with mean 1." (OEIS text, CC BY-SA 4.0; still a conjecture on 2026-11-05.)

**Reading.** X_n = number of adjacent transpositions of a uniform involution of [n]; the claim is
X_n → Poisson(1) in distribution, i.e. (X_n is N-valued) P(X_n = j) = T(n,j)/I(n) → e^{−1}/j! for every j.

**Result.** True: T(n,j)/I(n) → e^{−1}/j! for every j ≥ 0. Also E C(X_n,i) → 1/i!.

**Argument.** A set of i pairwise disjoint adjacent pairs of [n] can be chosen in C(n−i,i) ways, and the
involutions containing all of them as 2-cycles number I(n−2i). So b_i(n) := E C(X_n,i) =
C(n−i,i)·I(n−2i)/I(n) and, by inclusion–exclusion, T(n,j) = Σ_i (−1)^{i+j} C(i,j)·C(n−i,i)·I(n−2i).
From I(n+2) = I(n+1) + (n+1)I(n), y(n) = I(n+1)/I(n) satisfies √(n+1) ≤ y(n) ≤ √(n+1) + 1 (induction), so
c(n) = (n+1)I(n)/I(n+2) = 1/(1 + y(n)/(n+1)) → 1 and c(n) ≤ 1. The recursion
b_{i+1}(n+2) = (1/(i+1))·((n+1−i)/(n+1))·c(n)·b_i(n) gives b_i(n) → 1/i! and 0 ≤ b_i(n) ≤ 1/i!. Then
T(n,j)/I(n) = Σ_i (−1)^{i+j} C(i,j) b_i(n), and dominated convergence for series (Tannery, bound
C(i,j)/i! ≤ 2^i/i!) gives the limit Σ_i (−1)^{i+j} C(i,j)/i! = (1/j!) Σ_l (−1)^l/l! = e^{−1}/j!.
No method-of-moments theorem is needed.

**Evidence.**
- Lean (Mathlib): [`A217876_mathlib.lean`](A217876_mathlib.lean). `I` is A000085 by its recurrence; `T n k`
  is the inclusion–exclusion sum above; `T_data` (`decide`) checks rows 0–8 against the entry. Theorems:
  `A217876_conjecture (j)`: `Tendsto (fun n => (T n j : ℝ) / I n) atTop (𝓝 (Real.exp (-1) / j !))`;
  `binom_moment_tendsto (i)`: C(n−i,i)·I(n−2i)/I(n) → 1/i!; `Y_bounds`, `c_tendsto`, `b_rec`, `b_le`,
  `limit_hasSum`. Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: the formula equals brute-force counts over all involutions for n ≤ 10; rows 0–8
  equal the entry; row sums equal I(n) for n ≤ 60; the `Y_bounds` invariant (squared, exact integers) for
  n < 3000; e·j!·P(X_n = j) at n = 3000 is 1.018, 1.000, 0.982, 0.964, 0.946 for j = 0..4 (error O(1/√n)).
- Outside Lean: (1) the inclusion–exclusion formula counts involutions by adjacent transpositions
  (standard: C(n−i,i) disjoint i-sets of edges of the path 1–2–…–n, I(n−2i) completions); (2) pointwise
  convergence of N-valued probability mass functions is convergence in distribution.

**Review level.** `rechecked`: the limit is proved in Lean for the inclusion–exclusion formula; the
counting identity behind the formula is not formalized.

**Prior art.** New (checked 2026-11-05). Not in google-deepmind/formal-conjectures; web search found only
permutation analogues (adjacencies in random permutations, Kaplansky/Wolfowitz) and nothing on involutions.
