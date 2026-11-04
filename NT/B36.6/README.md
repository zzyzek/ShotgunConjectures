# Guy B36: convergence of Σφ(n)/n^x and Σ(−1)^(n+1)φ(n)/n^x

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B36. Ecker asks for which x each of the two series
Σ φ(n)/n^x and Σ (−1)^(n+1) φ(n)/n^x converges.

**Reading.** x real (the question is a convergence exercise; for complex x the abscissa
argument below gives the same half-plane Re x > 2 for absolute convergence).

**Result.** Both converge exactly for x > 2. The problem is a standard exercise, not open.

**Argument.**
- First series: terms are positive and Σ_(n≤N) φ(n) = (3/π²)N² + O(N log N), so by partial
  summation the series converges iff x > 2 (its sum is ζ(x − 1)/ζ(x)).
- Alternating series: for x > 2 it converges absolutely. For x ≤ 1 the terms do not tend to
  0 (φ(p)/p^x = (p − 1)/p^x along primes). For 1 < x ≤ 2: Σ_(n≤N, n odd) φ(n)/n = (4/π²)N + O(log N)
  and Σ_(n≤N) φ(n)/n = (6/π²)N + O(log N) (local factors ∏_(p>2)(1 − 1/p²) = 8/π²), so by partial
  summation Σ_(n odd ≤N) φ(n) = (2/π²)N² + O(N log N) and Σ_(n even ≤N) φ(n) = (1/π²)N² + O(N log N).
  Hence A(N) = Σ_(n≤N) (−1)^(n+1) φ(n) = N²/π² + O(N log N). Abel summation gives
  Σ_(n≤N) (−1)^(n+1)φ(n) n^(−x) = A(N)N^(−x) + x∫_1^N A(t) t^(−x−1) dt, which tends to +∞ for
  x < 2 (like N^(2−x)) and for x = 2 (like (2/π²) log N). So the series diverges for x ≤ 2.

**Evidence.** Hand proof (second reader re-derived the constants 2/π² and 1/π²).
Lean (Mathlib): [`B36_6_mathlib.lean`](B36_6_mathlib.lean) proves `B36_6_main`: for every real x,
Σ φ(n)/n^x is summable iff x > 2, and the partial sums of Σ (−1)^(n+1) φ(n)/n^x converge iff x > 2.
Parts: `B36_6_first`, `B36_6_alt_conv` (x > 2), `B36_6_alt_div` (x ≤ 1, terms do not tend to 0),
`alt_div_le_two` (0 < x ≤ 2): instead of the exact mean value, the elementary lower bound
Σ_(n<N) (−1)^(n+1) φ(n) ≥ N²/40 − (5/4)N − (N log N)/2 (`A_lower`) and Kronecker's lemma
(`kronecker`, summation by parts). Outside Lean: nothing.

**Review level.** `lean-proof`: the result is proved in Lean + Mathlib ([`B36_6_mathlib.lean`](B36_6_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`).
**Prior art.** Partly known / textbook: Σφ(n)/n^x = ζ(x−1)/ζ(x) for x > 2 is standard, and the alternating case follows by partial summation from the asymptotic of Σ(−1)^(n−1)φ(n) ([Tóth, J. Integer Seq. 20 (2017) 17.2.1](https://cs.uwaterloo.ca/journals/JIS/VOL20/Toth/toth25.html)). Ecker's published comment (AMATYC Review 5 (1983)) not seen. 2026-11-04.
