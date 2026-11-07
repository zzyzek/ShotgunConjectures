# OEIS A217866 / A217976: the last v in A217865 comes before the first v+2

**Source.** [A217866](https://oeis.org/A217866) (last time n appears in A217865) and
[A217976](https://oeis.org/A217976) (first time n appears in A217865); both carry the comment
"Conjecture: the last time n appears is always before the first time n+2 appears."
[A217865](https://oeis.org/A217865) is the sequence of first differences of A050504(n) = floor(n log n)
(its program: floor((i+1) log(i+1)) - floor(i log i)). OEIS entries checked 2026-11-07.

**Result.** True, and stronger: every occurrence of v in A217865 precedes every occurrence of v+2.

**Argument.** Let f(x) = x log x and g(n) = f(n+1) - f(n). Since f is strictly convex on [0, ∞),
g is strictly increasing. Floors move a number down by less than 1, so
A217865(n) = floor f(n+1) - floor f(n) lies strictly between g(n) - 1 and g(n) + 1.
If A217865(m) = v then g(m) < v + 1; if A217865(n) = v + 2 then g(n) > v + 1. So g(m) < g(n) and m < n.

**Evidence.**
- Lean (Mathlib): [`A217866_mathlib.lean`](A217866_mathlib.lean), theorem `A217866_conjecture`
  (A217865 m = v and A217865 n = v + 2 imply m < n), with `A050504 n = ⌊n log n⌋` over the reals.
  Route `g_strictMono` (from `strictConvexOn_mul_log`) and `diff_close`. Checked with
  `tools/leancheck-mathlib.sh`, no warnings, axioms propext, Classical.choice, Quot.sound.
- [`certificate/check.py`](certificate/check.py): recomputes A217865 for n <= 10^6 and reproduces
  the data of A217866 and A217976.
- Outside Lean: none. Not verified in Lean: agreement of the definitions with the OEIS data terms
  (check.py recomputes them in floating point).

**Review level.** `lean-proof`.

**Prior art.** OEIS A217865, A217866, A217976 (conjecture still listed, no proof),
google-deepmind/formal-conjectures (no file for these numbers), otoi-lab/oeis-lean-proofs (none);
2026-11-07. The argument is immediate from convexity of x log x.
