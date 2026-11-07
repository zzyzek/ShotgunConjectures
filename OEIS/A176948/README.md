# OEIS A176948: every n >= 4 except 6 has an n-gonal number that is not k-gonal for 3 <= k < n

**Source.** [A176948](https://oeis.org/A176948) (Shevelev, 2010): a(n) = least x with A176774(x) = n, where
A176774(x) is the least k >= 3 with x k-gonal; a(n) = 0 if there is none. Conjecture in the entry: for every
n >= 4, n != 6, some n-gonal number is not k-gonal for 3 <= k < n (so a(6) = 0 is the only zero). (OEIS text
checked 2026-11-06.)

**Result.** True.

**Argument.** P_k(m) = ((k-2)m(m-1) + 2m)/2. Fix n, put a = n-2 >= 2, a != 4, and for 3 <= k < n put
b = k-2 in [1, a-1] and C = b(a-2)^2 - a(b-2)^2 = (a-b)(ab-4).
1. C != 0: a > b, and ab = 4 with b < a forces (a, b) = (4, 1), i.e. n = 6. Also |C| < n^3.
2. If N = P_n(j) = P_k(i), then with X = 2aj - (a-2), Y = 2bi - (b-2) we have 8aN + (a-2)^2 = X^2,
   8bN + (b-2)^2 = Y^2, hence a(bX^2 - C) = (aY)^2.
3. For a prime p > 3 with p not dividing abC, some x in Z/p makes a(bx^2 - C) a non-square. Otherwise
   s -> a(bs - C) maps the set S of squares (with 0) injectively into itself, so permutes it; summing over S
   and using sum_{s in S} s = (1/2) sum_x x^2 = 0 gives aC|S| = 0 in Z/p, but 0 < |S| < p.
4. Take distinct primes p_k > n^3 + 2 (k = 3..n-1), the residues x_k of step 3, and j by the Chinese remainder
   theorem with 2aj - (a-2) = x_k mod p_k. Then N = P_n(j) is n-gonal, and by step 2 it is k-gonal for no
   3 <= k < n.

**Evidence.**
- Lean (Mathlib): [`A176948_mathlib.lean`](A176948_mathlib.lean). `IsPolygonal k N := ∃ m, 2N = (k-2)(m(m-1)) + 2m`.
  Main theorem `A176948_conjecture : 4 ≤ n → n ≠ 6 → ∃ N, IsPolygonal n N ∧ ∀ k, 3 ≤ k → k < n →
  ¬ IsPolygonal k N`. Lemmas `key_identity` (step 2), `C_bounds` (step 1), `sum_squares_zero`, `exists_nonsq`
  (step 3, library `OpenProblemsLib.Misc`), CRT via `Nat.chineseRemainderOfFinset` with primes `Nat.nth Nat.Prime (n^3 + k)`. Check
  `tools/leancheck-mathlib.sh`: OK, no warnings, axioms propext, Classical.choice, Quot.sound.
- [`certificate/check.py`](certificate/check.py): least witnesses for n = 4..150 (reproduces the data
  4, 5, 0, 7, 8, 24, 27, ...); none for n = 6.
- Outside Lean: none. Not in Lean: that the theorem's witness is the least one (the entry's a(n) values).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: entry and history (conjecture unchanged), web search (only A090467-type
material, no proof), google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs trees (no file). The scan
record's audit note sketched a Pell-counting heuristic; the residue argument here is ours.
