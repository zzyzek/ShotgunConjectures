# OEIS A094787: every prime is a least prime p with p + n a perfect power

**Source.** [A094787](https://oeis.org/A094787) (a(n) = smallest prime p with p + n a perfect power m^k,
k ≥ 2), comment: "Conjecture: every prime is contained in this sequence." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Fix a prime q. For m > q put n = m^2 − q ≥ 1, so q + n = m^2. For a prime p < q, p + n lies in
[m^2 − q + 2, m^2 − 1]; this window contains no square, since (m−1)^2 < m^2 − q + 2. So a(n) = q as soon as
the window holds no non-square perfect power. The windows for different m > q are disjoint, and the
non-square perfect powers up to M^2 number O(M^(2/3) log M) (cubes and higher powers), so fewer than
M − q values of m ≤ M are blocked once M is large. Hence some m works.

**Evidence.**
- `certificate/check.py`: for every prime q < 5000, finds such m and confirms a(m^2 − q) = q.
- Lean (Mathlib): [`A094787_mathlib.lean`](A094787_mathlib.lean), theorem `A094787_conjecture`: for every prime q
  there is n ≥ 1 with q the least prime p such that p + n = c^k, k ≥ 2. The counting bound is proved in the file
  (`card_blocked_le`: blocked m ≤ 2^(3t) inject into pairs (c, k) with c < 4^t, k < 6t). Nothing outside Lean.

**Review level.** `lean-proof`.
**Prior art.** New: no source found. [A094787](https://oeis.org/A094787) still has the conjecture. Searched OEIS entry, references and history, web. Checked 2026-11-04.
