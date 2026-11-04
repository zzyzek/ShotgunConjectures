# OEIS A165640: a(n) = floor(4(n+4)/5) - floor(2(n+4)/3)

**Source.** OEIS [A165640](https://oeis.org/A165640): number of multisets of n integers, each -2,
+1 or +3, with sum 3. Conjecture: "a(n) = Floor[4*(n+4)/5] - Floor[2*(n+4)/3]." (OEIS text,
CC BY-SA 4.0.) Offset 1.

**Result.** True for n ≥ 1 (at n = 0 the formula gives 1, the count is 0).

**Argument.** Let x, y, z be the multiplicities of -2, 1, 3. Then y = n - x - z and the sum
condition is 3x = n - 3 + 2z. So a(n) counts z ≥ 0 with z ≡ n (mod 3), 2z ≥ 3 - n and
5z ≤ 2n + 3 (from y ≥ 0). For n ≥ 3 this is the number of z ≡ n (mod 3) in
[0, floor((2n+3)/5)], a quasi-polynomial of degree 1 in n with period 15. The floor formula is a
quasi-polynomial of the same kind (periods 5 and 3). Two such functions that agree on 2 full
periods agree everywhere (METHODS §6); n = 1, 2 are checked directly.

**Evidence.**
- [`A165640.lean`](A165640.lean): brute-force count equals the formula for 1 ≤ n ≤ 60
  (`decide`). Outside Lean: the interval description of the count, i.e. that it is a degree-1
  quasi-polynomial with period 15 for n ≥ 3.
- `certificate/a165640.py`: agreement for 1 ≤ n ≤ 400.
- Lean (Mathlib): [`A165640_mathlib.lean`](A165640_mathlib.lean), `A165640_ms_main`: for every n ≥ 1, the number of multisets of size n from {-2, 1, 3} with sum 3 (`Finset.sym`) is floor(4(n+4)/5) - floor(2(n+4)/3). Nothing outside Lean.

**Review level.** `lean-proof` (Mathlib file above).

**Prior art.** Verdict new, immediate (OEIS status conjecture; searched 2026-11-04). No proof found. Sources: [OEIS A165640 (fetched 2026-11-04)](https://oeis.org/A165640): formula still labelled Conjecture; Barker g.f. labelled empirical. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; Google: A165640 multisets -2 1 3.
