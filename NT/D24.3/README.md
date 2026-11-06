# Guy D24 (Erdős): the weighted count of a primitive set is not x²/6 + O(x)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section D24 (end). Paraphrased: for A = {a_1 < … < a_k} ⊆ [1, x] with no a_i dividing another, let f(A; n) count the a_i below n. How large can Σ_{n=1}^{x} f(A; n) be; is the maximum x²/6 + O(x), attained perhaps by the integers in (x/3, 2x/3)?

**Reading.** Σ_{n=1}^{x} f(A; n) = Σ_{a ∈ A} (x + 1 − a) when f counts a_i ≤ n; Guy's "a_i < n" lowers it by |A| ≤ x, which is inside O(x).

**Result.** No. The maximum is at least (14/81)x² − O(x) > x²/6 + Cx for every C and all large x; a refinement gives (3/14)x² − O(x), and exact maxima for x ≤ 300 are about 0.227x².

**Argument.** Let x = 18N and A_N = {odd a : 6N < a < 18N} ∪ {a ≡ 2 (mod 4) : 4N < a < 12N}.
A_N is primitive: if a | b, a ≠ b, then b ≥ 2a. Two odd elements have b ≥ 3a > 18N. Two elements ≡ 2 (mod 4) have b/a odd, so b ≥ 3a > 12N. An odd a and b ≡ 2 (mod 4) give b ≥ 2a > 12N. An even a cannot divide an odd b.
The weights x + 1 − a are 12N, 12N − 2, …, 2 on the odd part (sum 36N² + 6N) and 14N − 1, 14N − 5, …, 6N + 3 on the other (sum 20N² + 2N). Total 56N² + 8N = (14/81)x² + (4/9)x, against x²/6 = 54N².
Refinement (not in Lean): with odd m ∈ (x/3^{l+1}, x/3^l] and a = 2^l m for l = 0, 1, 2, … the set is primitive (m | m', m ≠ m' forces m' ≥ 3m, hence a lower l for m') and has weight x²/2 · Σ_l [(2/3)3^{−l} − (4/9)(2/9)^l] + O(x log x) = (3/14)x² + O(x log x).

**Evidence.**
- Lean (core): [`D24_3.lean`](D24_3.lean). `D24_3_main`: for every C and x0 there are x ≥ x0 and a primitive A ⊆ [1, x] with x² + C·x < 6·Σ_{n=1}^{x} f(A; n), with f and the sum defined literally. Also `AN_primitive`, `S_AN` (S(A_N, 18N) = 56N² + 8N for all N). Axioms propext, Classical.choice, Quot.sound. Outside Lean: the reading of "a_i < n" versus "≤ n" (an O(x) change); the refinement and the MILP numbers are remarks only.
- `certificate/milp.py`, `certificate/milp.out`: exact maxima by integer programming (SciPy/HiGHS) for x ≤ 300; e.g. x = 300 gives 20443 (x²/6 = 15000, the interval (x/3, 2x/3] gives 15050).

**Review level.** `lean-proof`.

**Prior art.** No source found that states the answer. Searched web (Erdős primitive-set problems, erdosproblems.com, arXiv), formal-conjectures (Erdős 143, 164, 872, 1196, 1217 concern other questions), 2026-11-06. The true constant (between 3/14 and 1/4; 1/4 from one element per chain {m·2^j}) is not determined here.
