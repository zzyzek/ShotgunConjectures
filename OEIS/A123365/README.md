# OEIS A123365: cubes mod n, partial result (two prime factors)

**Source.** OEIS [A123365](https://oeis.org/A123365): numbers k with A046530(k) = (k+2)/3, where
A046530(k) is the number of distinct cubes mod k (offset 1). Conjecture: apart from a(1) = 1 these are
exactly the primes p = 1 (mod 6). (OEIS text, CC BY-SA 4.0.)

**Result (partial; the conjecture stays open).** Write c(n) for the number of cubes mod n.
- If n has at most two distinct prime factors and 3c(n) = n + 2, then n = 1 or n is a prime = 1 (mod 6)
  (`three_c_eq_one_factor`, `three_c_ne_of_two_factors`).
- For primes p = 1 (mod 6), q = 2 (mod 3) and e >= 1, (p + 2) c(q^e) != p q^e + 2 (`cq_equation_no_solution`).
  This is the prime-power case of the second equation left by the local bounds.

**Argument.** Local bounds (method multiplicative-local-bounds) reduce every other term to the two exact
equations 3c(n) = n + 2 (all prime factors = 2 mod 3) and (p + 2) c(B) = pB + 2 (B built from such primes).
For two prime factors the cases split by residues mod 3: both 1 mod 3 fails by a ratio bound, both
2 mod 3 fails since 3(x-1)(y-1) >= xy + 2, and the mixed case reduces to the second equation with B a
prime power. There, (p + 2) s1 = p G with G = 1 + q + ... + q^(e-1) = 1 (mod q), and s1 mod q is 0, 1 or
q by e mod 3; this forces q = 2, e = 3t + 1 and (8^t - 1)(3p - 8) = 7, impossible.

**Evidence.**
- Lean: `A123365_mathlib.lean` (Mathlib), with c = `cubeCount` (cubeCount n = #{x³ mod n : 0 ≤ x < n}):
  `three_cubeCount_eq_one_factor`, `three_cubeCount_prime`, `three_cubeCount_ne_of_two_factors`,
  `cq_equation_no_solution`. The closed forms of c at prime powers and the multiplicativity of c are proved
  there (`cubeCount_mul` by the Chinese remainder theorem; `cubeCount_prime_pow_two`,
  `cubeCount_prime_pow_one` from c(p^f) = #(unit cubes mod p^f) + c(p^(f−3)), where the unit cubes number
  φ(p^f) when 3 ∤ φ(p^f) and φ(p^f)/3 when the unit group is cyclic with 3 | φ(p^f)). Added 2026-11-08.
- `certificate/cube_checks.py`, `certificate/probe.py`: brute-force checks of the closed forms;
  `certificate/a123365_scan.py`: all n < 10^7 with 3c(n) = n + 2 are 1 and the primes 1 mod 6.

**Outside Lean.** For the two-prime-factor theorem: none (only reading `cubeCount` as A046530). With three or more prime factors the argument does not carry over (see methods/attempts.jsonl and the core
question core-multiplicative-exact-target).

**Review level.** `lean-proof` for the one- and two-prime-factor theorems and rung R2 (no hypotheses left);
`rechecked` for the paper rungs R4–R8.
**Prior art.** OEIS entry (still a conjecture), formal-conjectures (no file), web search, 2026-11-05: no
proof found.

## Ladder rungs (2026-11-08, conjecture-ladder experiment)

Full write-up: `../open-problems/docs/LADDER-perfect-2026-11-08.md`. Notation: exceptional n = a solution of
3c(n) = n + 2 other than 1 and the primes ≡ 1 (mod 6); case A: n = pB, case B: all primes ≡ 2 (mod 3).

### New results

| Rung | Statement | Evidence |
|---|---|---|
| R2 | no exceptional n is even with exactly 3 distinct prime factors (every p) | Lean `three_cubeCount_ne_two_and_two_odd` (no hypotheses; via `three_c_ne_two_and_two_odd`, `two_mixed`) in `A123365_ladder_mathlib.lean` |
| R4/R5 | for each K: finitely many case-B solutions with ω ≤ K; for each K and each p: finitely many case-A solutions n = pB with ω(B) ≤ K | paper (Dickson-type compactness; every limit equation fails mod 3) |
| R6 | the exceptional n ≤ x number O(x^(1/2)) | paper (B = 2^e · powerful, p determined by B) |
| R7 | an infinite exceptional family with bounded ω has p → ∞ and every odd prime q of B with (q − 1)/q² < 2/(p + 2) | paper |
| R8 | no exceptional n with ω(n) = 3 and p ≤ 10^5 | paper reduction (r pinned to a window of ≤ 5 integers by an exact identity; explicit bound on q^a) + complete search `certificate/k3solve.py` |

*Argument for R2.* Residues of the two odd primes x, y mod 3: (1, 1) and (2, 2) by local ratio bounds;
(1, 2) with the ≡ 1 prime squared or more by 3c(X) + 2 ≤ X; with it to the first power the equation is
(x + 2)c(2^e)c(r^b) = x 2^e r^b + 2: parity kills e ≢ 1 (mod 3), 8c(2^e) ≤ 5·2^e kills e ≥ 4, and e = 1
reduces, via (r² + r + 1)c(r^b) = r^(b+2) + β, to Y(2r² − x(r + 1)) = r² + r + 1 − (x + 2)β, which has no
solution for each class of b mod 3 (b ≡ 2 forces x = 2r − 1 and then r | 1).

*Argument for R4/R5.* Ratios c(q^a)/q^a = (q² + α/q^a)/(q² + q + 1) with α > 0 depending on a mod 3. Along a
hypothetical infinite family pass to a subsequence where each prime power is constant, has fixed prime and
exponent → ∞ (ratio → q²/(q² + q + 1)), or has prime → ∞ (ratio → 1). The limit equation
κ∏c(X_i)∏q_j² = θ∏X_i∏(q_j² + q_j + 1) with (θ, κ) = (1, 3) or (p, p + 2) fails mod 3.

### Boundary and posed conjecture

First rung not proved: ω(n) = 3 with two odd primes q, r ≡ 2 (mod 3), uniformly in p. The fixed-p
argument loses its contradiction because the target p/(p + 2) → 1. Exponent pattern (2, 2) is the
equation p x² y² + 2 = (p + 2)(x² − x + 1)(y² − y + 1), a bidegree-(2, 2) curve for each p.
Conjecture L: no exceptional n has ω(n) = 3. Conjecture L2: the only integer solution of the (2, 2)
equation with 2 ≤ x < y, p ≥ 1 is (2, 8, 4). Evidence: R8; `certificate/scanA3.py` (q < r < 200,
a, b ≤ 12: B − c(B) never divides 2(B − 1)); `certificate/ab22.c` (x ≤ 3000, y ≤ 2x^(3/2) + 3: only (2, 8, 4)).

### Outside Lean (this section)

Outside Lean: Theorem R4/R5 (paper), R6, R7, the reduction and the computation for R8. R2 is fully in Lean
(the closed forms and multiplicativity of c are proved for `cubeCount`, 2026-11-08).

### Prior art (2026-11-08)

Web search (A123365, number of cubes mod n, power-residue counts: Finch–Sebah, Seraj 2022): no result on the
equation. Methods compared: Dickson 1913, Pomerance 1977, Nielsen (fixed-K bounds for odd perfect and
Lehmer numbers). R4/R5 use Dickson's method on a new function; R2, R6, R7, R8 are specific to this equation.
