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
- Lean: `A123365_mathlib.lean` (Mathlib). The closed forms of c at prime powers and the multiplicativity of c
  enter as hypotheses of the theorems.
- `certificate/cube_checks.py`, `certificate/probe.py`: brute-force checks of the closed forms;
  `certificate/a123365_scan.py`: all n < 10^7 with 3c(n) = n + 2 are 1 and the primes 1 mod 6.

**Outside Lean.** The closed forms of c(q^e), c(p^e) and multiplicativity of c (checked by brute force only).
With three or more prime factors the argument does not carry over (see methods/attempts.jsonl and the core
question core-multiplicative-exact-target).

**Review level.** `rechecked` (Lean checked by the second reader; hypotheses checked numerically).
**Prior art.** OEIS entry (still a conjecture), formal-conjectures (no file), web search, 2026-11-05: no
proof found.
