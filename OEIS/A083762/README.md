# OEIS A083762: the sequence never terminates (partial; "every number appears" open)

**Source.** [A083762](https://oeis.org/A083762) (Amarnath Murthy and Meenakshi Srikanth, May 06 2003): rearrangement of
the natural numbers such that the concatenation of the terms from the first one, followed by the digit 1, is prime:
1, 3, 2, 4, 9, 5, 13, ... (11, 131, 1321, 13241, ... are prime). "Conjecture: every natural number belongs to this
sequence." (OEIS text, CC BY-SA 4.0, checked 2026-11-07.)

**Reading.** a(1) = 1 and a(n) is the least unused positive integer m such that C m 1 is prime, where C is the
concatenation of a(1..n-1).

**Result.** Partial: a(n) exists for every n (the greedy never gets stuck). Whether every number appears is open.

**Argument.** Let C be the current concatenation and eps = 1/(2C + 2). By the prime number theorem for primes
== 1 (mod 10), every interval (x, (1 + eps) x] with x large contains a prime p == 1 (mod 10). Take d large and
x = (10C + 1) 10^d; then (1 + eps) x < (10C + 10) 10^d, so p = 10(C 10^d + m) + 1 with 10^(d-1) < m < 10^d. So m has d
digits, is unused for d large, and the concatenation C m 1 = p is prime; a least such m exists.

**Evidence.** Lean: [`A083762_mathlib.lean`](A083762_mathlib.lean) (Mathlib + vendored PNT+), checked 2026-11-08.
- `prime_one_mod_ten_window`: for 1 ≤ A, A + 2 ≤ B there are arbitrarily large d with a prime p ≡ 1 (mod 10) in
  (A·10^d, B·10^d). From `WeakPNT_AP` (PNT+: ψ(N; 10, 1)/N → 1/4, Wiener–Ikehara with Dirichlet L-functions) and
  ψ − θ = O(√x) (`Chebyshev.psi_sub_theta_le_mul_sqrt`, Mathlib): the window carries ψ-mass ≥ 10^d/8, while
  proper prime powers carry O(10^(d/2)).
- `exists_next`: for every C and every finite set U there is m > 0, m ∉ U, with C‖m‖1 prime (A = 10C + 1,
  B = 10C + 10, m = (p − 1)/10 − C·10^d has exactly d digits).
- `a`, `state`, `a_spec`, `a_min`: the sequence as defined in **Reading**, total; `a_injective`; `a_zero`, `a_one`
  (a(1) = 1, a(2) = 3).
- Outside Lean: none for the partial result (only reading `concat1` and `a` as the OEIS definition).

**Review level.** `lean-proof` (partial result: the sequence never terminates).

**Prior art.** Checked 2026-11-07: entry and b-file reference (Diana Mecum, n <= 200); no statement that the sequence
is infinite was found. Obstruction analysis for the full conjecture: `open-problems/work/OEIS-A083762/REPORT.md`
(equivalent to primes in the orbit C_n 10^(d+1) + 10u + 1 for the least unused u; heuristically true with polynomial
delays, no method).
