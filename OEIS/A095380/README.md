# OEIS A095380: the proportion of non-values of σ up to 2^n tends to 1

**Source.** OEIS [A095380](https://oeis.org/A095380) (offset 1): number of integers not exceeding 2^n that are
not a value of σ (the sum-of-divisors function), i.e. terms of A007369 up to 2^n. Conjecture: "ratio of
non-sigma numbers tends to one. Increasing majority of numbers is impossible as a sum of divisors." (OEIS text,
CC BY-SA 4.0.)

**Reading.** "Ratio" is a(n)/2^n.

**Result.** True: a(n)/2^n → 1.

**Argument.** Let V_σ(x) = #{m ≤ x : m = σ(k) for some k}. Then a(n) = 2^n − V_σ(2^n). K. Ford, The
distribution of totients, Ramanujan J. 2 (1998) 67–151 (arXiv:1104.3264), Theorem 1 gives
V(x) = (x/log x) exp{C(log_3 x − log_4 x)^2 + D log_3 x − (D + 1/2 − 2C) log_4 x + O(1)} for totient values,
and Theorem 14 extends Theorem 1 to multiplicative f : ℕ → ℕ with {f(p) − p} finite and not containing 0 and
Σ_{h square-full} h^δ/f(h) ≪ 1 for some δ > 0; Ford names σ as satisfying these (f(p) − p = 1, and σ(h) ≥ h
makes the square-full sum converge for δ < 1/2). Hence V_σ(x) = x/(log x)^{1+o(1)} = o(x), and
a(n)/2^n = 1 − V_σ(2^n)/2^n → 1.

**Evidence.**
- `certificate/check.py` (under a second): recomputes a(1..17), equal to the printed terms, and prints
  a(n)/2^n (0.79 at n = 17). This confirms the reading only; the limit is Ford's theorem.
- No Lean file.
- Outside Lean: Ford 1998 Theorems 1 and 14 (σ case).

**Review level.** `rechecked`. Theorems 1 and 14 and the sentence naming σ read in arXiv:1104.3264 v2.

**Prior art.** Checked 2026-11-05: the entry cites no source for the conjecture (only Cf. A007369). Not in
google-deepmind/formal-conjectures (no `FormalConjectures/OEIS/95380.lean`).
