# OEIS A187941: a(n) = 2^n exactly for n prime or n = 1 (n ≥ 1); fails literally at n = 0

**Source.** [A187941](https://oeis.org/A187941) (least number with exactly n even divisors,
offset 0), comment: "Conjecture: a(n) = 2^n only if n is prime or if n = 1." (OEIS text,
CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** a(n) = least m ≥ 1 with exactly n even divisors. The entry has offset 0 and
a(0) = 1 = 2^0, with 0 neither prime nor 1, so the literal statement fails at n = 0; the
intended statement is for n ≥ 1.

**Result.** For n ≥ 1: a(n) = 2^n if and only if n is prime or n = 1. At n = 0 the literal
claim fails (a(0) = 2^0).

**Argument.** Odd m has no even divisors, and the even divisors of 2y are 2·(divisors of y), so
m with n ≥ 1 even divisors is 2y with d(y) = n.
- *n composite*, n = uv with u, v ≥ 2: 2^u 3^(v−1) = 2·(2^(u−1) 3^(v−1)) has u·v = n even
  divisors and 2^u 3^(v−1) < 2^u 4^(v−1) ≤ 2^u 2^(u(v−1)) = 2^n, so a(n) < 2^n.
- *n prime*: d(y) = n prime forces y = q^(n−1) with q prime (d is multiplicative), so
  m = 2y ≥ 2^n, and 2^n has n even divisors. *n = 1*: m ≥ 2 = 2^1.

**Evidence.**
- Lean (Mathlib): [`A187941_mathlib.lean`](A187941_mathlib.lean). `A187941_main n (hn : 1 ≤ n) :
  a n = 2 ^ n ↔ n.Prime ∨ n = 1` with `a n = Nat.find (∃ m, 0 < m ∧ evenDivs m = n)` and
  `evenDivs m` = number of even divisors (the entry's definition); `A187941_zero`: a 0 = 2^0.
  Axioms propext, Classical.choice, Quot.sound; zero warnings. Outside Lean: none.
- `certificate/check.py`: brute force (divisor sieve to 2^18) matches the data for n ≤ 18 and
  the equivalence there.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: the entry's own comment gives a(n) = 2·A005179(n) and the
even-divisor count k·Π(e_i + 1), from which the claim follows in a few lines; not stated as
proved there. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
