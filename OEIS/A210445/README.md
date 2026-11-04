# OEIS A210445: a(n) < n for n > 1 and a(n) < n/2 for n > 47 (least k with kn practical)

**Source.** OEIS [A210445](https://oeis.org/A210445): least positive k with k n practical.
Conjecture (Sun, 2013): "a(n)<n for all n>1, and a(n)<n/2 for all n>47." (OEIS text,
CC BY-SA 4.0.)

**Result.** True.

**Argument.** Stewart–Sierpiński: m = p_1^e_1 ··· p_r^e_r (p_1 < ... < p_r) is practical iff
p_1 = 2 and p_(i+1) ≤ 1 + σ(p_1^e_1 ··· p_i^e_i) for all i.
- n not prime, largest prime factor P: take k = 2^t with 2^t < P ≤ 2^(t+1) (k = 1 if n is a power
  of 2). In kn the power of 2 is ≥ 2^t, so 1 + σ(2-part) ≥ 2^(t+1) ≥ every odd prime of n:
  kn is practical. k < P ≤ n/2 (n composite) gives both bounds.
- n = p prime: k = 2^t with 2^t < p ≤ 2^(t+1) makes kp practical and k < p, so a(p) < p.
  For a(p) < p/2: k in the family {2^a·105, 2^a·165 : a ≥ 3} is practical, and for p > 11,
  kp is practical iff p ≤ 1 + σ(k). Consecutive σ-values in the family differ by a factor ≤ 1.5,
  the smallest is σ(8·105) = 2880, and k/σ(k) ≤ 0.306 in the family. So for p ≥ 2881 the least k
  in the family with σ(k) ≥ p - 1 has k ≤ 0.306 · 1.5 (p - 1) < p/2. Primes 47 < p < 2881 are
  checked directly.

**Evidence.**
- `certificate/a210445.py` (scan, re-run): a(n) computed for 2 ≤ n ≤ 6000 (no violation), and the
  family bound for primes 2881 ≤ p < 2·10^6 (max k/(p-1) = 0.4574).
- [`A210445_mathlib.lean`](A210445_mathlib.lean) (Mathlib): `A210445_main` proves both bounds
  (as: some k ≥ 1 with k < n, resp. 2k < n, and k n practical, with practical defined directly by
  sums of distinct divisors). Proves the sufficient direction of Stewart–Sierpiński (adding a
  prime q ≤ σ(m) + 1 keeps "every j ≤ σ(m) is a sum of distinct divisors"); primes
  47 < p ≤ 840 by a table of k and factorisations of k p checked with `decide +kernel` (coverage
  of all primes in the range included); primes p > 840 by the family 2^(a+2)·105, 2^(a+2)·165
  (starting at 420, σ = 1344, which already gives 2k < p there, so the 2881 threshold is not
  needed). Outside Lean: nothing.

**Review level.** `lean-proof` ([`A210445_mathlib.lean`](A210445_mathlib.lean)). Before:
`rechecked` (argument re-derived; script re-run).

**Depends on (Mathlib).** Stewart–Sierpiński characterisation of practical numbers (not in Mathlib).

**Prior art.** New. [OEIS A210445](https://oeis.org/A210445) (fetched 2026-11-04) still states the conjecture; its 2025-2026 edits are link fixes. Sun's linked [arXiv:1211.1588](https://arxiv.org/abs/1211.1588) and web searches (practical numbers, least k with kn practical) found no proof. Searched: entry, OEIS cross-reference search, edit history, arXiv, web. Worth an OEIS comment. (Prior-art review 2026-11-04.)
