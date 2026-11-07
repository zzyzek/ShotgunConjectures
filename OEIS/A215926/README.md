# OEIS A215926: the power-of-2 conjectures reduce to almost perfect numbers

**Source.** OEIS [A215926](https://oeis.org/A215926), smallest deficient k such that k·n is perfect or
abundant. Comments: "Conjecture: a(n) is 1, 3, or a power of 2." and "Conjecture: The first occurrence of
2^m happens at A014210(m)" (A014210(m) = nextprime(2^m)). (OEIS text, CC BY-SA 4.0.) Both are open
`research open` statements in google-deepmind/formal-conjectures (`OeisA215926`, m ≥ 1 for the second).

**Result (partial).** Call k *almost perfect* if σ(k) = 2k − 1 (powers of 2 are; no others are known).
1. Conjecture 2 holds for m if and only if no almost perfect k that is not a power of 2 satisfies
   nextprime(2^m) ≤ 2k − 1 and k < 2^m.
2. If such a k exists for some m, Conjecture 1 also fails (at n = nextprime(2^m)).
3. No almost perfect numbers other than powers of 2 exist below 2·10⁷, so Conjecture 2 holds for 1 ≤ m ≤ 24
   (the b-file covers m ≤ 13).
So Conjecture 2 is equivalent to a statement about almost perfect numbers (an open problem, Guy B2) and
Conjecture 1 implies it.

**Argument.** Write A(n) = σ(n)/n; k·n is non-deficient iff A(kn) ≥ 2. Let p = nextprime(2^m), so
2^m < p < 2^(m+1) (Bertrand).
- *a(p).* For k < p, p ∤ k and σ(kp) = σ(k)(p + 1). With d = 2k − σ(k) ≥ 1 (k deficient), kp is
  non-deficient iff (2k − d)(p + 1) ≥ 2kp iff 2k ≥ d(p + 1). Since k < p this forces d = 1 and p ≤ 2k − 1.
  k = 2^m works (2^(m+1) ≥ p + 1), a power 2^j with j < m does not (2^(j+1) ≤ 2^m < p + 1), and 3 does not.
  So a(p) = 2^m unless an almost perfect k, not a power of 2, has p ≤ 2k − 1 and k < 2^m; then a(p) is such a
  k, which is neither 1, 3 nor a power of 2 (this gives 2).
- *Nothing earlier.* For 2 ≤ n < p, a(n) ≤ max(3, 2^(m−1)), so a(n) ≠ 2^m. Write n = 2^e·u, u odd.
  If u = 1, a(n) = 3. If u is prime, u + 1 ≤ 2^m (u < 2^m when e = 0 since n < p and n ≠ 2^m; u < p/2 < 2^m
  when e ≥ 1), and 2^j works once 2^(e+j+1) ≥ u + 1, so j ≤ m − 1. If u is composite with least prime
  factor q ≤ √u, then A(u) ≥ 1 + 1/q and A(2^s·u) = (2 − 2^(−s))·A(u) ≥ 2 once 2^s ≥ (q + 1)/2, so 2^j works
  with 2^j ≤ q < 2^m, again j ≤ m − 1.
  Powers of 2 are deficient, so a(n) ≤ 2^j.

**Evidence.**
- Lean (Mathlib): [`A215926_mathlib.lean`](A215926_mathlib.lean), definition as in formal-conjectures.
  `A215926_at_prime`: for every prime p with 2^m < p < 2^(m+1), a(p) = 2^m, or a(p) is almost perfect, not a
  power of 2, with p + 1 ≤ 2·a(p) and a(p) < 2^m. Axioms propext, Classical.choice, Quot.sound; zero warnings.
- [`certificate/ap.py`](certificate/ap.py): σ sieve to 2·10⁷; the only almost perfect numbers are 1, 2, 4, …, 2^24.
- OEIS b-file (n ≤ 10⁴): every value is 1, 3 or a power of 2, and the first 2^m is at nextprime(2^m), m ≤ 13.
- Outside Lean: the "nothing earlier" step (hand proof above), Bertrand for nextprime(2^m) < 2^(m+1)
  (in Mathlib, not wired in), and the σ sieve.

**Review level.** `lean-witness` (main step in Lean; the lower bound for the first occurrence by hand).

**Prior art.** Checked 2026-11-06: both comments are still conjectures in the entry; formal-conjectures lists
them as open. The link to almost perfect numbers was not found in the entry or by web search. Kishore (Math.
Comp. 1978, 1981): an odd almost perfect number > 1 has at least six distinct prime factors.
