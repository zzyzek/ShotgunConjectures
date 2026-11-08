# OEIS A227864: base-reversal primes, Conjectures 2 and 3

**Source.** [A227864](https://oeis.org/A227864), Carl R. White, Nov 01 2013: smallest base in which n's digital
reversal is prime, or 0 if no such base exists. The entry states three conjectures:
1. 0, 1 and 4 are the only n with no base.
2. n = 2 is the only prime p that must be written in base p + 1 (as a single digit) for its reversal to be prime.
3. "With the restriction gcd(base,n) = 1, a(n) = 0 except for n = 2, 3 and 6k+-1".
(OEIS text, CC BY-SA 4.0, cached entry read 2026-11-08.)

**Reading.** rev_b(n) = the number whose base-b digits are those of n reversed (trailing zeros of n become
leading zeros and drop out). Conjecture 3 is read as stated: the restricted a(n) is 0 for every n that is not
2, 3 or of the form 6k +- 1. The converse (nonzero at every 6k +- 1) is the claim "except" may also suggest; it
is treated separately below.

**Result.**
- Conjecture 2: true. Every prime p >= 3 is written 11 in base p - 1, so its reversal there is p.
- Conjecture 3 (the zero half): true. If 2 | n or 3 | n, n not 2 or 3, b >= 2 and gcd(b, n) = 1, then
  rev_b(n) is not prime.
- Conjecture 1 and the converse half of Conjecture 3: open; checked for n <= 10^6 (no failure; largest
  smallest base 1320 at n = 80850; restricted, largest over composite 6k +- 1 is 467 at n = 709555).

**Argument (Conjecture 3).** Let q in {2, 3} divide n; gcd(b, n) = 1 gives q not dividing b, so b = +-1 mod q.
Write n = sum d_i b^i, i = 0..t. Then n = sum d_i c^i and rev_b(n) = sum d_i c^(t-i) = c^t sum d_i c^i mod q with
c = b mod q, c^2 = 1. So q | rev_b(n). If rev_b(n) is prime it equals q. Since b does not divide n, the last
digit d_0 is nonzero, so the digits of rev_b(n) are those of n reversed and n = rev_b(rev_b(n)) = rev_b(q) = q
(for b > q a single digit; b = 2, q = 3 gives 11). That contradicts n not in {2, 3}.

**Evidence.**
- Lean (Mathlib): [`A227864_mathlib.lean`](A227864_mathlib.lean). `rev b n = Nat.ofDigits b
  (Nat.digits b n).reverse`. Theorems `A227864_conj3` and `A227864_conj2` (with `rev_succ`); lemmas
  `ofDigits_reverse` (reversal multiplies by c^(|L|+1) when c^2 = 1), `dvd_rev`, `rev_rev`. Axioms propext,
  Classical.choice, Quot.sound.
- `certificate/search.py N`: Conjecture 1 and the restricted converse for n <= N (run with N = 10^6, 45 s).
- Outside Lean: the computation for Conjecture 1 to 10^6 (Python). Nothing else; the two theorems are complete.

**Open part.** Conjecture 1 for composite n: bases b in (n/2, n) write n = 1·b + j, with reversal
j(n - j) + 1, so it would follow if j(n - j) + 1 is prime for some 1 <= j < n/2. That is a question about prime
values of a family of quadratics on a short range, out of reach of current methods (it is implied by uniform
Bateman-Horn type conjectures, not by any proved theorem we know).

**Review level.** lean-proof (Conjectures 2 and 3); computation only for Conjecture 1.

**Prior art.** Checked 2026-11-08: OEIS entry and comments, google-deepmind/formal-conjectures (no OEIS/227864
file), otoi-lab/oeis-lean-proofs (no file), web search. No proof found.
