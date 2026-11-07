# OEIS A217738: numbers k with k(k+1) | Fibonacci(k): all terms are multiples of 12

**Source.** [A217738](https://oeis.org/A217738), numbers k such that Fibonacci(k) is divisible by k*(k+1).
Comment: "Conjectures: the sequence is infinite; all terms are divisible by 12." (entry checked 2026-11-07).

**Result.** The divisibility conjecture is true: every term is a multiple of 12. The infinitude
conjecture is open (see below).

**Argument.** Fibonacci numbers modulo 2 have period 3 with zeros exactly at multiples of 3, and modulo 3
period 8 with zeros exactly at multiples of 4. Since 2 divides k(k+1), 2 divides F(k), so 3 | k. Then
3 | k | F(k), so 4 | k. Hence 12 | k.

**Infinitude (open).** k is a term iff z(k) | k and z(k+1) | k, where z(m) is the rank of apparition
(least j with m | F(j)). If p = k+1 is a prime with p ≡ ±1 (mod 5) then z(p) | p-1 = k, so
k = p-1 is a term whenever p-1 belongs to A023172 (m | F(m)). For instance k = 2^a 3^b 5^c with
a >= 2, b >= 1, c >= 1 satisfies z(k) | k (z(2^a) | 3*2^(a-1), z(3^b) = 4*3^(b-1), z(5^c) = 5^c), and k+1 ≡ 1
(mod 5); so infinitely many primes of the form 2^a 3^b 5^c + 1 (a Pierpont-type question, open) would give
infinitely many terms. Among the 723 terms up to 10^6, k+1 is prime for 708; the 15 others have k+1
squarefree with every prime factor q satisfying z(q) | k (certificate/terms.out).

**Evidence.**
- Lean (core): [`A217738.lean`](A217738.lean), theorem `A217738_div12` (k(k+1) ∣ fib k → 12 ∣ k), via
  `fib_mod_two` (2 ∣ fib n ↔ 3 ∣ n) and `fib_mod_three` (3 ∣ fib n ↔ 4 ∣ n); `A217738_60` checks the first
  term. Checked with `tools/leancheck.sh`, no warnings, axioms at most propext, Quot.sound.
- [`certificate/terms.gp`](certificate/terms.gp), [`certificate/terms.out`](certificate/terms.out): all
  terms up to 10^6 (723 terms), and the factorizations of the 15 terms with k+1 composite.
- Outside Lean: none for the divisibility statement. The infinitude remarks are not proved here.

**Review level.** `lean-proof` (divisibility by 12 only).

**Prior art.** OEIS A217738 (conjectures still listed), A023172 (m | F(m)), google-deepmind/formal-conjectures
(no file), otoi-lab/oeis-lean-proofs (none); 2026-11-07. The divisibility argument is immediate from the
periods of F mod 2 and mod 3.
