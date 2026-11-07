# OEIS A180710: sigma(n) | a(n) fails at n = 64

**Source.** [A180710](https://oeis.org/A180710) (Hanna, 2010): a(1) = 1, a(n) = sigma(2^(n-1) a(n-1)) for n > 1.
Comment: "Conjecture: sigma(n) | a(n) for n>=1." (OEIS text checked 2026-11-06; data up to a(9).)

**Result.** False. sigma(n) | a(n) holds for 1 <= n <= 63, but sigma(64) = 127 and a(64) = 43 (mod 127). a(64) has 658
digits.

**Argument.** a(n) is computed exactly through its prime factorization: if 2^(n-1) a(n-1) = prod p^e, then
a(n) = prod (p^(e+1) - 1)/(p - 1), and each factor (p^(e+1) - 1)/(p - 1) is factored separately (PARI `factor`),
the results merged. Every prime found is certified by PARI `isprime` (proven primality, APR-CL), so each step
gives the exact prime factorization of a(n) and the next sigma is exact. The first terms equal the entry's data
(and direct `sigma` evaluation for n <= 12). Reducing the factorization of a(64) modulo 127 gives 43.

**Evidence.**
- [`certificate/d.gp`](certificate/d.gp): the computation (gp 2.15.4, `-D recover=0`, exit 0, no errors); prints
  "first failure n=64 sigma(n)=127 a(n) mod sigma(n)=43".
- [`certificate/factorizations.txt`](certificate/factorizations.txt): the prime factorizations of a(2), ..., a(64)
  (792 distinct primes, largest 74 digits, 26 above 2^64).
- Lean: none. Outside Lean: the whole computation (primality of 792 primes and 63 sigma steps). A Lean check is
  possible with Pratt certificates (`tools/pratt_cert.py`) for the 792 primes and Mathlib's multiplicativity of
  sigma, but was not done.

**Review level.** `rechecked` (two PARI scripts with different bookkeeping: whole-number factoring up to n = 40 and
factor-tracking up to n = 64 agree; terms match the data).

**Prior art.** Checked 2026-11-06: entry (no b-file, no annotation), not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs. The counterexample appears new.
