# OEIS A088082: the jump indices n do not all have n + 1 prime (n = 3, 5, 32, ...)

**Source.** [A088082](https://oeis.org/A088082) (Amarnath Murthy, 2003): indices n of terms in A088081 such that
A088081(n+1) > A088081(n). A088081(n): smallest prime(k) such that for every r = 1..n there exist i < j <= k with
prime(j) - prime(i) = 0 (mod r). "Conjecture: n+1 is a prime." (OEIS text, CC BY-SA 4.0, fetched 2026-11-07.)

**Result.** False. A088081 begins 3, 5, 5, 7, 7, 11, 17: A088081(4) = 7 > A088081(3) = 5, so n = 3 is a term with
n + 1 = 4, and A088081(6) = 11 > A088081(5) = 7 gives n = 5, n + 1 = 6. The entry's own data list 3 and 5 as terms.
Further: n = 32 (A088081(33) = 71 > 67, n + 1 = 33), 48, 54, 62, 74, 90, ... Among the 331 terms below 2000,
194 have n + 1 composite.

**Argument.** For r = 4 the primes 2, 3, 5 are distinct mod 4, and 3, 7 are congruent; for r <= 3 the primes up to
5 suffice (3 - 2, 5 - 3, 5 - 2). So A088081(3) = 5 and A088081(4) = 7. Similarly for r = 6: 2, 3, 5, 7 are
distinct mod 6, while 5, 11 are congruent.

**Evidence.**
- Lean (core): [`A088082.lean`](A088082.lean). `a n` is the least prime P < 200 with the property for r = 1..n;
  `a3`, `a4`, `a5`, `a6`, `a32`, `a33` and `counterexample_3`, `counterexample_5`, `counterexample_32`
  (jump at n with n + 1 not prime), all by `decide`. `tools/leancheck.sh`: OK, no warnings, no axioms.
- [`certificate/check.py`](certificate/check.py): A088081 and A088082 for n <= 2000 (matches the entry's data).
- Outside Lean: none. The Lean definition `a` is a direct transcription of the OEIS definition with a search
  bound of 200, which the found values respect.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-07. The counterexamples are in the entry's data; no comment notes them. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones, 2026-11-06).
