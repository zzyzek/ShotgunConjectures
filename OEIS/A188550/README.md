# OEIS A188550: Shevelev's extended-range conjecture is false (n = 208)

**Source.** [A188550](https://oeis.org/A188550): a(n) is the maximal number of divisors d > 1 of n - k such that
k | n - d, over k = 2, 3, ..., floor(sqrt(n)) (offset 4). Comment by Vladimir Shevelev, Apr 10 2011: if k runs
through 2, ..., floor((n-2)/2) instead, then from n = 6 on the sequence is unchanged. Further comments by
Shevelev, Jan 21 2013: 1) 5, 7, 13 are the only primes p with a(p) = 1; 2) 11 and 19 are the only primes p with
a(p) = 2. (OEIS text, CC BY-SA 4.0; entry checked 2026-11-07, conjectures still listed.)

**Result.** The 2011 conjecture is false. The least counterexample is n = 208: a(208) = 4, while k = 16 ≤ 103
gives 6. Below 20000 there are 381 counterexamples (first ones 208, 221, 312, 391, 504, 672, 799, 1000).
Side result: the 2013 conjectures 1) and 2) are also false: a(61) = 1 (this value is in the entry's own data)
and a(1321) = 2. Below 200000 the primes with a(p) = 1 are 5, 7, 13, 61 and those with a(p) = 2 are 11, 19, 1321.

**Argument.** 208 - 16 = 192 = 2^6·3. Its divisors d > 1 with 16 | 208 - d are the multiples of 16 among them:
16, 32, 48, 64, 96, 192, six in all. For k = 2..14 (floor(sqrt 208) = 14) the counts are at most 4 (attained at
k = 4 and k = 13). For p = 61 every k = 2..7 gives only d = 61 - k. For 1321 every k = 2..36 gives at most 2.

**Evidence.**
- Lean (core): [`A188550.lean`](A188550.lean): `a_208`, `cnt_208_16`, `aExt_208`, `A188550_conjecture_false`
  (`¬ ∀ n ≥ 6, aExt n = a n`), `a_61`, `a_1321`, `prime_61`, `prime_1321`, all by kernel evaluation of the
  definitions (sqrt range written as k·k ≤ n). Checked with `tools/leancheck.sh`; no axioms used.
- [`certificate/check_A188550.py`](certificate/check_A188550.py): the definition reproduces the entry's 117
  data terms; lists the counterexamples (`python3 check_A188550.py 20000`: 381).
- [`certificate/check_conj12.py`](certificate/check_conj12.py): primes with a(p) ∈ {1, 2} below 200000.
- Outside Lean: none. The counts below 20000 and 200000 are from the scripts only.

**Review level.** `lean-witness`.

**Prior art.** Checked 2026-11-07: the OEIS entry (current version, no mention of 208, 61 as an exception, or
1321), google-deepmind/formal-conjectures, otoi-lab/oeis-lean-proofs: nothing found. Shevelev's 2013
conjecture 3) (on the least k for n = m^2) was not examined.
