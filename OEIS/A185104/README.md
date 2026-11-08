# OEIS A185104: after 3911 the next terms are R19 and R23 (proved)

**Source.** [A185104](https://oeis.org/A185104): primes such that every swap of a pair of digits also gives a
prime. Data: 11, 13, 17, 31, 37, 71, 73, 79, 97, 113, 131, 179, 199, 311, 337, 373, 733, 919, 991, 3911.
Comment: "Conjecture: next terms are 1111111111111111111 and 11111111111111111111111." (Entry text via the scan
cache, checked 2026-11-07.)

**Reading.** A swap exchanges the digits at two positions of the decimal expansion (one swap applied to N, as in
the entry's example 1913 -> 9113). Swapping equal digits gives N again. One-digit primes have no pair and are not
listed; we follow the entry and consider N >= 10.

**Result.** True. The terms below 10^23 are the 20 listed terms and R19 = (10^19 - 1)/9; R23 = (10^23 - 1)/9 is a
term. Equivalently, no term has 5 to 23 digits except R19 and R23. Extension: no term has 24 to 40 digits
(the repunits R24..R40 are composite), so the terms below 10^40 are the 20 listed terms, R19 and R23.

**Argument.**
1. *Digits.* If N >= 10 is a term, every digit is in {1, 3, 7, 9}: a digit d in {0, 2, 4, 5, 6, 8} is either the
   last digit of N or can be swapped there, giving a number > 5 divisible by 2 or 5.
2. *Residues by classes.* For m in {7, 11, 13, 37}, 10^6 = 1 (mod m), so N mod m depends only on the counts
   c(d, r) of digit d at positions i = r (mod 6). A swap of digit a at a position of class r with digit b at class s
   changes N by (b - a)(10^r - 10^s) mod m. So whether N or some swap is divisible by 3 (digit sum, swap-invariant),
   7, 11, 13 or 37 is a function of the count vector c. All such numbers are composite (they exceed 37).
3. *Sieve.* `sieve.c` enumerates all count vectors for each length n = 5..23 class by class, keeps for each modulus
   the set of residues of N that would make N or an already-determined swap divisible by m, and prunes as soon as
   that set covers all residues. 353 count vectors survive at n = 23 (from 72 578 complete vectors), and the
   survivors expand to between 40 and 8936 actual numbers per length.
4. *Stage 2.* `stage2.py` tests every expanded number and all its swaps with sympy's `isprime` (BPSW); a swap
   declared composite is composite (BPSW never rejects a prime). The only numbers all of whose swaps pass are R19 and
   R23. Since a repunit is fixed by every swap, R19 and R23 are terms iff they are prime, which they are (Pratt
   certificates, checked in Lean).
5. *Up to 4 digits* and as a cross-check up to 6 digits, stage2.py tests every integer below 10^6 directly: exactly
   the 20 listed terms.

**Evidence.**
- Lean (Mathlib): [`A185104_mathlib.lean`](A185104_mathlib.lean). `R19_term`, `R23_term`: R19 and R23 satisfy the
  entry's definition (`IsTerm`, digits from `Nat.digits 10`, swap by `List.set`), via `repunit_term` and Pratt
  certificates (`prime_of_prattCertifies`, kernel `decide`). Check: `tools/leancheck-mathlib.sh`, exit 0, no
  warnings; axioms at most propext, Classical.choice, Quot.sound; no `sorry`, no `native_decide`.
- [`certificate/sieve.c`](certificate/sieve.c) (steps 2-3) and [`certificate/stage2.py`](certificate/stage2.py)
  (steps 4-5).
- Independent checks: [`certificate/xcheck.py`](certificate/xcheck.py) verifies, for n = 5..10 over all 4^n digit
  strings, that every string outside the surviving count vectors has N or a swap divisible by 3, 7, 11, 13 or 37
  (soundness of the pruning; no exception). [`certificate/brute.c`](certificate/brute.c) enumerates all 4^n strings
  for n = 5..14 directly and keeps those whose N and swaps have no prime factor below 1000: only R11 (n = 11,
  composite) survives, in agreement with stage 2.
- Extension to 24-40 digits: sieve.c for each length (at most 1395 surviving count vectors per length, about 1 minute per length) and
  [`certificate/stage2x.py`](certificate/stage2x.py) on all 24.7 million expanded numbers: no term.
- Outside Lean: the nonexistence of other terms with 5 to 40 digits (computation: sieve.c + stage2.py, checked
  independently by brute force up to 14 digits) and the list of terms below 10^5.

**Review level.** `rechecked` (two independent computations agree up to 14 digits; the main computation alone covers
15-23 digits).

**Prior art.** Checked 2026-11-07: OEIS entry (conjecture still open there), web search (no proof found; the
related absolute primes A003459 are handled by Richert-type arguments that use all permutations, not single
swaps), google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs (no A185104).
