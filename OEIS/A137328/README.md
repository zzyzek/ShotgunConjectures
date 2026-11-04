# OEIS A137328: the prime 2 never occurs

**Source.** OEIS [A137328](https://oeis.org/A137328): a(n) = prime(n) - primorial(k), k maximal
with primorial(k) ≤ prime(n). Conjecture: "Each prime number appears in this sequence at least
once." (OEIS text, CC BY-SA 4.0.)

**Result.** False: 2 is never a term. For odd primes the statement is open; every odd prime
q < 10^6 occurs.

**Argument.** For every prime p, primorial(1) = 2 ≤ p, so the maximal k is ≥ 1 and the subtracted
primorial P is even and ≥ 2. If p - P = 2 then p = P + 2 is even and ≥ 4, so not prime.
For an odd prime q to occur one needs k with p_k < q (otherwise q | P + q), P + q prime, and
P + q < primorial(k+1), i.e. q < P (p_(k+1) - 1); this is a finite search per q.

**Evidence.**
- [`A137328.lean`](A137328.lean): the parity step (`two_never`).
- [`A137328_mathlib.lean`](A137328_mathlib.lean), `A137328_main`: with primorial(k) = ∏_{i<k} `Nat.nth Nat.Prime` i
  and p = prime(n), every k with primorial(k) ≤ p < primorial(k+1) (the maximal k) has p − primorial(k) ≠ 2;
  `A137328_exists_k`: such k exists. Outside Lean: nothing (for "2 never occurs").
- `certificate/a137328.gp` (scan, PARI, 52 s): every odd prime q < 10^6 has a valid k (largest
  needed k = 732, at q = 687359). Not re-run for this write-up; the disproof does not depend on it.

**Review level.** `lean-proof` (of the statement "2 never occurs"), in [`A137328_mathlib.lean`](A137328_mathlib.lean).

**Prior art.** Verdict new, immediate (OEIS status conjecture; searched 2026-11-04). That 2 never occurs is not recorded for A137328; the odd-prime part stays open. Sources: [OEIS A137328 (fetched 2026-11-04)](https://oeis.org/A137328): still says Conjecture: each prime appears; [OEIS A137330 (fetched 2026-11-04)](https://oeis.org/A137330): reverse-difference sister: a comment notes 2 and 5 cannot appear there (not this sequence). Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; OEIS A136437, A137330; Google: A137328 primorial.
