# Guy A3: primes (p^p−1)/(p−1) and (p^p+1)/(p+1)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section A3. Paraphrased: (p^p−1)/(p−1) is prime for p = 2, 3, 19, 31 and (p^p+1)/(p+1) for p = 3, 5, 17, 157; are there more primes p of either kind?

**Result.** Partly answered elsewhere. Minus case: p = 7547 gives a probable prime of 29262 digits (H. Lifchitz; OEIS A088790), so a fifth value exists if that PRP is prime; no further p up to 230000 (Aggarwal, 2026, in A088790). Plus case: no further prime p is known; A088817 (Cyclotomic(2k,k) prime) lists k = 3977 = 41·97 as the next term, not prime, and reports no others below 4700. Both cases remain open in the strict sense (primality of the 7547 number is not proved; infinitude is open).

**Argument.** None of ours; recomputation only.

**Evidence.** `certificate/prp7547.gp`: PARI/gp confirms 7547 is prime, N = (7547^7547−1)/7546 has 29262 digits, 3^(N−1) ≡ 1 (mod N) and BPSW `ispseudoprime(N)` = 1. `certificate/small.gp` (output `small.out`): for primes 3 ≤ p ≤ 500 the probable primes are exactly minus: 3, 19, 31 and plus: 3, 5, 17, 157. Lean: none (a 29262-digit primality proof is out of reach here; a PRP test proves nothing).

**Review level.** `rechecked` (the PRP and the small range).

**Prior art.** OEIS A088790 (Lifchitz PRP 7547; Noe heuristic: next term 10^10–10^11; Aggarwal: Aurifeuillean factors force p ≡ 3 mod 4, none to 230000) and A088817. Searched OEIS, web, formal-conjectures (no entry), 2026-11-06.
