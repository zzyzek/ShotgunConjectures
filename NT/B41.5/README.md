# Guy B41: Finucane's lists for the iteration n → φ(n) + 1 are complete

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B41. Finucane iterates n → φ(n) + 1 (primes are fixed points) and
asks whether 5, 8, 10, 12 are the only numbers whose sequence ends at 5, and 7, 9, 14, 15, 16,
18, 20, 24, 30 the only ones ending at 7.

**Result.** Yes, both lists are complete.

**Argument.** The set of n reaching a prime q is closed under taking preimages, so it is
obtained from q by repeatedly solving φ(n) = m − 1. φ(n) is even for n ≥ 3, and the inverse
totient sets needed are φ⁻¹(4) = {5, 8, 10, 12}, φ⁻¹(6) = {7, 9, 14, 18},
φ⁻¹(8) = {15, 16, 20, 24, 30}, while 7, 9, 11, 13, 15, 17, 19, 23, 29 (odd) and 14 are not
totients. Preimages of 5: {5, 8, 10, 12}; of 8, 10, 12: none (7, 9, 11 are not totients).
Preimages of 7: {7, 9, 14, 18}; of 9: {15, 16, 20, 24, 30}; of 14, 18, 15, 16, 20, 24, 30:
none (13, 17, 14, 15, 19, 23, 29 are not totients). Inverse-totient sets are finite and
computable from φ(n) ≥ √(n/2).

**Evidence.** `certificate/misc_check.py` (second reader): follows every n ≤ 2000 to its end
point; output matches the two lists.
- Lean (Mathlib): [`B41_5_mathlib.lean`](B41_5_mathlib.lean) proves both lists complete:
  `B41_5_five` ({n | some iterate of n ↦ φ(n) + 1 equals 5} = {5, 8, 10, 12}) and `B41_5_seven`
  (the same for 7 = {7, 9, 14, 15, 16, 18, 20, 24, 30}). It proves n ≤ 2φ(n)^2 by multiplicative
  induction, uses Mathlib's `Nat.totient_even`, and checks n < 393 by `decide +kernel`.
  Outside Lean: none.

**Review level.** `lean-proof`: the result is proved in Lean + Mathlib.
**Prior art.** Not found proved. [OEIS A229487](https://oeis.org/A229487) gives a(3) = 12 and a(4) = 30 (largest n reaching 5 and 7) as conjectural; our result proves both. Related: [OEIS A039650](https://oeis.org/A039650), [Erdős Problems #409](https://www.erdosproblems.com/409) (Finucane; forum not readable here). Verdict: new (worth an OEIS comment). 2026-11-04.
