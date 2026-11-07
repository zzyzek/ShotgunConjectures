# OEIS A102237: a(n) = 2^n for n > 5

**Source.** [A102237](https://oeis.org/A102237) (Giovanni Teofilatto, 2005; corrected and extended by Ray Chandler):
smallest number equal to the product of n primes which is also equal to the sum of n distinct primes. Comment:
"Conjecture: a(n) = 2^n for n>5. - Ray Chandler Feb 25 2005". Data 2, 9, 12, 36, 48, 64, 128, ... (OEIS text,
CC BY-SA 4.0, revision #7 of Nov 01 2019, checked 2026-11-06.)

**Reading.** "Product of n primes" counts multiplicity (a(2) = 9 = 3·3). Every product of n primes is ≥ 2^n, so
a(n) = 2^n iff 2^n is a sum of n distinct primes.

**Result.** True: for every n ≥ 6, 2^n is a sum of n distinct primes, so a(n) = 2^n.

**Argument.** Parity: for even n use n odd primes summing to 2^n; for odd n use 2 plus n − 1 odd primes summing to
2^n − 2. Prime bound used: for every real x ≥ 25 there is a prime in (x, 1.21x] (library theorem
`OpenProblemsLib.ShortIntervalPrimes.exists_prime_Ioc_mul`, proved in Lean from Chebyshev's 1852 bounds plus 85
certified primes; see `lib/docs/short-interval-primes.md`). Write W(k, L, U, M) for: every N ≡ k (mod 2) with
L ≤ N ≤ U is a sum of k distinct odd primes, each ≤ M.
1. *Step.* Assume W(k, L, U, M) with L ≥ 0, M ≥ 25 and 0.42M ≤ 1.21(U − L). Let N ≡ k+1 (mod 2) with
   L + 1.21M ≤ N ≤ U + 2M/1.21. Put b = max(N − U, M) and take a prime q with b < q ≤ 1.21b. Then q > M and
   q > N − U. If b = M then q ≤ 1.21M ≤ min(2M, N − L). If b = N − U then q ≤ 1.21(N − U) ≤ 2M (from
   N ≤ U + 2M/1.21), and 1.21(N − U) ≤ N − L because 0.21N ≤ 0.21U + 0.42M/1.21 ≤ 0.21U + (U − L). So
   N − q ∈ [L, U] has the parity of k, is a sum of k distinct odd primes ≤ M < q, and adding q gives
   W(k+1, L + 1.21M, U + 2M/1.21, 2M).
2. *Iteration.* From W(6, L₀, U₀, M₀) the step gives W(6 + j, L₀ + 1.21M₀(2^j − 1), U₀ + (2/1.21)M₀(2^j − 1),
   M₀2^j) for all j: the width condition holds at every stage because the window widens at slope
   (2/1.21 − 1.21) = 0.443 per unit of M₀(2^j − 1), and 1.21·0.443 = 0.536 ≥ 0.42.
3. *Bases.* Every even N in [62, 152] is a sum of six distinct odd primes ≤ 39 (chain A, M₀ = 39), and every even
   N in [62, 374] is a sum of six distinct odd primes ≤ 78 (chain B, M₀ = 78). Explicit tables, checked in the
   kernel.
4. *Targets.* With t = 2^j ≥ 1: chain A has L = 62 + 47.19(t − 1) ≤ 64t ≤ 152 + 64.46(t − 1) = U, so 2^n
   (n = 6 + j even) is a sum of n distinct odd primes. Chain B has 62 + 94.38(t − 1) ≤ 128t − 2 ≤
   374 + 128.93(t − 1), so 2^n − 2 (n = 7 + j odd, k = n − 1 even) is a sum of n − 1 distinct odd primes; add 2.
5. *Minimality.* A product of n primes is ≥ 2^n, and 2^n = 2·…·2. So a(n) = 2^n for n ≥ 6.

Review note (2026-11-07): this induction replaces the earlier Dusart-based one (scoping proposal in
`../open-problems/docs/PRIME-BOUNDS-SCOPE-2026-11-07.md`). Re-derived on paper before formalising. The proposal used
"gap between consecutive primes in (M, 2M] ≤ U − L"; the version here takes one prime in (b, 1.21b] directly and
needs the slightly weaker width condition U − L ≥ 0.347M. No gap found.

**Evidence.**
- Lean: [`A102237_mathlib.lean`](A102237_mathlib.lean), checked with `tools/leancheck-mathlib.sh` (Lean 4.35.0,
  Mathlib 56a00585, axioms propext, Classical.choice, Quot.sound, no warnings). `A102237_main`: `a102237 n = 2 ^ n`
  for n ≥ 6, with `a102237 n` defined as the infimum of the numbers that are a product of n primes (list with
  multiplicity) and a sum of n distinct primes. Uses the library module `OpenProblemsLib.ShortIntervalPrimes`.
- [`certificate/base_tables.py`](certificate/base_tables.py): generates the two base tables in the Lean file and
  simulates the windows to j = 200 (floating point; the Lean proof does not depend on it).
- [`certificate/check.py`](certificate/check.py): the earlier Dusart-route check (explicit representations for
  n = 6..23, base range of 2,306,868 even N, recurrence to k = 10^5). Superseded by the Lean proof.
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry still states the conjecture. Representations of integers as sums of
exactly k distinct primes are open in general (OEIS A387215 gives conjectural thresholds; the k = 2 case is
Goldbach); here the targets are exponentially large in k, which lets Bertrand-type prime-gap bounds (P. Dusart,
"Estimates of some functions over primes without R.H.", arXiv:1002.0442, Prop. 6.8) carry an induction, as in
Richert's proof that every integer > 6 is a sum of distinct primes. No proof of this conjecture found (web search).
Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
