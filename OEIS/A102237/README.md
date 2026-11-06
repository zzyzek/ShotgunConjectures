# OEIS A102237: a(n) = 2^n for n > 5

**Source.** [A102237](https://oeis.org/A102237) (Giovanni Teofilatto, 2005; corrected and extended by Ray Chandler):
smallest number equal to the product of n primes which is also equal to the sum of n distinct primes. Comment:
"Conjecture: a(n) = 2^n for n>5. - Ray Chandler Feb 25 2005". Data 2, 9, 12, 36, 48, 64, 128, ... (OEIS text,
CC BY-SA 4.0, revision #7 of Nov 01 2019, checked 2026-11-06.)

**Reading.** "Product of n primes" counts multiplicity (a(2) = 9 = 3·3). Every product of n primes is ≥ 2^n, so
a(n) = 2^n iff 2^n is a sum of n distinct primes.

**Result.** True: for every n ≥ 6, 2^n is a sum of n distinct primes, so a(n) = 2^n.

**Argument.** Parity: for even n use n odd primes summing to 2^n; for odd n use 2 plus n − 1 odd primes summing to
2^n − 2. Call S(k, N): N is a sum of k distinct odd primes.
1. *Step.* Suppose S(k, N') holds for every N' ≡ k (mod 2) in [L_k, B_k], with L_k ≥ 2·396738. Let N ≡ k+1 (mod 2),
   2L_k/(1 − ε) ≤ N ≤ 2B_k, where ε = 1/(25 ln² L_k). By Dusart (2010, Prop. 6.8: for x ≥ 396738 there is a prime
   in (x, x(1 + 1/(25 ln² x))]) with x = N/2 ≥ L_k there is a prime p with N/2 < p ≤ (N/2)(1 + ε) ≤ N − L_k. Then
   N − p ∈ [L_k, B_k] has the parity of k, so it is a sum of k distinct odd primes, each ≤ N − p < N/2 < p. Adding p
   gives S(k+1, N). So the statement holds with L_{k+1} = 2L_k/(1 − 1/(25 ln² L_k)), B_{k+1} = 2B_k.
2. *Base.* k₀ = 22, L₂₂ = 3774874 ≈ 0.9·2^22, B₂₂ = 2^23: every even N in this range is the sum of the first 20 odd
   primes (3..73) and two distinct primes > 73 (computer check).
3. *Growth.* Then B_k = 2^{k+1} and L_k/2^k increases to about 0.9035 < 0.95 (computed to k = 10^5, with the tail
   bounded by exp(Σ ε_j) ≤ exp(8.5·10^−7)). So for even k ≥ 22 both 2^k and 2^{k+1} − 2 lie in [L_k, B_k]: 2^n is a
   sum of n distinct odd primes for even n ≥ 22, and 2^n = 2 + (sum of n − 1 distinct odd primes) for odd n ≥ 23.
4. *Small n.* For 6 ≤ n ≤ 23 explicit representations (e.g. 64 = 3 + 5 + 7 + 13 + 17 + 19,
   128 = 2 + 3 + 5 + 7 + 11 + 17 + 83).

**Evidence.**
- [`certificate/check.py`](certificate/check.py) (Python, exit 0, about 16 s): explicit representations for
  n = 6..23 (checked: distinct, prime, correct sum and count); the base range of step 2 (all 2,306,868 even N); the
  recurrence of step 3 to k = 10^5 with the analytic tail bound.
- Lean: none. Missing pieces: Dusart's explicit prime-gap theorem (not in Mathlib); the base range is too large for
  kernel evaluation.
- Outside Lean: everything.

**Review level.** `rechecked`.

**Prior art.** Checked 2026-11-06. The entry still states the conjecture. Representations of integers as sums of
exactly k distinct primes are open in general (OEIS A387215 gives conjectural thresholds; the k = 2 case is
Goldbach); here the targets are exponentially large in k, which lets Bertrand-type prime-gap bounds (P. Dusart,
"Estimates of some functions over primes without R.H.", arXiv:1002.0442, Prop. 6.8) carry an induction, as in
Richert's proof that every integer > 6 is a sum of distinct primes. No proof of this conjecture found (web search).
Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
