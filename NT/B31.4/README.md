# Guy B31 (Ruderman): is there n with n!(n+q)! ∣ (2n−p)! for every p, q ≥ 0?

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B31
(binomial coefficients). Guy records Harry Ruderman's request for a proof or disproof that for
every pair (p, q) of nonnegative integers some positive integer n makes (2n − p)!/(n!(n + q)!) an
integer. Reference given there: H. D. Ruderman, Problem 714, *Crux Math.* 8 (1982) 48; 9 (1983) 58.

**Reading.** (2n − p)! needs 2n ≥ p. Write R(p, q) for "some n ≥ 1 with 2n ≥ p has
n!(n + q)! ∣ (2n − p)!". Ruderman's question is "R(p, q) for all p, q".

**Result (partial; the question stays open).**

1. *Equivalence with Erdős problem 727 (ours, Lean).* Ruderman's question is equivalent to
   the conjecture of Erdős, Graham, Ruzsa and Straus (erdosproblems.com/727, open even for
   k = 2): for every k ≥ 2 there are infinitely many n with ((n + k)!)² ∣ (2n)!.
   It is also equivalent to the weak form "for every k there is one such n", i.e. to every
   term of OEIS A343507 existing.
2. *Known cases.* R(p, q) holds for p ≤ 2 and every q: Erdős–Graham–Ruzsa–Straus (1975), by
   Balakran's method, give infinitely many n with (n + k)!(n + 1)! ∣ (2n)!; with m = n + 1 this
   is m!(m + k − 1)! ∣ (2m − 2)!, i.e. R(2, k − 1), and R(p, q) is monotone (below).
3. *Computed cases.* R(p, q) holds for every pair with p + 2q ≤ 16 (from witnesses of
   ((n + k)!)² ∣ (2n)! for k ≤ 8, recomputed here to 3·10⁸; they agree with A343507), and for
   p + 2q ≤ 18 using the A343507 term a(9) = 2935782889 (not recomputed). Direct witnesses for
   larger q at fixed p are in the table below.

Largest q found with n ≤ 10⁷ for each p (so R(p, q′) holds for all q′ ≤ q; columns p = 13…16
have only q = 0 solutions, with n ≤ 3·10⁸):

| p | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 14 | 16 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| largest q | 17 | 16 | 12 | 12 | 10 | 9 | 6 | 6 | 2 | 2 | 0 | 0 |
| witness n | 8122350 | 7241455 | 1474547 | 1474547 | 2086261 | 7235030 | 5665647 | 5665647 | 3648841 | 7141719 | 72286099 | 159329615 |

**Argument.**

*Monotonicity.* If n works for (p, q) it works for (p′, q′) with p′ ≤ p, q′ ≤ q, since
n!(n + q′)! ∣ n!(n + q)! and (2n − p)! ∣ (2n − p′)!.

*Ruderman ⇒ one solution for each k.* R(2k, 0) gives n with n!² ∣ (2n − 2k)! and 2n ≥ 2k;
then n′ = n − k has ((n′ + k)!)² ∣ (2n′)!.

*One solution for each k ⇒ Ruderman.* Given (p, q) let k = p + q + 2 and take n with
((n + k)!)² ∣ (2n)!. Put m = n + p + 2 ≥ 1. Then m + q = n + k, so
m!(m + q)! ∣ ((n + k)!)² ∣ (2n)! ∣ (2m − p)! because 2m − p = 2n + p + 4 ≥ 2n.

*One solution for each k ⇒ infinitely many for each k.* Let ((n + K)!)² ∣ (2n)! with K ≥ 2.
Then n ≥ K: n = 0 is impossible (K!² > 1), and if 1 ≤ n < K, Bertrand gives a prime ℓ with
n < ℓ ≤ 2n ≤ n + K, so ℓ² ∣ ((n + K)!)², while ℓ ≤ 2n < 2ℓ and 2n < ℓ² give
v_ℓ((2n)!) = ⌊2n/ℓ⌋ = 1. A solution for K is a solution for every k ≤ K
((n + k)! ∣ (n + K)!). Taking K = k + a + 1 for each bound a gives a solution n > a for k.
(The fact that [a(k) + 1, a(k) + k] contains no prime is noted in A343507 by Schoenfield.)

*Why the question is hard (obstruction).* For a prime ℓ with ℓ² > 2n and ℓ > p + 2q, write
r = n mod ℓ and r′ = (n + q) mod ℓ. Since 2n − p = n + (n + q) − (p + q), the ℓ-adic valuation
of (2n − p)!/(n!(n + q)!) is ⌊(r + r′ − p − q)/ℓ⌋ ∈ {−1, 0, 1}, and it is −1 exactly when
r = j < p/2 (then r′ = j + q), i.e. when ℓ ∣ n − j for some 0 ≤ j < p/2. So every solution for p ≥ 3 needs n and
n − 1 to be √(2n)-smooth, and for p ≥ 2j + 1 the j + 1 consecutive integers n, …, n − j
must all be √(2n)-smooth, plus carry conditions at every prime ≤ √(2n). Strings of
consecutive smooth numbers exist (Balog–Wooley), but nobody controls the carry conditions
at all small primes simultaneously; that is the open core of Erdős 727. The counts of
solutions drop fast with k (below 3·10⁸: 282 for k = 6, 18 for k = 7, 2 for k = 8).

**Evidence.**
- Lean + Mathlib: [`B31_4_mathlib.lean`](B31_4_mathlib.lean). `B31_4_main : B31_Ruderman ↔
  B31_Erdos727`, where `B31_Ruderman := ∀ p q, ∃ n, 0 < n ∧ p ≤ 2 * n ∧ n ! * (n + q) ! ∣
  (2 * n - p) !` and `B31_Erdos727 := ∀ k ≥ 2, Set.Infinite {n | ((n + k) !) ^ 2 ∣ (2 * n) !}`
  (the statement of `Erdos727.erdos_727` in google-deepmind/formal-conjectures);
  `B31_4_weak : B31_Ruderman ↔ ∀ k, ∃ n, ((n + k) !) ^ 2 ∣ (2 * n) !`. Mathlib inputs:
  Bertrand (`Nat.exists_prime_lt_and_le_two_mul`), `Nat.Prime.pow_dvd_factorial_iff`.
  Axioms: propext, Classical.choice, Quot.sound. Checked with `tools/leancheck-mathlib.sh`,
  no warnings.
- `certificate/rud.c` (search for n with n!(n+q)! ∣ (2n−p)!, Legendre valuations at all primes
  ≤ √(2n) plus the prime factors of n, …, n − ⌈p/2⌉ + 1), `certificate/E_scan_3e8.txt`
  (p = 12…24, q = 0, n ≤ 3·10⁸), `certificate/rudq.c` and `certificate/Q_scan_1e7.txt`
  (largest q per p, n ≤ 10⁷); `certificate/verify.py` rechecks witnesses by Legendre's formula
  over every prime ≤ n + q (done for (3,17), (5,12), (8,9), (11,2) and fails for (3,18) at the
  same n, as it should). The program agrees with exact factorial division for n < 600,
  p ≤ 6, q ≤ 3.
- Outside Lean: the computed witnesses (items 3 and the table); the known theorem of item 2.

**Review level.** lean-proof for the equivalence; computations rechecked against exact
arithmetic for small n and against A343507.

**Prior art (2026-11-07).** Web search for Ruderman's problem in this factorial form found
nothing beyond Guy. Erdős problem 727 (erdosproblems.com; formal-conjectures
`ErdosProblems/727.lean`, tagged open) is the same question up to the equivalence above; the
equivalence itself was not found stated anywhere. OEIS A343507 (Mizrahi, 2021) lists the least
n for k ≤ 9. Erdős, Graham, Ruzsa, Straus, *On the prime factors of C(2n, n)*, Math. Comp. 29
(1975) 83–92, give the p ≤ 2 case.
