# OEIS A083143 / A083144: no entry is zero (proved, modulo the Dias da Silva–Hamidoune theorem)

**Source.** OEIS [A083143](https://oeis.org/A083143): smallest n-digit palindromic multiple of
prime(n), or 0 if no such number exists; [A083144](https://oeis.org/A083144) = A083143(n)/prime(n).
Conjecture for both (OEIS wiki list): "no entry is zero" (OEIS text, CC BY-SA 4.0).

**Result.** For every n ≥ 1 there is an n-digit palindrome divisible by prime(n). So no entry of
A083143 or A083144 is zero.

**Argument.** Let p = prime(n), t = n − 1, d = ord_p(10), h = ⌊(n − 2)/2⌋ and
u_i = 10^i + 10^{t−i} (1 ≤ i ≤ h), the value of a symmetric pair of digits 1.
Computation covers n ≤ 459 (below), so take n ≥ 460 (then p ∉ {2, 3, 5}).

*Case d ≤ n/2.* p | 10^d − 1 = 9·R_d and p ≠ 3, so p divides the repunit R_d. The n-digit
palindrome R_d 0^{n−2d} R_d = R_d (10^{n−d} + 1) is divisible by p.

*Case d > n/2.* (i) For 1 ≤ i < j ≤ h:
u_i − u_j = (10^i − 10^j)(1 − 10^{t−i−j}). Since j − i < h < d, 10^i ≢ 10^j, so u_i ≡ u_j only if
d | t − i − j; for each i at most one j ∈ [1, h] satisfies this (h < d). So each residue is taken by
at most two indices, and the u_i take at least ⌈h/2⌉ distinct values mod p.
(ii) Dias da Silva–Hamidoune (Bull. London Math. Soc. 26 (1994) 140–146): for A ⊆ ℤ/p and
1 ≤ k ≤ |A|, the set of sums of k distinct elements of A has size at least min(p, k(|A| − k) + 1).
With |A| = ℓ = ⌊√(4p − 7)⌋ + 1 and k = ⌊ℓ/2⌋ this is min(p, ⌊ℓ²/4⌋ + 1) = p, since ℓ² ≥ 4p − 6.
(iii) If ⌈h/2⌉ ≥ ⌊√(4p − 7)⌋ + 1, pick ℓ indices with distinct u-values and k of them, I, with
Σ_{i∈I} u_i ≡ −(10^t + 1) (mod p). Then 10^t + 1 + Σ_{i∈I} u_i is an n-digit palindrome
(digits 0/1, leading digit 1) divisible by p.
(iv) The condition in (iii) holds for all n ≥ 460 (`certificate/thresh.py`: checked with the
actual primes for n ≤ 20000, last failure at n = 459; for n > 20000 from
p_n < n(ln n + ln ln n) (Rosser–Schoenfeld 1962, n ≥ 6), since
(n − 3)/4 − 2√(n(ln n + ln ln n)) − 1 is positive at 20000 and increasing).

*Small n.* `certificate/pal.py` finds a(n) for every n ≤ 460 (all nonzero; the 18 listed terms
agree). With the bound for n ≥ 460 this covers all n.

**Evidence.** No Lean: the Dias da Silva–Hamidoune theorem is not in Mathlib (Cauchy–Davenport
is, but it only gives 9h + 1 residues, which needs h ≥ p/9, and p ≈ n ln n). Outside Lean: the
Dias da Silva–Hamidoune theorem (published), the Rosser–Schoenfeld bound, and the computations
`certificate/pal.py` (n ≤ 460; each hit re-verified as an n-digit palindrome divisible by
prime(n)) and `certificate/thresh.py`.

**Review level.** `rechecked` (paper proof plus computation).

**Prior art.** OEIS A083143/A083144 (checked 2026-11-07) list the conjecture only. Banks–Hart–Sakata
(2004) give per-length equidistribution of palindromes mod p only for lengths L ≥ 10p − 5, too
long here. Col (Acta Arith. 137 (2009)) gives equidistribution on average over moduli coprime
to 990; as quoted in Tuxanidy–Panario (arXiv:2307.16637, Thm 1.3) it would give the result for
n ≥ n_0 with n_0 not explicit. google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs:
no entry. Web search 2026-11-07 found no proof.
