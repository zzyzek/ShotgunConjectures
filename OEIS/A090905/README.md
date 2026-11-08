# OEIS A090904-A090907: the rows end at 2p for n > 4 (Bertrand-prime rows)

**Source.** [A090905](https://oeis.org/A090905) (and A090904 row products, A090906 row lengths, A090907 ratios of
row products), Amarnath Murthy 2003: split 1, 2, 3, ... into consecutive rows, each row the shortest block after
the previous one whose product is a multiple of the previous row's product: (1), (2), (3,4), (5..8), (9..14),
(15..26), ... Conjecture in all four entries: for n > 4 the last term of row n is 2p, where p is the largest prime
in row n-1, "and these are the Bertrand primes" (A006992: 2, 3, 5, 7, 13, 23, 43, ..., each the largest prime
below twice the previous). A090906 has the formula a(n) = 2(A006992(n) - A006992(n-1)) for n > 4; A090907 has a
factorial formula "verified for 4 < n < 21". (OEIS text, CC BY-SA 4.0, cached revisions checked 2026-11-07.)

**Result.** True for every n > 4. The proof uses Nagura's theorem (1952: for x ≥ 25 there is a prime in (x, 6x/5)),
which is proved in the library (`OpenProblemsLib.Nagura.nagura_nat_lt`).
Row n is (2b(n-2), 2b(n-1)] for n ≥ 6 with b = A006992 (b(1) = 2), row 5 is (8, 14]. Hence the A090906 formula and
the A090907 formula hold for all n ≥ 6, and A090904(n) = (2b(n-1))!/(2b(n-2))!.

**Argument.** Write e(n) for the last entry of row n. Rows 1-6 end at 1, 2, 4, 8, 14, 26 (direct computation;
the claim holds for n = 5, 6: 14 = 2·7, 26 = 2·13; at n = 4 it fails, 8 ≠ 2·3).

Induction for n ≥ 7. Suppose row n-1 is (2r, 2q] with r < q consecutive Bertrand primes, so q is the largest prime
below 2r (true for n-1 = 6: r = 7, q = 13). Let p be the largest prime below 2q.

1. *Prime gaps.* p > 5q/3: for q ≥ 15 Nagura's theorem at x = 5q/3 gives a prime in (5q/3, 2q); for q = 13,
   p = 23 > 65/3. In the same way q > 5r/3. So p > 25r/9 > 2r: p lies in row n-1 and is its largest prime.
2. *Lower bound.* p divides the product of row n-1, so it divides a factor of row n. The multiples of p are p ≤ 2q
   and 2p > 2q, so e(n) ≥ 2p.
3. *2p suffices.* Row n = (2q, 2p] works iff (2q)!^2 divides (2p)!·(2r)!. By Legendre's formula this means
   Σ_j N(ℓ^j) ≥ 0 for every prime ℓ, where N(x) = ⌊2p/x⌋ + ⌊2r/x⌋ - 2⌊2q/x⌋. Use p > 5q/3 and r > q/2 (from q < 2r).
   Put u = q/x.
   - N(x) ≥ 0 unless p < x < 2q. Cases: u < 1/2: ⌊2q/x⌋ = 0. 1/2 ≤ u < 1 and x ≤ p: ⌊2p/x⌋ ≥ 2 = 2⌊2q/x⌋.
     1 ≤ u < 3/2: ⌊2p/x⌋ ≥ ⌊2p/q⌋ ≥ 3 (2p/q > 10/3), ⌊2r/x⌋ ≥ 1; sum ≥ 4. 3/2 ≤ u < 2: 2p/x ≥ 3p/q > 5,
     2r/x ≥ 3r/q > 3/2; sum ≥ 6. 2 ≤ u < 5/2: 2p/x > 20/3, 2r/x > 2; sum ≥ 8. 5/2 ≤ u < 3: 2p/x > 25/3,
     2r/x > 5/2; sum ≥ 10. u ≥ 3: N(x) > D/x - 2 with D = 2p + 2r - 4q > 10q/3 + q - 4q = q/3, so
     D/x > 1 and N(x) > -1.
   - N(x) ≥ 1 for x < D/2 (then N(x) > D/x - 2 > 0), in particular for x ≤ q/6.
   - For p < x < 2q: N(x) ≥ -1, since (2p - 2q) ≥ (2q - 2r) gives ⌊2p/x⌋ - ⌊2q/x⌋ ≥ ⌊2q/x⌋ - ⌊2r/x⌋ - 1.
     No prime lies in (p, 2q), so x = ℓ^j with j ≥ 2, and 2q/p < 6/5 < ℓ, so only one power of ℓ lies there.
     When q > 72, ℓ ≤ √(2q) < q/6, so N(ℓ) ≥ 1 compensates. For q ∈ {13, 23, 43} the divisibility is checked
     exactly (certificate/chaincheck.py).
   So e(n) = 2p, row n = (2q, 2p] with q < p consecutive Bertrand primes, and the induction continues.

The largest prime of row n-1 is p = b(n-1), so e(n) = 2·b(n-1) (n ≥ 5), the row length is 2(b(n-1) - b(n-2)) for
n ≥ 6, and the ratio of row products is (2p)!(2r)!/(2q)!^2, A090907's formula.

**Evidence.**
- [`certificate/rows.py`](certificate/rows.py): rows from the definition (prime factorisations, no shortcut) for
  e(n) ≤ 2·10^6, i.e. n ≤ 22; output [`certificate/rows.out`](certificate/rows.out): e(n) = 2·(largest prime of
  row n-1) for 5 ≤ n ≤ 22, false at n = 4. Matches the entry's data.
- [`certificate/chaincheck.py`](certificate/chaincheck.py): Bertrand chain to 1.3·10^12, p > 5q/3 at every step
  from q = 7 on, and the exact Legendre check of step 3 for q ≤ 10^4.
- Lean (Mathlib): [`A090905_mathlib.lean`](A090905_mathlib.lean). The triangle is defined from scratch
  (`P`, `st`, `e`; least next row end by `Nat.find`). Main theorem `A090905_main (n) (hn : 5 ≤ n)`: some prime
  p is the largest prime of row n-1 and e n = 2p. Steps: `core_dvd` (step 3), `step` (steps 2-3), `nagura_p`
  (step 1), `st1`..`st7` (rows up to (86, 166] by kernel computation), `inv_all` (induction),
  `A090905_of_nagura` (the theorem from the hypothesis `NaguraNat`: for integers x ≥ 25 a prime p with
  x < p < 6x/5), `naguraNat_holds` (`NaguraNat` from the library theorem `OpenProblemsLib.Nagura.nagura_nat_lt`,
  [`lib/docs/short-interval-primes.md`](../../lib/docs/short-interval-primes.md) section 6: Chebyshev's
  weight sharpened to ψ(x) ≤ 1.1726·a·x + O(log³ x), plus 88 Pratt-certified primes below 1.2·10^8).
  Check: `tools/leancheck-mathlib.sh`, no warnings, axioms propext, Classical.choice, Quot.sound; no `sorry`,
  no `native_decide`. The library's 1.21 ratio (`exists_prime_Ioc_mul`) would not be enough: with p < 5q/3 a
  prime ℓ in (max(r, 2p/5), 2q/3] would give N(ℓ) = -1.
- Outside Lean: that `P`, `st`, `e` match the OEIS description of the triangle (cross-checked against the
  entry's data by `certificate/rows.py`); for A090904, A090906, A090907 also the one-line translation from row
  ends to row products, lengths and ratios.

**Review level.** `lean-proof` (unconditional).

**Prior art.** Checked 2026-11-07: the four OEIS entries (conjecture still stated; A090907's formula "verified
for 4 < n < 21"), google-deepmind/formal-conjectures, otoi-lab/oeis-lean-proofs: no proof found.
