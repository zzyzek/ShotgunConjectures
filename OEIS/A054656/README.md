# OEIS A054656: for n >= 23, a(n) = [n-6 prime] + [n-4 prime] + [n-1 prime]

**Source.** [A054656](https://oeis.org/A054656) (offset 0, Henry Bottomley, Apr 17 2000): "Number of primes <= n
which do not appear in any partitions of n into distinct primes." Comment in the entry: "Conjecture: if n >= 23
then a(n)=2 if both (n-6) and (n-4) are prime, a(n)=1 if one of (n-6), (n-4) or (n-1) is prime, a(n)=0
otherwise". (OEIS text, CC BY-SA 4.0, revision #8 of Feb 15 2022, checked 2026-11-06.)

**Result.** True for every n >= 23. The bound is sharp: a(22) = 1 (the prime 11) while the formula gives 0.

**Argument.** A prime p <= n is a part of some partition of n into distinct primes iff m = n - p is a sum of
distinct primes none equal to p ("m avoids p").

1. *Two primes in (x, 2x] for x >= 6.* For x >= 512 this is the Erdős proof of Bertrand's postulate with one extra
   factor: if q is the only prime in (x, 2x], then centralBinom x <= (2x)^sqrt(2x) 4^(2x/3) (2x), since q^v_q <= 2x;
   with 4^x < x centralBinom x this contradicts x (2x) (2x)^sqrt(2x) 4^(2x/3) <= 4^x, which holds for x >= 512
   (f(x) = 2 log x + log 2 + sqrt(2x) log(2x) - (log 4 / 3) x is concave, f(18) >= 0, f(512) <= 0). For
   6 <= x < 512 the chain 523, 521, 269, 263, 139, 137, 73, 71, 41, 37, 29, 23, 19, 17, 13, 11, 7 (each term at
   most twice the term two places later) gives two primes, and x = 6 has 7, 11. So for any p, (x, 2x] holds a
   prime other than p.
2. *Richert-type induction.* Claim: if m > 27, r >= 31 and m <= 27 + r, then m is a sum of distinct primes, all
   below r and none equal to p. For m <= 87 an explicit table gives two or three representations with parts below
   max(31, m - 27) and no part common to all of them, so one avoids p. For m >= 88 take x = (m - 28)/2 >= 30 and a
   prime q != p in (x, 2x] (step 1); then 27 < m - q <= 27 + q and q >= 31, so by induction m - q is a sum of
   distinct primes below q avoiding p; add q (and q < r because q <= m - 28).
3. *All m.* With r = m + 31, every m > 27 avoids every p. For m <= 27 the table shows that m avoids p unless m is
   1, 4 or 6 (no representation at all) or (m, p) is one of (2,2), (3,3), (8,3), (8,5), (9,2), (9,7), (10,3),
   (11,11), (12,7). In each of these pairs m + p <= 22.
4. *Count.* For n >= 23 the prime p <= n is missing from every partition iff n - p is 1, 4 or 6, so
   a(n) = [n-1 prime] + [n-4 prime] + [n-6 prime]. For n >= 23, n-1 is never prime together with n-4 or n-6 (one of
   the two is even and larger than 2), which gives the three cases of the conjecture.

**Evidence.**
- Lean (Mathlib): [`A054656_mathlib.lean`](A054656_mathlib.lean). `a n` counts the primes `p <= n` such that no
  finite set `s` of primes with sum `n` contains `p` (`IsPart`). Main theorem `A054656_formula : 23 <= n -> a n =
  if (n-6).Prime ∧ (n-4).Prime then 2 else if (n-6).Prime ∨ (n-4).Prime ∨ (n-1).Prime then 1 else 0`. Route:
  `real_ineq`, `main_ineq`, `centralBinom_le_of_one_prime`, `G_large`, `G_step`, `G_of_ge` (step 1, the large
  case adapted from Mathlib's `Mathlib/NumberTheory/Bertrand.lean`); `tab`, `tab_ok`, `tab_cover`, `tab_bound`,
  `rep_large` (step 2); `rep_avoid`, `excL`, `no_rep_146` (step 3); `appears_iff` and the final count (step 4).
  Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext, Classical.choice, Quot.sound.
  No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): a(n) from the definition for n <= 3000; equals the 87 data terms
  and the formula for 23 <= n <= 3000; a(22) = 1 differs from the formula.
- [`certificate/bad.py`](certificate/bad.py): all pairs (m, p), p <= 2000, m <= 3000, with m not a sum of distinct
  primes avoiding p (the list of step 3). [`certificate/table.py`](certificate/table.py) produces `tab`.
- Outside Lean: none. Not verified in Lean: agreement of `a` with the OEIS data terms (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The OEIS entry (revision #8) still states the conjecture; no proof is linked.
Richert (1949) proved that every integer > 6 is a sum of distinct primes; the version avoiding one given prime and
the two-primes form of Bertrand's postulate used here (Ramanujan's R_2 = 11) are standard in spirit, but no
written proof of this conjecture was found. Not in google-deepmind/formal-conjectures (no
`FormalConjectures/OEIS/54656.lean`) or otoi-lab/oeis-lean-proofs. Web search found nothing on the avoiding-one-prime
variant.
