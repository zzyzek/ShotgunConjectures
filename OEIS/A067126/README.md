# OEIS A067126: 4 and 9 are the only composite terms — partial result

**Source.** [A067126](https://oeis.org/A067126) (A. Murthy, Jan 09 2002): "Numbers for which phi(n) >= phi(k) for
all k = 1 to n-1." Comment: "Conjecture: 4 and 9 are the only composite terms." C. R. Greathouse IV (2010): no
more composite terms below 1.5e18; such a term needs a prime gap greater than sqrt(p).
OEIS text, CC BY-SA 4.0, checked 2026-11-07.

**Result (partial).**
1. *Gap criterion (Lean).* If n > 1 is a composite term and p < n is prime, then isqrt(n) <= n - p + 1.
   Take p = prevprime(n): then n < nextprime(p), so nextprime(p) - p > n - p >= isqrt(n) - 1 >= isqrt(p + 1) - 1.
   Hence if every prime p >= p_0 satisfies nextprime(p) - p < isqrt(p + 1), there is no composite term n
   with prevprime(n) >= p_0.
2. *Verification below 2^64.* Direct sieve to 2·10^6 finds only 4 and 9. Every record (maximal) prime gap
   g_k, first occurring after p_k, with p_k >= 523 satisfies g_k < isqrt(p_k + 1); since every prime p in
   [p_k, p_{k+1}) has gap <= g_k, criterion 1 holds for all primes 523 <= p < 2^64 (maximal gaps are known
   exhaustively below 2^64: OEIS A002386, A005250). Hence 4 and 9 are the only composite terms below 2^64
   (the entry states 1.5·10^18).
3. *The conjecture implies an Oppermann-type statement (Lean).* If q is prime and there is no prime in
   [q^2 - q + 2, q^2 - 1], then q^2 is a term. So the conjecture implies: for every prime q >= 5 there is a
   prime p with q^2 - q + 1 < p < q^2 (the lower half of Oppermann's conjecture at prime arguments, slightly
   sharpened). The conjecture is therefore at least as hard as that case of Oppermann's conjecture, and it
   follows from the gap bound nextprime(p) - p < isqrt(p + 1) for p >= 523 (implied by Cramér's conjecture;
   RH gives only O(sqrt(p) log p), which does not suffice).

**Argument.**
- For composite n with least prime factor q, q^2 <= n and the n/q multiples of q below n are not coprime to n,
  so phi(n) + n/q <= n, and n/q >= isqrt(n). A term satisfies phi(p) = p - 1 <= phi(n), so
  p - 1 + isqrt(n) <= n.
- For item 3: phi(q^2) = q(q - 1). Primes k < q^2 satisfy k <= q^2 - q + 1, so phi(k) <= q^2 - q. Composite
  k < q^2 satisfy phi(k) <= k - isqrt(k) <= q^2 - q (if k > q(q - 1) then isqrt(k) >= q - 1).

**Evidence.**
- Lean (Mathlib): [`A067126_mathlib.lean`](A067126_mathlib.lean): `A067126_totient_add_div_le`,
  `A067126_gap` (item 1), `A067126_composite_bound`, `A067126_square_term` (item 3), `A067126_four`,
  `A067126_nine`. Checked with `tools/leancheck-mathlib.sh`: OK, no warnings, axioms at most propext,
  Classical.choice, Quot.sound.
- [`certificate/check.py`](certificate/check.py) with the record-gap tables
  [`certificate/b002386.txt`](certificate/b002386.txt), [`certificate/b005250.txt`](certificate/b005250.txt);
  output [`certificate/check.out`](certificate/check.out).
- Outside Lean: the sieve to 2·10^6, the record-gap check, and the completeness of the maximal-gap list below
  2^64 (cited, not recomputed).

**Review level.** `lean-proof` for items 1 and 3; `rechecked` for item 2.

**Prior art.** Checked 2026-11-07: OEIS entry (conjecture still stated; Greathouse's comment gives the gap
idea and 1.5e18), google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs (no entry).
The implication to Oppermann's conjecture was not found stated.
