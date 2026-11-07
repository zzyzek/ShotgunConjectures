# OEIS A124000: semiprime binomial coefficients are 35 and p(2p ± 1)

**Source.** [A124000](https://oeis.org/A124000), semiprimes among C(n,k), 2 <= k <= n-2. Conjectures (R. G. Wilson v):
"all a(n) except a(1) = 6 and a(2) = 10 are odd"; "all a(n) except a(5) = 35 are triangular numbers of the form
p*(2p +/- 1)". A 2026 comment (Lien-Hung Su, Oct 29 2026) states the characterization with a Zenodo reference
(entry checked 2026-11-07).

**Result.** Both conjectures are true: the terms are exactly 35 and the numbers p(2p+1), p(2p-1) with p and
2p ± 1 prime; the only even ones are 6 = 2·3 and 10 = 2·5.

**Argument.** (1) k >= 3. By symmetry take 3 <= k <= n/2. Every prime power dividing C(n,k) is at most n
(Kummer / Legendre), so a semiprime C(n,k) = pq has p, q <= n and C(n,k) <= n^2. But
C(n,k) >= C(n,3) = n(n-1)(n-2)/6 > n^2 for n >= 9. For n <= 8 the only semiprime is C(7,3) = 35.
(2) k = 2. C(n,2) = m(2m-1) (n = 2m) or m(2m+1) (n = 2m+1), with coprime factors both >= 2 when n >= 4;
a product of two primes with two factors >= 2 forces both factors prime. So C(n,2) = p(2p ± 1).
(3) p(2p ± 1) is even only for p = 2: 6 and 10.

**Evidence.**
- Lean (Mathlib): [`A124000_mathlib.lean`](A124000_mathlib.lean): `A124000_char` (InA124000 x ↔ x = 35 ∨ x = p(2p+1)
  or p(2p-1) with both primes), `A124000_odd`, `A124000_triangular`; route `choose_le_sq`
  (via `Nat.pow_factorization_choose_le`), `choose_three_le`, `big_case`, `small_case`, `two_case`. Checked with
  `tools/leancheck-mathlib.sh`, no warnings, axioms at most propext, Classical.choice, Quot.sound.
- Outside Lean: none. Not verified in Lean: agreement with the b-file terms.

**Review level.** `lean-proof`.

**Prior art.** Known: L.-H. Su, "Divisibility Thresholds, Binomial Counts, and Record Growth in Pascal's
Triangle", Zenodo 2026, doi:10.5281/zenodo.23478066, cited in the entry (comment of Oct 29 2026; not read here).
google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs: no file (2026-11-07). The Lean proof is new.
