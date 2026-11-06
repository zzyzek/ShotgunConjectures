# OEIS A007645 = A002383 ∪ A162471 (proved), and the A002383 intersection conjecture (open)

**Source.** [A007645](https://oeis.org/A007645) (generalized cuban primes: "primes of the form x^2 + xy + y^2; or
primes of the form x^2 + 3*y^2; or primes == 0 or 1 (mod 3)"), comment "Conjecture: this sequence is
Union(A002383,A162471). - Daniel Tisdale, Jul 04 2009" (revision #116, Jul 19 2026). [A002383](https://oeis.org/A002383)
(primes k^2 + k + 1), comment "Conjecture: the set of these numbers, except 3, is the intersection of sets A085104
and A059055. See A225148. - Thomas Ordowski, May 02 2013" (revision #116, Nov 04 2025). A162471: "Prime divisors
of {n^2+n+1} which do not occur in A002383". A085104: primes 1 + n + ... + n^k with n > 1, k > 1 (Brazilian
primes). A059055: primes (b^k+1)/(b+1) with b, k positive. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** A007645 is taken in its first form, primes x^2 + xy + y^2 with x, y natural numbers (integer x, y
give the same primes: `nat_rep` turns any integer solution into a natural one).

**Result.**
- A007645 = A002383 ∪ A162471: true (classical; proved in Lean here).
- A002383 \ {3} = A085104 ∩ A059055: the inclusion ⊆ is true; the inclusion ⊇ is open. It is equivalent to: every
  prime p = (n^q - 1)/(n - 1) = (b^r + 1)/(b + 1) with odd q, r >= 5 and n, b >= 2 is of the form c^2 + c + 1. With
  y = -b this is the Goormaghtigh equation (x^m - 1)/(x - 1) = (y^n - 1)/(y - 1) with one negative base; no such
  coincidence exists below 10^26 (search below), and no general result is known.

**Argument (A007645).** First, a prime is x^2 + xy + y^2 iff it is 0 or 1 mod 3. The form is never 2 mod 3
(check residues). Conversely 3 = 1 + 1 + 1, and for p ≡ 1 (mod 3) take s with p | s^2 + s + 1 (below). Among the
(m+1)^2 > p pairs (i, j) with 0 <= i, j <= m = floor(sqrt p), two give the same i - s j mod p (Thue's lemma); the
differences a, b satisfy a ≡ s b, so p | a^2 + ab + b^2, and 0 < a^2 + ab + b^2 <= 3m^2 < 3p. The value 2p is
impossible (it would force a, b even, so 4 | 2p). Hence p = a^2 + ab + b^2, and a sign change makes x, y natural.
Second, A002383 ∪ A162471 is the set of primes dividing some n^2 + n + 1 (k^2 + k + 1 divides
itself). If p | n^2 + n + 1 and p != 3, then n^3 ≡ 1 and n ≢ 1 (mod p), so n has order 3 and 3 | p - 1; and
3 | 1 + 1 + 1. Conversely p = 3 divides 1^2 + 1 + 1, and for p ≡ 1 (mod 3) Cauchy's theorem gives x of order 3 in
(Z/p)^*, so (x - 1)(x^2 + x + 1) = 0 with x != 1.

**Argument (A002383, partial).** For k >= 2, k^2 + k + 1 = 111 in base k (A085104 form) and
((k+1)^3 + 1)/((k+1) + 1) (A059055 form); 3 is not Brazilian. Conversely, if a prime in A085104 ∩ A059055 has a
representation with exponent 3 on either side, it is n^2 + n + 1 or b^2 - b + 1 = (b-1)^2 + (b-1) + 1, so in
A002383; an even number of digits gives a composite repunit. So a counterexample needs odd exponents q, r >= 5 on
both sides and no third representation c^2 + c + 1.

**Evidence.**
- Lean (Mathlib): [`A007645_mathlib.lean`](A007645_mathlib.lean). Main theorem `A007645_union : InA007645 p ↔
  InA002383 p ∨ InA162471 p`, with `InA007645 p := p.Prime ∧ ∃ x y : ℕ, p = x^2 + x*y + y^2` (the entry's
  definition); route `form_iff_mod_three` (`form_mod_three`, `rep_of_root`, `even_both`, `nat_rep`) and
  `dvd_iff_mod_three`. Also `A002383_sub` (the
  two identities behind ⊆). Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms propext,
  Classical.choice, Quot.sound.
- [`certificate/goormaghtigh_neg_search.py`](certificate/goormaghtigh_neg_search.py): all values
  (n^q - 1)/(n - 1) and (b^r + 1)/(b + 1) up to 10^26 with odd q, r >= 5 and n, b >= 2; no common value
  (run 2026-11-06, about 7 s, 0.9 GB).
- Outside Lean: for A007645, none (agreement with the data terms not checked in Lean). For A002383: the
  reduction above (short, by hand) and the search.

**Review level.** `lean-proof` for A007645; `agent` for the A002383 partial result.

**Prior art.** Checked 2026-11-06. The A007645 statement is the classical fact that the prime divisors of
n^2 + n + 1 are 3 and the primes ≡ 1 (mod 3) (stated in the entry's own comments, e.g. W. Lang 2021). For A002383:
A059055 (B. Schott 2021) and A343774 describe the partition of A059055 assuming the conjecture; A225148 lists the
coincidences 31 and 8191 for the positive-base equation. Known Goormaghtigh results (He 2009 for exponent 3; Shorey's
survey) do not cover the negative-base case in general. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs.
