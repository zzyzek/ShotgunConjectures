# OEIS A196226: the term 690 violates all three σ_k congruences

**Source.** [A196226](https://oeis.org/A196226) (John W. Layman, Sep 29 2011): "m such that A054024(m) (sum of
divisors of m reduced modulo m) is 3 + m/2." Comment: "Conjectures. (1) If m>=14 is a term of this sequence,
then sigma(2,m) is congruent to 5 + m/2 modulo m; (2) If m>=22 ..., sigma(3,m) ... 9 + m/2 ...; If m>=38 ...,
sigma(4,m) ... 17 + m/2 modulo m." R. J. Mathar (Aug 24 2023): "The terms in this sequence which are not even
semiprimes are 8, 690, 12978, 176946, ..." (OEIS text, CC BY-SA 4.0, revision #21 of Aug 24 2023, checked
2026-11-06.)

**Result.** All three conjectures are false. m = 690 = 2·3·5·23 is a term (σ(690) = 1728 ≡ 348 = 3 + 345), but
σ₂(690) ≡ 380 (claimed 350), σ₃(690) ≡ 426 (claimed 354), σ₄(690) ≡ 668 (claimed 362) mod 690. Up to 200000 the
violating terms are exactly the non-semiprime terms 690, 12978, 176946.

**Argument.** Direct computation, σ_k(690) = (1+2^k)(1+3^k)(1+5^k)(1+23^k). For the even semiprimes m = 2p
(p > 3 prime), the congruences do hold for every k: σ_k(2p) = (1+2^k)(1+p^k), and (1+2^k)p^k ≡ p mod 2p since
1+2^k and p^k are odd multiples of p, so σ_k(2p) ≡ 2^k + 1 + p.

**Evidence.**
- Lean (Mathlib): [`A196226_mathlib.lean`](A196226_mathlib.lean). `A196226_conjectures_false`: σ 1 690 % 690 =
  3 + 690/2, 690 ≥ 38, and the three congruences fail at 690. Axioms propext, Classical.choice, Quot.sound; no
  sorry, no native_decide; checked with `tools/leancheck-mathlib.sh`.
- [`certificate/check.py`](certificate/check.py): terms ≤ 200000 and the violations listed above.
- Outside Lean: the semiprime remark (not needed for the disproof) and the scan to 200000.

**Review level.** `lean-witness`.

**Prior art.** Checked 2026-11-06. Mathar's 2023 comment lists 690 as a term, but the entry does not note that it
breaks the conjectures, which are still stated. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs (trees at HEAD 2026-11-06).
