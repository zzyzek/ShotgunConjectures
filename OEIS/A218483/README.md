# OEIS A218483: Coman's 8pn + p² conjectures are true (form ⇔ P ≡ 1 mod 8)

**Source.** [A218483](https://oeis.org/A218483) (Fermat pseudoprimes to base 2 congruent to 1 mod 8; old name "of the
form 8*p*n + p^2, where p is prime and n natural"). Comments by Marius Coman (Oct 2012): (1) if a base-2 Fermat
pseudoprime can be written as 8pn + p² (n an integer, p one of its prime factors), it can be written so for any of its
prime factors; (2) if P = p1·p2 is 8·p1·n + p1², then P = 8·p2·(−n) + p2²; (3) if it cannot be written so for one
prime factor, it cannot for any. Also: no base-2 pseudoprime is 40n + 15. Charles R Greathouse IV (Dec 07 2014): "All
three conjectures are true (obvious from new characterization)." (OEIS text, CC BY-SA 4.0.)

**Result.** True. For odd P and a prime p ∣ P: P = 8pn + p² for an integer n ⇔ P ≡ 1 (mod 8). Base-2 pseudoprimes
are odd, so (1) and (3) follow; (2) holds for any p1 ≠ 0, p2. No base-2 pseudoprime is 15 mod 40.

**Argument.** Write P = p·m. P = 8pn + p² ⇔ m = 8n + p ⇔ m ≡ p (mod 8). For odd p, p² ≡ 1 (mod 8), so
m ≡ p ⇔ pm ≡ 1 (mod 8). For (2): p2 = 8n + p1, so p2² − 8p2n = p2(p2 − 8n) = p2·p1. For 15 mod 40: 5 ∣ P ∣ 2^(P−1) − 1,
but P − 1 ≡ 2 (mod 4) and 2^(4k+2) ≡ 4 (mod 5).

**Evidence.**
- Lean (Mathlib): [`A218483_mathlib.lean`](A218483_mathlib.lean): `rep_iff`, `odd_of_psp`, `conj1`, `conj2`, `conj3`,
  `not_15_mod_40` (Mathlib `Nat.FermatPsp`). Exit 0, no warnings; axioms propext, Classical.choice, Quot.sound.
- [`certificate/check.py`](certificate/check.py): all 264239 base-2 pseudoprimes below 10¹³ (Feitsma–Galway) agree.
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Known: Greathouse (2014), via the renaming of the entry. Not in google-deepmind/formal-conjectures (clone
2026-11-05) or otoi-lab/oeis-lean-proofs (clone 2026-10-13). Checked 2026-11-06.
