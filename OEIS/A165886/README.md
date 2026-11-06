# OEIS A165886: a(n)/A141459(n+1) = A006519(n+1)

**Source.** [A165886](https://oeis.org/A165886) (Paul Curtz, Sep 29 2009): a(n) = A165641(n+1)/A165641(n), where
A165641(n) = A091137(n)/A001316(n), A091137(n) = Π_{p prime, p ≤ n+1} p^⌊n/(p-1)⌋ (Hirzebruch numbers) and
A001316(n) = 2^(binary weight of n). Comment: "Conjecture: a(n)/A141459(n+1) = A006519(n+1)", with "correct at least
up to n<=2000" (R. J. Mathar, 2011). A141459(m) = product of the odd primes p with p - 1 | m; A006519(m) = highest
power of 2 dividing m. (OEIS text, CC BY-SA 4.0, revision #12 of Dec 19 2018, checked 2026-11-06.)

**Result.** True for every n ≥ 0: a(n) = A141459(n+1) · A006519(n+1).

**Argument.**
1. ⌊(n+1)/d⌋ - ⌊n/d⌋ is 1 if d | n+1 and 0 otherwise. With d = p - 1 (and the new prime p = n+2, whose exponent
   for n is 0), A091137(n+1)/A091137(n) = Π_{p prime, p-1 | n+1} p = 2 · A141459(n+1) (p = 2 always occurs).
2. Adding 1 to n turns the v₂(n+1) trailing ones of n into zeros and sets one bit, so s(n) + 1 = s(n+1) + v₂(n+1) for the binary
   weight s (induction: n = 2k gives s(2k) + 1 = s(2k+1); n = 2k+1 reduces to k). So
   A001316(n)/A001316(n+1) = 2^(v₂(n+1) - 1).
3. a(n) = 2 · A141459(n+1) · 2^(v₂(n+1) - 1) = A141459(n+1) · A006519(n+1).

**Evidence.**
- Lean (Mathlib): [`A165886_mathlib.lean`](A165886_mathlib.lean). The sequence is defined as in the entry (A091137
  by the entry's PARI program, A001316 via `Nat.digits 2`, A165641 and a(n) as rationals). Main theorem
  `A165886_conjecture n : A165886 n / A141459 (n+1) = A006519 (n+1)`; steps `A091137_succ`, `weight_succ`,
  `A165886_formula`. Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms propext, Classical.choice,
  Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): a(n) from the definition equals the formula and the b-file
  ([`certificate/b165886.txt`](certificate/b165886.txt), Antti Karttunen) for n = 0..2000.
- Outside Lean: none beyond reading the definitions. Not verified in Lean: agreement with the OEIS data terms.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry (last edited 2018) still states the conjecture; Mathar checked n ≤ 2000.
The two facts used (ratio of consecutive Hirzebruch numbers, carries when adding 1 in binary) are elementary and
standard, but no statement of this identity's proof was found (web search). Not in google-deepmind/formal-conjectures
(no `FormalConjectures/OEIS/165886.lean`) or otoi-lab/oeis-lean-proofs.
