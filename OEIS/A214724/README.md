# OEIS A214724: p | a(n) for n >= p when p = m^2 + 1 is prime

**Source.** [A214724](https://oeis.org/A214724) (Paul D. Hanna, Jul 26 2012): e.g.f. exp(Sum_{n>=0}
x^(n^2+1)/(n^2+1)). Comment: "Conjecture: p | a(n) for n>=p when p is a prime of the form m^2+1 (A002496)."
The entry (revision #17, Oct 17 2026, checked 2026-11-06) now adds "[Proved in Kallat (2026).]".

**Result.** True; proved by A. Kallat, *Universal Shift Congruences for Weighted Permutation Sequences*,
arXiv:2610.15849 (2026), Theorem `thm:hanna`, with a Lean 4 proof (`hanna_conjecture`) in
[ahaankallat/congruence-phenomena-higher-order-lean](https://github.com/ahaankallat/congruence-phenomena-higher-order-lean),
file `CongruenceTheoryHigherOrder/OEISHannaRichman.lean`. That Lean theorem is stated for the weighted-permutation
sequence `Aw hannaW` (weights 1 on lengths n^2+1, 0 elsewhere); the identification with the e.g.f. is the
exponential formula.

**Argument (second reading, independent of the paper).** By the exponential formula a(n) is the number of
permutations of {1..n} all of whose cycle lengths lie in S = {k^2 + 1 : k >= 0}; note 1 ∈ S and p ∈ S. Let
n >= p and let σ be the p-cycle (1 2 ... p). The group <σ> of order p acts by conjugation on these permutations
(conjugation keeps the cycle type), so a(n) is congruent mod p to the number of fixed permutations, those that
commute with σ. The centraliser of σ in S_n is <σ> × Sym({p+1..n}), and σ^k has cycle type (p) for k != 0 and
1^p for k = 0, both allowed. So the fixed permutations number p · a(n - p), and p | a(n). (The paper argues
differently: A(n+p) ≡ A(n)A(p) mod p and A(p) ≡ w_1^p + w_p - 1 ≡ 0 mod p.)

**Evidence.**
- External Lean: `CongruenceTheory.Shift.hanna_conjecture` (Kallat), stated for `Aw hannaW`; not rechecked here.
- [`certificate/check.gp`](certificate/check.gp): a(n) from the e.g.f. for n <= 449; p | a(n) for every prime
  p = m^2+1 <= 449 and p <= n <= 449 (PARI, exit 0, no errors).
- Outside Lean (here): the whole argument; this repo adds no Lean file, since a Lean proof exists.

**Review level.** `rechecked`.

**Prior art.** Checked 2026-11-06: OEIS entry and history (Kallat's proof note of Oct 14 2026), arXiv:2610.15849
and its two Lean repositories; not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
