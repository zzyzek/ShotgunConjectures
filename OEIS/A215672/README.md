# OEIS A215672: Coman's q((r+1)q − r) claim for Poulet numbers is false (617093)

**Source.** [A215672](https://oeis.org/A215672) (Fermat pseudoprimes to base 2 with three prime factors). Comment by
Marius Coman (Aug 2012): "Conjecture: Any Poulet number P with three or more prime divisors has at least one prime
divisor q for that can be written as P = q*((r + 1)*q - r), where r is a natural number." Same entry, Charles R
Greathouse IV (Dec 07 2014): the conjecture fails for a(80) = 617093 = 43 · 113 · 127. (OEIS text, CC BY-SA 4.0.)

**Result.** False; 617093 is the least counterexample. Below 10⁷ the counterexamples are 617093, 1534541, 2537641,
7455709; below 10¹³ there are 3352 (Feitsma–Galway list).

**Argument.** P = q((r+1)q − r) means P/q = q + r(q − 1). For q = 43, 113, 127: P/q = 14351, 5461, 4859, and
14351 − 43 = 14308, 5461 − 113 = 5348, 4859 − 127 = 4732 are not divisible by 42, 112, 126 respectively.

**Evidence.**
- Lean (Mathlib + lib): [`A215672_mathlib.lean`](A215672_mathlib.lean), main `A215672_false`: ¬ ∀ P, FermatPsp P 2 →
  3 ≤ P.primeFactors.card → ∃ q prime, q ∣ P ∧ ∃ r : ℕ, P = q*((r+1)*q − r). `P_psp` by lib `pspCheck`
  (kernel powMod), `P_primeFactors`, `no_q` (omega). Exit 0, no warnings; axioms propext, Classical.choice,
  Quot.sound; no `native_decide`.
- [`certificate/search.py`](certificate/search.py): counterexamples from the Feitsma–Galway table.
- Outside Lean: minimality and counts.

**Review level.** `lean-witness`.

**Prior art.** Known: Greathouse's comment in the entry (2014). Not in google-deepmind/formal-conjectures (clone
2026-11-05) or otoi-lab/oeis-lean-proofs (clone 2026-10-13). Checked 2026-11-06.
