# OEIS A158110: exp(Σ q^(n^m) x^n/n) is an integer series (known; reproved in Lean)

**Source.** [A158110](https://oeis.org/A158110) (P. D. Hanna, Mar 2009), g.f. exp(Σ 2^(n^3) x^n/n). "Conjecture:
given q and m are nonnegative integers, then exp( Sum_{n>=1} q^(n^m)*x^n/n ) is a power series in x with
integer coefficients." The entry now adds "The conjecture is true (see Fried link)." (S. Fried, Dec 15 2025.)
(OEIS text, CC BY-SA 4.0, read 2026-11-06.)

**Result.** True (known: S. Fried, "Further proofs of conjectures from the OEIS", arXiv:2607.24832,
Theorem 43). Reproved here in Lean for all q, m ≥ 0.

**Argument.** By Dwork's lemma it suffices that b(n) = q^(n^m) satisfies b(k p^a) ≡ b(k p^(a-1)) (mod p^a).
m = 0: b is constant. m ≥ 1: write (k p^a)^m = K p^E p^(a-1+m), (k p^(a-1))^m = K p^E p^(a-1) with
K = k^m, E = (a-1)(m-1), and x = q^(K p^E). Then x^(p^(a-1+i)) ≡ x^(p^(a-1)) (mod p^a) for all i ≥ 0 (telescoping
x^(p^(j+1)) ≡ x^(p^j) (mod p^(j+1)), Fermat-Euler), valid for every integer x.

**Evidence.**
- Lean (Mathlib): [`A158110_mathlib.lean`](A158110_mathlib.lean), namespace `A158110`. Main theorem
  `A158110_conjecture (q m : ℕ) n : ∃ z : ℤ, expCoeff (fun n => (q : ℤ) ^ (n ^ m)) n = z`; `A158110_int` is
  q = 2, m = 3. Gauss congruence `LG_qpow` (via `pw`, `pow_gauss`); `dwork`, `expCoeff_int_of_euler` copied
  from [`../A181316/A181316_mathlib.lean`](../A181316/A181316_mathlib.lean). `tools/leancheck-mathlib.sh`: OK, no
  warnings, axioms at most propext, Classical.choice, Quot.sound.
- [`certificate/check.py`](certificate/check.py): integral for q ≤ 5, m ≤ 3 (to x^10 or x^7); data match.
- Outside Lean: only the reading of exp(...) as its coefficient recurrence.

**Review level.** `lean-proof`.

**Prior art.** Fried, arXiv:2607.24832 (2026), Theorem 43 (case m = 2 earlier by P. Bala in A155200). Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones), so the Lean proof is new.
