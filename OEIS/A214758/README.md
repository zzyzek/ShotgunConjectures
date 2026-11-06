# OEIS A214758: Coman's midpoint claim for Carmichael numbers is false (46657)

**Source.** [A214758](https://oeis.org/A214758) (Carmichael numbers divisible by a smaller Carmichael number). Comment
by Marius Coman (Aug 2012): "Conjecture: A Carmichael number C1 can be written as C1 = (C2 + C3)/2, where C2 and C3
are also Carmichael numbers, only if both C1 and C3 are divisible by C2." Same entry, Charles R Greathouse IV
(Dec 08 2014): "Counterexample: 46657 = (29341 + 63973)/2." (OEIS text, CC BY-SA 4.0.)

**Result.** False. 46657 = 13·37·97, 29341 = 13·37·61, 63973 = 7·13·19·37 are Carmichael numbers,
2·46657 = 29341 + 63973, and neither 29341 nor 63973 divides 46657 (so swapping C2 and C3 does not help). Below 10⁶
there are 6 midpoint triples of Carmichael numbers and 5 of them are counterexamples; 46657 is the least C1.

**Evidence.**
- Lean (Mathlib + lib): [`A214758_mathlib.lean`](A214758_mathlib.lean), main `A214758_false`: ¬ ∀ C1 C2 C3,
  IsCarmichael C1 → IsCarmichael C2 → IsCarmichael C3 → 2*C1 = C2 + C3 → C2 ∣ C1 ∧ C2 ∣ C3 (Mathlib
  `Nat.IsCarmichael`, Korselt via lib `isCarmichael_of_factors`). Exit 0, no warnings; axioms propext,
  Classical.choice, Quot.sound; no `native_decide`.
- [`certificate/search.py`](certificate/search.py): all triples below 10⁶ (Korselt with sympy, 4 s).
- Outside Lean: minimality.

**Review level.** `lean-witness`.

**Prior art.** Known: Greathouse's comment (2014). Not in google-deepmind/formal-conjectures (clone 2026-11-05) or
otoi-lab/oeis-lean-proofs (clone 2026-10-13). Checked 2026-11-06.
